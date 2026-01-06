/* Copyright (c) 2026, Oracle and/or its affiliates.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License, version 2.0,
   as published by the Free Software Foundation.

   This program is designed to work with certain software (including
   but not limited to OpenSSL) that is licensed under separate terms,
   as designated in a particular file or component or in included license
   documentation.  The authors of MySQL hereby grant you an additional
   permission to link the program and your derivative works with the
   separately licensed software that they have either included with
   the program or referenced in the documentation.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License, version 2.0, for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301  USA */

#include "sql/sql_masking_policy.h"

#include <optional>
#include <span>
#include <string_view>
#include <utility>

#include "lex_string.h"
#include "my_inttypes.h"
#include "my_sys.h"
#include "mysql/components/my_service.h"
#include "mysql/components/service.h"
#include "mysql/components/services/mysql_string.h"
#include "mysql/components/services/object_policy_service.h"
#include "mysql/strings/m_ctype.h"
#include "mysqld_error.h"
#include "sql/auth/sql_security_ctx.h"
#include "sql/create_field.h"
#include "sql/derror.h"
#include "sql/enum_query_type.h"
#include "sql/field.h"
#include "sql/item.h"
#include "sql/item_cmpfunc.h"
#include "sql/item_func.h"
#include "sql/mysqld.h"
#include "sql/mysqld_cs.h"
#include "sql/sp.h"
#include "sql/sql_class.h"
#include "sql/sql_const.h"
#include "sql/sql_error.h"
#include "sql/table.h"
#include "sql_string.h"
#include "string_with_len.h"
#include "template_utils.h"

struct MEM_ROOT;

constexpr char kComponentUnavailable[] = "component is unavailable";
constexpr char kStringConversionFailed[] = "string conversion failed";
constexpr char kNoMessage[] = "(no message)";

static LEX_CSTRING make_lex_cstring(MEM_ROOT *root, const String &string) {
  const char *dup = string.dup(root);
  if (dup == nullptr) return NULL_CSTR;
  return {dup, string.length()};
}

/// Returns true if the two names are considered equal when they are used either
/// as masking policy names or as masking policy argument names.
static bool equal_names_for_masking_policy(std::string_view name1,
                                           std::string_view name2) {
  return my_strnncoll(system_charset_info,
                      pointer_cast<const uchar *>(name1.data()), name1.size(),
                      pointer_cast<const uchar *>(name2.data()),
                      name2.size()) == 0;
}

bool drop_masking_policy(THD *thd, LEX_CSTRING policy_name, bool if_exists) {
  my_service<SERVICE_TYPE(column_masking_policy_management)> service(
      "column_masking_policy_management", srv_registry);

  if (!service.is_valid()) {
    my_error(ER_MASKING_POLICY_COMPONENT_ERROR, MYF(0), kComponentUnavailable);
    return true;
  }

  String policy_name_buffer{policy_name.str, policy_name.length,
                            system_charset_info};
  String message_buffer;
  if (service->drop(thd, pointer_cast<my_h_string>(&policy_name_buffer),
                    pointer_cast<my_h_string>(&message_buffer)) != 0) {
    const char *message =
        message_buffer.is_empty() ? kNoMessage : message_buffer.c_ptr_safe();
    if (if_exists) {
      // We assume it failed because the policy did not exist, which should only
      // cause a note to be printed for DROP IF EXISTS, and no error is raised.
      // This is an assumption. It is the most likely reason why it fails here,
      // but we can't tell for sure.
      push_warning_printf(
          thd, Sql_condition::SL_NOTE, ER_MASKING_POLICY_COMPONENT_ERROR,
          ER_THD(thd, ER_MASKING_POLICY_COMPONENT_ERROR), message);
      return false;
    }
    my_error(ER_MASKING_POLICY_COMPONENT_ERROR, MYF(0), message);
    return true;
  }

  // TODO(khatlen): When DML support is added, make sure prepared statements
  // referencing the dropped masking policy are invalidated here.

  return false;
}

std::optional<Sql_masking_policy_spec> get_masking_policy_spec(
    THD *thd, LEX_CSTRING policy_name, std::string *reason) {
  my_service<SERVICE_TYPE(column_masking_policy_retrieval)> service(
      "column_masking_policy_retrieval", srv_registry);

  if (!service.is_valid()) {
    *reason = kComponentUnavailable;
    return {};
  }

  String policy_name_buffer{policy_name.str, policy_name.length,
                            system_charset_info};
  String expression;
  String argument_name;
  String extra_information;
  String message_buffer;
  if (service->get(thd, pointer_cast<my_h_string>(&policy_name_buffer),
                   pointer_cast<my_h_string>(&expression),
                   pointer_cast<my_h_string>(&argument_name),
                   pointer_cast<my_h_string>(&extra_information),
                   pointer_cast<my_h_string>(&message_buffer)) != 0) {
    *reason =
        message_buffer.is_empty() ? kNoMessage : to_string(message_buffer);
    return {};
  }

  Sql_masking_policy_spec spec{
      .policy_name = make_lex_cstring(thd->mem_root, policy_name_buffer),
      .masking_expression = make_lex_cstring(thd->mem_root, expression),
      .argument_name = make_lex_cstring(thd->mem_root, argument_name),
  };

  if (spec.policy_name.str == nullptr ||
      spec.masking_expression.str == nullptr ||
      spec.argument_name.str == nullptr) {
    *reason = kStringConversionFailed;
    return {};
  }

  return spec;
}

bool check_masking_policy_manage_privilege(THD *thd) {
  // Masking policy DDL requires the MANAGE_DATA_MASKING_POLICY privilege.
  if (!thd->security_context()
           ->has_global_grant(STRING_WITH_LEN("MANAGE_DATA_MASKING_POLICY"))
           .first) {
    my_error(ER_SPECIFIC_ACCESS_DENIED_ERROR, MYF(0),
             "MANAGE_DATA_MASKING_POLICY");
    return true;
  }
  return false;
}

bool create_masking_policy(THD *thd, bool if_not_exists,
                           const Sql_masking_policy_spec &spec) {
  if (std::string reason;
      if_not_exists &&
      get_masking_policy_spec(thd, spec.policy_name, &reason).has_value()) {
    push_warning_printf(
        thd, Sql_condition::SL_NOTE, ER_MASKING_POLICY_ALREADY_EXISTS,
        ER_THD(thd, ER_MASKING_POLICY_ALREADY_EXISTS), spec.policy_name.str);
    return false;
  }

  my_service<SERVICE_TYPE(column_masking_policy_management)> service(
      "column_masking_policy_management", srv_registry);
  if (!service.is_valid()) {
    my_error(ER_MASKING_POLICY_COMPONENT_ERROR, MYF(0), kComponentUnavailable);
    return true;
  }

  String policy_name_buffer{spec.policy_name.str, spec.policy_name.length,
                            system_charset_info};
  String expression{spec.masking_expression.str, spec.masking_expression.length,
                    &my_charset_utf8mb4_bin};
  String argument_name{spec.argument_name.str, spec.argument_name.length,
                       system_charset_info};
  String extra_information{"[]", 2, &my_charset_utf8mb4_bin};
  String message_buffer;
  if (service->create(thd, pointer_cast<my_h_string>(&policy_name_buffer),
                      /*replace=*/false, pointer_cast<my_h_string>(&expression),
                      pointer_cast<my_h_string>(&argument_name),
                      pointer_cast<my_h_string>(&extra_information),
                      pointer_cast<my_h_string>(&message_buffer)) != 0) {
    const char *message =
        message_buffer.is_empty() ? kNoMessage : message_buffer.c_ptr_safe();
    my_error(ER_MASKING_POLICY_COMPONENT_ERROR, MYF(0), message);
    return true;
  }

  return false;
}

/**
  Validates constraints for masking policy assignment on a column.
  Central checker for column-level eligibility: enforces the constraints listed
  under "Checked here" and enumerates related constraints validated elsewhere
  (with pointers), so this block is the canonical index of eligibility rules.

  Constraints checked here:
  - The column must not be a generated column.
  - For existing columns (create_field.field != nullptr), the column must not
    have a histogram.

  Constraints validated elsewhere:
  - The column must not be indexed. Checked in prepare_key_column().
  - The column must not be referenced by generated columns, functional indexes,
    DEFAULT value expressions or CHECK constraints. Checked by
    Item_field::check_function_as_value_generator().
  - The column must not be used by the table partitioning/subpartitioning
    function. This is enforced during partition function fixing in
    sql_partition.cc (fix_partition_func/create_partition_field_array), which
    raises ER_MASKING_POLICY_INCOMPATIBLE_COLUMN_FEATURE when a partition key
    references a masked column.

  @param create_field Create_field object for the column to validate
  @retval true  Validation failed, error was reported
  @retval false Validation succeeded
*/
static bool validate_masking_policy_column_constraints(
    const Create_field &create_field) {
  if (create_field.is_gcol()) {
    my_error(ER_UNSUPPORTED_ACTION_ON_GENERATED_COLUMN, MYF(0),
             "MASKING POLICY");
    return true;
  }

  // For an existing column (create_field.field != nullptr), also check that it
  // has no histogram.
  if (const Field *const field = create_field.field; field != nullptr) {
    if (field->table->find_histogram(field->field_index()) != nullptr) {
      my_error(ER_MASKING_POLICY_INCOMPATIBLE_COLUMN_FEATURE, MYF(0),
               field->field_name, "have a histogram");
      return true;
    }
  }

  return false;
}

bool check_masking_policy_name(LEX_CSTRING name) {
  // Use the same rules for policy names and their arguments as for stored
  // procedure names and their parameters.
  return sp_check_name(name);
}

static bool validate_masking_policy_gatekeeper(Item *gatekeeper_expr) {
  if (!is_function_of_type(gatekeeper_expr, Item_func::CURRENT_USER_IN_FUNC) &&
      !is_function_of_type(gatekeeper_expr, Item_func::CURRENT_ROLE_IN_FUNC)) {
    my_error(ER_MASKING_POLICY_INVALID_GATEKEEPER, MYF(0),
             "MASKING POLICY gatekeeper must be CURRENT_USER_IN or "
             "CURRENT_ROLE_IN.");
    return true;
  }

  Item_func *item_func = down_cast<Item_func *>(gatekeeper_expr);
  for (Item *arg : std::span{item_func->arguments(), item_func->arg_count}) {
    if (!arg->basic_const_item() || arg->type() != Item::STRING_ITEM) {
      my_error(ER_MASKING_POLICY_NON_LITERAL_GATEKEEPER_ARG, MYF(0));
      return true;
    }
  }

  return false;
}

/// The only column references allowed in a masking function are unqualified
/// names (no schema or table) that are equal to the policy's argument name.
static bool validate_policy_argument_reference(Item_field *field,
                                               LEX_CSTRING argument_name) {
  if (field->table_name != nullptr ||
      !equal_names_for_masking_policy(field->field_name,
                                      to_string_view(argument_name))) {
    my_error(ER_MASKING_POLICY_INVALID_COLUMN_REFERENCE, MYF(0),
             argument_name.str, field->full_name());
    return true;
  }
  return false;
}

/// Perform pre-resolving checks for the validity of the masking function:
///
/// - Must not reference other columns than the argument to the masking policy.
/// - Must return exactly one value.
/// - Must not use functions that are not allowed in a generated column
///   (exception: UDFs are allowed).
static bool validate_masking_function_syntax(THD *thd, Item *masking_func,
                                             LEX_CSTRING argument_name) {
  // Disallow all column references that do not reference the policy's argument.
  // The reference must be unqualified, since we have no table at this stage.
  if (WalkItem(masking_func, enum_walk::POSTFIX, [&](Item *item) {
        if (item->type() != Item::FIELD_ITEM) return false;
        return validate_policy_argument_reference(down_cast<Item_field *>(item),
                                                  argument_name);
      })) {
    return true;
  }

  if (masking_func->check_cols(1)) {
    return true;
  }

  /// Perform the generated column pre-resolving check, with exception for UDFs.
  Check_function_as_value_generator_parameters param{
      ER_MASKING_POLICY_DISALLOWED_CONSTRUCT, VGS_GENERATED_COLUMN};
  Item *disallowed_item = nullptr;
  WalkItem(masking_func, enum_walk::POSTFIX, [&](Item *item) {
    if (!is_function_of_type(item, Item_func::UDF_FUNC) &&
        item->check_function_as_value_generator(
            pointer_cast<uchar *>(&param))) {
      disallowed_item = item;
      return true;
    }
    return false;
  });
  if (disallowed_item != nullptr) {
    String name;
    if (param.banned_function_name != nullptr) {
      name = String{param.banned_function_name, system_charset_info};
    } else {
      disallowed_item->print(thd, &name, QT_ORDINARY);
    }
    my_error(ER_MASKING_POLICY_DISALLOWED_CONSTRUCT, MYF(0), name.c_ptr_safe());
    return true;
  }

  return false;
}

// Validate high-level structural restrictions for a masking policy expression.
// Returns true (with error) if validation fails.
bool validate_masking_policy_syntax(THD *thd, LEX_CSTRING argument_name,
                                    Item *expr) {
  if (!is_function_of_type(expr, Item_func::CASE_FUNC)) {
    my_error(ER_MASKING_POLICY_EXPECTS_CASE, MYF(0));
    return true;
  }

  Item_func_case *case_expr = down_cast<Item_func_case *>(expr);
  if (case_expr->get_first_expr_num() != -1) {
    my_error(ER_MASKING_POLICY_EXPECTS_CASE_WHEN, MYF(0));
    return true;
  }

  if (case_expr->get_else_expr_num() == -1) {
    my_error(ER_MASKING_POLICY_MISSING_ELSE, MYF(0));
    return true;
  }

  if (case_expr->arg_count != 3) {
    my_error(ER_MASKING_POLICY_ONE_WHEN_REQUIRED, MYF(0));
    return true;
  }

  if (validate_masking_policy_gatekeeper(case_expr->get_arg(0))) {
    return true;
  }

  Item *const then_expr = case_expr->get_arg(1);
  if (validate_masking_function_syntax(thd, then_expr, argument_name)) {
    return true;
  }

  Item *const else_expr = case_expr->get_arg(case_expr->get_else_expr_num());
  if (validate_masking_function_syntax(thd, else_expr, argument_name)) {
    return true;
  }

  // Either the THEN clause or the ELSE clause must be a reference to the
  // argument.
  if (then_expr->type() != Item::FIELD_ITEM &&
      else_expr->type() != Item::FIELD_ITEM) {
    my_error(ER_MASKING_POLICY_MUST_RETURN_ARGUMENT, MYF(0));
    return true;
  }

  return false;
}

// Validates masking policies for CREATE/ALTER TABLE.
bool validate_masking_policy_for_create_alter_table(const Create_field &field) {
  if (field.m_masking_policy_name.length == 0) return false;

  if (validate_masking_policy_column_constraints(field)) {
    return true;
  }

  // TODO: Validate that the policy expression resolves when assigned to this
  // column.

  return false;
}
