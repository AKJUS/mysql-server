/* Copyright (c) 2024, 2026, Oracle and/or its affiliates. */

#include "sql/json_duality_view/dml.h"

#include <algorithm>
#include <cstddef>
#include <cstdlib>
#include <memory>
#include <optional>
#include <ostream>
#include "scope_guard.h"
#include "sql/sql_error.h"

#include <version>
#ifdef __cpp_lib_source_location
#include <source_location>
#define SOURCE_LOCATION_CUR_FUNC std::source_location::current().function_name()
#else
#define SOURCE_LOCATION_CUR_FUNC ""
#endif /* __cpp_lib_source_location */
#include <concepts>
#include <ranges>
#include <type_traits>

#include "base64.h"
#include "field_types.h"
#include "mysql/strings/m_ctype.h"
#include "mysqld_error.h"
#include "sql-common/json_dom.h"
#include "sql/binlog.h"
#include "sql/debug_sync.h"
#include "sql/derror.h"
#include "sql/item_json_func.h"  //  get_json_wrapper()
#include "sql/json_duality_view/content_tree.h"
#include "sql/json_duality_view/utils.h"
#include "sql/parse_tree_nodes.h"
#include "sql/sql_class.h"
#include "sql/sql_data_change.h"
#include "sql/sql_insert.h"  // Sql_cmd_insert_base
#include "sql/sql_lex.h"
#include "sql/statement/statement.h"
#include "sql/table.h"
#include "sql_string.h"

namespace jdv {

/**
  Identity wrapper for types that does not require wrapping.

  @param arg error message argument to use as is

  @return arg passed in
*/
static decltype(auto) em_wrap(auto arg) { return arg; }

/**
  Overload which wraps string_views in strings which are
  guaranteed to be null-terminated.

  @param sv string view to wrap.

  @return string containing copy of argument
*/
static std::string em_wrap(std::string_view sv) {
  return {sv.data(), sv.size()};
}

/**
  Overload which wraps Json_paths in strings, after first
  creating string representation in String buffer. This allows
  passing Json_paths directly to error message function as
  const char *without having to worry about ownership.

  @param jp Json_path to wrap
  @return std:string containing the string representation of the path
*/
static std::string em_wrap(const Json_path &jp) {
  String buf;
  jp.to_string(&buf);
  return {buf.ptr(), buf.length()};
}

/**
  Identity unwrapper.

  @param arg argument to return
  @return argument passed in
*/
static decltype(auto) em_unwrap(auto arg) { return arg; }

/**
  Overload which unwraps strings by calling c_str()-

  @param str string to call c_str() on
  @return c-string from string
*/
static const char *em_unwrap(const std::string &str) { return str.c_str(); }

/**
  Wraps calls to my_error() unwrapping wrapped arguments.

  @tparam CODE error code to report
  @param args_to_wrap arguments for format specifiers in error message
 */
template <int CODE, typename... Args>
static void my_jdv_error(Args... args_to_wrap) {
  [](const auto &...wrapped_args) {
    my_error(CODE, MYF(0), em_unwrap(wrapped_args)...);
  }(em_wrap(std::forward<Args>(args_to_wrap))...);
}

static constexpr std::string_view metadatakey = "_metadata";
static constexpr std::string_view etagkey = "etag";

/** Comparator which orders in the same way as Json_object orders its keys. */
struct Size_first_comparator {
  template <typename RA, typename RB>
    requires std::ranges::contiguous_range<RA> &&
             std::ranges::contiguous_range<RB> &&
             std::is_same_v<std::ranges::range_value_t<RA>,
                            std::ranges::range_value_t<RB>>
  constexpr bool operator()(RA &&ra, RB &&rb) const {
    auto sra = std::ranges::size(ra);
    auto srb = std::ranges::size(rb);
    return sra != srb
               ? sra < srb
               : std::memcmp(std::ranges::data(std::forward<RA>(ra)),
                             std::ranges::data(std::forward<RB>(rb)),
                             sra * sizeof(std::ranges::range_value_t<RA>)) < 0;
  }
};
constexpr Size_first_comparator size_less;

template <typename JSON_TYPE>
struct Json_type_traits;

template <>
struct Json_type_traits<Json_object> {
  static constexpr enum_json_type jt = enum_json_type::J_OBJECT;
  static constexpr std::string_view name = "Json_object";
};

template <>
struct Json_type_traits<Json_array> {
  static constexpr enum_json_type jt = enum_json_type::J_ARRAY;
  static constexpr std::string_view name = "Json_array";
};

/**
  Inspects an assumed valid Json_dom (typically an exising value in UPDATE).
  Returns nullptr if the argument is nullptr or has type J_NULL. Otherwise
  returns the dom cast JT*. Asserts if the type is not JT.

  @tparam JT the expected actual type of the argument
  @param valid_dom assumed valid Json_dom
  @return the dom cast to the expectd type or nullptr
 */
template <typename JT>
static JT *inspect_valid_dom(Json_dom *valid_dom) {
  if (valid_dom == nullptr) {
    return nullptr;
  }

  enum_json_type vjt = valid_dom->json_type();
  if (vjt == enum_json_type::J_NULL) {
    return nullptr;
  }
  assert(vjt == Json_type_traits<JT>::jt);

  return static_cast<JT *>(valid_dom);
}

/**
  Inspects a Json_dom which may or may not have the expected type and may also
  be nullptr, (typically a value provided as user input). Returns
  {J_NULL,nullptr} if the argument is nullptr or has type J_NULL. Returns
  {J_ERROR, nullptr} if the argument does not have type JT. Otherwise returns
  {enum_json_type of JT, argument cast to JT*}.

  @tparam JT the expected actual type of the argument
  @param dom dom that may not have the expected type
  @return pair of actual json type enum value and the argument cast to JT* or
  nullptr
 */
template <typename JT>
static std::pair<enum_json_type, JT *> inspect_dom(Json_dom *dom) {
  if (dom == nullptr) {
    return {enum_json_type::J_NULL, nullptr};
  }
  enum_json_type jt = dom->json_type();
  if (jt == enum_json_type::J_NULL) {
    return {jt, nullptr};
  }
  if (jt != Json_type_traits<JT>::jt) {
    return {enum_json_type::J_ERROR, nullptr};
  }
  return {jt, static_cast<JT *>(dom)};
}

/**
  Formats a Json_wrapper as string for debugging.

  @param jw Json_wrapper to format
  @return string containing formatted representation
 */
static std::string json_wrapper_to_string(const Json_wrapper &jw) {
  String pretty;
  if (jw.to_pretty_string(&pretty, "json_wrapper_to_string",
                          JsonDepthErrorHandler)) {
    return "<Failed to format Json_value as pretty string>";
  }
  return to_string(pretty);
}

/**
  Formats a Json_dom as string for debugging.

  @param jdom Json_dom to format
  @return string containing formatted representation
 */
static std::string json_dom_to_string(Json_dom *jdom) {
  if (jdom == nullptr) {
    return "Json_dom{nullptr}";
  }
  return json_wrapper_to_string(Json_wrapper{jdom, true});
}

/**
  Predicate to determine if a dom represents a void value i.e.
  that either the pointer itself is nullptr, or that the dom has
  enum_json_type::J_NULL.

  @param jdom dom to check
  @return true if represents a void value
 */
static bool represents_NULL(Json_dom *jdom) {
  return jdom == nullptr || jdom->json_type() == enum_json_type::J_NULL;
}

/**
 Convenience wrapper predicate which returns true for AUTO_INCREMENT columns.

 @param fld column to report for.

 @return true if column is AUTO_INCREMENT
*/
static bool is_auto_increment(const Field &fld) {
  return (fld.auto_flags & Field::NEXT_NUMBER) != 0;
}

/**
  Compares Json_dom pointers which may be nullptr by considering nullptrs to be
  greater than all non-nullptr values. This convention is chosen so that
  sorting with {compare_doms(a,b) < 0} places nullptr entries last (the
  assumption being that searches into the sorted range most often are for
  a non-nullptr elements).

  @param ajd lhs
  @param bjd rhs

  @return -1,0,1 for less, equal, greater.
*/
static int compare_doms(Json_dom *ajd, Json_dom *bjd) {
  if (ajd != nullptr && bjd != nullptr) {
    return Json_wrapper{ajd, true}.compare(Json_wrapper{bjd, true});
  }
  if (ajd == nullptr && bjd == nullptr) {
    return 0;
  }

  return bjd == nullptr ? -1 : 1;
}

/**
  Predicate to determine if json dom is expected to be base64 encoded based on
  SQL type and charset-

  @param ft actual field type
  @param csi character set object

  @return true if json dom is expected to be base64 encooded
*/
[[nodiscard]] static bool expect_b64_dom(enum_field_types ft,
                                         const CHARSET_INFO &csi) {
  bool bin_csi = (&csi == &my_charset_bin);
  switch (ft) {
    case MYSQL_TYPE_BIT:
      return true;

    case MYSQL_TYPE_BLOB:
    case MYSQL_TYPE_LONG_BLOB:
    case MYSQL_TYPE_MEDIUM_BLOB:
    case MYSQL_TYPE_TINY_BLOB:
      DBUG_LOG("jdv_dml",
               " ft:" << ft << " bin_cs:" << bin_csi << " returns " << bin_csi);
      return bin_csi;

    case MYSQL_TYPE_VAR_STRING:
    case MYSQL_TYPE_VARCHAR:
    case MYSQL_TYPE_ENUM:
    case MYSQL_TYPE_SET:
    case MYSQL_TYPE_STRING: {
      DBUG_LOG("jdv_dml",
               " ft:" << ft << " bin_csi:" << bin_csi
                      << " ci.mbminlen:" << csi.mbminlen
                      << " returns: " << (bin_csi || csi.mbminlen > 1));
      return (bin_csi || csi.mbminlen > 1);
    }

    default:
      return false;
  }
}

/**
  Predicate to determine if base column expects json values to be base64
  encoded.

  @param kci base table column

  @return true if column expects json values to be base64 encooded
*/
[[nodiscard]] static bool col_expects_b64(const Key_column_info &kci) {
  return expect_b64_dom(kci.field()->type(), *kci.field()->charset());
}

static constexpr std::string_view TYPE_HEADER_PREFIX = "base64:type";
static constexpr std::size_t TYPE_HEADER_MAXSZ =
    TYPE_HEADER_PREFIX.size() + 4;  // 3 digits and :

static constexpr auto ERROR_INDICATOR = static_cast<std::size_t>(-1);

/**
  Converts base64 string to its binary representation, escapes this to be
  a string literal, wraps in single quotes, prepends character
  set introducer _binary before appending to statement.
  Checks to see if input is valid base64.

  @param sbufp statement buffer
  @param buf string representation of dom
  @param jd dom (for error reporting)

  @return true in case of errors
*/
[[nodiscard]] static bool append_b64_dom(std::string *sbufp, const String &buf,
                                         Json_dom *jd) {
  // Assume to_string() value inside buf is base64-encoded with metadata type
  // header (as if returned by select).
  const auto type_header =
      std::string_view(buf.ptr(), std::min(TYPE_HEADER_MAXSZ, buf.length()));

  if (!type_header.starts_with(TYPE_HEADER_PREFIX)) {
    my_jdv_error<ER_JDV_INVALID_BINARY_TYPE_HEADER>(jd->get_location());
    return true;
  }

  auto type_header_last = type_header.find(':', TYPE_HEADER_PREFIX.size());
  if (type_header_last == std::string_view::npos) {
    my_jdv_error<ER_JDV_INVALID_BINARY_TYPE_HEADER>(jd->get_location());
    return true;
  }
  assert(type_header_last <= TYPE_HEADER_PREFIX.size() + 3);
  const auto bv = std::string_view(buf.ptr(), buf.length());
  const auto b64_payload =
      std::string_view(bv.begin() + type_header_last + 1, bv.end());

  auto decode_needed_size = base64_needed_decoded_length(b64_payload.size());
  char *decode_buf =
      current_thd->mem_root->ArrayAlloc<char>(decode_needed_size);
  if (decode_buf == nullptr) {
    return true;
  }
  auto decode_resulting_size = base64_decode(
      b64_payload.data(), b64_payload.size(), decode_buf, nullptr, 0);

  if (decode_resulting_size == -1) {
    my_jdv_error<ER_BASE64_DECODE_ERROR>();
    return true;
  }

  sbufp->append("_binary '");

  std::size_t sbuf_existing_size = sbufp->size();
  // *2 is worst-case when every byte must be escaped
  auto escape_needed_size = decode_resulting_size * 2;

  sbufp->resize(sbufp->size() + escape_needed_size);
  char *escape_dst = sbufp->data() + sbuf_existing_size;
  auto escape_resulting_size =
      escape_string_for_mysql(&my_charset_bin, escape_dst, escape_needed_size,
                              decode_buf, decode_resulting_size);

  if (escape_resulting_size == ERROR_INDICATOR) {
    assert(false);  // Only fails if buffer is too small - not expected.
    my_jdv_error<ER_BASE64_DECODE_ERROR>();
    return true;
  }
  sbufp->resize(sbuf_existing_size + escape_resulting_size);
  sbufp->append(1, '\'');
  DBUG_LOG("jdv_dml",
           "escape_resulting_size:" << escape_resulting_size
                                    << " b64 decoded string literal: "
                                    << sbufp->substr(sbuf_existing_size));
  return false;
}

/**
  Append a Json_dom to a string. If the Json_dom pointer is nullptr 'DEFAULT' is
  appended. If the json type is J_NULL, 'NULL' is appended. For numeric values
  the bare to_string value is appended. For other non-base64 types the
  to_string value is quote escaped and wrapped in single quotes with the
  character set introducer _utf8mb4.

  If the base table column returns values as base64 the raw string
  representation of the dom is expected to be a type header followed by a
  base64 encoded payload. This is handled by append_b64_dom().

  @param sbufp statement buffer
  @param jd dom to convert to string and append
  @param b64 true if resulting string is expected to be base64 encoded
  @return true if error
 */
[[nodiscard]] static bool append_json_dom(std::string *sbufp, Json_dom *jd,
                                          bool b64 = false) {
  assert(sbufp != nullptr);
  std::string &sbuf = *sbufp;
  if (jd == nullptr) {
    sbuf.append("DEFAULT");
    return false;
  }

  Json_wrapper jw{jd, true};
  String buf;
  jw.to_string(&buf, false, "", []() {});
  DBUG_LOG("jdv_dml",
           "jw(jd).to_string():'" << buf.c_ptr_safe() << "', b64:" << b64);

  switch (jd->json_type()) {
    case enum_json_type::J_DECIMAL:
    case enum_json_type::J_INT:
    case enum_json_type::J_UINT:
    case enum_json_type::J_DOUBLE:
    case enum_json_type::J_BOOLEAN:
      sbuf.append(buf.ptr(), buf.length());
      break;
    case enum_json_type::J_NULL:
      sbuf.append("NULL");
      break;

    case enum_json_type::J_STRING:
    case enum_json_type::J_OPAQUE:
      if (b64) {
        return append_b64_dom(&sbuf, buf, jd);
      }
      [[fallthrough]];
    case enum_json_type::J_DATE:
    case enum_json_type::J_TIME:
    case enum_json_type::J_DATETIME:
    case enum_json_type::J_TIMESTAMP:
    case enum_json_type::J_OBJECT:
    case enum_json_type::J_ARRAY: {
      sbuf.append("_utf8mb4 '");
      auto cur_size = sbuf.size();
      std::size_t bytes_generated = ERROR_INDICATOR;
      for (sbuf.resize(cur_size + 1);
           (bytes_generated = escape_string_for_mysql(
                &my_charset_utf8mb4_bin, &sbuf.front() + cur_size,
                sbuf.size() - cur_size, buf.ptr(), buf.length())) ==
           ERROR_INDICATOR;
           sbuf.resize((sbuf.size() * 2) - cur_size)) {
      }
      sbuf.resize(cur_size + bytes_generated);
      sbuf.append(1, '\'');
      break;
    }

    // These are not expected
    case enum_json_type::J_ERROR:
    default:
      assert(false);
      my_jdv_error<ER_JDV_UNEXPECTED_JSON_TYPE>(jd->get_location(), "Unknown");
      return true;
      break;
  }
  return false;
}

/**
  Sets up the environment for using Regular_statement_handle
  for JDVs. The creation and usage of
  the Regular_statement_handle is done in the callable F passed
  in which returns true to indicate errors. The caller DA is passed as an
  argument to F. The callable f is responsible for copying
  information back to caller_da if/when needed.

  @param thd THD
  @param f callable to invoke

  @return value of f
*/
[[nodiscard]] static bool do_in_substatement_context(THD *thd, auto &&f) {
  bool ret_val = false;

  Diagnostics_area *caller_da = thd->get_stmt_da();
  Diagnostics_area da(false);
  thd->push_diagnostics_area(&da);

  // Stores state before sub-statement execution.
  Open_tables_backup open_tables_state_backup;
  thd->reset_n_backup_open_tables_state(&open_tables_state_backup, 0);

  // Backup current item list.
  Item *saved_item_list = thd->item_list();
  thd->reset_item_list();

  /*
     This is needed to indicate statements are sub-statements. Statements access
     tables and acquire locks for which connection already has MDL locks. So
     executing statement should be safe with this. Also statements are executed
     under main transaction and committed/rolled back as part of main
     transaction only (which is not possible with rw_transaction).
  */
  Sub_statement_state statement_state;
  thd->reset_sub_statement_state(&statement_state, SUB_STMT_DUALITY_VIEW);

  ret_val = f(caller_da);

  thd->restore_sub_statement_state(&statement_state);

  // Restore item list state.
  thd->free_items();
  thd->set_item_list(saved_item_list);

  if (ret_val) {
    caller_da->set_error_status(thd->get_stmt_da()->mysql_errno(),
                                thd->get_stmt_da()->message_text(),
                                thd->get_stmt_da()->returned_sqlstate());
  }
  thd->pop_diagnostics_area();

  /*
     Restore table open state only.
     We can not invoke "restore_backup_open_tables_state" here.It will
     release even MDL locks. MDL locks acquired by INSERT on v1 and base
     tables is same. Releasing MDL locks here will release lock acquired
     on base tables too. So only table state is restored here.
  */
  thd->set_open_tables_state(&open_tables_state_backup);
  return ret_val;
}

/**
  Convenience function for obtaining the member of a Json_object.
  Returns nullptr if the Json_object argument is nullptr or does not
  have the requested key.
 */
static Json_dom *get_val(const Json_object *jo, std::string_view k) {
  return jo == nullptr ? nullptr : jo->get(k);
}

/**
  Holds the resolved values for a row of a base table. Index in vector
  corresponds to index of columns in content tree node.
 */
struct Resolve_row {
  Resolve_row *parent = nullptr;
  std::vector<std::pair<std::string_view, Json_dom *>> columns;
};

template <typename BIN>
static int compare_bindings(const BIN &a, const BIN &b);
/**
  Binds a single Json_object and a jdv::Content_tree_node.
  Single_object_binding is used for INSERT and DELETE operations
  on JSON duality view.
 */
struct Single_object_binding {
  Json_object *bound_object = nullptr;
  const Content_tree_node *ct_node = nullptr;
  std::unique_ptr<Resolve_row> resolve_row;

  int operator<=>(const Single_object_binding &other) const {
    return compare_bindings(*this, other);
  }

  // Equality is only determined by the Content_tree pointer and the primary key
  // value, but compare_bindings() still defined an order for objects which are
  // equal according to this definition. So operator<=>(that) == 0 implies
  // equality, but the converse is not true. Note that operator==() is only
  // generated from a defaulted operator<=>(). The justfication for this seems
  // to be that with a custom operator<=>() the struct typically would benefit
  // from having a customized operator==() since equality-comparison often can
  // be done cheaper than relying on operator<=>().
  bool operator==(const Single_object_binding &that) const {
    bool eq =
        (ct_node == that.ct_node &&
         compare_doms(
             resolve_row->columns[ct_node->primary_key_column_index()].second,
             that.resolve_row->columns[that.ct_node->primary_key_column_index()]
                 .second) == 0);
    assert(operator<=>(that) != 0 || eq);
    return eq;
  }
  [[nodiscard]] bool is_empty() const { return bound_object == nullptr; }
  void set_empty() { bound_object = nullptr; }
};
static_assert(std::totally_ordered<Single_object_binding>);

struct Two_object_binding;
static Json_dom *get_pk_dom(const Two_object_binding &);

/**
  Binds two Json_objects (existing_object and new_object) and a
  jdv::Content_tree_node.
  Two_object_binding is used for UPDATE operations on duality view.
 */
struct Two_object_binding {
  Json_object *bound_object = nullptr;
  Json_object *existing_object = nullptr;
  const Content_tree_node *ct_node = nullptr;
  std::unique_ptr<Resolve_row> resolve_row;

  int operator<=>(const Two_object_binding &other) const {
    return compare_bindings(*this, other);
  }

  // Equality is only determined by the Content_tree pointer and the primary key
  // value, but compare_bindings() still defined an order for objects which are
  // equal according to this definition. So operator<=>(that) == 0 implies
  // equality, but the converse is not true. Note that operator==() is only
  // generated from a defaulted operator<=>(). The justfication for this seems
  // to be that with a custom operator<=>() the struct typically would benefit
  // from having a customized operator==() since equality-comparison often can
  // be done cheaper than relying on operator<=>().
  bool operator==(const Two_object_binding &that) const {
    bool eq = (ct_node == that.ct_node &&
               compare_doms(get_pk_dom(*this), get_pk_dom(that)) == 0);
    assert(operator<=>(that) != 0 || eq);
    return eq;
  }

  [[nodiscard]] bool is_empty() const {
    return existing_object == nullptr && bound_object == nullptr;
  }
  void set_empty() {
    existing_object = nullptr;
    bound_object = nullptr;
  }
};
static_assert(std::totally_ordered<Two_object_binding>);

/**
  Convenince function which returns the TABLE_SHARE* for the binding.

  @param bin binding
  @return TABLE_SHARE* for the binding
 */
[[nodiscard]] static const TABLE_SHARE *get_share(const auto &bin) {
  return bin.ct_node->table_ref()->table->s;
}

/**
  Convenince function which returns a reference to the
  Resolve_row's column vector.

  @param bin binding
  @return reference to vector of resolved columns
 */
[[nodiscard]] static const decltype(Resolve_row::columns) &get_resolve_columns(
    const auto &bin) {
  return bin.resolve_row->columns;
}

/**
  Goes through the input json (bound_object) and uses the join condition to
  infer column values which are not provided explicitly. Reports error if the
  values provided in the input does not match what is expressed by the join
  condition.

  @param bindings vector of bindings
  @return true if error
  */
[[nodiscard]] static bool resolve_columns(const auto &bindings) {
  // Populate Resolve_row with values provided directly by json document
  DBUG_LOG("jdv_dml", "DML-RESOLVE: " << SOURCE_LOCATION_CUR_FUNC);
  for (const auto &bin : bindings) {
    DBUG_LOG("jdv_dml", "Node '" << bin.ct_node->name() << "': "
                                 << bin.ct_node->quoted_qualified_table_name()
                                 << "(");
    for ([[maybe_unused]] auto &col : bin.ct_node->key_column_info_list()) {
      DBUG_LOG("jdv_dml", col.column_name() << ",");
    }
    if (bin.bound_object == nullptr) {
      continue;
    }

    auto &columns = bin.resolve_row->columns;
    for (auto &col : bin.ct_node->key_column_info_list()) {
      // For non-projected columns an empty string_view is stored for the key
      columns.emplace_back(col.column_name(),
                           get_val(bin.bound_object, col.key()));
    }
  }

  // Look for resolving opportunities in join conditions
  // Outer loop ensures that resolving opportunities in earlier bindings
  // which are made possible by the current iteration can also be discovered
  for (bool restart = true; restart;) {
    restart = false;
    for (const auto &bin : bindings) {
      // Note that in the case of update we sometimes have to create separate
      // "half-bindings", one for the logical delete and one for the logical
      // insert of the update, (this is necessary because it generally is not
      // possible to match the before and after Json_dom using primary key
      // until after resloving is done). The half-binding for the logical
      // delete will only have an existing object and so bin.bound_object ==
      // nullptr for them.
      if (bin.bound_object == nullptr) {
        continue;
      }
      assert(bin.resolve_row->columns.size() ==
             bin.ct_node->key_column_info_list().size());
      DBUG_LOG("jdv_dml",
               "bin.bound_object: " << bin.bound_object
                                    << " bin->resolve_row->columns.empty():"
                                    << bin.resolve_row->columns.empty());
      if (bin.ct_node->has_join_condition()) {
        auto cix = bin.ct_node->join_column_index();
        auto pix = bin.ct_node->parent_join_column_index();
        auto &[child_col, child_val] = bin.resolve_row->columns[cix];
        auto &[parent_col, parent_val] = bin.resolve_row->parent->columns[pix];

        if (child_val != nullptr && parent_val == nullptr) {
          // resolve parent column from our column
          parent_val = child_val;
          restart = true;
          DBUG_LOG("jdv_dml", "DML-RESOLVE: Resolved "
                                  << parent_col << "(" << pix << ") in "
                                  << bin.ct_node->parent()->name() << " from "
                                  << child_col << "(" << cix << ") in "
                                  << bin.ct_node->name());
          continue;
        }
        if (child_val == nullptr && parent_val != nullptr) {
          // resolve our column from parent column
          child_val = parent_val;
          restart = true;
          DBUG_LOG("jdv_dml", "DML-RESOLVE: Resolved "
                                  << child_col << "(" << cix << ") in "
                                  << bin.ct_node->name() << " from "
                                  << parent_col << "(" << pix << ") in "
                                  << bin.ct_node->parent()->name());
        }
      }
    }
  }

  // Check that resolved values are valid and consistent
  // (no PK values are missing and values used in join conditions match)
  for (const auto &bin : bindings) {
    if (bin.bound_object == nullptr) {
      continue;
    }
    assert(bin.resolve_row->columns.size() ==
           bin.ct_node->key_column_info_list().size());

    auto &columns = bin.resolve_row->columns;
    const auto &pkc = bin.ct_node->primary_key_column();
    if (bin.bound_object != nullptr &&
        represents_NULL(
            columns[bin.ct_node->primary_key_column_index()].second)) {
      my_jdv_error<ER_JDV_PRIMARY_KEY_MUST_BE_PROVIDED>(
          bin.ct_node->quoted_qualified_table_name(), pkc.column_name(),
          bin.bound_object->get_location(), pkc.key());
      return true;
    }

    if (bin.ct_node->has_join_condition()) {
      auto cix = bin.ct_node->join_column_index();
      auto pix = bin.ct_node->parent_join_column_index();

      auto &[child_col, child_val] = bin.resolve_row->columns[cix];
      auto &[parent_col, parent_val] = bin.resolve_row->parent->columns[pix];

      if (represents_NULL(child_val) || represents_NULL(parent_val) ||
          compare_doms(child_val, parent_val) != 0) {
        DBUG_LOG("jdv_dml", "bin.bound_object:" << bin.bound_object);
        const auto &jci = bin.ct_node->join_column_info();
        const auto &pjci = bin.ct_node->parent_join_column_info();
        my_jdv_error<ER_JDV_JOIN_CONDITION_NOT_SATISFIED>(
            child_val->get_location(),
            bin.ct_node->quoted_qualified_table_name(), jci.column_name(),
            parent_val->get_location(),
            bin.ct_node->parent()->quoted_qualified_table_name(),
            pjci.column_name());
        return true;
      }
    }
  }
  return false;
}

/**
  Returns the resolved pk value for a Single_object binding.

  @param bin binding to get pk dom for
  @return dom representing PK
 */
static Json_dom *get_pk_dom(const Single_object_binding &bin) {
  auto pk_col_idx = bin.ct_node->primary_key_column_index();
  return bin.resolve_row->columns[pk_col_idx].second;
}

/**
  Returns either the existing or the resolved pk value for a Two_object_binding.
  @param bin binding to get pk dom for
  @return dom representing PK
 */
static Json_dom *get_pk_dom(const Two_object_binding &bin) {
  if (bin.bound_object == nullptr) {
    assert(bin.existing_object != nullptr);
    return bin.existing_object->get(bin.ct_node->primary_key_column().key());
  }

  return bin.resolve_row->columns[bin.ct_node->primary_key_column_index()]
      .second;
}

/**
  Returns the resolved pk value for a binding (even if bound_object
  is nullptr).
  @param bin binding to get resolved pk dom for
  @return dom representing resolved PK
 */
static Json_dom *get_resolved_pk_dom(const auto &bin) {
  assert(bin.resolve_row);
  assert(!bin.resolve_row->columns.empty());
  return bin.resolve_row->columns[bin.ct_node->primary_key_column_index()]
      .second;
}

/**
  Compares bindings based on:
   - fk_dep_weight,
   - jdv::Content_tree_node pointer value,
   - resolved primary key value
   Sorting with this comparator < 0 orders bindings so that inserts don't
  violate fk-constraints, and groups statements for the same SO ordered by pk so
   that duplicates can be found and removed.

   - In addition to this it is necessary to maintain a predictable order also
   for bindings with the same primary key value, so that half-bindings (bindings
   which have either only the existing or only the bound object) can be
   correctly merged, and duplicates in user input identified.

  @param abin lhs
  @param bbin rhs

  @return -1,0,1 for less, equal, greater.
  */
template <typename BIN>
static int compare_bindings(const BIN &abin, const BIN &bbin) {
  if (abin.ct_node->dependency_weight() < bbin.ct_node->dependency_weight()) {
    return -1;
  }
  if (abin.ct_node->dependency_weight() > bbin.ct_node->dependency_weight()) {
    return 1;
  }
  assert(abin.ct_node->dependency_weight() ==
         bbin.ct_node->dependency_weight());

  // Need a predictable order of ct nodes which have the same weight
  if (abin.ct_node < bbin.ct_node) {
    return -1;
  }
  if (abin.ct_node > bbin.ct_node) {
    return 1;
  }
  // Multiple bindings can reference the same ct_node for nested, for singleton
  // decendants of nested
  assert(abin.ct_node == bbin.ct_node);

  Json_dom *apk = get_pk_dom(abin);
  assert(apk != nullptr);
  Json_dom *bpk = get_pk_dom(bbin);
  assert(bpk != nullptr);
  int cd = compare_doms(apk, bpk);
  if (cd != 0) {
    return cd;
  }
  // PK values compare equal (this is the case whenever there
  // are separate bindings for existing and updated object).
  // Need a predictable order also of bindings which have the same pk-value.
  // Sort existing_object bindings before bound_object bindings (there can be
  // duplicate bound_object bindings)
  if (abin.bound_object == nullptr && bbin.bound_object != nullptr) {
    return -1;
  }
  if (abin.bound_object != nullptr && bbin.bound_object == nullptr) {
    return 1;
  }
  return 0;
}

#define RFL(x) #x << ":" << (em_wrap(x)) << " "
/**
  Creates an index over the bindings sorted on
  TABLE_SHARE* and pk-dom value. Verifies that duplicates
  are identical for all columns and marks it as empty.
  Otherwise reports error.

  @param bindings bindings vector
  @return true if error
*/
template <typename BV>
[[nodiscard]] static bool check_for_share_pk_duplicates(BV &bindings) {
  // Need to create an index over the bindings which is sorted just on share and
  // pk to find all duplicates even if they reference different
  // Content_tree_nodes.
  std::vector<typename BV::pointer> bound_index;
  bound_index.reserve(bindings.size());
  for (auto &b : bindings) {
    if (b.bound_object == nullptr) {
      continue;
    }
    bound_index.push_back(&b);
  }

  auto cmp_share_pk = [](const auto *a, const auto *b) {
    const TABLE_SHARE *a_s = get_share(*a);
    const TABLE_SHARE *b_s = get_share(*b);
    if (a_s != b_s) {
      return a_s < b_s ? -1 : 1;
    }

    // If they, in fact reference the same table, these should be the same
    assert(a->ct_node->primary_key_column_index() ==
           b->ct_node->primary_key_column_index());
    assert(get_resolved_pk_dom(*a) != nullptr);
    assert(get_resolved_pk_dom(*b) != nullptr);
    return compare_doms(get_resolved_pk_dom(*a), get_resolved_pk_dom(*b));
  };
  std::ranges::sort(bound_index, [&](const auto *a, const auto *b) {
    int c = cmp_share_pk(a, b);
    return c != 0 ? c < 0
                  : em_wrap(get_resolved_pk_dom(*a)->get_location()) <
                        em_wrap(get_resolved_pk_dom(*b)->get_location());
  });
  // Loop over the index - examining each range of share-pk duplicates in turn
  for (auto eqit = bound_index.begin(); eqit != bound_index.end();) {
    auto eqr = std::ranges::equal_range(
        bound_index, *eqit,
        [&](const auto *a, const auto *b) { return cmp_share_pk(a, b) < 0; });
    const auto &cur = *eqr.front();
    const auto &cur_cols = get_resolve_columns(cur);

    DBUG_LOG("jdv_dml", "DML-DUP-CHECK2: On share@"
                            << get_share(cur)
                            << ", pk:" << json_dom_to_string(get_pk_dom(cur))
                            << " " << RFL(get_pk_dom(cur)->get_location()));

    // Loop over all those that have the same share-pk as the first,
    // and verify that all column values are identical
    for (auto *np : eqr | std::ranges::views::drop(1)) {
      auto &nxt = *np;
      const auto &nxt_cols = get_resolve_columns(nxt);

      DBUG_LOG("jdv_dml", "DML-DUP-CHECK2: Duplicate from: "
                              << nxt.ct_node->name() << ", "
                              << nxt.ct_node->table_ref()->table_name << ", "
                              << nxt.ct_node->table_ref()->alias << " "
                              << RFL(get_pk_dom(*np)->get_location()));

      // run mismatch to see if any columns have a different value
      auto mmr = std::ranges::mismatch(
          cur_cols, nxt_cols, [](const auto &a, const auto &b) {
            return compare_doms(a.second, b.second) == 0;
          });

      if (mmr.in1 != cur_cols.end()) {
        DBUG_LOG("jdv_dml",
                 "DML-DUP-CHECK2: Invalid duplicate from: "
                     << nxt.ct_node->name() << ", "
                     << nxt.ct_node->table_ref()->table_name << ", "
                     << nxt.ct_node->table_ref()->alias
                     << ", offending column: " << mmr.in1->first << ", values ("
                     << json_dom_to_string(mmr.in1->second) << " vs. "
                     << json_dom_to_string(mmr.in2->second) << ")");

        my_jdv_error<ER_JDV_PK_DUPLICATES_NOT_IDENTICAL>(
            nxt.bound_object->get_location(),
            cur.ct_node->quoted_qualified_table_name(),
            nxt_cols[nxt.ct_node->primary_key_column_index()].first,
            mmr.in1->first, mmr.in2->second->get_location(),
            mmr.in1->second->get_location());
        return true;
      }
      nxt.set_empty();
    }
    eqit = eqr.end();
  }
  return false;
}

/**
  Merges bindings for existing and input rows when doing UPDATE. This cannot
  be done when binding as the pk value for the input row may not known until
  after resolving.

  @param bindings vector of binding to merge
 */
static void merge_bindings_for_update(
    std::vector<Two_object_binding> &bindings) {
  assert(std::ranges::is_sorted(bindings));

  // Look for adjacent same-pk bindings.
  // We need to copy exiting_object from "delete" binding to "insert" binding to
  // create an "update" binding.
  for (auto adjit = std::ranges::adjacent_find(bindings);
       adjit != bindings.end();
       adjit = std::ranges::adjacent_find(adjit + 1, bindings.end())) {
    Two_object_binding &cur = *adjit;
    Two_object_binding &nxt = *(adjit + 1);
    DBUG_LOG(
        "jdv_dml",
        "cur.(bound_object:"
            << cur.bound_object << " .existing_object:" << cur.existing_object
            << " .ct_node->type:" << (int)cur.ct_node->type()
            << " .qtn:" << cur.ct_node->quoted_qualified_table_name()
            << "), nxt.(bound_object:" << nxt.bound_object
            << " .existing_object:" << nxt.existing_object
            << " .ct_node->type:" << (int)nxt.ct_node->type()
            << " .qtn:" << nxt.ct_node->quoted_qualified_table_name() << ")");

    if (cur.existing_object == nullptr) {
      // Nothing to merge
      continue;
    }
    if (nxt.existing_object != nullptr) {
      // Existing/input duplicate - can not happen directly in array_agg but if
      // different array_aggs element reference same subobject
      cur.existing_object = nullptr;
      assert(cur.bound_object == nullptr);
      continue;
    }

    // We are not guaranteed that cur is the "delete"-binding, since there
    // may be duplicate "insert" bindings
    assert(nxt.existing_object == nullptr);
    // Copy the existing object "forward",
    // delete binding -> insert binding(>update binding) -> duplicate insert
    // binding
    nxt.existing_object = cur.existing_object;

    DBUG_LOG("jdv_dml", "DML-UPDATE-MERGE: Merging bindings for "
                            << cur.ct_node->quoted_qualified_table_name() << "."
                            << cur.ct_node->primary_key_column().column_name()
                            << " = "
                            << json_dom_to_string(cur.existing_object->get(
                                   cur.ct_node->primary_key_column().key())));
    // Clear the existing object of "delete" binding, so that it becomes a noop
    if (cur.bound_object == nullptr) {
      cur.existing_object = nullptr;
    }
  }
}

/**
  Check Json_object being passed in for keys which are not present in the
  JDV definition (including _metadata for the root object), and report error
  if that is the case.

  @param thd THD
  @param input_obj input object
  @param ct_node jdv definition

  @return true if error
 */
[[nodiscard]] static bool check_for_unmatched_input_keys(
    THD *thd, Json_object *input_obj, const Content_tree_node &ct_node) {
  assert(
      std::ranges::is_sorted(*input_obj | std::ranges::views::keys, size_less));
  auto keys_as_string_view_adaptor = std::ranges::views::transform(
      [](const auto &a) -> std::string_view { return a.first; });

  // Add 1 for _metadata in root objects
  std::size_t jdv_key_count = ct_node.key_column_map().size() +
                              ct_node.children().size() +
                              (ct_node.is_root_object() ? 1 : 0);

  // Mem-root string_view array to hold the JDV keys and all of the input keys
  // (if they are all unmatched)
  std::string_view *all_keys = thd->mem_root->ArrayAlloc<std::string_view>(
      jdv_key_count + input_obj->cardinality());

  // Create a view of the array slice for the JDV keys
  auto jdv_keys_rng = std::ranges::views::counted(all_keys, jdv_key_count);

  // Create a view of the array slice where the unmatched keys will be stored
  auto unmatched_dst_rng =
      std::ranges::views::counted(jdv_keys_rng.end(), input_obj->cardinality());

  // Grab all the JDV keys and sort them in the Json way
  // Returns std::ranges::copy_result
  auto cpr =
      std::ranges::copy(ct_node.key_column_map() | std::ranges::views::keys,
                        jdv_keys_rng.begin());

  // Returns std::ranges::unary_transform_result
  auto utr = std::ranges::transform(
      ct_node.children(), cpr.out,
      [](const auto *ctn) -> std::string_view { return ctn->name(); });

  // Add the _metadata key for root nodes
  if (ct_node.is_root_object()) {
    *utr.out = metadatakey;
  }
  std::ranges::sort(jdv_keys_rng, size_less);

  // Use set_difference to find unmatched keys and report an error if (at least)
  // one was found.
  auto diffres = std::ranges::set_difference(
      *input_obj | keys_as_string_view_adaptor, jdv_keys_rng,
      unmatched_dst_rng.begin(), size_less);
  if (diffres.out != unmatched_dst_rng.begin()) {
    my_jdv_error<ER_JDV_UNMAPPED_KEY>(
        input_obj->get(*unmatched_dst_rng.begin())->get_location(),
        ct_node.quoted_qualified_table_name());
    return true;
  }
  return false;
}

/**
  Compare Json_doms for equality using a Json_wrapper.

  @param ajd left-hand side of comparison
  @param bjd right-hand side of comparison
  @return true if equal
*/
static bool is_equal(Json_dom *ajd, Json_dom *bjd) {
  auto ajw = Json_wrapper{ajd, /*alias*/ true};
  auto bjw = Json_wrapper{bjd, /*alias*/ true};
  return ajw.compare(bjw) == 0;
}

/**
  Helper function to create unique_ptr to Resolve_row. (On mac
  std::make_unique() does not do init-list initialization).

  @param parent parent
  @return resolve_row
 */

[[maybe_unused]] [[nodiscard]] static std::unique_ptr<Resolve_row> make_rr_up(
    Resolve_row *parent) {
  auto rrptr = std::make_unique<Resolve_row>();
  rrptr->parent = parent;
  return rrptr;
}

/**
 Overload for Single_object_binding (INSERT/DELETE) with Json_object
 (JSON_OBJECT).
 The Json_object* argument is used as tag for choosing the correct overload,
 (instead of creating a separate tag type).

 @param pbx parent binding index
 @param child_ct_node child content tree node
 @param stack binding stack
 @return true if error
*/
[[nodiscard]] static bool push_object_child_bindings(
    std::size_t pbx, const Content_tree_node *child_ct_node,
    std::vector<Single_object_binding> *stack) {
  auto &stk = *stack;
  Json_dom *child_dom = stk[pbx].bound_object->get(child_ct_node->name());
  Resolve_row *prr = stk[pbx].resolve_row.get();

  auto [jtc, child_object] = inspect_dom<Json_object>(child_dom);
  if (jtc == enum_json_type::J_ERROR) {
    my_jdv_error<ER_JDV_UNEXPECTED_JSON_TYPE>(
        child_dom->get_location(), Json_type_traits<Json_object>::name);
    return true;
  }
  if (child_object != nullptr) {
    stack->push_back({child_object, child_ct_node, make_rr_up(prr)});
  }
  return false;
}

/**
  Overload for Single_object_binding (INSERT/DELETE) with Json_array
  (JSON_ARRAYAGG).
  The Json_array* argument is used as tag for choosing the correct overload,
  (instead of creating a separate tag type).

  @param pbx parent binding index
  @param child_ct_node child content tree node
  @param stack binding stack
  @return true if error
 */
[[nodiscard]] static bool push_array_child_bindings(
    std::size_t pbx, const Content_tree_node *child_ct_node,
    std::vector<Single_object_binding> *stack) {
  auto &stk = *stack;
  Json_dom *child_dom = stk[pbx].bound_object->get(child_ct_node->name());
  Resolve_row *prr = stk[pbx].resolve_row.get();
  auto [jtc, child_array] = inspect_dom<Json_array>(child_dom);
  if (jtc == enum_json_type::J_ERROR) {
    my_jdv_error<ER_JDV_UNEXPECTED_JSON_TYPE>(
        child_dom->get_location(), Json_type_traits<Json_array>::name);
    return true;
  }
  if (child_array == nullptr) {
    return false;
  }

  for (const auto &elt : *child_array) {
    auto [ejtc, elt_object] = inspect_dom<Json_object>(elt.get());
    if (ejtc == enum_json_type::J_ERROR) {
      my_jdv_error<ER_JDV_UNEXPECTED_JSON_TYPE>(
          elt->get_location(), Json_type_traits<Json_object>::name);
      return true;
    }
    if (elt_object != nullptr) {
      stack->push_back({elt_object, child_ct_node, make_rr_up(prr)});
    }
  }
  return false;
}

/**
  Overload for Two_object_binding (UPDATE) with Json_object (JSON_OBJECT).
  The Json_object* argument is used as tag for choosing the correct overload,
  (instead of creating a separate tag type).

  @param pbx parent binding index
  @param child_ct_node child content tree node
  @param stack binding stack
  @return true if error
*/
[[nodiscard]] static bool push_object_child_bindings(
    std::size_t pbx, const Content_tree_node *child_ct_node,
    std::vector<Two_object_binding> *stack) {
  auto &stk = *stack;
  Resolve_row *prr = stk[pbx].resolve_row.get();
  const std::string_view &child_name = child_ct_node->name();
  Json_object *existing_child_object = inspect_valid_dom<Json_object>(
      get_val(stk[pbx].existing_object, child_name));

  Json_dom *bound_child_dom = get_val(stk[pbx].bound_object, child_name);
  auto [jtc, bound_child_object] = inspect_dom<Json_object>(bound_child_dom);
  if (jtc == enum_json_type::J_ERROR) {
    my_jdv_error<ER_JDV_UNEXPECTED_JSON_TYPE>(
        bound_child_dom->get_location(), Json_type_traits<Json_object>::name);
    return true;
  }
  if (existing_child_object != nullptr || bound_child_object != nullptr) {
    stack->push_back({.bound_object = bound_child_object,
                      .existing_object = existing_child_object,
                      .ct_node = child_ct_node,
                      .resolve_row = make_rr_up(prr)});
  }
  return false;
}

/**
  Overload for Two_object_binding (UPDATE) with Json_array (JSON_ARRAY_AGG).
  The Json_array* argument is used as tag for choosing the correct overload,
  (instead of creating a separate tag type).

  @param pbx parent binding index
  @param child_ct_node child content tree node
  @param stack binding stack
  @return true if error
 */
[[nodiscard]] static bool push_array_child_bindings(
    std::size_t pbx, const Content_tree_node *child_ct_node,
    std::vector<Two_object_binding> *stack) {
  DBUG_LOG("jdv_dml", "DML-BIND: Enter " << SOURCE_LOCATION_CUR_FUNC
                                         << " on child "
                                         << child_ct_node->name());
  auto &stk = *stack;
  Resolve_row *prr = stk[pbx].resolve_row.get();
  const std::string_view &child_name = child_ct_node->name();

  Json_array *existing_child_array = inspect_valid_dom<Json_array>(
      get_val(stk[pbx].existing_object, child_name));

  Json_dom *bound_child_dom = stk[pbx].bound_object->get(child_name);
  auto [jtc, bound_child_array] = inspect_dom<Json_array>(bound_child_dom);
  if (jtc == enum_json_type::J_ERROR) {
    my_jdv_error<ER_JDV_UNEXPECTED_JSON_TYPE>(
        bound_child_dom->get_location(), Json_type_traits<Json_array>::name);
    return true;
  }

  DBUG_LOG("jdv_dml", "DML-BIND: At line " << __LINE__);

  if (existing_child_array != nullptr) {
    DBUG_LOG("jdv_dml", "DML-BIND: existing_child_array->size(): "
                            << existing_child_array->size());
    for (const auto &elt : *existing_child_array) {
      Json_object *elt_object = inspect_valid_dom<Json_object>(elt.get());
      if (elt_object != nullptr) {
        stack->push_back({.bound_object = nullptr,
                          .existing_object = elt_object,
                          .ct_node = child_ct_node,
                          .resolve_row = make_rr_up(prr)});
      }
    };
  }
  if (bound_child_array != nullptr) {
    DBUG_LOG("jdv_dml", "DML-BIND: bound_child_array->size(): "
                            << bound_child_array->size());
    for (const auto &elt : *bound_child_array) {
      auto [ejtc, elt_object] = inspect_dom<Json_object>(elt.get());
      if (ejtc == enum_json_type::J_ERROR) {
        my_jdv_error<ER_JDV_UNEXPECTED_JSON_TYPE>(
            elt->get_location(), Json_type_traits<Json_object>::name);
        return true;
      }
      if (elt_object != nullptr) {
        stack->push_back({.bound_object = elt_object,
                          .existing_object = nullptr,
                          .ct_node = child_ct_node,
                          .resolve_row = make_rr_up(prr)});
      }
    }
  }
  return false;
}

/**
  Takes a stack (std::vector) with a single binding at the top. Creates
  bindings for all the children of that binding by combining each Json child
  with the corresponding CTN child and place these on the stack. Proceeds with
  the next element now on the stack. When there are no more element left on the
  stack the process is complete and the stack contains a flattened sequence of
  bindings for each Json_object in the input which corresponds to a
  jdv::Content_tree_node. This flattened sequence can then be sorted and
  traversed in either direction as needed when generating statements
  for the base tables.

  @param stack binding stack
  @return true if error
  */
template <typename BIN>
[[nodiscard]] static bool flatten(std::vector<BIN> *stack) {
  for (std::size_t pbx = 0; pbx < stack->size(); ++pbx) {
    if (std::ranges::any_of(
            (*stack)[pbx].ct_node->children(),
            [&](const Content_tree_node *child_ct_node) {
              return (child_ct_node->is_root_object() ||
                      child_ct_node->is_singleton_child())
                         ? push_object_child_bindings(pbx, child_ct_node, stack)
                         : push_array_child_bindings(pbx, child_ct_node, stack);
            })) {
      return true;
    }
  }
  return false;
}

/**
  Check if the row represented by the binding already exists, and if
  so return a diff vector (true for columns which currently does not have
  the value of the binding).
  This function can only be called when already inside
  do_in_substatement_context().

  @param thd THD
  @param binding checkee
  @return diff vector or nullopt if error or row not found
 */

[[nodiscard]] static std::optional<std::vector<bool>> select_diff_vector(
    THD *thd, const auto &binding) {
  assert((thd->in_sub_stmt & SUB_STMT_DUALITY_VIEW) != 0);
  const auto &ct_node = *binding.ct_node;

  const auto &[pkcol, pkval] =
      binding.resolve_row->columns[ct_node.primary_key_column_index()];
  if (pkval == nullptr) {
    assert(false);
    return std::nullopt;
  }

  std::string query = "SELECT ";
  const auto &kcilst = ct_node.key_column_info_list();

  for (std::size_t rci = 0; const auto &[c, v] : binding.resolve_row->columns) {
    const Key_column_info &kci = kcilst[rci];
    std::size_t cur_rci = rci;
    ++rci;
    if (cur_rci == ct_node.primary_key_column_index() || v == nullptr) {
      // If we are not going to modify the value, we don't care what it
      // currently is
      query.append("0, ");
      continue;
    }

    append_identifier(&query, c);
    query.append(" <> ");
    if (append_json_dom(&query, v, col_expects_b64(kci))) {
      return std::nullopt;
    }

    query.append(", ");
  }
  query.replace(query.size() - 2, 2, " FROM ");
  query.append(ct_node.quoted_qualified_table_name());
  query.append(" WHERE ");
  append_identifier(&query, pkcol);
  query.append(" = ");
  assert(!col_expects_b64(ct_node.primary_key_column()));
  if (append_json_dom(&query, pkval)) {
    return std::nullopt;
  }
  query.append(" FOR UPDATE");

  DBUG_LOG("jdv_dml", "DML-DIFF: query:" << query);
  Regular_statement_handle stmt_handle(thd, query.data(), query.length());
  stmt_handle.set_capacity(binding.resolve_row->columns.size() *
                               sizeof(std::int64_t) +
                           std::size_t{1});
  bool ret_val = stmt_handle.execute();
  if (ret_val) {
    DBUG_LOG("jdv_dml", "DML-DIFF: SELECT query '" << query << "' failed");
    return std::nullopt;
  }
  Result_set *rs = stmt_handle.get_current_result_set();
  assert(rs != nullptr);
  DBUG_LOG("jdv_dml",
           "DML-DIFF: SELECT query returned " << rs->size() << " rows");

  if (rs->size() != 1) {
    // Row does not exist
    return std::nullopt;
  }
  const auto *row = rs->get_next_row();
  assert(row != nullptr);

  std::optional<std::vector<bool>> ret = std::vector<bool>{};
  for (std::size_t ci = 0; ci < row->size(); ++ci) {
    auto *c = row->get_column(ci);
    if (c->index() == 0) {
      ret->push_back(true);
      continue;
    }
    DBUG_LOG("jdv_dml", "c->index(): " << c->index());
    std::int64_t cv = *std::get<std::int64_t *>(*c);
    ret->push_back(cv != 0);
  }
  return ret;
}

/**
  Uses a Regular_statement_handle to execute a single statement passed as
  argument.

  @param       thd            THD
  @param       caller_da      DA in which to accumulate diagnostics
  @param       stmt           statement text
  @param [out] affected_rows  Number of affected rows.

  @return true if error
 */
static bool run_substmt(THD *thd, Diagnostics_area *caller_da,
                        std::string_view stmt, ulonglong *affected_rows) {
  assert(affected_rows != nullptr);
  caller_da->mark_preexisting_sql_conditions();

  Regular_statement_handle stmt_handle(thd, stmt.data(), stmt.length());
  stmt_handle.set_clear_diagnostics_area_on_success(false);
  if (stmt_handle.execute()) {
    DBUG_LOG("jdv_dml", "DML: statement " << stmt << " failed");
    caller_da->copy_new_sql_conditions(thd, thd->get_stmt_da());
    return true;
  }

  assert(!thd->is_error());
  /*
    Update affected_rows from DA after successful execution of a statement.
  */
  *affected_rows = *affected_rows + thd->get_stmt_da()->affected_rows();

  caller_da->copy_new_sql_conditions(thd, thd->get_stmt_da());

  // Reset DA status for next statement execution.
  thd->get_stmt_da()->reset_diagnostics_area();

  return false;
}

// These values are arbitrary.
constexpr std::size_t STMT_RESERVE_SIZE = 512;
constexpr std::size_t BINDINGS_RESERVE_SIZE = 48;

enum class Stmt_state { EXECUTE = 0, SKIP = 1, ERROR = 2 };

static Json_uint ZERO{0};
static const Json_wrapper ZEROW{&ZERO, true};

/**
  Produces an INSERT statement from a binding. For INSERT this is
  a Single_object_binding, but when an update decays into and INSERT,
  this function is also invoked with a Two_object_binding.

  @param thd THD
  @param binding insertee
  @param sbufp statement text buffer
  @return Statement_status - indicates if statement must be executed, skipped or
  an error occured
 */
[[nodiscard]] static Stmt_state make_insert(THD *thd, const auto &binding,
                                            auto *sbufp) {
  assert(binding.bound_object != nullptr);
  assert(binding.ct_node != nullptr);

  const Content_tree_node &ct_noder = *binding.ct_node;
  assert(!ct_noder.key_column_info_list().empty());
  assert(binding.resolve_row);
  const auto &resolved_columns = binding.resolve_row->columns;
  assert(resolved_columns.size() == ct_noder.key_column_info_list().size());

  // Report error if an AUTO_INCREMENT value
  // is the value 0 (explicit request to generate value) and
  // NO_AUTO_VALUE_ON_ZERO is off
  for (std::size_t rix = 0; rix < resolved_columns.size(); ++rix) {
    const auto &kci = ct_noder.key_column_info_list()[rix];
    const auto &[col, val] = resolved_columns[rix];

    if (is_auto_increment(*kci.field()) && !represents_NULL(val) &&
        Json_wrapper{val, true}.compare(ZEROW) == 0 &&
        (thd->variables.sql_mode & MODE_NO_AUTO_VALUE_ON_ZERO) == 0) {
      my_jdv_error<ER_JDV_EXPLICIT_AUTO_INCREMENT_NOT_ALLOWED>(
          ct_noder.quoted_qualified_table_name(), col,
          binding.bound_object->get_location(), kci.key());
      return Stmt_state::ERROR;
    }
  }
  assert(!thd->is_error());

  bool is_with_insert = ct_noder.allows_insert();
  bool is_with_update = ct_noder.allows_update();
  constexpr bool is_insert_for_update =
      std::is_same_v<decltype(binding), const Two_object_binding &>;
  bool is_root_or_nested_insert_update =
      ct_noder.is_root_object() ||
      (ct_noder.is_nested_child() && is_insert_for_update);
  DBUG_LOG("jdv_dml",
           "DML-INSERT: is_insert_for_update:" << is_insert_for_update);

  if (is_root_or_nested_insert_update && !is_with_insert) {
    my_jdv_error<ER_JDV_MISSING_INSERT_TAG>(
        ct_noder.quoted_qualified_table_name(),
        binding.bound_object->get_location());
    return Stmt_state::ERROR;
  }

  if (!is_root_or_nested_insert_update) {
    const auto &[pkcol, pkval] =
        binding.resolve_row->columns[ct_noder.primary_key_column_index()];
    assert(pkval != nullptr);

    auto dr = select_diff_vector(thd, binding);
    if (thd->is_error()) {
      return Stmt_state::ERROR;
    }
    bool row_exists = static_cast<bool>(dr);

    if (!row_exists) {
      if (!is_with_insert) {
        DBUG_LOG("jdv_dml", "Diff check returned no rows");
        if (ct_noder.is_singleton_child() && is_insert_for_update) {
          my_jdv_error<ER_JDV_MISSING_INSERT_TAG>(
              ct_noder.quoted_qualified_table_name(),
              binding.bound_object->get_location());
          return Stmt_state::ERROR;
        }
        my_jdv_error<ER_JDV_MISSING_READONLY_SUBOBJECT>(
            binding.bound_object->get_location(),
            ct_noder.quoted_qualified_table_name(), pkcol,
            json_dom_to_string(pkval));
        return Stmt_state::ERROR;
      }
    } else {
      if (!is_with_update) {
        auto cs = dr.value();
        if (cs[ct_noder.join_column_index()]) {
          // The existing value of the join condtion does not match what is
          // being inserted.
          my_jdv_error<ER_JDV_JOIN_CONDITION_VIOLATION>(
              binding.bound_object->get_location(),
              ct_noder.quoted_qualified_table_name(),
              ct_noder.key_column_info_list()[ct_noder.join_column_index()]
                  .column_name());
          return Stmt_state::ERROR;
        }
        return Stmt_state::SKIP;
      }
    }
  }

  auto &sbuf = *sbufp;
  sbuf.reserve(STMT_RESERVE_SIZE);
  sbuf.append("INSERT INTO ");
  sbuf.append(ct_noder.quoted_qualified_table_name());
  sbuf.append(" (");

  DBUG_LOG("jdv_dml", "DML-INSERT: Listing columns to be populated");
  const auto &kcilst = ct_noder.key_column_info_list();
  for ([[maybe_unused]] const auto &kc : kcilst) {
    DBUG_LOG("jdv_dml", kc.column_name() << " => \"" << kc.key() << "\":, ");
  }

  for (const auto &col : kcilst) {
    append_identifier(&sbuf, col.column_name());
    sbuf.append(", ");
  }
  sbuf.replace(sbuf.size() - 2, 2, ") VALUES (");

  if (is_root_or_nested_insert_update) {
    for (std::size_t rci = 0; auto &[col, rdom] : resolved_columns) {
      if (append_json_dom(&sbuf, rdom, col_expects_b64(kcilst[rci++]))) {
        return Stmt_state::ERROR;
      }
      sbuf.append(", ");
    }
    sbuf.replace(sbuf.size() - 2, 2, ")");
    return Stmt_state::EXECUTE;
  }

  // Updatable sub-nodes can have existing row, so need ON DUPLICATE KEY UPDATE
  auto values_pos = sbuf.size();
  for (std::size_t rci = 0; const auto &[col, val] : resolved_columns) {
    const Key_column_info &kci = kcilst[rci++];
    DBUG_LOG("jdv_dml", "DML-INSERT: Considering " << col << " <- " << val);
    if (val == nullptr) {
      // If we could not deduce a value for the column, we add DEFAULT to the
      // values list, and omit the column from the ON DUPLICATE assignment list.
      sbuf.insert(values_pos, "DEFAULT, ");
      values_pos += 9;
      continue;
    }
    append_identifier(&sbuf, col);
    sbuf.append(" = ");
    auto vstart = sbuf.size();

    if (append_json_dom(&sbuf, val, col_expects_b64(kci))) {
      return Stmt_state::ERROR;
    }

    sbuf.append(", ");
    auto vsize = sbuf.size() - vstart;

    // Insert value into VALUES list also
    sbuf.insert(values_pos, sbuf.c_str() + vstart, vsize);
    values_pos += vsize;
  }

  // Replace trailing ", " in values list with the start of the ON DUPLICATE
  // section
  sbuf.replace(values_pos - 2, 2, ") ON DUPLICATE KEY UPDATE ");
  sbuf.resize(sbuf.size() - 2);

  return Stmt_state::EXECUTE;
}

static Stmt_state make_delete(THD *, const Single_object_binding &, auto *);

/**
  Obtains the dom of the etag sub-object.

  @param root_object containing the etag sub-object
  @return etag sub-object dom
 */
static Json_dom *etag_dom(Json_object *root_object) {
  assert(root_object != nullptr);
  if (root_object == nullptr) {
    return nullptr;
  }
  Json_dom *metadata = root_object->get(metadatakey);
  if (metadata == nullptr) {
    return nullptr;
  }
  Json_object *metadata_object = down_cast<Json_object *>(metadata);
  return metadata_object->get(etagkey);
}

/**
  Checks if etags in existing and bound objects match. Succeeds with warning if
  etag is not provided in bound object.

  @param binding root binding
  @return true if error (mismatch)
 */
static bool check_etag(const Two_object_binding &binding) {
  Json_dom *before_etag = etag_dom(binding.existing_object);
  assert(before_etag != nullptr);

  Json_dom *cur_etag = etag_dom(binding.bound_object);
  if (cur_etag == nullptr) {
    push_warning(current_thd, ER_JDV_MISSING_ETAG);
    return false;
  }
  if (is_equal(before_etag, cur_etag)) {
    return false;
  }

  my_jdv_error<ER_JDV_ETAG_MISMATCH>(json_dom_to_string(cur_etag).c_str());
  return true;
}

/**
  Produces an UPDATE statement from a Two_object_binding. If there is no
  existing object an INSERT is generated. If there is no bound object a DELETE
  statement is generated.

  @param thd THD
  @param binding updatee
  @param sbufp statement text buffer
  @return Statement_status - indicates if statement must be executed, skipped or
  an error occured
 */
[[nodiscard]] static Stmt_state make_update(THD *thd,
                                            const Two_object_binding &binding,
                                            auto *sbufp) {
  const Content_tree_node &ct_node = *binding.ct_node;
  assert(!ct_node.key_column_info_list().empty());
  assert(binding.resolve_row);

  if (binding.existing_object == nullptr) {
    DBUG_LOG("jdv_dml",
             "DML-UPDATE: b.existing_object == nullptr for UPDATE of ("
                 << ct_node.name() << " -> "
                 << ct_node.quoted_qualified_table_name()
                 << "), generating INSERT of bound object instead.");
    return make_insert(thd, binding, sbufp);
  }
  assert(binding.existing_object != nullptr);
  if (binding.bound_object == nullptr) {
    DBUG_LOG("jdv_dml",
             "DML-UPDATE: b.bound_object == nullptr for UPDATE of ("
                 << ct_node.name() << " -> "
                 << ct_node.quoted_qualified_table_name()
                 << "), generating DELETE of existing object instead.");
    return make_delete(thd,
                       {.bound_object = binding.existing_object,
                        .ct_node = binding.ct_node,
                        .resolve_row = {}},
                       sbufp);
  }

  // Check if any singleton child is removed or set to null
  for (const auto &c : binding.ct_node->children()) {
    if (!c->is_singleton_child()) {
      continue;
    }
    if (!represents_NULL(binding.existing_object->get(c->name())) &&
        represents_NULL(binding.bound_object->get(c->name()))) {
      my_jdv_error<ER_JDV_MISSING_DELETE_TAG>(
          c->quoted_qualified_table_name(),
          binding.existing_object->get(c->name())->get_location());
      return Stmt_state::ERROR;
    }
  }

  auto &sbuf = *sbufp;
  sbuf.reserve(STMT_RESERVE_SIZE);

  sbuf.append("UPDATE ");
  sbuf.append(ct_node.quoted_qualified_table_name());
  sbuf.append(" SET ");
  auto emptysize = sbuf.size();

  const auto &resolved_columns = binding.resolve_row->columns;
  assert(resolved_columns.size() == ct_node.key_column_info_list().size());

  // On update all columns must be resolved in order the perform
  // etag check.
  if (std::ranges::any_of(resolved_columns, [&](const auto &p) {
        if (p.second == nullptr) {
          my_jdv_error<ER_JDV_MISSING_VALUE>(
              binding.bound_object->get_location(),
              ct_node.quoted_qualified_table_name(), p.first);
          return true;
        }
        return false;
      })) {
    return Stmt_state::ERROR;
  }

  const auto &pk_col_info = ct_node.primary_key_column();
  Json_dom *pk_edom = binding.existing_object->get(pk_col_info.key());
  assert(pk_edom != nullptr);
  Json_dom *pk_rdom =
      binding.resolve_row->columns[ct_node.primary_key_column_index()].second;
  assert(pk_rdom != nullptr);
  if (!is_equal(pk_edom, pk_rdom)) {
    // This is a PK update.
    if (ct_node.is_root_object()) {
      my_jdv_error<ER_JDV_PK_UPDATES_NOT_ALLOWED>(
          ct_node.quoted_qualified_table_name(), pk_col_info.column_name(),
          pk_rdom->get_location());
      return Stmt_state::ERROR;
    }
    assert(ct_node.is_singleton_child());

    // We can only proceed if a row with the new
    // PK value already exists in the base table.
    auto dr = select_diff_vector(thd, binding);
    if (thd->is_error()) {
      return Stmt_state::ERROR;
    }

    if (!dr) {
      // Seems like it would be more appopriate to report an error
      // about pk updates not being allowed here... but
      my_jdv_error<ER_JDV_MISSING_UPDATE_TAG>(
          ct_node.quoted_qualified_table_name(), pk_col_info.column_name(),
          pk_rdom->get_location());
      return Stmt_state::ERROR;
    }
    assert(dr);

    // A row with this pk already exists in the base table
    DBUG_LOG("jdv_dml",
             "DML-UPDATE: pk value of "
                 << ct_node.name() << ", "
                 << ct_node.quoted_qualified_table_name()
                 << " is changed, but a row with the new pk value exists");

    if (ct_node.read_only()) {
      // Note that this implies that the existing subobject need not be
      // identical to what is being passed in
      return Stmt_state::SKIP;
    }

    // Must generate an update statement for this existing row. However,
    // comparisons with the existing json object from the binding is
    // meaningless since the row which will actually be updated is completely
    // unrelated in this case.
    const auto &kcis = ct_node.key_column_info_list();
    for (std::size_t i = 0; i < dr->size(); ++i) {
      if ((*dr)[i]) {
        append_identifier(&sbuf, kcis[i].column_name());
        sbuf.append(" = ");
        if (append_json_dom(&sbuf, binding.resolve_row->columns[i].second,
                            col_expects_b64(kcis[i]))) {
          return Stmt_state::ERROR;
        }
        sbuf.append(", ");
      }
    }
  }  // Pk update
  else {
    // Generate assignment list from projected columns in base_columns and the
    // resolved column values. Presumably resolving is not actually necessary
    // for true UPDATEs (only when UPDATE performs INSERT), but since we have
    // already resolved the columns, it is cheaper to get them from resolve_row,
    // even if they must also exist in binding.bound_object.
    for (std::size_t rci_ = 0;
         const auto &col : ct_node.key_column_info_list()) {
      auto rci = rci_++;
      Json_dom *existing_col_dom = binding.existing_object->get(col.key());
      Json_dom *updated_col_dom = binding.resolve_row->columns[rci].second;

      if (updated_col_dom == nullptr) {
        DBUG_LOG(
            "jdv_dml",
            "DML-UPDATE: " << col.key() << " not found in new value. Skipping");
        continue;
      }

      if (existing_col_dom != nullptr && updated_col_dom != nullptr &&
          is_equal(updated_col_dom, existing_col_dom)) {
        std::string before_value;
        if (append_json_dom(&before_value, existing_col_dom,
                            col_expects_b64(col))) {
          return Stmt_state::ERROR;
        }
        DBUG_LOG("jdv_dml", "DML-UPDATE: Key: '"
                                << col.key() << "', col: '" << col.column_name()
                                << "' is unchanged, ('" << before_value
                                << "'). Skipping.");
        continue;
      }
      assert(rci != ct_node.primary_key_column_index());

      if (!col.allows_update()) {
        my_jdv_error<ER_JDV_MISSING_UPDATE_TAG>(
            ct_node.quoted_qualified_table_name(), col.column_name(),
            updated_col_dom->get_location());
        return Stmt_state::ERROR;
      }

      append_identifier(&sbuf, col.column_name());
      sbuf.append(" = ");
      if (append_json_dom(&sbuf, updated_col_dom, col_expects_b64(col))) {
        return Stmt_state::ERROR;
      }
      sbuf.append(", ");
    }
  }  // else

  // Check if any columns were actually added. If not return empty statement.
  if (sbuf.size() == emptysize) {
    sbuf = "/* Nothing to do for ";
    sbuf.append(ct_node.name()).append(" (");
    sbuf.append(ct_node.quoted_qualified_table_name());
    sbuf.append(") */");
    return Stmt_state::SKIP;
  }
  sbuf.replace(sbuf.size() - 2, 2, " WHERE ");

  append_identifier(&sbuf, pk_col_info.column_name());
  sbuf.append(" = ");
  assert(!col_expects_b64(pk_col_info));
  return append_json_dom(&sbuf, pk_rdom) ? Stmt_state::ERROR
                                         : Stmt_state::EXECUTE;
}

/**
  Produces a delete statement from a Single_object_binding.
  When an update decays into a DELETE, this function is called
  a with a Single_object_binding created on the fly from
  the Two_object_binding - which is only possible because
  DELETE does not require a populated resolve_row.

  @param binding deletee
  @param sbufp statement text buffer
  @return Statement_status - indicates if statement must be executed, skipped or
  an error occured
 */
[[nodiscard]] static Stmt_state make_delete(
    THD *, const Single_object_binding &binding, auto *sbufp) {
  assert(binding.bound_object != nullptr);
  const auto &ct_node = *binding.ct_node;
  assert(!ct_node.key_column_info_list().empty());
  if (!ct_node.allows_delete()) {
    if (ct_node.is_singleton_child()  //&&
                                      // Not delete for update
                                      // binding.resolve_row.get() != nullptr
    ) {
      return Stmt_state::SKIP;
    }
    DBUG_LOG("jdv_dml", "DELETE on " << binding.ct_node->name()
                                     << " rejected due to missing TAG");
    my_jdv_error<ER_JDV_MISSING_DELETE_TAG>(
        binding.ct_node->quoted_qualified_table_name(),
        binding.bound_object->get_location());
    return Stmt_state::ERROR;
  }

  auto &sbuf = *sbufp;
  sbuf.reserve(STMT_RESERVE_SIZE);

  sbuf.append("DELETE FROM ");
  sbuf.append(ct_node.quoted_qualified_table_name());
  sbuf.append(" WHERE ");

  append_identifier(&sbuf, ct_node.primary_key_column().column_name());
  sbuf.append(" = ");

  Json_dom *pk_val =
      binding.bound_object->get(ct_node.primary_key_column().key());
  assert(pk_val != nullptr);
  assert(!col_expects_b64(ct_node.primary_key_column()));
  return append_json_dom(&sbuf, pk_val) ? Stmt_state::ERROR
                                        : Stmt_state::EXECUTE;
}

[[nodiscard]] static bool check_input_json(Json_dom *input_dom) {
  if (input_dom->json_type() != enum_json_type::J_OBJECT) {
    my_jdv_error<ER_JDV_UNEXPECTED_JSON_TYPE>("$", "Json_object");
    return true;
  }
  return false;
}

/**
  Creates bindings from inserted Json_object,
  orders them, creates and executes INSERT statements against the base tables.

  @param thd THD
  @param jw JSON object to insert
  @param ct_node content tree root node of view
  @param[out] affected_rows number of affected base table rows
 */
[[nodiscard]] static bool jdv_handle_insert(THD *thd, Json_wrapper *jw,
                                            Content_tree_node *ct_node,
                                            ulonglong *affected_rows) {
  Json_dom *dom = jw->to_dom();
  assert(dom != nullptr);
  if (check_input_json(dom)) {
    return true;
  }
  assert(dom->json_type() == enum_json_type::J_OBJECT);

  std::vector<Single_object_binding> bindings;
  bindings.reserve(BINDINGS_RESERVE_SIZE);
  bindings.push_back({down_cast<Json_object *>(dom), ct_node,
                      std::make_unique<Resolve_row>()});

  if (flatten(&bindings)) {
    return true;
  }

  if (std::ranges::any_of(bindings, [&](const auto &bin) {
        return check_for_unmatched_input_keys(thd, bin.bound_object,
                                              *bin.ct_node);
      })) {
    return true;
  }

  if (resolve_columns(bindings)) {
    return true;
  }

  // Sort the binding so that
  // - statements are executed in the correct order (so that FK relationships
  // are satisfied)
  // - It becomes possible to use algorithms such as unique and adjacent_find
  // (which operate on sorted ranges)
  std::ranges::sort(bindings);

  DBUG_LOG("jdv_dml", "\nDML-INSERT: Rank-sorted order: ");
  for ([[maybe_unused]] const auto &bin : bindings) {
    DBUG_LOG("jdv_dml", bin.ct_node->name()
                            << " ("
                            << bin.ct_node->quoted_qualified_table_name()
                            << "), ");
  }

  if (check_for_share_pk_duplicates(bindings)) {
    return true;
  }

  return do_in_substatement_context(thd, [&](Diagnostics_area *caller_da) {
    std::string stmt;
    return std::ranges::any_of(bindings, [&](const Single_object_binding &bin) {
      if (bin.is_empty()) {
        return false;
      }
      stmt.resize(0);
      auto res = make_insert(thd, bin, &stmt);
      DBUG_LOG("jdv_dml", "DML-INSERT: Insert from node '"
                              << bin.ct_node->name() << "'"
                              << " using '" << stmt << "'");

      return res == Stmt_state::ERROR ||
             (res != Stmt_state::SKIP &&
              run_substmt(thd, caller_da, stmt, affected_rows));
    });
  });
}

/**
  Creates bindings from existing and updated Json_object,
  orders them, creates and executes UPDATE/INSERT/DELETE
  statements against the base tables.

  @param thd THD
  @param jw updated JSON object
  @param existing existing JSON object
  @param ct_node content tree root node
  @param[out] affected_rows affected base table rows
 */
[[nodiscard]] static bool jdv_handle_update(THD *thd, Json_wrapper *jw,
                                            Json_wrapper *existing,
                                            Content_tree_node *ct_node,
                                            ulonglong *affected_rows) {
  assert(jw != nullptr);
  assert(existing != nullptr);
  assert(ct_node != nullptr);
  Json_dom *dom = jw->to_dom();
  assert(dom != nullptr);
  if (check_input_json(dom)) {
    return true;
  }
  assert(dom->json_type() == enum_json_type::J_OBJECT);

  std::vector<Two_object_binding> bindings;
  bindings.reserve(BINDINGS_RESERVE_SIZE);
  bindings.push_back({down_cast<Json_object *>(dom),
                      down_cast<Json_object *>(existing->to_dom()), ct_node,
                      std::make_unique<Resolve_row>()});

  if (check_etag(bindings.front())) {
    return true;
  }

  if (flatten(&bindings)) {
    return true;
  }

  if (std::ranges::any_of(bindings, [&](const auto &bin) {
        return (bin.bound_object != nullptr &&
                check_for_unmatched_input_keys(thd, bin.bound_object,
                                               *bin.ct_node));
      })) {
    return true;
  }

  if (resolve_columns(bindings)) {
    return true;
  }

  for ([[maybe_unused]] const auto &bin : bindings) {
    DBUG_LOG("jdv_dml", "DML-UPDATE: Flattened order: " << bin.ct_node->name());
  }

  // Sort the binding so that
  // - statements are executed in the correct order (so that FK relationships
  // are satisfied)
  // - It becomes possible to use algorithms such as unique and adjacent_find
  // (which operate on sorted ranges)
  // - We can correctly merge together bindings that represent a single update.
  std::ranges::sort(bindings);

  for ([[maybe_unused]] const auto &bin : bindings) {
    if (bin.bound_object == nullptr) {
      DBUG_LOG("jdv_dml", "DML-UPDATE: Rank-sorted order (EX): "
                              << bin.ct_node->name() << "@" << &bin
                              << " bin.existing_object:" << bin.existing_object
                              << " bin.bound_object:" << bin.bound_object);
      continue;
    }
    DBUG_LOG(
        "jdv_dml",
        "DML-UPDATE: Rank-sorted order: "
            << bin.ct_node->name() << "@" << &bin
            << " Table_ref:" << bin.ct_node->table_ref()->table_name << "("
            << bin.ct_node->table_ref()->alias << "): @"
            << bin.ct_node->table_ref() << " share: @"
            << bin.ct_node->table_ref()->table->s
            << " bin.existing_object:" << bin.existing_object
            << " bin.resolve_row->columns[pk_index].second:"
            << bin.resolve_row->columns[bin.ct_node->primary_key_column_index()]
                   .second);
  }

  merge_bindings_for_update(bindings);

  if (check_for_share_pk_duplicates(bindings)) {
    return true;
  }

  return do_in_substatement_context(thd, [&](Diagnostics_area *caller_da) {
    std::string stmt;
    return std::ranges::any_of(bindings, [&](const Two_object_binding &bin) {
      if (bin.is_empty()) {
        return false;
      }
      stmt.resize(0);
      auto res = make_update(thd, bin, &stmt);
      DBUG_LOG("jdv_dml", "DML-UPDATE: Update from node '"
                              << bin.ct_node->name() << "'"
                              << " using '" << stmt << "'");

      return res == Stmt_state::ERROR ||
             (res != Stmt_state::SKIP &&
              run_substmt(thd, caller_da, stmt, affected_rows));
    });
  });
}

/**
  Creates bindings from deleted Json_object,
  orders them, creates and executes DELETE statements against the base tables.

  @param thd THD
  @param jw existing JSON object to delete
  @param ct_node content tree root node
  @param[out] affected_rows affected base table rows
 */
[[nodiscard]] static bool jdv_handle_delete(THD *thd, Json_wrapper *jw,
                                            Content_tree_node *ct_node,
                                            ulonglong *affected_rows) {
  assert(jw != nullptr);
  Json_dom *dom = jw->to_dom();
  assert(dom != nullptr);
  assert(dom->json_type() == enum_json_type::J_OBJECT);

  std::vector<Single_object_binding> bindings;
  bindings.push_back({down_cast<Json_object *>(dom), ct_node,
                      std::make_unique<Resolve_row>()});

  if (flatten(&bindings)) {
    return true;
  }
  if (resolve_columns(bindings)) {
    return true;
  }
  return do_in_substatement_context(thd, [&](Diagnostics_area *caller_da) {
    std::string stmt;
    return std::ranges::any_of(
        std::ranges::reverse_view{bindings},
        [&](const Single_object_binding &bin) {
          stmt.resize(0);
          auto res = make_delete(thd, bin, &stmt);
          DBUG_LOG("jdv_dml", "DML-DELETE: Delete from node '"
                                  << bin.ct_node->name() << "'"
                                  << " using '" << stmt << "'");

          return res == Stmt_state::ERROR ||
                 (res != Stmt_state::SKIP &&
                  run_substmt(thd, caller_da, stmt, affected_rows));
        });
  });
}

/**
  Performs common sanity checks.

  @param thd THD
  @param view JDV to check
  @param is_single_table_plan true if single table plan
  @return true if error
 */
[[nodiscard]] static bool jdv_prepare_base(THD *thd, const Table_ref *view,
                                           bool is_single_table_plan) {
  // LOW PRIORITY is not supported.
  if (view->lock_descriptor().type == TL_WRITE_LOW_PRIORITY) {
    my_error(ER_JDV_OPERATION_NOT_SUPPORTED, MYF(0), "LOW_PRIORITY modifier");
    return true;
  }

  // IGNORE
  if (thd->lex->is_ignore()) {
    my_error(ER_JDV_OPERATION_NOT_SUPPORTED, MYF(0), "IGNORE modifier");
    return true;
  }

  // Is Multi-table operation ?
  if (!is_single_table_plan) {
    my_error(ER_JDV_OPERATION_NOT_SUPPORTED, MYF(0),
             "Multi-table DML operation");
    return true;
  }

  return false;
}

// API

/**
  Performs sanity checks specific to insert.

  @param thd THD
  @param view JDV to check
  @param sql_insert_cmd insert command object
  @return true if error
 */
bool jdv_prepare_insert(THD *thd, const Table_ref *view,
                        Sql_cmd_insert_base *sql_insert_cmd) {
  assert(view->is_json_duality_view());
  if (!view->is_json_duality_view()) {
    return false;
  }

  // REPLACE statement is not supported.
  if (sql_insert_cmd->duplicates == DUP_REPLACE) {
    my_error(ER_JDV_OPERATION_NOT_SUPPORTED, MYF(0), "REPLACE");
    return true;
  }

  // INSERT... ON DUPLICATE KEY UPDATE is not supported.
  if (sql_insert_cmd->duplicates == DUP_UPDATE) {
    my_error(ER_JDV_OPERATION_NOT_SUPPORTED, MYF(0),
             "INSERT... ON DUPLICATE KEY UPDATE");
    return true;
  }

  // INSERT... SELECT is not supported.
  const bool select_insert = sql_insert_cmd->insert_many_values.empty();
  if (select_insert) {
    my_error(ER_JDV_OPERATION_NOT_SUPPORTED, MYF(0), "INSERT... SELECT");
    return true;
  }

  // HIGH PRIORITY is not supported.
  if (view->lock_descriptor().type == TL_WRITE) {
    my_error(ER_JDV_OPERATION_NOT_SUPPORTED, MYF(0), "INSERT HIGH_PRIORITY");
    return true;
  }

  // Column list (i.e. column "data") is not supported.
  if (sql_insert_cmd->insert_field_list.size() > 0) {
    my_error(ER_JDV_OPERATION_NOT_SUPPORTED, MYF(0), "Column list in INSERT");
    return true;
  }

  if (jdv_prepare_base(thd, view, sql_insert_cmd->is_single_table_plan())) {
    return true;
  }

  return false;
}

/**
  Performs sanity checks specific to update.

  @param thd THD
  @param view JDV to check
  @param is_single_table_plan true if single table plan
  @return true if error
 */
bool jdv_prepare_update(THD *thd, const Table_ref *view,
                        bool is_single_table_plan) {
  if (view->query_block->order_list.first != nullptr) {
    my_jdv_error<ER_JDV_OPERATION_NOT_SUPPORTED>("UPDATE with ORDER BY clause");
    return true;
  }

  // LIMIT without ORDER BY is meaningless and disallowing is consistent
  // with DELETE.
  DBUG_LOG("jdv_dml", "DML-UPDATE: "
                          << " vqb_limit:"
                          << view->query_block->get_limit(thd));
  if (view->query_block->get_limit(thd) != HA_POS_ERROR) {
    my_jdv_error<ER_JDV_OPERATION_NOT_SUPPORTED>("UPDATE with LIMIT clause");
    return true;
  }

  // Mark the root object table's columns for read here. For sub-objects
  // table, columns are already marked during resolve stage by
  // Item_subselect::fix_fields().
  //
  // TODO: Find a better way to handle read_set marking for root object
  //       table columns
  const auto content_tree = view->jdv_content_tree;
  for (const auto &kci : *content_tree->key_column_info_list()) {
    auto field = kci.field();
    bitmap_set_bit(field->table->read_set, field->field_index());
  }

  return jdv_prepare_base(thd, view, is_single_table_plan);
}

/**
  Performs sanity checks specific to delete.

  @param thd THD
  @param view JDV to check
  @param is_single_table_plan true if single table plan
  @return true if error
 */

bool jdv_prepare_delete(THD *thd, const Table_ref *view,
                        bool is_single_table_plan) {
  if (view->query_block->order_list.first != nullptr) {
    my_jdv_error<ER_JDV_OPERATION_NOT_SUPPORTED>("DELETE with ORDER BY clause");
    return true;
  }

  // LIMIT without WHERE does not work with JDVs since the rows will not be
  // fetched so there is no way to generate statements against the base table.
  // (LIMIT n for n > 1 would not work anyway since we multi-object deletes are
  // not allowed. LIMIT 1 with WHERE could be made to work, but as long as
  // ORDER BY is not supported it makes little sense).
  DBUG_LOG("jdv_dml",
           "DML-DELETE: vqb_limit:" << view->query_block->get_limit(thd));

  if (view->query_block->get_limit(thd) != HA_POS_ERROR) {
    my_jdv_error<ER_JDV_OPERATION_NOT_SUPPORTED>("DELETE with LIMIT clause");
    return true;
  }

  return jdv_prepare_base(thd, view, is_single_table_plan);
}

/**
  Installs the view's security context if it exists and creates a scope
  guard to restore the original context.

  @param thd THD
  @param dvtr duality view reference

  @return scope guard which restores original security context
*/
[[nodiscard]] static decltype(auto) create_sctx_guard(THD *thd,
                                                      const Table_ref *dvtr) {
  Security_context *orig_sctx = thd->security_context();
  if (dvtr->view_sctx != nullptr) {
    thd->set_security_context(dvtr->view_sctx);
  }

  return create_scope_guard([=] { thd->set_security_context(orig_sctx); });
}

/**
  Performs statement-based binlogging for DML operations on a JSON Duality view.

  @param thd THD
  @return true if error
*/
static bool write_binlog(THD *thd) {
  /*
    If row-based binlogging, we don't need to binlog the function's call, let
    each substatement be binlogged its way.
  */
  bool need_binlog_call = mysql_bin_log.is_open() &&
                          (thd->variables.option_bits & OPTION_BIN_LOG) &&
                          !thd->is_current_stmt_binlog_format_row();
  if (!need_binlog_call) {
    return false;
  }

  if (thd->binlog_evt_union.unioned_events) {
    int errcode = query_error_code(thd, thd->killed == THD::NOT_KILLED);
    Query_log_event qinfo(thd, thd->query().str, thd->query().length,
                          thd->binlog_evt_union.unioned_events_trans, false,
                          false, errcode);
    if (mysql_bin_log.write_event(&qinfo)) {
      push_warning(thd, Sql_condition::SL_WARNING, ER_UNKNOWN_ERROR,
                   "Failed to write event to binary log.");
      return true;
    }
  }

  return false;
}

/**
  Entry point called from sql_insert.cc,
  bool Sql_cmd_insert_values::execute_inner(THD *thd);

  @param thd THD
  @param dvtr Duality view content tree
  @param values clause
  @return true if error
 */
bool jdv_insert(THD *thd, const Table_ref *dvtr,
                const mem_root_deque<List_item *> &values) {
  auto scg = create_sctx_guard(thd, dvtr);
  if (values.size() > 1) {
    my_jdv_error<ER_JDV_OPERATION_NOT_SUPPORTED>("Multiple object insert");
    return true;
  }

  assert(dvtr->jdv_content_tree != nullptr);
  auto &content_tree = *(dvtr->jdv_content_tree);

  DBUG_LOG("jdv_dml", "DML-INSERT: " << SOURCE_LOCATION_CUR_FUNC << ": stmt:'"
                                     << thd->query().str << "'");

  ulonglong affected_rows = 0;
  for (List_item *li : values) {
    if (li->empty()) {
      my_jdv_error<ER_WRONG_VALUE_COUNT_ON_ROW>(1);
      return true;
    }

    for (Item *itm : *li) {
      if (!itm->fixed) {
        my_jdv_error<ER_JDV_INSERT_VALUE_NOT_FIXED>();
        return true;
      }
      Json_wrapper jw;
      String buf;
      if (get_json_wrapper(&itm, 0, &buf, "get_json_wrapper", &jw)) {
        DBUG_LOG("jdv_dml", "DML-INSERT item data type:"
                                << itm->data_type()
                                << ", error from get_json_wrapper(): "
                                << thd->get_stmt_da()->message_text());
        return true;
      }
      if (jw.empty()) {
        DBUG_LOG("jdv_dml", "DML-INSERT item data type:"
                                << itm->data_type()
                                << ", produced an empty json wrapper.");

        my_jdv_error<ER_JDV_NULL_INSERT_VALUE>();
        return true;
      }
      DBUG_LOG("jdv_dml",
               "DML-INSERT: new value: " << json_wrapper_to_string(jw));
      if (jdv_handle_insert(thd, &jw, &content_tree, &affected_rows)) {
        return true;
      }
    }
  }

  if (write_binlog(thd)) return true;

  char buff[MYSQL_ERRMSG_SIZE];
  snprintf(
      buff, sizeof(buff), ER_THD(thd, ER_JDV_DML_INFO),
      static_cast<long>(affected_rows),
      static_cast<long>(thd->get_stmt_da()->current_statement_cond_count()));
  my_ok(thd, affected_rows, 0, buff);
  return false;
}

/**
  Entry point called from sql_update.cc
  bool Sql_cmd_update::update_single_table(THD *thd);

  @param thd THD
  @param dvtr duality view
  @param seldq selected items
  @param upddq updated items
  @param[out]  affected_rows  Number of affected rows.
  @return true if error
*/
bool jdv_update(THD *thd, const Table_ref *dvtr,
                const mem_root_deque<Item *> *seldq,
                const mem_root_deque<Item *> *upddq, ulonglong *affected_rows) {
  auto scg = create_sctx_guard(thd, dvtr);
  DBUG_LOG("jdv_dml", "DML-UPDATE: " << SOURCE_LOCATION_CUR_FUNC
                                     << " for query:'" << thd->query().str
                                     << "'");

  assert(dvtr != nullptr && dvtr->is_json_duality_view() &&
         dvtr->jdv_content_tree != nullptr);
  auto *content_tree = dvtr->jdv_content_tree;

  // The following code is not currently necessary, as the Item can be
  // obtained directly from dvtr->field_translation->item.
  // It is kept for now since it is expected to come in handy when the
  // review of the execution layer changes starts.
  assert(seldq != nullptr && seldq->size() == 1);
  Item *sel_itm = seldq->front();
  assert(sel_itm->data_type() == enum_field_types::MYSQL_TYPE_JSON);
  assert(sel_itm->type() == Item::REF_ITEM);
  Item *itm = sel_itm;
  for (; itm->type() == Item::REF_ITEM;
       itm = down_cast<Item_ref *>(itm)->ref_item()) {
  }
  assert(itm->type() == Item::FUNC_ITEM);

  auto *sel_func_item = down_cast<Item_func *>(itm);
  assert(sel_func_item == dvtr->field_translation->item);
  Json_wrapper sel_jw;
  if (sel_func_item->val_json(&sel_jw)) {
    return true;
  }
  DBUG_LOG("jdv_dml",
           "DML-UPDATE: selected data: " << json_wrapper_to_string(sel_jw));

  assert(upddq != nullptr && upddq->size() == 1);
  Item *upd_itm = upddq->front();
  if (upd_itm->null_value) {
    my_jdv_error<ER_JDV_NULL_UPDATE_VALUE>();
    return true;
  }

  for (; upd_itm->type() == Item::REF_ITEM;
       upd_itm = down_cast<Item_ref *>(upd_itm)->ref_item()) {
    DBUG_LOG("jdv_dml", "DML-UPDATE: Stripping ref-layer from upd-item");
  }

  if (!upd_itm->fixed) {
    my_jdv_error<ER_JDV_UPDATE_VALUE_NOT_FIXED>();
    return true;
  }

  Json_wrapper upd_jw;
  String buf;
  if (get_json_wrapper(&upd_itm, 0, &buf, "get_json_wrapper", &upd_jw)) {
    DBUG_LOG("jdv_dml", "DML-UPDATE: item data type:" << upd_itm->data_type());
    return true;
  }
  DBUG_LOG("jdv_dml",
           "DML-UPDATE: set data to: " << json_wrapper_to_string(upd_jw));

  if (jdv_handle_update(thd, &upd_jw, &sel_jw, content_tree, affected_rows)) {
    assert(thd->is_error());
    return true;
  }

  if (write_binlog(thd)) return true;

  return false;
}

/**
  Entry point called from sql_delete.cc,
  bool Sql_cmd_delete::delete_from_single_table(THD *thd);

  @param thd THD
  @param dvtr duality view
  @param[out] affected_rows  Number of affected rows.
  @return true if error
*/
bool jdv_delete(THD *thd, const Table_ref *dvtr, ulonglong *affected_rows) {
  auto scg = create_sctx_guard(thd, dvtr);
  DBUG_LOG("jdv_dml", "DML-DELETE: " << SOURCE_LOCATION_CUR_FUNC
                                     << " for query:'" << thd->query().str);
  Item *field_xlation = dvtr->field_translation->item;

  Json_wrapper fldx_jw;
  String fldx_buf;
  if (get_json_wrapper(&field_xlation, 0, &fldx_buf, "get_json_wrapper",
                       &fldx_jw)) {
    DBUG_LOG("jdv_dml", "DML-DELETE: data type:" << field_xlation->data_type());
    return true;
  }
  DBUG_LOG("jdv_dml", "DML-DELETE: field_translation item = "
                          << json_wrapper_to_string(fldx_jw));

  assert(dvtr != nullptr && dvtr->is_json_duality_view() &&
         dvtr->jdv_content_tree != nullptr);

  if (jdv_handle_delete(thd, &fldx_jw, dvtr->jdv_content_tree, affected_rows)) {
    assert(thd->is_error());
    return true;
  }

  if (write_binlog(thd)) return true;

  return false;
}

}  // namespace jdv
