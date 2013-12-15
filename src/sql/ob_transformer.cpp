/**
 * (C) 2010-2012 Alibaba Group Holding Limited.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * version 2 as published by the Free Software Foundation.
 *
 * Version: $Id$
 *
 * ob_transformer.cpp
 *
 * Authors:
 *   Guibin Du <tianguan.dgb@taobao.com>
 *
 */
#include "ob_transformer.h"
#include "ob_table_rpc_scan.h"
#include "ob_table_mem_scan.h"
#include "ob_merge_join.h"
#include "ob_sql_expression.h"
#include "ob_filter.h"
#include "ob_project.h"
#include "ob_set_operator.h"
#include "ob_merge_union.h"
#include "ob_merge_intersect.h"
#include "ob_merge_except.h"
#include "ob_sort.h"
#include "ob_merge_distinct.h"
#include "ob_merge_groupby.h"
#include "ob_merge_join.h"
#include "ob_scalar_aggregate.h"
#include "ob_limit.h"
#include "ob_physical_plan.h"
#include "ob_add_project.h"
#include "ob_insert.h"
#include "ob_update.h"
#include "ob_delete.h"
#include "ob_explain.h"
#include "ob_explain_stmt.h"
#include "ob_delete_stmt.h"
#include "ob_update_stmt.h"
#include "ob_create_table.h"
#include "ob_create_table_stmt.h"
#include "ob_drop_table.h"
#include "ob_drop_table_stmt.h"
#include "common/ob_row_desc_ext.h"
#include "ob_create_user_stmt.h"
#include "ob_prepare.h"
#include "ob_prepare_stmt.h"
#include "ob_variable_set.h"
#include "ob_variable_set_stmt.h"
#include "ob_execute.h"
#include "ob_execute_stmt.h"
#include "ob_deallocate.h"
#include "ob_deallocate_stmt.h"
#include "tblog.h"
#include "WarningBuffer.h"
#include "common/ob_obj_cast.h"
#include "ob_ups_modify.h"
#include "ob_insert_dbsem_filter.h"
#include "ob_inc_scan.h"
#include "ob_mem_sstable_scan.h"
#include "ob_multiple_scan_merge.h"
#include "ob_multiple_get_merge.h"
#include "ob_start_trans_stmt.h"
#include "ob_start_trans.h"
#include "ob_end_trans_stmt.h"
#include "ob_end_trans.h"
#include "ob_expr_values.h"
#include "ob_ups_executor.h"
#include "ob_lock_filter.h"
#include "common/hash/ob_hashmap.h"
#include "common/ob_privilege.h"
#include "common/ob_privilege_type.h"
#include "ob_create_user_stmt.h"
#include "ob_drop_user_stmt.h"
#include "ob_grant_stmt.h"
#include "ob_revoke_stmt.h"
#include "ob_set_password_stmt.h"
#include "ob_lock_user_stmt.h"
#include "ob_rename_user_stmt.h"
#include "sql/ob_priv_executor.h"
#include "ob_dual_table_scan.h"
#include "common/ob_trace_log.h"
#include "ob_empty_row_filter.h"
#include "ob_sql_read_strategy.h"
#include "ob_alter_table_stmt.h"
#include "ob_alter_table.h"
#include "ob_alter_sys_cnf_stmt.h"
#include "ob_alter_sys_cnf.h"
#include "ob_schema_checker.h"
using namespace oceanbase::common;
using namespace oceanbase::sql;

#define TRANS_LOG(...)                                                  \
  do{                                                                   \
    snprintf(err_stat.err_msg_, MAX_ERROR_MSG, __VA_ARGS__);            \
    TBSYS_LOG(WARN, __VA_ARGS__);                                       \
  } while(0)

#define CREATE_PHY_OPERRATOR(op, type_name, physical_plan, err_stat)    \
  ({                                                                    \
  op = (type_name*)trans_malloc(sizeof(type_name));   \
  if (op == NULL) \
  { \
    err_stat.err_code_ = OB_ERR_PARSER_MALLOC_FAILED; \
    TRANS_LOG("Can not malloc space for %s", #type_name);  \
  } \
  else\
  {\
  op = new(op) type_name();    \
  op->set_phy_plan(physical_plan);              \
  if ((err_stat.err_code_ = physical_plan->store_phy_operator(op)) != OB_SUCCESS) \
  { \
    TRANS_LOG("Add physical operator failed");  \
  } \
  else\
  {\
    ob_inc_phy_operator_stat(op->get_type());\
  }\
  } \
  op;})

ObTransformer::ObTransformer(ObSqlContext &context)
{
  mem_pool_ = context.transformer_allocator_;
  OB_ASSERT(mem_pool_);
  sql_context_ = &context;
  group_agg_push_down_param_ = false;
}

ObTransformer::~ObTransformer()
{
}

inline void *ObTransformer::trans_malloc(const size_t nbyte)
{
  OB_ASSERT(mem_pool_);
  return mem_pool_->alloc(nbyte);
}

inline void ObTransformer::trans_free(void* p)
{
  OB_ASSERT(mem_pool_);
  mem_pool_->free(p);
}

int ObTransformer::generate_physical_plans(
    ObMultiLogicPlan &logical_plans,
    ObMultiPhyPlan &physical_plans,
    ErrStat& err_stat)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  // check environment
  if (NULL == sql_context_
      || NULL == sql_context_->merger_rpc_proxy_
      || NULL == sql_context_->schema_manager_
      || NULL == sql_context_->session_info_)
  {
    ret = OB_NOT_INIT;
    TRANS_LOG("sql_context not init");
  }
  else
  {
    // get group_agg_push_down_param_
    ObString param_str = ObString::make_string(OB_GROUP_AGG_PUSH_DOWN_PARAM);
    ObObj val;
    if (sql_context_->session_info_->get_sys_variable_value(param_str, val) != OB_SUCCESS
      || val.get_bool(group_agg_push_down_param_) != OB_SUCCESS)
    {
      TBSYS_LOG(DEBUG, "Can not get param %s", OB_GROUP_AGG_PUSH_DOWN_PARAM);
      // default off
      group_agg_push_down_param_ = false;
    }
  }
  ObLogicalPlan *logical_plan = NULL;
  ObPhysicalPlan *physical_plan = NULL;
  for (int32_t i = 0; ret == OB_SUCCESS && i < logical_plans.size(); i++)
  {
    logical_plan = logical_plans.at(i);
    if ((ret = generate_physical_plan(logical_plan, physical_plan, err_stat)) == OB_SUCCESS)
    {
      if ((ret = physical_plans.push_back(physical_plan)) != OB_SUCCESS)
      {
        TRANS_LOG("Add physical plan failed");
        break;
      }
    }
  }
  return ret;
}

int ObTransformer::generate_physical_plan(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan*& physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    int32_t* index)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  bool new_generated = false;
  if (logical_plan)
  {
    if (OB_LIKELY(NULL == physical_plan))
    {
      if ((physical_plan = (ObPhysicalPlan*)trans_malloc(sizeof(ObPhysicalPlan))) == NULL)
      {
        ret = OB_ERR_PARSER_MALLOC_FAILED;
        TRANS_LOG("Can not malloc space for ObPhysicalPlan");
      }
      else
      {
        physical_plan = new(physical_plan) ObPhysicalPlan();
        TBSYS_LOG(DEBUG, "new physical plan, addr=%p", physical_plan);
        new_generated = true;
      }
    }
    ObBasicStmt *stmt = NULL;
    if (ret == OB_SUCCESS)
    {
      if (query_id == OB_INVALID_ID)
        stmt = logical_plan->get_main_stmt();
      else
        stmt = logical_plan->get_query(query_id);
      if (stmt == NULL)
      {
        ret = OB_ERR_ILLEGAL_ID;
        TRANS_LOG("Wrong query id to find query statement");
      }
    }
    TBSYS_LOG(DEBUG, "generate physical plan for query_id=%lu stmt_type=%d",
              query_id, stmt->get_stmt_type());
    if (OB_LIKELY(ret == OB_SUCCESS))
    {
      switch (stmt->get_stmt_type())
      {
        case ObBasicStmt::T_SELECT:
          ret = gen_physical_select(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_DELETE:
          ret = gen_physical_delete_new(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_INSERT:
          ret = gen_physical_insert_new(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_REPLACE:
          ret = gen_physical_replace(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_UPDATE:
          ret = gen_physical_update_new(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_EXPLAIN:
          ret = gen_physical_explain(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_CREATE_TABLE:
          ret = gen_physical_create_table(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_DROP_TABLE:
          ret = gen_physical_drop_table(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_ALTER_TABLE:
          ret = gen_physical_alter_table(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_SHOW_TABLES:
        case ObBasicStmt::T_SHOW_VARIABLES:
        case ObBasicStmt::T_SHOW_COLUMNS:
        case ObBasicStmt::T_SHOW_SCHEMA:
        case ObBasicStmt::T_SHOW_CREATE_TABLE:
        case ObBasicStmt::T_SHOW_TABLE_STATUS:
        case ObBasicStmt::T_SHOW_SERVER_STATUS:
        case ObBasicStmt::T_SHOW_WARNINGS:
        case ObBasicStmt::T_SHOW_GRANTS:
        case ObBasicStmt::T_SHOW_PARAMETERS:
          ret = gen_physical_show(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_PREPARE:
          ret = gen_physical_prepare(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_VARIABLE_SET:
          ret = gen_physical_variable_set(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_EXECUTE:
          ret = gen_physical_execute(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_DEALLOCATE:
          ret = gen_physical_deallocate(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_START_TRANS:
          ret = gen_physical_start_trans(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_END_TRANS:
          ret = gen_physical_end_trans(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_ALTER_SYSTEM:
          ret = gen_physical_alter_system(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        case ObBasicStmt::T_CREATE_USER:
        case ObBasicStmt::T_DROP_USER:
        case ObBasicStmt::T_SET_PASSWORD:
        case ObBasicStmt::T_LOCK_USER:
        case ObBasicStmt::T_RENAME_USER:
        case ObBasicStmt::T_GRANT:
        case ObBasicStmt::T_REVOKE:
          ret = gen_physical_priv_stmt(logical_plan, physical_plan, err_stat, query_id, index);
          break;
        default:
          ret = OB_NOT_SUPPORTED;
          TRANS_LOG("Unknown logical plan, stmt_type=%d", stmt->get_stmt_type());
          break;
      }
    }
    if (ret != OB_SUCCESS && new_generated && physical_plan != NULL)
    {
      physical_plan->~ObPhysicalPlan();
      trans_free(physical_plan);
      physical_plan = NULL;
    }
  }
  return ret;
}

template <class T>
int ObTransformer::get_stmt(
    ObLogicalPlan *logical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    T *& stmt)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  /* get statement */
  TBSYS_LOG(DEBUG, "999 enter func %s\n", __func__);
  if (query_id == OB_INVALID_ID)
    stmt = dynamic_cast<T*>(logical_plan->get_main_stmt());
  else
    stmt = dynamic_cast<T*>(logical_plan->get_query(query_id));
  if (stmt == NULL)
  {
    err_stat.err_code_ = OB_ERR_PARSER_SYNTAX;
    TRANS_LOG("Get Stmt error");
  }
  return ret;
}

template <class T>
int ObTransformer::add_phy_query(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    T * stmt,
    ObPhyOperator *phy_op,
    int32_t* index
    )
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  if (query_id == OB_INVALID_ID || stmt == dynamic_cast<T*>(logical_plan->get_main_stmt()))
    ret = physical_plan->add_phy_query(phy_op, index, true);
  else
    ret = physical_plan->add_phy_query(phy_op, index);
  if (ret != OB_SUCCESS)
    TRANS_LOG("Add query of physical plan failed");
  return ret;
}


int ObTransformer::gen_physical_select(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    int32_t* index)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObSelectStmt  *select_stmt = NULL;
  ObPhyOperator *result_op = NULL;

  TBSYS_LOG(DEBUG, "999 enter func %s\n", __func__);
  /* get statement */
  if ((ret = get_stmt(logical_plan, err_stat, query_id, select_stmt)) != OB_SUCCESS)
  {
  }
  else if (select_stmt->is_for_update())
  {
    if ((ret = gen_phy_select_for_update(
                   logical_plan,
                   physical_plan,
                   err_stat,
                   query_id,
                   index)) != OB_SUCCESS)
    {
      //TRANS_LOG("Transform select for update statement failed");
    }
  }
  else
  {
    ObSelectStmt::SetOperator set_type = select_stmt->get_set_op();
  	TBSYS_LOG(DEBUG, "999 select_stmt %p\n", select_stmt);
    if (set_type != ObSelectStmt::NONE)
    {
      ObSetOperator *set_op = NULL;
      if (ret == OB_SUCCESS)
      {
        switch (set_type)
        {
          case ObSelectStmt::UNION :
          {
  					TBSYS_LOG(DEBUG, "999 enter case 1");
            ObMergeUnion *union_op = NULL;
            CREATE_PHY_OPERRATOR(union_op, ObMergeUnion, physical_plan, err_stat);
            set_op = union_op;
            break;
          }
          case ObSelectStmt::INTERSECT :
          {
  					TBSYS_LOG(DEBUG, "999 enter case 2");
            ObMergeIntersect *intersect_op = NULL;
            CREATE_PHY_OPERRATOR(intersect_op, ObMergeIntersect, physical_plan, err_stat);
            set_op = intersect_op;
            break;
          }
          case ObSelectStmt::EXCEPT :
          {
  					TBSYS_LOG(DEBUG, "999 enter case 3");
            ObMergeExcept *except_op = NULL;
            CREATE_PHY_OPERRATOR(except_op, ObMergeExcept, physical_plan, err_stat);
            set_op = except_op;
            break;
          }
          default:
            break;
        }
        if (OB_SUCCESS == ret)  // ret is a reference to err_stat.err_code_
        {
  					TBSYS_LOG(DEBUG, "999 enter case 5");
          set_op->set_distinct(select_stmt->is_set_distinct() ? true : false);
        }
      }
      int32_t lidx = OB_INVALID_INDEX;
      int32_t ridx = OB_INVALID_INDEX;
      if (ret == OB_SUCCESS)
      {
  			TBSYS_LOG(DEBUG, "999 enter case 6");
        ret = gen_physical_select(
                 logical_plan,
                 physical_plan,
                 err_stat,
                 select_stmt->get_left_query_id(),
                 &lidx);
      }
      if (ret == OB_SUCCESS)
      {
  			TBSYS_LOG(DEBUG, "999 enter case 7");
        ret = gen_physical_select(
                 logical_plan,
                 physical_plan,
                 err_stat,
                 select_stmt->get_right_query_id(),
                 &ridx);
      }

      if (ret == OB_SUCCESS)
      {
  			TBSYS_LOG(DEBUG, "999 enter case 8");
        ObPhyOperator *left_op = physical_plan->get_phy_query(lidx);
        ObPhyOperator *right_op = physical_plan->get_phy_query(ridx);
        ObSelectStmt *lselect = dynamic_cast<ObSelectStmt*>(logical_plan->get_query(select_stmt->get_left_query_id()));
        ObSelectStmt *rselect = dynamic_cast<ObSelectStmt*>(logical_plan->get_query(select_stmt->get_right_query_id()));
        if (set_type != ObSelectStmt::UNION || select_stmt->is_set_distinct())
        {
          // 1
          // select c1+c2 from tbl
          // union
          // select c3+c4 rom tbl
          // order by 1;

          // 2
          // select c1+c2 as cc from tbl
          // union
          // select c3+c4 from tbl
          // order by cc;

          // there must be a Project operator on union part,
          // so do not worry non-column expr appear in sot operator

          //CREATE sort operators
          /* Create first sort operator */
          ObSort *left_sort = NULL;
          if (CREATE_PHY_OPERRATOR(left_sort, ObSort, physical_plan, err_stat) == NULL)
          {
          }
          else if (ret == OB_SUCCESS && (ret = left_sort->set_child(0, *left_op)) != OB_SUCCESS)
          {
             TRANS_LOG("Set child of sort operator failed");
          }
          ObSqlRawExpr *sort_expr = NULL;
          for (int32_t i = 0; ret == OB_SUCCESS && i < lselect->get_select_item_size(); i++)
          {
            sort_expr = logical_plan->get_expr(lselect->get_select_item(i).expr_id_);
            if (sort_expr == NULL || sort_expr->get_expr() == NULL)
            {
              ret = OB_ERR_ILLEGAL_ID;
              TRANS_LOG("Get internal expression failed");
              break;
            }
            ret = left_sort->add_sort_column(sort_expr->get_table_id(), sort_expr->get_column_id(), true);
            if (ret != OB_SUCCESS)
            {
              TRANS_LOG("Add sort column failed");
            }
          }

          /* Create second sort operator */
          ObSort *right_sort = NULL;
          if (ret == OB_SUCCESS)
            CREATE_PHY_OPERRATOR(right_sort, ObSort, physical_plan, err_stat);
          if (ret == OB_SUCCESS && (ret = right_sort->set_child(0 /* first child */, *right_op)) != OB_SUCCESS)
          {
             TRANS_LOG("Set child of sort operator failed");
          }
          for (int32_t i = 0; ret == OB_SUCCESS && i < rselect->get_select_item_size(); i++)
          {
            sort_expr = logical_plan->get_expr(rselect->get_select_item(i).expr_id_);
            if (sort_expr == NULL || sort_expr->get_expr() == NULL)
            {
              ret = OB_ERR_ILLEGAL_ID;
              TRANS_LOG("Get internal expression failed");
              break;
            }
            ret = right_sort->add_sort_column(sort_expr->get_table_id(), sort_expr->get_column_id(), true);
            if (ret != OB_SUCCESS)
            {
              TRANS_LOG("Add sort column failed");
              break;
            }
          }
          left_op = left_sort;
          right_op = right_sort;
        }
        OB_ASSERT(NULL != set_op);
        set_op->set_child(0 /* first child */, *left_op);
        set_op->set_child(1 /* second child */, *right_op);
      }
      result_op = set_op;

      // generate physical plan for order by
      if (ret == OB_SUCCESS && select_stmt->get_order_item_size() > 0)
        ret = gen_phy_order_by(logical_plan, physical_plan, err_stat, select_stmt, result_op, result_op, true);

      // generate physical plan for limit
      if (ret == OB_SUCCESS && select_stmt->has_limit())
      {
        ret = gen_phy_limit(logical_plan, physical_plan, err_stat, select_stmt, result_op, result_op);
      }

      if (ret == OB_SUCCESS)
      {
        ret = add_phy_query(logical_plan, physical_plan, err_stat, query_id, select_stmt, result_op, index);
      }
    }
    else
    {
      /* Normal Select Statement */
      bool group_agg_pushed_down = false;
      bool limit_pushed_down = false;

      // 1. generate physical plan for base-table/outer-join-table/temporary table
      ObList<ObPhyOperator*> phy_table_list;
      ObList<ObBitSet<> > bitset_list;
      ObList<ObSqlRawExpr*> remainder_cnd_list;
      ObList<ObSqlRawExpr*> none_columnlize_alias;
      if (ret == OB_SUCCESS)
        ret = gen_phy_tables(
                  logical_plan,
                  physical_plan,
                  err_stat,
                  select_stmt,
                  group_agg_pushed_down,
                  limit_pushed_down,
                  phy_table_list,
                  bitset_list,
                  remainder_cnd_list,
                  none_columnlize_alias);

      // 2. Join all tables
      if (ret == OB_SUCCESS && phy_table_list.size() > 1)
        ret = gen_phy_joins(
                  logical_plan,
                  physical_plan,
                  err_stat,
                  select_stmt,
                  phy_table_list,
                  bitset_list,
                  remainder_cnd_list,
                  none_columnlize_alias);
      if (ret == OB_SUCCESS)
        phy_table_list.pop_front(result_op);

      // 3. add filter(s) to the join-op/table-scan-op result
      if (ret == OB_SUCCESS && remainder_cnd_list.size() >= 1)
      {
        ObFilter *filter_op = NULL;
        CREATE_PHY_OPERRATOR(filter_op, ObFilter, physical_plan, err_stat);
        if (ret == OB_SUCCESS && (ret = filter_op->set_child(0, *result_op)) != OB_SUCCESS)
        {
          TRANS_LOG("Set child of filter plan failed");
        }
        oceanbase::common::ObList<ObSqlRawExpr*>::iterator cnd_it;
        for (cnd_it = remainder_cnd_list.begin();
            ret == OB_SUCCESS && cnd_it != remainder_cnd_list.end();
            cnd_it++)
        {
          ObSqlExpression *filter = ObSqlExpression::alloc();
          if (NULL == filter
              || (ret = (*cnd_it)->fill_sql_expression(
                                    *filter,
                                    this,
                                    logical_plan,
                                    physical_plan)) != OB_SUCCESS
              || (ret = filter_op->add_filter(filter)) != OB_SUCCESS)
          {
            TRANS_LOG("Add filters to filter plan failed");
            break;
          }
        }
        if (ret == OB_SUCCESS)
          result_op = filter_op;
      }

      // 4. generate physical plan for group by/aggregate
      if (ret == OB_SUCCESS && (select_stmt->get_group_expr_size() > 0 || select_stmt->get_agg_fun_size() > 0))
      {
        if (group_agg_pushed_down == false)
        {
          if (select_stmt->get_group_expr_size() > 0)
            ret = gen_phy_group_by(logical_plan, physical_plan, err_stat, select_stmt, result_op, result_op);
          else if (select_stmt->get_agg_fun_size() > 0)
            ret = gen_phy_scalar_aggregate(logical_plan, physical_plan, err_stat, select_stmt, result_op, result_op);
        }
        if (ret == OB_SUCCESS && none_columnlize_alias.size() > 0)
        {
          // compute complex expressions that contain aggreate functions
          ObAddProject *project_op = NULL;
          oceanbase::common::ObList<ObSqlRawExpr*>::iterator alias_it;
          for (alias_it = none_columnlize_alias.begin(); ret == OB_SUCCESS && alias_it != none_columnlize_alias.end();)
          {
            if ((*alias_it)->is_columnlized() == false
              && (*alias_it)->is_contain_aggr() && (*alias_it)->get_expr()->get_expr_type() != T_REF_COLUMN)
            {
              if (project_op == NULL)
              {
                CREATE_PHY_OPERRATOR(project_op, ObAddProject, physical_plan, err_stat);
                if (ret == OB_SUCCESS && (ret = project_op->set_child(0, *result_op)) != OB_SUCCESS)
                {
                  TRANS_LOG("Set child of filter plan failed");
                  break;
                }
              }
              (*alias_it)->set_columnlized(true);
              ObSqlExpression alias_expr;
              if ((ret = (*alias_it)->fill_sql_expression(
                                        alias_expr,
                                        this,
                                        logical_plan,
                                        physical_plan)) != OB_SUCCESS
                || (ret = project_op->add_output_column(alias_expr)) != OB_SUCCESS)
              {
                TRANS_LOG("Add project on aggregate plan failed");
                break;
              }
            }
            common::ObList<ObSqlRawExpr*>::iterator del_alias = alias_it;
            alias_it++;
            if ((ret = none_columnlize_alias.erase(del_alias)) != OB_SUCCESS)
            {
              TRANS_LOG("Add project on aggregate plan failed");
              break;
            }
          }
          if (ret == OB_SUCCESS && project_op != NULL)
            result_op = project_op;
        }
      }

      // 5. generate physical plan for having
      if (ret == OB_SUCCESS && select_stmt->get_having_expr_size() > 0)
      {
        ObFilter *having_op = NULL;
        CREATE_PHY_OPERRATOR(having_op, ObFilter, physical_plan, err_stat);
        ObSqlRawExpr *having_expr;
        int32_t num = select_stmt->get_having_expr_size();
        for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
        {
          having_expr = logical_plan->get_expr(select_stmt->get_having_expr_id(i));
          OB_ASSERT(NULL != having_expr);
          ObSqlExpression *having_filter = ObSqlExpression::alloc();
          if (NULL == having_filter
              || (ret = having_expr->fill_sql_expression(
                                      *having_filter,
                                      this,
                                      logical_plan,
                                      physical_plan)) != OB_SUCCESS
              || (ret = having_op->add_filter(having_filter)) != OB_SUCCESS)
          {
            TRANS_LOG("Add filters to having plan failed");
            break;
          }
        }
        if (ret == OB_SUCCESS)
        {
          if ((ret = having_op->set_child(0, *result_op)) == OB_SUCCESS)
          {
            result_op = having_op;
          }
          else
          {
            TRANS_LOG("Add child of having plan failed");
          }
        }
      }

      // 6. generate physical plan for distinct
      if (ret == OB_SUCCESS && select_stmt->is_distinct())
        ret = gen_phy_distinct(logical_plan, physical_plan, err_stat, select_stmt, result_op, result_op);

      // 7. generate physical plan for order by
      if (ret == OB_SUCCESS && select_stmt->get_order_item_size() > 0)
        ret = gen_phy_order_by(logical_plan, physical_plan, err_stat, select_stmt, result_op, result_op);

      // 8. generate physical plan for limit
      if (ret == OB_SUCCESS && limit_pushed_down == false && select_stmt->has_limit())
      {
        ret = gen_phy_limit(logical_plan, physical_plan, err_stat, select_stmt, result_op, result_op);
      }

      // 8. generate physical plan for select clause
      if (ret == OB_SUCCESS && select_stmt->get_select_item_size() > 0)
      {
        ObProject *project_op = NULL;
        CREATE_PHY_OPERRATOR(project_op, ObProject, physical_plan, err_stat);
        if (ret == OB_SUCCESS && (ret = project_op->set_child(0, *result_op)) != OB_SUCCESS)
        {
          TRANS_LOG("Add child of project plan failed");
        }

        ObSqlRawExpr *select_expr;
        int32_t num = select_stmt->get_select_item_size();
        for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
        {
          const SelectItem& select_item = select_stmt->get_select_item(i);
          select_expr = logical_plan->get_expr(select_item.expr_id_);
          OB_ASSERT(NULL != select_expr);
          if (select_item.is_real_alias_ && select_expr->is_columnlized())
          {
            ObBinaryRefRawExpr col_raw(OB_INVALID_ID, select_expr->get_column_id(), T_REF_COLUMN);
            ObSqlRawExpr col_sql_raw(*select_expr);
            col_sql_raw.set_expr(&col_raw);
            ObSqlExpression  col_expr;
            if ((ret = col_sql_raw.fill_sql_expression(col_expr)) != OB_SUCCESS
              || (ret = project_op ->add_output_column(col_expr)) != OB_SUCCESS)
            {
              TRANS_LOG("Add output column to project plan failed");
              break;
            }
          }
          else
          {
            ObSqlExpression  col_expr;
            if ((ret = select_expr->fill_sql_expression(
                                        col_expr,
                                        this,
                                        logical_plan,
                                        physical_plan)) != OB_SUCCESS
              || (ret = project_op ->add_output_column(col_expr)) != OB_SUCCESS)
            {
              TRANS_LOG("Add output column to project plan failed");
              break;
            }
          }
          select_expr->set_columnlized(true);
        }
        if (ret == OB_SUCCESS)
          result_op = project_op;
      }

      if (ret == OB_SUCCESS)
      {
        ret = add_phy_query(logical_plan, physical_plan, err_stat, query_id, select_stmt, result_op, index);
      }
    }
  }
  return ret;
}

int ObTransformer::gen_phy_limit(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObSelectStmt *select_stmt,
    ObPhyOperator *in_op,
    ObPhyOperator *&out_op)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObLimit *limit_op = NULL;
  if (!select_stmt->has_limit())
  {
    /* skip */
  }
  else if (CREATE_PHY_OPERRATOR(limit_op, ObLimit, physical_plan, err_stat) == NULL)
  {
  }
  else if ((ret = limit_op->set_child(0, *in_op)) != OB_SUCCESS)
  {
    TRANS_LOG("Add child of limit plan failed");
  }
  else
  {
    ObSqlExpression limit_count;
    ObSqlExpression limit_offset;
    ObSqlExpression *ptr = &limit_count;
    uint64_t id = select_stmt->get_limit_expr_id();
    int64_t i = 0;
    for (; ret == OB_SUCCESS && i < 2;
         i++, id = select_stmt->get_offset_expr_id(), ptr = &limit_offset)
    {
      ObSqlRawExpr *raw_expr = NULL;
      if (id == OB_INVALID_ID)
      {
        continue;
      }
      else if ((raw_expr = logical_plan->get_expr(id)) == NULL)
      {
        ret = OB_ERR_ILLEGAL_ID;
        TRANS_LOG("Wrong internal expression id = %lu, ret=%d", id, ret);
        break;
      }
      else if ((ret = raw_expr->fill_sql_expression(
                                  *ptr,
                                  this,
                                  logical_plan,
                                  physical_plan)) != OB_SUCCESS)
      {
        TRANS_LOG("Add limit/offset faild");
        break;
      }
    }
    if (ret == OB_SUCCESS && (ret = limit_op->set_limit(limit_count, limit_offset)) != OB_SUCCESS)
    {
      TRANS_LOG("Set limit/offset failed, ret=%d", ret);
    }
  }
  if (ret == OB_SUCCESS)
    out_op = limit_op;
  return ret;
}

int ObTransformer::gen_phy_order_by(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObSelectStmt *select_stmt,
    ObPhyOperator *in_op,
    ObPhyOperator *&out_op,
    bool use_generated_id)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObSort *sort_op = NULL;
  ObProject *project_op = NULL;
  CREATE_PHY_OPERRATOR(sort_op, ObSort, physical_plan, err_stat);

  ObSqlRawExpr *order_expr;
  int32_t num = select_stmt->get_order_item_size();
  for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
  {
    const OrderItem& order_item = select_stmt->get_order_item(i);
    order_expr = logical_plan->get_expr(order_item.expr_id_);
    if (order_expr->get_expr()->is_const())
    {
      // do nothing, const column is of no usage for sorting
    }
    else if (order_expr->get_expr()->get_expr_type() == T_REF_COLUMN)
    {
      ObBinaryRefRawExpr *col_expr = dynamic_cast<ObBinaryRefRawExpr*>(order_expr->get_expr());
      if ((ret = sort_op->add_sort_column(
                              use_generated_id? order_expr->get_table_id() : col_expr->get_first_ref_id(),
                              use_generated_id? order_expr->get_column_id() : col_expr->get_second_ref_id(),
                              order_item.order_type_ == OrderItem::ASC ? true : false
                              )) != OB_SUCCESS)
      {
        TRANS_LOG("Add sort column to sort plan failed");
        break;
      }
    }
    else
    {
      if (!project_op)
      {
        CREATE_PHY_OPERRATOR(project_op, ObAddProject, physical_plan, err_stat);
        if (ret != OB_SUCCESS)
          break;
        if ((ret = project_op->set_child(0, *in_op)) != OB_SUCCESS)
        {
          TRANS_LOG("Add child of project plan failed");
          break;
        }
      }
      ObSqlExpression col_expr;
      if ((ret = order_expr->fill_sql_expression(
                                col_expr,
                                this,
                                logical_plan,
                                physical_plan)) != OB_SUCCESS
        || (ret = project_op->add_output_column(col_expr)) != OB_SUCCESS)
      {
        TRANS_LOG("Add output column to project plan failed");
        break;
      }
      if ((ret = sort_op->add_sort_column(
                              order_expr->get_table_id(),
                              order_expr->get_column_id(),
                              order_item.order_type_ == OrderItem::ASC ? true : false
                              )) != OB_SUCCESS)
      {
        TRANS_LOG("Add sort column to sort plan failed");
        break;
      }
    }
  }
  if (ret == OB_SUCCESS)
  {
    if (project_op)
      ret = sort_op->set_child(0, *project_op);
    else
      ret = sort_op->set_child(0, *in_op);
    if (ret != OB_SUCCESS)
    {
      TRANS_LOG("Add child of sort plan failed");
    }
  }
  if (ret == OB_SUCCESS)
  {
    if (sort_op->get_sort_column_size() > 0)
      out_op = sort_op;
    else
      out_op = in_op;
  }

  return ret;
}

int ObTransformer::gen_phy_distinct(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObSelectStmt *select_stmt,
    ObPhyOperator *in_op,
    ObPhyOperator *&out_op)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObMergeDistinct *distinct_op = NULL;
  ObSort *sort_op = NULL;
  ObProject *project_op = NULL;
  if (ret == OB_SUCCESS)
    CREATE_PHY_OPERRATOR(sort_op, ObSort, physical_plan, err_stat);
  if (ret == OB_SUCCESS)
    CREATE_PHY_OPERRATOR(distinct_op, ObMergeDistinct, physical_plan, err_stat);
  if (ret == OB_SUCCESS && (ret = distinct_op->set_child(0, *sort_op)) != OB_SUCCESS)
  {
    TRANS_LOG("Add child of distinct plan failed");
  }

  ObSqlRawExpr *select_expr;
  int32_t num = select_stmt->get_select_item_size();
  for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
  {
    const SelectItem& select_item = select_stmt->get_select_item(i);
    select_expr = logical_plan->get_expr(select_item.expr_id_);
    if (select_expr->get_expr()->is_const())
    {
      // do nothing, const column is of no usage for sorting
    }
    else if (select_item.is_real_alias_)
    {
      ret = sort_op->add_sort_column(select_expr->get_table_id(), select_expr->get_column_id(), true);
      if (ret != OB_SUCCESS)
      {
        TRANS_LOG("Add sort column of sort plan failed");
        break;
      }
      ret = distinct_op->add_distinct_column(select_expr->get_table_id(), select_expr->get_column_id());
      if (ret != OB_SUCCESS)
      {
        TRANS_LOG("Add distinct column of distinct plan failed");
        break;
      }
    }
    else if (select_expr->get_expr()->get_expr_type() == T_REF_COLUMN)
    {
      ObBinaryRefRawExpr *col_expr = dynamic_cast<ObBinaryRefRawExpr*>(select_expr->get_expr());
      ret = sort_op->add_sort_column(col_expr->get_first_ref_id(), col_expr->get_second_ref_id(), true);
      if (ret != OB_SUCCESS)
      {
        TRANS_LOG("Add sort column to sort plan failed");
        break;
      }
      ret = distinct_op->add_distinct_column(col_expr->get_first_ref_id(), col_expr->get_second_ref_id());
      if (ret != OB_SUCCESS)
      {
        TRANS_LOG("Add distinct column to distinct plan failed");
        break;
      }
    }
    else
    {
      if (!project_op)
      {
        CREATE_PHY_OPERRATOR(project_op, ObAddProject, physical_plan, err_stat);
        if (ret != OB_SUCCESS)
          break;
        if ((ret = project_op->set_child(0, *in_op)) != OB_SUCCESS)
        {
          TRANS_LOG("Add child of project plan failed");
          break;
        }
      }
      ObSqlExpression col_expr;
      if ((ret = select_expr->fill_sql_expression(
                                  col_expr,
                                  this,
                                  logical_plan,
                                  physical_plan)) != OB_SUCCESS
        || (ret = project_op->add_output_column(col_expr)) != OB_SUCCESS)
      {
        TRANS_LOG("Add output column to project plan failed");
        break;
      }
      if ((ret = sort_op->add_sort_column(
                              select_expr->get_table_id(),
                              select_expr->get_column_id(),
                              true)) != OB_SUCCESS)
      {
        TRANS_LOG("Add sort column to sort plan failed");
        break;
      }
      if ((ret = distinct_op->add_distinct_column(
                                  select_expr->get_table_id(),
                                  select_expr->get_column_id())) != OB_SUCCESS)
      {
        TRANS_LOG("Add distinct column to distinct plan failed");
        break;
      }
    }
  }
  if (ret == OB_SUCCESS)
  {
    if (project_op)
      ret = sort_op->set_child(0, *project_op);
    else
      ret = sort_op->set_child(0, *in_op);
    if (ret != OB_SUCCESS)
    {
      TRANS_LOG("Add child to sort plan failed");
    }
  }
  if (ret == OB_SUCCESS)
  {
    out_op = distinct_op;
  }

  return ret;
}

int ObTransformer::gen_phy_group_by(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObSelectStmt *select_stmt,
    ObPhyOperator *in_op,
    ObPhyOperator *&out_op)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObMergeGroupBy *group_op = NULL;
  ObSort *sort_op = NULL;
  ObProject *project_op = NULL;
  if (ret == OB_SUCCESS)
    CREATE_PHY_OPERRATOR(sort_op, ObSort, physical_plan, err_stat);
  if (ret == OB_SUCCESS)
    CREATE_PHY_OPERRATOR(group_op, ObMergeGroupBy, physical_plan, err_stat);
  if (ret == OB_SUCCESS && (ret = group_op->set_child(0, *sort_op)) != OB_SUCCESS)
  {
    TRANS_LOG("Add child of group by plan faild");
  }

  ObSqlRawExpr *group_expr;
  int32_t num = select_stmt->get_group_expr_size();
  for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
  {
    group_expr = logical_plan->get_expr(select_stmt->get_group_expr_id(i));
    OB_ASSERT(NULL != group_expr);
    if (group_expr->get_expr()->get_expr_type() == T_REF_COLUMN)
    {
      ObBinaryRefRawExpr *col_expr = dynamic_cast<ObBinaryRefRawExpr*>(group_expr->get_expr());
      OB_ASSERT(NULL != col_expr);
      ret = sort_op->add_sort_column(col_expr->get_first_ref_id(), col_expr->get_second_ref_id(), true);
      if (ret != OB_SUCCESS)
      {
        TRANS_LOG("Add sort column faild, table_id=%lu, column_id=%lu",
            col_expr->get_first_ref_id(), col_expr->get_second_ref_id());
        break;
      }
      ret = group_op->add_group_column(col_expr->get_first_ref_id(), col_expr->get_second_ref_id());
      if (ret != OB_SUCCESS)
      {
        TRANS_LOG("Add group column faild, table_id=%lu, column_id=%lu",
            col_expr->get_first_ref_id(), col_expr->get_second_ref_id());
        break;
      }
    }
    else if (group_expr->get_expr()->is_const())
    {
      // do nothing, const column is of no usage for sorting
    }
    else
    {
      if (!project_op)
      {
        CREATE_PHY_OPERRATOR(project_op, ObAddProject, physical_plan, err_stat);
        if (ret != OB_SUCCESS)
          break;
        if ((ret = project_op->set_child(0, *in_op)) != OB_SUCCESS)
        {
          TRANS_LOG("Add child of project plan faild");
          break;
        }
      }
      ObSqlExpression col_expr;
      if ((ret = group_expr->fill_sql_expression(
                                col_expr,
                                this,
                                logical_plan,
                                physical_plan)) != OB_SUCCESS
        || (ret = project_op->add_output_column(col_expr)) != OB_SUCCESS)
      {
        TRANS_LOG("Add output column to project plan faild");
        break;
      }
      if ((ret = sort_op->add_sort_column(
                              group_expr->get_table_id(),
                              group_expr->get_column_id(),
                              true)) != OB_SUCCESS)
      {
        TRANS_LOG("Add sort column to sort plan faild");
        break;
      }
      if ((ret = group_op->add_group_column(
                              group_expr->get_table_id(),
                              group_expr->get_column_id())) != OB_SUCCESS)
      {
        TRANS_LOG("Add group column to group plan faild");
        break;
      }
    }
  }
  if (ret == OB_SUCCESS)
  {
    if (project_op)
      ret = sort_op->set_child(0, *project_op);
    else
      ret = sort_op->set_child(0, *in_op);
    if (ret != OB_SUCCESS)
    {
      TRANS_LOG("Add child to sort plan faild");
    }
  }

  num = select_stmt->get_agg_fun_size();
  ObSqlRawExpr *agg_expr = NULL;
  for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
  {
    agg_expr = logical_plan->get_expr(select_stmt->get_agg_expr_id(i));
    OB_ASSERT(NULL != agg_expr);
    if (agg_expr->get_expr()->is_aggr_fun())
    {
      ObSqlExpression new_agg_expr;
      if ((ret = agg_expr->fill_sql_expression(
                              new_agg_expr,
                              this,
                              logical_plan,
                              physical_plan)) != OB_SUCCESS
        || (ret = group_op->add_aggr_column(new_agg_expr)) != OB_SUCCESS)
      {
        TRANS_LOG("Add aggregate function to group plan faild");
        break;
      }
    }
    else
    {
      TRANS_LOG("Wrong aggregate function, exp_id = %lu", agg_expr->get_expr_id());
      break;
    }
    agg_expr->set_columnlized(true);
  }
  if (ret == OB_SUCCESS)
    out_op = group_op;

  return ret;
}

int ObTransformer::gen_phy_scalar_aggregate(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObSelectStmt *select_stmt,
    ObPhyOperator *in_op,
    ObPhyOperator *&out_op)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObScalarAggregate *scalar_agg_op = NULL;
  CREATE_PHY_OPERRATOR(scalar_agg_op, ObScalarAggregate, physical_plan, err_stat);
  if (ret == OB_SUCCESS && (ret = scalar_agg_op->set_child(0, *in_op)) != OB_SUCCESS)
  {
    TRANS_LOG("Add child of scalar aggregate plan failed");
  }

  int32_t num = select_stmt->get_agg_fun_size();
  ObSqlRawExpr *agg_expr = NULL;
  for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
  {
    agg_expr = logical_plan->get_expr(select_stmt->get_agg_expr_id(i));
    OB_ASSERT(NULL != agg_expr);
    if (agg_expr->get_expr()->is_aggr_fun())
    {
      ObSqlExpression new_agg_expr;
      if ((ret = agg_expr->fill_sql_expression(
                    new_agg_expr,
                    this,
                    logical_plan,
                    physical_plan)) != OB_SUCCESS
        || (ret = scalar_agg_op->add_aggr_column(new_agg_expr)) != OB_SUCCESS)
      {
        TRANS_LOG("Add aggregate function to scalar aggregate plan failed");
        break;
      }
    }
    else
    {
      TRANS_LOG("wrong aggregate function, exp_id = %ld", agg_expr->get_expr_id());
      break;
    }
    agg_expr->set_columnlized(true);
  }
  if (ret == OB_SUCCESS)
    out_op = scalar_agg_op;

  return ret;
}

int ObTransformer::gen_phy_joins(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObSelectStmt *select_stmt,
    oceanbase::common::ObList<ObPhyOperator*>& phy_table_list,
    oceanbase::common::ObList<ObBitSet<> >& bitset_list,
    oceanbase::common::ObList<ObSqlRawExpr*>& remainder_cnd_list,
    oceanbase::common::ObList<ObSqlRawExpr*>& none_columnlize_alias)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  while (ret == OB_SUCCESS && phy_table_list.size() > 1)
  {
    ObAddProject *project_op = NULL;
    ObMergeJoin *join_op = NULL;
    CREATE_PHY_OPERRATOR(join_op, ObMergeJoin, physical_plan, err_stat);
    if (ret != OB_SUCCESS)
      break;
    join_op->set_join_type(ObJoin::INNER_JOIN);

    ObBitSet<> join_table_bitset;
    ObBitSet<> left_table_bitset;
    ObBitSet<> right_table_bitset;
    ObSort *left_sort = NULL;
    ObSort *right_sort = NULL;
    oceanbase::common::ObList<ObSqlRawExpr*>::iterator cnd_it;
    oceanbase::common::ObList<ObSqlRawExpr*>::iterator del_it;
    for (cnd_it = remainder_cnd_list.begin(); ret == OB_SUCCESS && cnd_it != remainder_cnd_list.end(); )
    {
      if ((*cnd_it)->get_expr()->is_join_cond() && join_table_bitset.is_empty())
      {
        ObBinaryOpRawExpr *join_cnd = dynamic_cast<ObBinaryOpRawExpr*>((*cnd_it)->get_expr());
        ObBinaryRefRawExpr *lexpr = dynamic_cast<ObBinaryRefRawExpr*>(join_cnd->get_first_op_expr());
        ObBinaryRefRawExpr *rexpr = dynamic_cast<ObBinaryRefRawExpr*>(join_cnd->get_second_op_expr());
        int32_t left_bit_idx = select_stmt->get_table_bit_index(lexpr->get_first_ref_id());
        int32_t right_bit_idx = select_stmt->get_table_bit_index(rexpr->get_first_ref_id());
        CREATE_PHY_OPERRATOR(left_sort, ObSort, physical_plan, err_stat);
        if (ret != OB_SUCCESS)
          break;
        ret = left_sort->add_sort_column(lexpr->get_first_ref_id(), lexpr->get_second_ref_id(), true);
        if (ret != OB_SUCCESS)
        {
          TRANS_LOG("Add sort column faild table_id=%lu, column_id =%lu",
              lexpr->get_first_ref_id(), lexpr->get_second_ref_id());
          break;
        }
        CREATE_PHY_OPERRATOR(right_sort, ObSort, physical_plan, err_stat);
        if (ret != OB_SUCCESS)
          break;
        ret = right_sort->add_sort_column(rexpr->get_first_ref_id(), rexpr->get_second_ref_id(), true);
        if (ret != OB_SUCCESS)
        {
          TRANS_LOG("Add sort column faild table_id=%lu, column_id =%lu",
              lexpr->get_first_ref_id(), lexpr->get_second_ref_id());
          break;
        }

        oceanbase::common::ObList<ObPhyOperator*>::iterator table_it = phy_table_list.begin();
        oceanbase::common::ObList<ObPhyOperator*>::iterator del_table_it;
        oceanbase::common::ObList<ObBitSet<> >::iterator bitset_it = bitset_list.begin();
        oceanbase::common::ObList<ObBitSet<> >::iterator del_bitset_it;
        ObPhyOperator *left_table_op = NULL;
        ObPhyOperator *right_table_op = NULL;
        while (ret == OB_SUCCESS
            && (!left_table_op || !right_table_op)
            && table_it != phy_table_list.end()
            && bitset_it != bitset_list.end())
        {
          if (bitset_it->has_member(left_bit_idx))
          {
            left_table_op = *table_it;
            left_table_bitset = *bitset_it;
            del_table_it = table_it;
            del_bitset_it = bitset_it;
            table_it++;
            bitset_it++;
            if ((ret = phy_table_list.erase(del_table_it)) != OB_SUCCESS)
              break;
            if ((ret = bitset_list.erase(del_bitset_it)) != OB_SUCCESS)
              break;
          }
          else if (bitset_it->has_member(right_bit_idx))
          {
            right_table_op = *table_it;
            right_table_bitset = *bitset_it;
            del_table_it = table_it;
            del_bitset_it = bitset_it;
            table_it++;
            bitset_it++;
            if ((ret = phy_table_list.erase(del_table_it)) != OB_SUCCESS)
            {
              TRANS_LOG("Generate join plan faild");
              break;
            }
            if ((ret = bitset_list.erase(del_bitset_it)) != OB_SUCCESS)
            {
              TRANS_LOG("Generate join plan faild");
              break;
            }
          }
          else
          {
            table_it++;
            bitset_it++;
          }
        }
        if (ret != OB_SUCCESS)
          break;

        // Two columns must from different table, that expression from one table has been erased in gen_phy_table()
        OB_ASSERT(left_table_op && right_table_op);
        if ((ret = left_sort->set_child(0, *left_table_op)) != OB_SUCCESS )
        {
          TRANS_LOG("Add child of join plan faild");
          break;
        }
        if ((ret = right_sort->set_child(0, *right_table_op)) != OB_SUCCESS )
        {
          TRANS_LOG("Add child of join plan faild");
          break;
        }
        ObSqlExpression join_op_cnd;
        if ((ret = (*cnd_it)->fill_sql_expression(
                                  join_op_cnd,
                                  this,
                                  logical_plan,
                                  physical_plan)) != OB_SUCCESS)
          break;
        if ((ret = join_op->add_equijoin_condition(join_op_cnd)) != OB_SUCCESS)
        {
          TRANS_LOG("Add condition of join plan faild");
          break;
        }
        join_table_bitset.add_members(left_table_bitset);
        join_table_bitset.add_members(right_table_bitset);

        del_it = cnd_it;
        cnd_it++;
        if ((ret = remainder_cnd_list.erase(del_it)) != OB_SUCCESS)
        {
          TRANS_LOG("Generate join plan faild");
          break;
        }
      }
      else if ((*cnd_it)->get_expr()->is_join_cond()
        && (*cnd_it)->get_tables_set().is_subset(join_table_bitset))
      {
        ObBinaryOpRawExpr *join_cnd = dynamic_cast<ObBinaryOpRawExpr*>((*cnd_it)->get_expr());
        ObBinaryRefRawExpr *expr1 = dynamic_cast<ObBinaryRefRawExpr*>(join_cnd->get_first_op_expr());
        ObBinaryRefRawExpr *expr2 = dynamic_cast<ObBinaryRefRawExpr*>(join_cnd->get_second_op_expr());
        int32_t bit_idx1 = select_stmt->get_table_bit_index(expr1->get_first_ref_id());
        int32_t bit_idx2 = select_stmt->get_table_bit_index(expr2->get_first_ref_id());
        if (left_table_bitset.has_member(bit_idx1))
          ret = left_sort->add_sort_column(expr1->get_first_ref_id(), expr1->get_second_ref_id(), true);
        else
          ret = right_sort->add_sort_column(expr1->get_first_ref_id(), expr1->get_second_ref_id(), true);
        if (ret != OB_SUCCESS)
        {
          TRANS_LOG("Add sort column faild table_id=%lu, column_id =%lu",
              expr1->get_first_ref_id(), expr1->get_second_ref_id());
          break;
        }
        if (right_table_bitset.has_member(bit_idx2))
          ret = right_sort->add_sort_column(expr2->get_first_ref_id(), expr2->get_second_ref_id(), true);
        else
          ret = left_sort->add_sort_column(expr2->get_first_ref_id(), expr2->get_second_ref_id(), true);
        if (ret != OB_SUCCESS)
        {
          TRANS_LOG("Add sort column faild table_id=%lu, column_id =%lu",
              expr2->get_first_ref_id(), expr2->get_second_ref_id());
          break;
        }
        ObSqlExpression join_op_cnd;
        if ((ret = ((*cnd_it)->fill_sql_expression(
                                  join_op_cnd,
                                  this,
                                  logical_plan,
                                  physical_plan))) != OB_SUCCESS
          || (ret = join_op->add_equijoin_condition(join_op_cnd)) != OB_SUCCESS)
        {
          TRANS_LOG("Add condition of join plan faild");
          break;
        }
        del_it = cnd_it;
        cnd_it++;
        if ((ret = remainder_cnd_list.erase(del_it)) != OB_SUCCESS)
        {
          TRANS_LOG("Generate join plan faild");
          break;
        }
      }
      else if ((*cnd_it)->get_tables_set().is_subset(join_table_bitset)
        && !((*cnd_it)->is_contain_alias()
        && (*cnd_it)->get_tables_set().overlap(left_table_bitset)
        && (*cnd_it)->get_tables_set().overlap(right_table_bitset)))
      {
        ObSqlExpression join_other_cnd;
        if ((ret = ((*cnd_it)->fill_sql_expression(
                                  join_other_cnd,
                                  this,
                                  logical_plan,
                                  physical_plan))) != OB_SUCCESS
          || (ret = join_op->add_other_join_condition(join_other_cnd)) != OB_SUCCESS)
        {
          TRANS_LOG("Add condition of join plan faild");
          break;
        }
        del_it = cnd_it;
        cnd_it++;
        if ((ret = remainder_cnd_list.erase(del_it)) != OB_SUCCESS)
        {
          TRANS_LOG("Generate join plan faild");
          break;
        }
      }
      else
      {
        cnd_it++;
      }
    }

    if (ret == OB_SUCCESS)
    {
      if (join_table_bitset.is_empty() == false)
      {
        // find a join condition, a merge join will be used here
        OB_ASSERT(left_sort != NULL);
        OB_ASSERT(right_sort != NULL);
        if ((ret = join_op->set_child(0, *left_sort)) != OB_SUCCESS)
        {
          TRANS_LOG("Add child of join plan faild");
          break;
        }
        if ((ret = join_op->set_child(1, *right_sort)) != OB_SUCCESS)
        {
          TRANS_LOG("Add child of join plan faild");
          break;
        }
      }
      else
      {
        // Can not find a join condition, a product join will be used here
        // FIX me, should be ObJoin, it will be fixed when Join is supported
        ObPhyOperator *op = NULL;
        if ((ret = phy_table_list.pop_front(op)) != OB_SUCCESS)
        {
          TRANS_LOG("Generate join plan faild");
          break;
        }
        if ((ret = join_op->set_child(0, *op)) != OB_SUCCESS)
        {
          TRANS_LOG("Add child of join plan faild");
          break;
        }
        if ((ret = phy_table_list.pop_front(op)) != OB_SUCCESS)
        {
          TRANS_LOG("Generate join plan faild");
          break;
        }
        if ((ret = join_op->set_child(1, *op)) != OB_SUCCESS)
        {
          TRANS_LOG("Add child of join plan faild");
          break;
        }

        bitset_list.pop_front(left_table_bitset);
        join_table_bitset.add_members(left_table_bitset);
        bitset_list.pop_front(right_table_bitset);
        join_table_bitset.add_members(right_table_bitset);
      }
    }

    // add other join conditions
    for (cnd_it = remainder_cnd_list.begin(); ret == OB_SUCCESS && cnd_it != remainder_cnd_list.end(); )
    {
      if ((*cnd_it)->is_contain_alias()
        && (*cnd_it)->get_tables_set().overlap(left_table_bitset)
        && (*cnd_it)->get_tables_set().overlap(right_table_bitset))
      {
        cnd_it++;
      }
      else if ((*cnd_it)->get_tables_set().is_subset(join_table_bitset))
      {
        ObSqlExpression other_cnd;
        if ((ret = (*cnd_it)->fill_sql_expression(
                                  other_cnd,
                                  this,
                                  logical_plan,
                                  physical_plan)) != OB_SUCCESS
          || (ret = join_op->add_other_join_condition(other_cnd)) != OB_SUCCESS)
        {
          TRANS_LOG("Add condition of join plan faild");
          break;
        }
        del_it = cnd_it;
        cnd_it++;
        if ((ret = remainder_cnd_list.erase(del_it)) != OB_SUCCESS)
        {
          TRANS_LOG("Generate join plan faild");
          break;
        }
      }
      else
      {
        cnd_it++;
      }
    }

    // columnlize the alias expression
    oceanbase::common::ObList<ObSqlRawExpr*>::iterator alias_it;
    for (alias_it = none_columnlize_alias.begin(); ret == OB_SUCCESS && alias_it != none_columnlize_alias.end(); )
    {
      if ((*alias_it)->is_columnlized())
      {
        common::ObList<ObSqlRawExpr*>::iterator del_alias = alias_it;
        alias_it++;
        if ((ret = none_columnlize_alias.erase(del_alias)) != OB_SUCCESS)
        {
          TRANS_LOG("Generate join plan faild");
          break;
        }
      }
      else if ((*alias_it)->get_tables_set().is_subset(join_table_bitset))
      {
        (*alias_it)->set_columnlized(true);
        if (project_op == NULL)
        {
          CREATE_PHY_OPERRATOR(project_op, ObAddProject, physical_plan, err_stat);
          if (ret != OB_SUCCESS)
            break;
          if ((ret = project_op->set_child(0, *join_op)) != OB_SUCCESS)
          {
            TRANS_LOG("Generate project operator on join plan faild");
            break;
          }
        }
        ObSqlExpression alias_expr;
        if ((ret = (*alias_it)->fill_sql_expression(
                                  alias_expr,
                                  this,
                                  logical_plan,
                                  physical_plan)) != OB_SUCCESS
          || (ret = project_op->add_output_column(alias_expr)) != OB_SUCCESS)
        {
          TRANS_LOG("Add project column on join plan faild");
          break;
        }
        common::ObList<ObSqlRawExpr*>::iterator del_alias = alias_it;
        alias_it++;
        if ((ret = none_columnlize_alias.erase(del_alias)) != OB_SUCCESS)
        {
          TRANS_LOG("Generate join plan faild");
          break;
        }
      }
      else
      {
        alias_it++;
      }
    }

    if (ret == OB_SUCCESS)
    {
      ObPhyOperator *result_op = NULL;
      if (project_op == NULL)
        result_op = join_op;
      else
        result_op = project_op;
      if ((ret = phy_table_list.push_back(result_op)) != OB_SUCCESS
        || (ret = bitset_list.push_back(join_table_bitset)) != OB_SUCCESS)
      {
        TRANS_LOG("Generate join plan failed");
        break;
      }
      join_table_bitset.clear();
    }
  }

  return ret;
}

int ObTransformer::gen_phy_tables(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObSelectStmt *select_stmt,
    bool& group_agg_pushed_down,
    bool& limit_pushed_down,
    oceanbase::common::ObList<ObPhyOperator*>& phy_table_list,
    oceanbase::common::ObList<ObBitSet<> >& bitset_list,
    oceanbase::common::ObList<ObSqlRawExpr*>& remainder_cnd_list,
    oceanbase::common::ObList<ObSqlRawExpr*>& none_columnlize_alias)
{
  int ret = err_stat.err_code_ = OB_SUCCESS;
  ObPhyOperator *table_op = NULL;
  ObBitSet<> bit_set;

  TBSYS_LOG(DEBUG, "999 enter func %s\n", __func__);
  int32_t num = select_stmt->get_select_item_size();
  for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
  {
    const SelectItem& select_item = select_stmt->get_select_item(i);
    if (select_item.is_real_alias_)
    {
      ObSqlRawExpr *alias_expr = logical_plan->get_expr(select_item.expr_id_);
      if (alias_expr == NULL)
      {
        ret = OB_ERR_ILLEGAL_ID;
        TRANS_LOG("Add alias to internal list failed");
        break;
      }
      else if (alias_expr->is_columnlized() == false
        && (ret = none_columnlize_alias.push_back(alias_expr)) != OB_SUCCESS)
      {
        TRANS_LOG("Add alias to internal list failed");
        break;
      }
    }
  }

  int32_t num_table = select_stmt->get_from_item_size();
  // no from clause of from DUAL
  if (ret == OB_SUCCESS && num_table <= 0)
  {
    ObDualTableScan *dual_table_op = NULL;
    if (CREATE_PHY_OPERRATOR(dual_table_op, ObDualTableScan, physical_plan, err_stat) == NULL)
    {
      TRANS_LOG("Generate dual table operator failed, ret=%d", ret);
    }
    else if ((ret = phy_table_list.push_back(dual_table_op)) != OB_SUCCESS)
    {
      TRANS_LOG("Add table to internal list failed");
    }
    // add empty bit set
    else if ((ret = bitset_list.push_back(bit_set)) != OB_SUCCESS)
    {
      TRANS_LOG("Add bitset to internal list failed");
    }
  }
  for(int32_t i = 0; ret == OB_SUCCESS && i < num_table; i++)
  {
    const FromItem& from_item = select_stmt->get_from_item(i);
    if (from_item.is_joined_ == false)
    {
      /* base-table or temporary table */
      if ((ret = gen_phy_table(
                    logical_plan,
                    physical_plan,
                    err_stat,
                    select_stmt,
                    from_item.table_id_,
                    table_op,
                    &group_agg_pushed_down,
                    &limit_pushed_down)) != OB_SUCCESS)
        break;
      bit_set.add_member(select_stmt->get_table_bit_index(from_item.table_id_));
    }
    else
    {
      /* Outer Join */
      JoinedTable *joined_table = select_stmt->get_joined_table(from_item.table_id_);
      if (joined_table == NULL)
      {
        ret = OB_ERR_ILLEGAL_ID;
        TRANS_LOG("Wrong joined table id '%lu'", from_item.table_id_);
        break;
      }
      OB_ASSERT(joined_table->table_ids_.count() >= 2);
      OB_ASSERT(joined_table->table_ids_.count() - 1 == joined_table->join_types_.count());
      OB_ASSERT(joined_table->join_types_.count() == joined_table->expr_ids_.count());

      if ((ret = gen_phy_table(
                    logical_plan,
                    physical_plan,
                    err_stat,
                    select_stmt,
                    joined_table->table_ids_.at(0),
                    table_op)) != OB_SUCCESS)
      {
        break;
      }
      bit_set.add_member(select_stmt->get_table_bit_index(joined_table->table_ids_.at(0)));

      ObPhyOperator *right_op = NULL;
      ObJoin *join_op = NULL;
      ObSqlRawExpr *join_expr = NULL;
      for (int32_t j = 1; ret == OB_SUCCESS && j < joined_table->table_ids_.count(); j++)
      {
        if ((ret = gen_phy_table(
                    logical_plan,
                    physical_plan,
                    err_stat,
                    select_stmt,
                    joined_table->table_ids_.at(j),
                    right_op)) != OB_SUCCESS)
        {
          break;
        }
        ObList<ObPhyOperator*>  outer_join_tabs;
        ObList<ObBitSet<> >        outer_join_bitsets;
        ObList<ObSqlRawExpr*>   outer_join_cnds;
        if (OB_SUCCESS != (ret = outer_join_tabs.push_back(table_op))
            || OB_SUCCESS != (ret = outer_join_tabs.push_back(right_op))
            || OB_SUCCESS != (ret = outer_join_bitsets.push_back(bit_set)))
        {
          TBSYS_LOG(WARN, "fail to push op to outer_join tabs. ret=%d", ret);
          break;
        }
        ObBitSet<> right_table_bitset;
        int32_t  right_table_bit_index = select_stmt->get_table_bit_index(joined_table->table_ids_.at(j));
        right_table_bitset.add_member(right_table_bit_index);
        bit_set.add_member(right_table_bit_index);
        if (OB_SUCCESS != (ret = outer_join_bitsets.push_back(right_table_bitset)))
        {
          TBSYS_LOG(WARN, "fail to push bitset to list. ret=%d", ret);
          break;
        }
        join_expr = logical_plan->get_expr(joined_table->expr_ids_.at(j - 1));
        if (join_expr == NULL)
        {
          ret = OB_ERR_ILLEGAL_INDEX;
          TRANS_LOG("Add outer join condition faild");
          break;
        }
        else if (OB_SUCCESS != (ret = outer_join_cnds.push_back(join_expr)))
        {
          TBSYS_LOG(WARN, "fail to push bitset to list. ret=%d", ret);
          break;
        }
        // Now we don't optimize outer join
        // outer_join_cnds is empty, we will do something when optimizing.
        if ((ret = gen_phy_joins(
                        logical_plan,
                        physical_plan,
                        err_stat,
                        select_stmt,
                        outer_join_tabs,
                        outer_join_bitsets,
                        outer_join_cnds,
                        none_columnlize_alias)) != OB_SUCCESS)
        {
          break;
        }
        if ((ret = outer_join_tabs.pop_front(table_op)) != OB_SUCCESS
          || (join_op = dynamic_cast<ObJoin*>(table_op)) == NULL)
        {
          ret = OB_ERR_OPERATOR_UNKNOWN;
          TRANS_LOG("Generate outer join operator failed");
          break;
        }
        switch (joined_table->join_types_.at(j - 1))
        {
          case JoinedTable::T_FULL:
            ret = join_op->set_join_type(ObJoin::FULL_OUTER_JOIN);
            break;
          case JoinedTable::T_LEFT:
            ret = join_op->set_join_type(ObJoin::LEFT_OUTER_JOIN);
            break;
          case JoinedTable::T_RIGHT:
            ret = join_op->set_join_type(ObJoin::RIGHT_OUTER_JOIN);
            break;
          case JoinedTable::T_INNER:
            ret = join_op->set_join_type(ObJoin::INNER_JOIN);
            break;
          default:
            /* won't be here */
            ret = join_op->set_join_type(ObJoin::INNER_JOIN);
            break;
        }
      }
    }
    if (ret == OB_SUCCESS && (ret = phy_table_list.push_back(table_op)) != OB_SUCCESS)
    {
      TRANS_LOG("Add table to internal list failed");
      break;
    }
    if (ret == OB_SUCCESS && (ret = bitset_list.push_back(bit_set)) != OB_SUCCESS)
    {
      TRANS_LOG("Add bitset to internal list failed");
      break;
    }
    bit_set.clear();
  }

  num = select_stmt->get_condition_size();
  for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
  {
    uint64_t expr_id = select_stmt->get_condition_id(i);
    ObSqlRawExpr *where_expr = logical_plan->get_expr(expr_id);
    if (where_expr && where_expr->is_apply() == false
      && (ret = remainder_cnd_list.push_back(where_expr)) != OB_SUCCESS)
    {
      TRANS_LOG("Add condition to internal list failed");
      break;
    }
  }

  return ret;
}

int ObTransformer::gen_phy_table(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObStmt *stmt,
    uint64_t table_id,
    ObPhyOperator*& table_op,
    bool* group_agg_pushed_down,
    bool* limit_pushed_down)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  TableItem* table_item = NULL;
  ObSqlReadStrategy sql_read_strategy;
  ObBitSet<> table_bitset;
  int32_t num = 0;

  TBSYS_LOG(DEBUG, "999 enter func %s\n", __func__);
  if (table_id == OB_INVALID_ID || (table_item = stmt->get_table_item_by_id(table_id)) == NULL)
  {
    ret = OB_ERR_ILLEGAL_ID;
    TRANS_LOG("Wrong table id");
  }

  ObRpcScanHint hint;
  if (OB_SUCCESS == ret)
  {
    const ObTableSchema *table_schema = NULL;
    if (NULL == (table_schema = sql_context_->schema_manager_->get_table_schema(table_item->ref_id_)))
    {
      ret = OB_ERROR;
      TRANS_LOG("Fail to get table schema for table[%ld]", table_item->ref_id_);
    }
    else
    {
      if (stmt->get_query_hint().read_static_)
        hint.only_static_data_ = true;
      else
        hint.only_static_data_ = !table_schema->is_merge_dynamic_data();
    }
  }

  ObTableScan *table_scan_op = NULL;
  if (ret == OB_SUCCESS)
  {
    switch (table_item->type_)
    {
      case TableItem::BASE_TABLE:
        /* get through */
      case TableItem::ALIAS_TABLE:
      {
  			TBSYS_LOG(DEBUG, "999 run case ALIAS_TABLE");
        ObTableRpcScan *table_rpc_scan_op = NULL;
        CREATE_PHY_OPERRATOR(table_rpc_scan_op, ObTableRpcScan, physical_plan, err_stat);
        if (ret == OB_SUCCESS
          && (ret = table_rpc_scan_op->set_table(table_item->table_id_, table_item->ref_id_)) != OB_SUCCESS)
        {
          TRANS_LOG("ObTableRpcScan set table faild");
        }

        /// determin request type: scan/get
        if (ret == OB_SUCCESS)
        {
          int32_t bit_index = stmt->get_table_bit_index(table_item->table_id_);
          table_bitset.add_member(bit_index);
        }
        if (OB_SUCCESS == ret)
        {
          const ObTableSchema *table_schema = NULL;
          if (NULL == (table_schema = sql_context_->schema_manager_->get_table_schema(table_item->ref_id_)))
          {
            ret = OB_ERROR;
            TRANS_LOG("Fail to get table schema for table[%ld]", table_item->ref_id_);
          }
          else
          {
            sql_read_strategy.set_rowkey_info(table_schema->get_rowkey_info());
          }
        }
        num = stmt->get_condition_size();
        for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
        {
          ObSqlRawExpr *cnd_expr = logical_plan->get_expr(stmt->get_condition_id(i));
          if (cnd_expr && table_bitset.is_superset(cnd_expr->get_tables_set()))
          {
            cnd_expr->set_applied(true);
            ObSqlExpression filter;
            if ((ret = cnd_expr->fill_sql_expression(filter, this, logical_plan, physical_plan)) != OB_SUCCESS)
            {
              TRANS_LOG("Add table filter condition faild");
              break;
            }
            else if (OB_SUCCESS != (ret = sql_read_strategy.add_filter(filter)))
            {
              TBSYS_LOG(WARN, "fail to add filter:ret[%d]", ret);
            }
          }
        }
        if ( OB_SUCCESS == ret)
        {
          int32_t read_method = ObSqlReadStrategy::USE_SCAN;
          // Determine Scan or Get?
          ObArray<ObRowkey> rowkey_array;
          // TODO: rowkey obj storage needed. varchar use orginal buffer, will be copied later
          PageArena<ObObj,ModulePageAllocator> rowkey_objs_allocator(
              PageArena<ObObj, ModulePageAllocator>::DEFAULT_PAGE_SIZE,ModulePageAllocator(ObModIds::OB_SQL_TRANSFORMER));
          // ObObj rowkey_objs[OB_MAX_ROWKEY_COLUMN_NUMBER];

          if (OB_SUCCESS != (ret = sql_read_strategy.get_read_method(rowkey_array, rowkey_objs_allocator, read_method)))
          {
            TBSYS_LOG(WARN, "fail to get read method:ret[%d]", ret);
          }
          else
          {
            TBSYS_LOG(DEBUG, "use [%s] method", read_method == ObSqlReadStrategy::USE_SCAN ? "SCAN" : "GET");
          }
          hint.read_method_ = read_method;
        }

        if (ret == OB_SUCCESS && (ret = table_rpc_scan_op->init(sql_context_, hint)) != OB_SUCCESS)
        {
          TRANS_LOG("ObTableRpcScan init faild");
        }
        if (ret == OB_SUCCESS)
          table_scan_op = table_rpc_scan_op;
        break;
      }
      case TableItem::GENERATED_TABLE:
      {
        ObTableMemScan *table_mem_scan_op = NULL;
        int32_t idx = OB_INVALID_INDEX;
        ret = gen_physical_select(logical_plan, physical_plan, err_stat, table_item->ref_id_, &idx);
        if (ret == OB_SUCCESS)
          CREATE_PHY_OPERRATOR(table_mem_scan_op, ObTableMemScan, physical_plan, err_stat);
        // the sub-query's physical plan is set directly, so base_table_id is no need to set
        if (ret == OB_SUCCESS
          && (ret = table_mem_scan_op->set_table(table_item->table_id_, OB_INVALID_ID)) != OB_SUCCESS)
        {
          TRANS_LOG("ObTableMemScan set table faild");
        }
        if (ret == OB_SUCCESS
          && (ret = table_mem_scan_op->set_child(0, *(physical_plan->get_phy_query(idx)))) != OB_SUCCESS)
        {
          TRANS_LOG("Set child of ObTableMemScan operator faild");
        }
        if (ret == OB_SUCCESS)
          table_scan_op = table_mem_scan_op;
        break;
      }
      default:
        // won't be here
        OB_ASSERT(0);
        break;
    }
  }

  num = stmt->get_condition_size();
  for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
  {
    ObSqlRawExpr *cnd_expr = logical_plan->get_expr(stmt->get_condition_id(i));
    if (cnd_expr && table_bitset.is_superset(cnd_expr->get_tables_set()))
    {
      cnd_expr->set_applied(true);
      ObSqlExpression *filter = ObSqlExpression::alloc();
      if (NULL == filter)
      {
        ret = OB_ALLOCATE_MEMORY_FAILED;
        TRANS_LOG("no memory");
        break;
      }
      else if ((ret = cnd_expr->fill_sql_expression(*filter, this, logical_plan, physical_plan)) != OB_SUCCESS
        || (ret = table_scan_op->add_filter(filter)) != OB_SUCCESS)
      {
        TRANS_LOG("Add table filter condition faild");
        break;
      }
    }
  }

  // add output columns
  num = stmt->get_column_size();
  for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
  {
    const ColumnItem *col_item = stmt->get_column_item(i);
    if (col_item && col_item->table_id_ == table_item->table_id_)
    {
      ObBinaryRefRawExpr col_expr(col_item->table_id_, col_item->column_id_, T_REF_COLUMN);
      ObSqlRawExpr col_raw_expr(
          common::OB_INVALID_ID,
          col_item->table_id_,
          col_item->column_id_,
          &col_expr);
      ObSqlExpression output_expr;
      if ((ret = col_raw_expr.fill_sql_expression(
                                  output_expr,
                                  this,
                                  logical_plan,
                                  physical_plan)) != OB_SUCCESS
        || (ret = table_scan_op->add_output_column(output_expr)) != OB_SUCCESS)
      {
        TRANS_LOG("Add table output columns faild");
        break;
      }
    }
  }
  ObSelectStmt *select_stmt = dynamic_cast<ObSelectStmt*>(stmt);
  if (ret == OB_SUCCESS && select_stmt)
  {
    num = select_stmt->get_select_item_size();
    for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
    {
      const SelectItem& select_item = select_stmt->get_select_item(i);
      if (select_item.is_real_alias_)
      {
        ObSqlRawExpr *alias_expr = logical_plan->get_expr(select_item.expr_id_);
        if (alias_expr && alias_expr->is_columnlized() == false
          && table_bitset.is_superset(alias_expr->get_tables_set()))
        {
          ObSqlExpression output_expr;
          if ((ret = alias_expr->fill_sql_expression(
                                    output_expr,
                                    this,
                                    logical_plan,
                                    physical_plan)) != OB_SUCCESS
            || (ret = table_scan_op->add_output_column(output_expr)) != OB_SUCCESS)
          {
            TRANS_LOG("Add table output columns faild");
            break;
          }
          alias_expr->set_columnlized(true);
        }
      }
    }
  }

  if (ret == OB_SUCCESS)
    table_op = table_scan_op;

  bool group_down = false;
  bool limit_down = false;

  if (hint.read_method_ == ObSqlReadStrategy::USE_SCAN)
  {
    /* Try to push down aggregations */
    if (ret == OB_SUCCESS && group_agg_push_down_param_ && select_stmt)
    {
      ret = try_push_down_group_agg(
                logical_plan,
                physical_plan,
                err_stat,
                select_stmt,
                group_down,
                table_op);
      if (group_agg_pushed_down)
        *group_agg_pushed_down = group_down;
    }
    /* Try to push down limit */
    if (ret == OB_SUCCESS && select_stmt)
    {
      ret = try_push_down_limit(
                logical_plan,
                physical_plan,
                err_stat,
                select_stmt,
                limit_down,
                table_op);
      if (limit_pushed_down)
        *limit_pushed_down = limit_down;
    }
  }
  else
  {
    if (group_agg_pushed_down)
      *group_agg_pushed_down = false;
    if (limit_pushed_down)
      *limit_pushed_down = false;
  }

  return ret;
}

int ObTransformer::try_push_down_group_agg(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const ObSelectStmt *select_stmt,
    bool& group_agg_pushed_down,
    ObPhyOperator *& scan_op)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObTableRpcScan *table_rpc_scan_op = dynamic_cast<ObTableRpcScan*>(scan_op);
  ObAddProject *project_op = NULL;

  if (table_rpc_scan_op == NULL)
  {
    // ignore
  }
  // 1. normal select statement, not UNION/EXCEPT/INTERSECT
  // 2. only one table, whose type is BASE_TABLE or ALIAS_TABLE
  // 3. can not be joined table.
  // 4. has group clause or aggregate function(s)
  // 6. no distinct aggregate function(s)
  else if (select_stmt->get_from_item_size() == 1
    && select_stmt->get_from_item(0).is_joined_ == false
    && select_stmt->get_table_size() == 1
    && (select_stmt->get_table_item(0).type_ == TableItem::BASE_TABLE
    || select_stmt->get_table_item(0).type_ == TableItem::ALIAS_TABLE)
    && (select_stmt->get_group_expr_size() > 0
    || select_stmt->get_agg_fun_size() > 0))
  {
    ObSqlRawExpr *expr = NULL;
    ObAggFunRawExpr *agg_expr = NULL;
    int32_t agg_num = select_stmt->get_agg_fun_size();
    for (int32_t i = 0; ret == OB_SUCCESS && i < agg_num; i++)
    {
      if ((expr = logical_plan->get_expr(select_stmt->get_agg_expr_id(i))) == NULL)
      {
        ret = OB_ERR_ILLEGAL_ID;
        TRANS_LOG("Wrong expression id of aggregate function");
        break;
      }
      else if ((agg_expr = dynamic_cast<ObAggFunRawExpr*>(expr->get_expr())) == NULL)
      {
        // agg(*), skip
        continue;
      }
      else if (agg_expr->is_param_distinct())
      {
        break;
      }
      else if (i == agg_num - 1)
      {
        group_agg_pushed_down = true;
      }
    }
  }

  // push down aggregate function(s)
  if (ret == OB_SUCCESS && group_agg_pushed_down)
  {
    // push down group column(s)
    ObSqlRawExpr *group_expr = NULL;
    int32_t num = select_stmt->get_group_expr_size();
    for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
    {
      if ((group_expr = logical_plan->get_expr(select_stmt->get_group_expr_id(i))) == NULL)
      {
        ret = OB_ERR_ILLEGAL_ID;
        TRANS_LOG("Wrong expression id  of group column");
      }
      else if (group_expr->get_expr()->get_expr_type() == T_REF_COLUMN)
      {
        ObBinaryRefRawExpr *col_expr = dynamic_cast<ObBinaryRefRawExpr*>(group_expr->get_expr());
        if ((ret = table_rpc_scan_op->add_group_column(
                                        col_expr->get_first_ref_id(),
                                        col_expr->get_second_ref_id())) != OB_SUCCESS)
        {
          TRANS_LOG("Add group column faild, table_id=%lu, column_id=%lu",
              col_expr->get_first_ref_id(), col_expr->get_second_ref_id());
        }
      }
      else if (group_expr->get_expr()->is_const())
      {
        // do nothing, const column is of no usage for sorting
        continue;
      }
      else
      {
        ObSqlExpression col_expr;
        if ((ret = group_expr->fill_sql_expression(
                                  col_expr,
                                  this,
                                  logical_plan,
                                  physical_plan)) != OB_SUCCESS
          || (ret = table_rpc_scan_op->add_output_column(col_expr)) != OB_SUCCESS)
        {
          TRANS_LOG("Add complex group column to project plan faild");
        }
        else if ((ret = table_rpc_scan_op->add_group_column(
                                            group_expr->get_table_id(),
                                            group_expr->get_column_id())) != OB_SUCCESS)
        {
          TRANS_LOG("Add group column to group plan faild");
        }
      }
    }

    // push down function(s)
    num = select_stmt->get_agg_fun_size();
    ObSqlRawExpr *agg_expr = NULL;
    for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
    {
      if ((agg_expr = logical_plan->get_expr(select_stmt->get_agg_expr_id(i))) == NULL)
      {
        ret = OB_ERR_ILLEGAL_ID;
        TRANS_LOG("Wrong expression id  of aggregate function");
        break;
      }
      else if (agg_expr->get_expr()->get_expr_type() ==  T_FUN_AVG)
      {
        // avg() ==> sum() / count()
        ObAggFunRawExpr *avg_expr = NULL;
        if ((avg_expr = dynamic_cast<ObAggFunRawExpr*>(agg_expr->get_expr())) == NULL)
        {
          ret = OB_ERR_RESOLVE_SQL;
          TRANS_LOG("Wrong aggregate function, exp_id = %lu", agg_expr->get_expr_id());
          break;
        }

        // add sum(), count() to TableRpcScan
        uint64_t table_id = agg_expr->get_table_id();
        uint64_t sum_cid = logical_plan->generate_range_column_id();
        uint64_t count_cid = logical_plan->generate_range_column_id();
        ObAggFunRawExpr sum_node;
        ObAggFunRawExpr count_node;
        sum_node.set_expr_type(T_FUN_SUM);
        sum_node.set_param_expr(avg_expr->get_param_expr());
        count_node.set_expr_type(T_FUN_COUNT);
        count_node.set_param_expr(avg_expr->get_param_expr());
        ObSqlRawExpr raw_sum_expr(OB_INVALID_ID, table_id, sum_cid, &sum_node);
        ObSqlRawExpr raw_count_expr(OB_INVALID_ID, table_id, count_cid, &count_node);
        ObSqlExpression sum_expr;
        ObSqlExpression count_expr;
        if ((ret = raw_sum_expr.fill_sql_expression(
                                    sum_expr,
                                    this,
                                    logical_plan,
                                    physical_plan)) != OB_SUCCESS
          || (ret = table_rpc_scan_op->add_aggr_column(sum_expr)) != OB_SUCCESS)
        {
          TRANS_LOG("Add sum aggregate function failed, ret = %d", ret);
          break;
        }
        else if ((ret = raw_count_expr.fill_sql_expression(
                                    count_expr,
                                    this,
                                    logical_plan,
                                    physical_plan)) != OB_SUCCESS
          || (ret = table_rpc_scan_op->add_aggr_column(count_expr)) != OB_SUCCESS)
        {
          TRANS_LOG("Add count aggregate function failed, ret = %d", ret);
          break;
        }

        // add a '/' expression
        ObBinaryRefRawExpr sum_col_node(table_id, sum_cid, T_REF_COLUMN);
        ObBinaryRefRawExpr count_col_node(table_id, count_cid, T_REF_COLUMN);
        ObBinaryOpRawExpr div_node(&sum_col_node, &count_col_node, T_OP_DIV);
        ObSqlRawExpr div_raw_expr(OB_INVALID_ID, table_id, agg_expr->get_column_id(), &div_node);
        ObSqlExpression div_expr;
        if (project_op == NULL)
        {
          if (CREATE_PHY_OPERRATOR(project_op, ObAddProject, physical_plan, err_stat) == NULL
            || (ret = project_op->set_child(0, *table_rpc_scan_op)) != OB_SUCCESS)
          {
            TRANS_LOG("Add ObAddProject on ObTableRpcScan failed, ret = %d", ret);
            break;
          }
          else
          {
            scan_op = project_op;
          }
        }
        if ((ret = div_raw_expr.fill_sql_expression(div_expr)) != OB_SUCCESS)
        {
          TRANS_LOG("Generate div expr for avg() function failed, ret = %d", ret);
        }
        else if ((ret = project_op->add_output_column(div_expr)) != OB_SUCCESS)
        {
          TRANS_LOG("Add column to ObAddProject operator failed, ret = %d", ret);
        }
      }
      else if (agg_expr->get_expr()->is_aggr_fun())
      {
        ObSqlExpression new_agg_expr;
        if ((ret = agg_expr->fill_sql_expression(
                                new_agg_expr,
                                this,
                                logical_plan,
                                physical_plan)) != OB_SUCCESS
          || (ret = table_rpc_scan_op->add_aggr_column(new_agg_expr)) != OB_SUCCESS)
        {
          TRANS_LOG("Add aggregate function to group plan faild");
          break;
        }
      }
      else
      {
        ret = OB_ERR_RESOLVE_SQL;
        TRANS_LOG("Wrong aggregate function, exp_id = %lu", agg_expr->get_expr_id());
        break;
      }
      agg_expr->set_columnlized(true);
    }
  }
  return ret;
}

int ObTransformer::try_push_down_limit(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const ObSelectStmt *select_stmt,
    bool& limit_pushed_down,
    ObPhyOperator *scan_op)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObTableRpcScan *table_rpc_scan_op = dynamic_cast<ObTableRpcScan*>(scan_op);

  if (table_rpc_scan_op == NULL)
  {
    // ignore
  }
  // 1. normal select statement, not UNION/EXCEPT/INTERSECT
  // 2. only one table, whose type is BASE_TABLE or ALIAS_TABLE
  // 3. can not be joined table.
  // 4. does not have group clause or aggregate function(s)
  // 5. does not have order by caluse
  // 6. limit is initialed
  else if (select_stmt->get_from_item_size() == 1
    && select_stmt->get_from_item(0).is_joined_ == false
    && select_stmt->get_table_size() == 1
    && (select_stmt->get_table_item(0).type_ == TableItem::BASE_TABLE
    || select_stmt->get_table_item(0).type_ == TableItem::ALIAS_TABLE)
    && select_stmt->get_group_expr_size() == 0
    && select_stmt->get_agg_fun_size() == 0
    && select_stmt->get_order_item_size() == 0)
  {
    limit_pushed_down = true;
    ObSqlExpression limit_count;
    ObSqlExpression limit_offset;
    ObSqlExpression *ptr = &limit_count;
    uint64_t id = select_stmt->get_limit_expr_id();
    int64_t i = 0;
    for (; ret == OB_SUCCESS && i < 2;
         i++, id = select_stmt->get_offset_expr_id(), ptr = &limit_offset)
    {
      ObSqlRawExpr *raw_expr = NULL;
      if (id == OB_INVALID_ID)
      {
        continue;
      }
      else if ((raw_expr = logical_plan->get_expr(id)) == NULL)
      {
        ret = OB_ERR_ILLEGAL_ID;
        TRANS_LOG("Wrong internal expression id = %lu, ret=%d", id, ret);
        break;
      }
      else if ((ret = raw_expr->fill_sql_expression(
                                  *ptr,
                                  this,
                                  logical_plan,
                                  physical_plan)) != OB_SUCCESS)
      {
        TRANS_LOG("Add limit/offset faild");
        break;
      }
    }
    if (ret == OB_SUCCESS && (ret = table_rpc_scan_op->set_limit(limit_count, limit_offset)) != OB_SUCCESS)
    {
      TRANS_LOG("Set limit/offset failed, ret=%d", ret);
    }
  }
  return ret;
}

int ObTransformer::gen_phy_values(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const ObInsertStmt *insert_stmt,
    const ObRowDesc& row_desc,
    const ObRowDescExt& row_desc_ext,
    const ObSEArray<int64_t, 64> *row_desc_map,
    ObExprValues& value_op)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  OB_ASSERT(logical_plan);
  OB_ASSERT(insert_stmt);
  value_op.set_row_desc(row_desc, row_desc_ext);
  int64_t num = insert_stmt->get_value_row_size();
  for (int64_t i = 0; ret == OB_SUCCESS && i < num; i++) // for each row
  {
    const ObArray<uint64_t>& value_row = insert_stmt->get_value_row(i);
    if (OB_UNLIKELY(0 == i))
    {
      value_op.reserve_values(num * value_row.count());
      FILL_TRACE_LOG("expr_values_count=%ld", num * value_row.count());
    }
    for (int64_t j = 0; ret == OB_SUCCESS && j < value_row.count(); j++)
    {
      ObSqlExpression val_expr;
      int64_t expr_idx = OB_INVALID_INDEX;
      if (NULL != row_desc_map)
      {
        OB_ASSERT(value_row.count() == row_desc_map->count());
        expr_idx = value_row.at(row_desc_map->at(j));
      }
      else
      {
        expr_idx = value_row.at(j);
      }
      ObSqlRawExpr *value_expr = logical_plan->get_expr(expr_idx);
      OB_ASSERT(NULL != value_expr);
      if (OB_SUCCESS != (ret = value_expr->fill_sql_expression(val_expr, this, logical_plan, physical_plan)))
      {
        TRANS_LOG("Failed to fill expr, err=%d", ret);
      }
      else if (OB_SUCCESS != (ret = value_op.add_value(val_expr)))
      {
        TRANS_LOG("Failed to add value into expr_values, err=%d", ret);
      }
    } // end for
  } // end for
  return ret;
}

int ObTransformer::gen_physical_replace(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    int32_t* index)
{
  int ret = err_stat.err_code_ = OB_SUCCESS;
  ObInsertStmt *insert_stmt = NULL;
  ObPhysicalPlan* inner_plan = NULL;
  ObUpsModify *ups_modify = NULL;
  ObSEArray<int64_t, 64> row_desc_map;
  ObRowDesc row_desc;
  ObRowDescExt row_desc_ext;
  const ObRowkeyInfo *rowkey_info = NULL;

  if (OB_SUCCESS != (ret = wrap_ups_executor(physical_plan, query_id, inner_plan, index, err_stat)))
  {
    TBSYS_LOG(WARN, "err=%d", ret);
  }
  else if (OB_SUCCESS != (ret = get_stmt(logical_plan, err_stat, query_id, insert_stmt)))
  {
    TRANS_LOG("Fail to get statement");
  }
  else if (NULL == CREATE_PHY_OPERRATOR(ups_modify, ObUpsModify, inner_plan, err_stat))
  {
    ret = OB_ALLOCATE_MEMORY_FAILED;
  }
  else if (OB_SUCCESS != (ret = inner_plan->add_phy_query(ups_modify, NULL, true))) // always main query
  {
    TRANS_LOG("Failed to add phy query, err=%d", ret);
  }
  else if (OB_SUCCESS != (ret = cons_row_desc(insert_stmt->get_table_id(), insert_stmt, row_desc_ext, row_desc, rowkey_info, row_desc_map, err_stat)))
  {
    TRANS_LOG("Failed to cons row desc, err=%d", ret);
  }
  else
  {
    // check primary key columns
    uint64_t tid = insert_stmt->get_table_id();
    uint64_t cid = OB_INVALID_ID;
    for (int64_t i = 0; OB_SUCCESS == ret && i < rowkey_info->get_size(); ++i)
    {
      if (OB_SUCCESS != (ret = rowkey_info->get_column_id(i, cid)))
      {
        TBSYS_LOG(USER_ERROR, "primary key can not be empty");
        ret = OB_ERR_INSERT_NULL_ROWKEY;
        break;
      }
      else if (OB_INVALID_INDEX == row_desc.get_idx(tid, cid))
      {
        TBSYS_LOG(USER_ERROR, "primary key can not be empty");
        ret = OB_ERR_INSERT_NULL_ROWKEY;
        break;
      }
    } // end for

    if (OB_LIKELY(OB_SUCCESS == ret))
    {
      // check column data type
      ObObj data_type;
      for (int i = 0; i < row_desc_ext.get_column_num(); ++i)
      {
        if (OB_SUCCESS != (ret = row_desc_ext.get_by_idx(i, tid, cid, data_type)))
        {
          TBSYS_LOG(ERROR, "failed to get type, err=%d", ret);
          ret = OB_ERR_UNEXPECTED;
          break;
        }
        else if (data_type.get_type() == ObCreateTimeType
                 || data_type.get_type() == ObModifyTimeType)
        {
          ret = OB_ERR_CREAT_MODIFY_TIME_COLUMN;
          TRANS_LOG("Column of type ObCreateTimeType/ObModifyTimeType can not be inserted");
          break;
        }
      } // end for
    }
  }
  FILL_TRACE_LOG("cons_row_desc");
  if (ret == OB_SUCCESS)
  {
    if (OB_LIKELY(insert_stmt->get_insert_query_id() == OB_INVALID_ID))
    {
      ObExprValues *value_op = NULL;
      CREATE_PHY_OPERRATOR(value_op, ObExprValues, physical_plan, err_stat);
      if (ret == OB_SUCCESS && (ret = ups_modify->set_child(0, *value_op)) != OB_SUCCESS)
      {
        TRANS_LOG("Set child of insert operator failed");
      }
      if (ret == OB_SUCCESS && (ret = value_op->set_row_desc(row_desc, row_desc_ext)) != OB_SUCCESS)
      {
        TRANS_LOG("Set descriptor of value operator failed");
      }
      if (ret == OB_SUCCESS)
        ret = gen_phy_values(logical_plan, physical_plan, err_stat, insert_stmt,
                             row_desc, row_desc_ext, &row_desc_map, *value_op);
      FILL_TRACE_LOG("gen_phy_values");
    }
    else
    {
      // replace ... select
      TRANS_LOG("REPLACE INTO ... SELECT is not supported yet");
      ret = OB_NOT_SUPPORTED;
    }
  }
  return ret;
}

int ObTransformer::gen_physical_delete(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    int32_t* index)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObDeleteStmt *delete_stmt = NULL;
  ObDelete     *delete_op = NULL;

  /* get statement */
  if (OB_SUCCESS != (ret = get_stmt(logical_plan, err_stat, query_id, delete_stmt)))
  {
    TRANS_LOG("Fail to get statement");
  }

  /* generate operator */
  if (ret == OB_SUCCESS)
  {
    CREATE_PHY_OPERRATOR(delete_op, ObDelete, physical_plan, err_stat);
    if (ret == OB_SUCCESS)
    {
      ret = add_phy_query(logical_plan, physical_plan, err_stat, query_id, delete_stmt, delete_op, index);
    }
  }

  ObRowDescExt row_desc_ext;
  const ObTableSchema *table_schema = NULL;
  if (OB_SUCCESS == ret)
  {
    if (NULL == (table_schema = sql_context_->schema_manager_->get_table_schema(delete_stmt->get_delete_table_id())))
    {
      ret = OB_ERROR;
      TRANS_LOG("Fail to get table schema for table[%ld]", delete_stmt->get_delete_table_id());
    }
  }
  if (ret == OB_SUCCESS)
  {
    delete_op->set_table_id(delete_stmt->get_delete_table_id());
    delete_op->set_rpc_stub(sql_context_->merger_rpc_proxy_);
    delete_op->set_rowkey_info(table_schema->get_rowkey_info());
    int32_t num = delete_stmt->get_column_size();
    for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
    {
      const ColumnItem* column_item = delete_stmt->get_column_item(i);
      if (column_item == NULL)
      {
        ret = OB_ERR_ILLEGAL_ID;
        TRANS_LOG("Get column item failed");
        break;
      }
      const ObColumnSchemaV2* column_schema = sql_context_->schema_manager_->get_column_schema(
        column_item->table_id_, column_item->column_id_);
      if (NULL == column_schema)
      {
        ret = OB_ERR_COLUMN_NOT_FOUND;
        TRANS_LOG("Get column item failed");
        break;
      }
      ObObj data_type;
      data_type.set_type(column_schema->get_type());
      ret = row_desc_ext.add_column_desc(column_item->table_id_, column_item->column_id_, data_type);
      if (ret != OB_SUCCESS)
      {
        TRANS_LOG("Add column '%.*s' to descriptor failed",
            column_item->column_name_.length(), column_item->column_name_.ptr());
        break;
      }
    }
    if (ret == OB_SUCCESS && (ret = delete_op->set_columns_desc(row_desc_ext)) != OB_SUCCESS)
    {
      TRANS_LOG("Set descriptor of delete operator failed");
    }
  }

  if (ret == OB_SUCCESS)
  {
    if (OB_UNLIKELY(delete_stmt->get_delete_table_id() == OB_INVALID_ID))
    {
        ret = OB_NOT_INIT;
        TRANS_LOG("table is not given in delete statment. check syntax");
    }
    else
    {
      ObPhyOperator *table_op = NULL;
      if ((ret = gen_phy_table(
                logical_plan,
                physical_plan,
                err_stat,
                delete_stmt,
                delete_stmt->get_delete_table_id(),
                table_op)) == OB_SUCCESS
         && NULL != table_op
         && (ret = delete_op->set_child(0, *table_op)) == OB_SUCCESS)
      {
        // success
      }
      else
      {
        TRANS_LOG("Set child of delete operator failed");
      }
    }
  }

  return ret;
}

int ObTransformer::gen_physical_update(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    int32_t* index)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObUpdateStmt *update_stmt = NULL;
  ObUpdate     *update_op = NULL;
  uint64_t table_id = OB_INVALID_ID;
  int64_t column_idx = 0;
  uint64_t column_id = OB_INVALID_ID;
  uint64_t expr_id = OB_INVALID_ID;
  ObSqlExpression expr;
  ObSqlRawExpr *raw_expr = NULL;
  const ObTableSchema *table_schema = NULL;
  const ObColumnSchemaV2* column_schema = NULL;
  ObObj data_type;
  ObRowDescExt row_desc_ext;

  /* get statement */
  if (ret == OB_SUCCESS)
  {
    get_stmt(logical_plan, err_stat, query_id, update_stmt);
  }
  /* generate operator */
  if (ret == OB_SUCCESS)
  {
    CREATE_PHY_OPERRATOR(update_op, ObUpdate, physical_plan, err_stat);
    if (ret == OB_SUCCESS)
    {
      ret = add_phy_query(logical_plan, physical_plan, err_stat, query_id, update_stmt, update_op, index);
    }
  }

  /* init update op param */
  /* set table id and other stuff, only support update single table now */
  if (ret == OB_SUCCESS)
  {
    if (OB_INVALID_ID == (table_id = update_stmt->get_update_table_id()))
    {
      ret = OB_ERR_ILLEGAL_ID;
      TRANS_LOG("Get update statement table ID error");
    }
    else if (NULL == (table_schema = sql_context_->schema_manager_->get_table_schema(table_id)))
    {
      ret = OB_ERR_ILLEGAL_ID;
      TRANS_LOG("Fail to get table schema for table[%ld]", table_id);
    }
  }

  if (ret == OB_SUCCESS)
  {
    update_op->set_table_id(table_id);
    update_op->set_rpc_stub(sql_context_->merger_rpc_proxy_);
    update_op->set_rowkey_info(table_schema->get_rowkey_info());
  }
  if (ret == OB_SUCCESS)
  {
    // construct row desc ext
    int32_t num = update_stmt->get_column_size();
    for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
    {
      const ColumnItem* column_item = update_stmt->get_column_item(i);
      if (column_item == NULL)
      {
        ret = OB_ERR_ILLEGAL_ID;
        TRANS_LOG("Get column item failed");
        break;
      }
      const ObColumnSchemaV2* column_schema = sql_context_->schema_manager_->get_column_schema(
          column_item->table_id_, column_item->column_id_);
      if (NULL == column_schema)
      {
        ret = OB_ERR_COLUMN_NOT_FOUND;
        TRANS_LOG("Get column item failed");
        break;
      }
      else if (column_schema->get_type() == ObCreateTimeType || column_schema->get_type() == ObModifyTimeType)
      {
        ret = OB_ERR_CREAT_MODIFY_TIME_COLUMN;
        TRANS_LOG("Column '%s' of type ObCreateTimeType/ObModifyTimeType can not be updated",
            column_schema->get_name());
        break;
      }
      data_type.set_type(column_schema->get_type());
      ret = row_desc_ext.add_column_desc(column_item->table_id_, column_item->column_id_, data_type);
      if (ret != OB_SUCCESS)
      {
        TRANS_LOG("Add column '%.*s' to descriptor faild",
            column_item->column_name_.length(), column_item->column_name_.ptr());
        break;
      }
    }
    if (ret == OB_SUCCESS && (ret = update_op->set_columns_desc(row_desc_ext)) != OB_SUCCESS)
    {
      TRANS_LOG("Set ext descriptor of update operator failed");
    }
  }
  /* fill column=expr pairs to update operator */
  if (OB_SUCCESS == ret)
  {
    for (column_idx = 0; column_idx < update_stmt->get_update_column_count(); column_idx++)
    {
      expr.reset();
      // valid check
      // 1. rowkey can't be updated
      // 2. joined column can't be updated
      if (OB_SUCCESS != (ret = update_stmt->get_update_column_id(column_idx, column_id)))
      {
        TBSYS_LOG(WARN, "fail to get update column id for table %lu column_idx=%lu", table_id, column_idx);
        break;
      }
      else if (NULL == (column_schema = sql_context_->schema_manager_->get_column_schema(table_id, column_id)))
      {
        ret = OB_ERR_COLUMN_NOT_FOUND;
        TRANS_LOG("Get column item failed");
        break;
      }
      else if (true == column_schema->is_join_column())
      {
        ret = OB_ERR_UPDATE_JOIN_COLUMN;
        TRANS_LOG("join column '%s' can not be updated", column_schema->get_name());
        break;
      }
      else if (table_schema->get_rowkey_info().is_rowkey_column(column_id))
      {
        ret = OB_ERR_UPDATE_ROWKEY_COLUMN;
        TRANS_LOG("rowkey column '%s' can not be updated", column_schema->get_name());
        break;
      }

      // get expression
      if ((OB_SUCCESS == ret) && (OB_SUCCESS != (ret = update_stmt->get_update_expr_id(column_idx, expr_id))))
      {
        TBSYS_LOG(WARN, "fail to get update expr for table %lu column %lu. column_idx=%ld", table_id, column_id, column_idx);
        break;
      }
      else if (NULL == (raw_expr = logical_plan->get_expr(expr_id)))
      {
        TBSYS_LOG(WARN, "fail to get expr from logical plan for table %lu column %lu. column_idx=%ld", table_id, column_id, column_idx);
        ret = OB_ERR_UNEXPECTED;
        break;
      }
      else if (OB_SUCCESS != (ret = raw_expr->fill_sql_expression(expr, this, logical_plan, physical_plan)))
      {
        TBSYS_LOG(WARN, "fail to fill sql expression. ret=%d", ret);
        break;
      }
      // add <column_id, expression> to update operator
      else if (OB_SUCCESS != (ret = update_op->add_update_expr(column_id, expr)))
      {
        TBSYS_LOG(WARN, "fail to add update expr to update operator");
        break;
      }
    }
  }
  if (OB_SUCCESS == ret)
  {
    ObPhyOperator *table_op = NULL;
    if ((ret = gen_phy_table(
            logical_plan,
            physical_plan,
            err_stat,
            update_stmt,
            table_id,
            table_op)) == OB_SUCCESS
        && NULL != table_op
        && (ret = update_op->set_child(0, *table_op)) == OB_SUCCESS)
    {
      // success
    }
    else
    {
      TRANS_LOG("Set child of update operator failed");
    }
  }

  return ret;
}

int ObTransformer::gen_physical_explain(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    int32_t* index)
{
  int ret = err_stat.err_code_ = OB_SUCCESS;
  ObExplainStmt *explain_stmt = NULL;
  ObExplain     *explain_op = NULL;

  if (ret == OB_SUCCESS)
  {
    get_stmt(logical_plan, err_stat, query_id, explain_stmt);
  }
  if (ret == OB_SUCCESS)
  {
    CREATE_PHY_OPERRATOR(explain_op, ObExplain, physical_plan, err_stat);
    if (ret == OB_SUCCESS)
    {
      ret = add_phy_query(logical_plan, physical_plan, err_stat, query_id, explain_stmt, explain_op, index);
    }
  }

  int32_t idx = OB_INVALID_INDEX;
  if (ret == OB_SUCCESS)
  {
    ret = generate_physical_plan(
              logical_plan,
              physical_plan,
              err_stat,
              explain_stmt->get_explain_query_id(),
              &idx);
  }
  if (ret == OB_SUCCESS)
  {
    ObPhyOperator* op = physical_plan->get_phy_query(idx);
    if ((ret = explain_op->set_child(0, *op)) != OB_SUCCESS)
      TRANS_LOG("Set child of Explain Operator failed");
  }

  return ret;
}

int ObTransformer::gen_physical_create_table(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    int32_t* index)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObCreateTableStmt *crt_tab_stmt = NULL;
  ObCreateTable     *crt_tab_op = NULL;

  /* get statement */
  if (ret == OB_SUCCESS)
  {
    get_stmt(logical_plan, err_stat, query_id, crt_tab_stmt);
  }

  if (OB_SUCCESS == ret)
  {
    const ObString& table_name = crt_tab_stmt->get_table_name();
    if (TableSchema::is_system_table(table_name)
        && sql_context_->session_info_->is_create_sys_table_disabled())
    {
      ret = OB_ERR_NO_PRIVILEGE;
      TBSYS_LOG(USER_ERROR, "invalid table name to create, table_name=%.*s",
                table_name.length(), table_name.ptr());
    }
  }

  /* generate operator */
  if (ret == OB_SUCCESS)
  {
    CREATE_PHY_OPERRATOR(crt_tab_op, ObCreateTable, physical_plan, err_stat);
    if (ret == OB_SUCCESS)
    {
      crt_tab_op->set_sql_context(*sql_context_);
      ret = add_phy_query(logical_plan, physical_plan, err_stat, query_id, crt_tab_stmt, crt_tab_op, index);
    }
  }

  if (OB_SUCCESS == ret)
  {
    if (crt_tab_stmt->get_column_size() > OB_MAX_USER_DEFINED_COLUMNS_COUNT)
    {
      TRANS_LOG("Too many columns (max allowed is %ld).",
               OB_MAX_USER_DEFINED_COLUMNS_COUNT);
      ret = OB_ERR_INVALID_COLUMN_NUM;
    }
  }

  if (ret == OB_SUCCESS)
  {
    int buf_len = 0;
    int len = 0;
    TableSchema& table_schema = crt_tab_op->get_table_schema();
    const ObString& table_name = crt_tab_stmt->get_table_name();
    buf_len = sizeof(table_schema.table_name_);
    if (table_name.length() < buf_len)
    {
      len = table_name.length();
    }
    else
    {
      len = buf_len - 1;
      TRANS_LOG("Table name is truncated to '%.*s'", len, table_name.ptr());
    }
    memcpy(table_schema.table_name_, table_name.ptr(), len);
    table_schema.table_name_[len] = '\0';
    const ObString& expire_info = crt_tab_stmt->get_expire_info();
    buf_len = sizeof(table_schema.expire_condition_);
    if (expire_info.length() < buf_len)
    {
      len = expire_info.length();
    }
    else
    {
      len = buf_len - 1;
      TRANS_LOG("Expire_info is truncated to '%.*s'", len, expire_info.ptr());
    }
    memcpy(table_schema.expire_condition_, expire_info.ptr(), len);
    table_schema.expire_condition_[len] = '\0';
    crt_tab_op->set_if_not_exists(crt_tab_stmt->get_if_not_exists());
    if (crt_tab_stmt->get_tablet_max_size() > 0)
      table_schema.tablet_max_size_ = crt_tab_stmt->get_tablet_max_size();
    if (crt_tab_stmt->get_tablet_block_size() > 0)
      table_schema.tablet_block_size_ = crt_tab_stmt->get_tablet_block_size();
    table_schema.replica_num_ = crt_tab_stmt->get_replica_num();
    table_schema.is_use_bloomfilter_ = crt_tab_stmt->use_bloom_filter();
    table_schema.is_read_static_ = crt_tab_stmt->read_static();
    table_schema.rowkey_column_num_ = static_cast<int32_t>(crt_tab_stmt->get_primary_key_size());
    const ObString& compress_method = crt_tab_stmt->get_compress_method();
    buf_len = sizeof(table_schema.compress_func_name_);
    const char *func_name = compress_method.ptr();
    len = compress_method.length();
    if (len <= 0)
    {
      func_name = OB_DEFAULT_COMPRESS_FUNC_NAME;
      len = static_cast<int>(strlen(OB_DEFAULT_COMPRESS_FUNC_NAME));
    }
    if (len >= buf_len)
    {
      len = buf_len - 1;
      TRANS_LOG("Compress method name is truncated to '%.*s'", len, func_name);
    }
    memcpy(table_schema.compress_func_name_, func_name, len);
    table_schema.compress_func_name_[len] = '\0';

    for (int64_t i = 0; ret == OB_SUCCESS && i < crt_tab_stmt->get_column_size(); i++)
    {
      const ObColumnDef& col_def = crt_tab_stmt->get_column_def(i);
      ColumnSchema col;
      col.column_id_ = col_def.column_id_;
      if (static_cast<int64_t>(col.column_id_) > table_schema.max_used_column_id_)
      {
        table_schema.max_used_column_id_ = col.column_id_;
      }
      buf_len = sizeof(col.column_name_);
      if (col_def.column_name_.length() < buf_len)
      {
        len = col_def.column_name_.length();
      }
      else
      {
        len = buf_len - 1;
        TRANS_LOG("Column name is truncated to '%.*s'", len, col_def.column_name_.ptr());
      }
      memcpy(col.column_name_, col_def.column_name_.ptr(), len);
      col.column_name_[len] = '\0';
      col.data_type_ = col_def.data_type_;
      col.data_length_ = col_def.type_length_;
      col.length_in_rowkey_ = col_def.type_length_;
      col.data_precision_ = col_def.precision_;
      col.data_scale_ = col_def.scale_;
      col.nullable_ = !col_def.not_null_;
      col.rowkey_id_ = col_def.primary_key_id_;
      col.column_group_id_ = 0;
      col.join_table_id_ = OB_INVALID_ID;
      col.join_column_id_ = OB_INVALID_ID;

      // @todo default_value_;
      if ((ret = table_schema.add_column(col)) != OB_SUCCESS)
      {
        TRANS_LOG("Add column definition of '%s' failed", table_schema.table_name_);
        break;
      }
    }
  }

  if (OB_SUCCESS == ret && 0 < crt_tab_stmt->get_expire_info().length())
  {
    TableSchema& table_schema = crt_tab_op->get_table_schema();
    // check expire condition
    void *ptr = ob_malloc(sizeof(ObSchemaManagerV2), ObModIds::OB_SCHEMA);
    if (NULL == ptr)
    {
      TRANS_LOG("no memory");
      ret = OB_ALLOCATE_MEMORY_FAILED;
    }
    else
    {
      ObSchemaManagerV2 *tmp_schema_mgr = new(ptr) ObSchemaManagerV2();
      table_schema.table_id_ = OB_NOT_EXIST_TABLE_TID;
      if (OB_SUCCESS != (ret = tmp_schema_mgr->add_new_table_schema(table_schema)))
      {
        TRANS_LOG("failed to add new table, err=%d", ret);
      }
      else if (OB_SUCCESS != (ret = tmp_schema_mgr->sort_column()))
      {
        TRANS_LOG("failed to sort column for schema manager, err=%d", ret);
      }
      else if (!tmp_schema_mgr->check_table_expire_condition())
      {
        ret = OB_ERR_INVALID_SCHEMA;
        TRANS_LOG("invalid expire info `%.*s'", crt_tab_stmt->get_expire_info().length(),
                  crt_tab_stmt->get_expire_info().ptr());
      }
      tmp_schema_mgr->~ObSchemaManagerV2();
      ob_free(tmp_schema_mgr);
      tmp_schema_mgr = NULL;
      table_schema.table_id_ = OB_INVALID_ID;
    }
  }
  return ret;
}

int ObTransformer::gen_physical_alter_table(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    int32_t* index)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObAlterTableStmt *alt_tab_stmt = NULL;
  ObAlterTable     *alt_tab_op = NULL;

  /* get statement */
  if (ret == OB_SUCCESS)
  {
    get_stmt(logical_plan, err_stat, query_id, alt_tab_stmt);
  }

  if (OB_SUCCESS == ret)
  {
    const ObString& table_name = alt_tab_stmt->get_table_name();
    if (TableSchema::is_system_table(table_name)
        && sql_context_->session_info_->is_create_sys_table_disabled())
    {
      ret = OB_ERR_NO_PRIVILEGE;
      TBSYS_LOG(USER_ERROR, "invalid table name to alter, table_name=%.*s",
                table_name.length(), table_name.ptr());
    }
  }

  /* generate operator */
  if (ret == OB_SUCCESS)
  {
    CREATE_PHY_OPERRATOR(alt_tab_op, ObAlterTable, physical_plan, err_stat);
    if (ret == OB_SUCCESS)
    {
      alt_tab_op->set_sql_context(*sql_context_);
      ret = add_phy_query(logical_plan, physical_plan, err_stat, query_id, alt_tab_stmt, alt_tab_op, index);
    }
  }

  if (ret == OB_SUCCESS)
  {
    AlterTableSchema& alter_schema = alt_tab_op->get_alter_table_schema();
    const ObString& table_name = alt_tab_stmt->get_table_name();
    memcpy(alter_schema.table_name_, table_name.ptr(), table_name.length());
    alter_schema.table_name_[table_name.length()] = '\0';
    alter_schema.table_id_ = alt_tab_stmt->get_table_id();

    hash::ObHashMap<common::ObString, ObColumnDef>::iterator iter;
    for (iter = alt_tab_stmt->column_begin();
        ret == OB_SUCCESS && iter != alt_tab_stmt->column_end();
        iter++)
    {
      AlterTableSchema::AlterColumnSchema alt_col;
      ObColumnDef& col_def = iter->second;
      alt_col.column_.column_id_ = col_def.column_id_;
      memcpy(alt_col.column_.column_name_, col_def.column_name_.ptr(), col_def.column_name_.length());
      alt_col.column_.column_name_[col_def.column_name_.length()] = '\0';
      switch (col_def.action_)
      {
        case ADD_ACTION:
          alt_col.type_ = AlterTableSchema::ADD_COLUMN;
          alt_col.column_.data_type_ = col_def.data_type_;
          alt_col.column_.data_length_ = col_def.type_length_;
          alt_col.column_.data_precision_ = col_def.precision_;
          alt_col.column_.data_scale_ = col_def.scale_;
          alt_col.column_.nullable_ = !col_def.not_null_;
          alt_col.column_.rowkey_id_ = col_def.primary_key_id_;
          alt_col.column_.column_group_id_ = 0;
          alt_col.column_.join_table_id_ = OB_INVALID_ID;
          alt_col.column_.join_column_id_ = OB_INVALID_ID;
          break;
        case DROP_ACTION:
          alt_col.type_ = AlterTableSchema::DEL_COLUMN;
          break;
        case ALTER_ACTION:
        {
          alt_col.type_ = AlterTableSchema::MOD_COLUMN;
          alt_col.column_.nullable_ = !col_def.not_null_;
          /* default value doesn't exist in ColumnSchema */
          /* FIX ME, get other attributs from schema */
          const ObColumnSchemaV2 *col_schema = NULL;
          if ((col_schema = sql_context_->schema_manager_->get_column_schema(
                                alter_schema.table_id_,
                                col_def.column_id_)) == NULL)
          {
            ret = OB_ERR_TABLE_UNKNOWN;
            TRANS_LOG("Can not find schema of table '%s'", alter_schema.table_name_);
            break;
          }
          else
          {
            alt_col.column_.data_type_ = col_schema->get_type();
            // alt_col.column_.data_length_ = iter->type_length_;
            // alt_col.column_.data_precision_ = iter->precision_;
            // alt_col.column_.data_scale_ = iter->scale_;
            // alt_col.column_.rowkey_id_ = iter->primary_key_id_;
            alt_col.column_.column_group_id_ = col_schema->get_column_group_id();
            alt_col.column_.join_table_id_ = col_schema->get_join_info()->join_table_;
            alt_col.column_.join_column_id_ = col_schema->get_join_info()->correlated_column_;
          }
          break;
        }
        default:
          ret = OB_ERR_GEN_PLAN;
          TRANS_LOG("Alter action '%d' is not supported", col_def.action_);
          break;
      }
      if (ret == OB_SUCCESS
        && (ret = alter_schema.add_column(alt_col.type_, alt_col.column_)) != OB_SUCCESS)
      {
        TRANS_LOG("Add alter column '%s' failed", alt_col.column_.column_name_);
        break;
      }
    }
  }
  return ret;
}

int ObTransformer::gen_physical_drop_table(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    int32_t* index)
{
  int ret = err_stat.err_code_ = OB_SUCCESS;
  ObDropTableStmt *drp_tab_stmt = NULL;
  ObDropTable     *drp_tab_op = NULL;

  /* get statement */
  if (ret == OB_SUCCESS)
  {
    get_stmt(logical_plan, err_stat, query_id, drp_tab_stmt);
  }
  bool disallow_drop_sys_table = sql_context_->session_info_->is_create_sys_table_disabled();
  /* generate operator */
  if (ret == OB_SUCCESS)
  {
    CREATE_PHY_OPERRATOR(drp_tab_op, ObDropTable, physical_plan, err_stat);
    if (ret == OB_SUCCESS)
    {
      drp_tab_op->set_rpc_stub(sql_context_->rs_rpc_proxy_);
      ret = add_phy_query(logical_plan, physical_plan, err_stat, query_id, drp_tab_stmt, drp_tab_op, index);
    }
  }

  if (ret == OB_SUCCESS)
  {
    drp_tab_op->set_if_exists(drp_tab_stmt->get_if_exists());
    for (int64_t i = 0; ret == OB_SUCCESS && i < drp_tab_stmt->get_table_size(); i++)
    {
      const ObString& table_name = drp_tab_stmt->get_table_name(i);
      if (TableSchema::is_system_table(table_name)
        && disallow_drop_sys_table)
      {
        ret = OB_ERR_NO_PRIVILEGE;
        TBSYS_LOG(USER_ERROR, "system table can not be dropped, table_name=%.*s",
                  table_name.length(), table_name.ptr());
        break;
      }
      if ((ret = drp_tab_op->add_table_name(table_name)) != OB_SUCCESS)
      {
        TRANS_LOG("Add drop table %.*s failed", table_name.length(), table_name.ptr());
        break;
      }
    }
  }

  return ret;
}

int ObTransformer::gen_phy_show_tables(
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObShowStmt *show_stmt,
    ObPhyOperator *&out_op)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObRowDesc row_desc;
  uint64_t table_id = OB_INVALID_ID;
  uint64_t column_id = OB_INVALID_ID;
  ObValues *values_op = NULL;
  CREATE_PHY_OPERRATOR(values_op, ObValues, physical_plan, err_stat);

  if (show_stmt->get_column_size() != 1)
  {
    TBSYS_LOG(WARN, "wrong columns' number of %s", OB_TABLES_SHOW_TABLE_NAME);
    ret = OB_ERR_COLUMN_SIZE;
    TRANS_LOG("wrong columns' number of %s", OB_TABLES_SHOW_TABLE_NAME);
  }
  else
  {
    const ColumnItem* column_item = show_stmt->get_column_item(0);
    table_id = column_item->table_id_;
    column_id = column_item->column_id_;
    if ((ret = row_desc.add_column_desc(table_id, column_id)) != OB_SUCCESS
      || (ret = values_op->set_row_desc(row_desc)) != OB_SUCCESS)
    {
      TRANS_LOG("add row desc error, err=%d", ret);
    }
  }
  const ObTableSchema* it = sql_context_->schema_manager_->table_begin();
  for(; ret == OB_SUCCESS && it != sql_context_->schema_manager_->table_end(); it++)
  {
    ObRow val_row;
    int32_t len = static_cast<int32_t>(strlen(it->get_table_name()));
    ObString val(len, len, it->get_table_name());
    ObObj value;
    value.set_varchar(val);
    val_row.set_row_desc(row_desc);
    if (it->get_table_id() >= OB_TABLES_SHOW_TID
      && it->get_table_id() <= OB_SERVER_STATUS_SHOW_TID)
    {
      /* skip local show tables */
      continue;
    }
    else if ((ret = val_row.set_cell(table_id, column_id, value)) != OB_SUCCESS)
    {
      TRANS_LOG("Add value to ObRow failed");
      break;
    }
    else if (ret == OB_SUCCESS && (ret = values_op->add_values(val_row)) != OB_SUCCESS)
    {
      TRANS_LOG("Add value row failed");
      break;
    }
  }

  if (ret == OB_SUCCESS)
  {
    out_op = values_op;
  }

  return ret;
}

int ObTransformer::gen_phy_show_columns(
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObShowStmt *show_stmt,
    ObPhyOperator *&out_op)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObRowDesc row_desc;
  ObValues *values_op = NULL;
  CREATE_PHY_OPERRATOR(values_op, ObValues, physical_plan, err_stat);

  int32_t num = show_stmt->get_column_size();
  if (OB_UNLIKELY(num < 1))
  {
    TBSYS_LOG(WARN, "wrong columns' number of %s", OB_COLUMNS_SHOW_TABLE_NAME);
    ret = OB_ERR_COLUMN_SIZE;
    TRANS_LOG("wrong columns' number of %s", OB_COLUMNS_SHOW_TABLE_NAME);
  }
  else
  {
    for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
    {
      const ColumnItem* column_item = show_stmt->get_column_item(i);
      if ((ret = row_desc.add_column_desc(column_item->table_id_, column_item->column_id_)) != OB_SUCCESS)
      {
        TRANS_LOG("add row desc error, err=%d", ret);
      }
    }
    if (ret == OB_SUCCESS && (ret = values_op->set_row_desc(row_desc)) != OB_SUCCESS)
    {
      TRANS_LOG("set row desc error, err=%d", ret);
    }
  }

  if (ret == OB_SUCCESS)
  {
    const ObColumnSchemaV2* columns = NULL;
    int32_t column_size = 0;
    ObRowkeyColumn rowkey_column;
    const ObRowkeyInfo& rowkey_info = sql_context_->schema_manager_->get_table_schema(show_stmt->get_show_table_id())->get_rowkey_info();
    columns = sql_context_->schema_manager_->get_table_schema(show_stmt->get_show_table_id(), column_size);
    if (NULL != columns && column_size > 0)
    {
      for (int64_t i = 0; ret == OB_SUCCESS && i < column_size; i++)
      {
        uint64_t table_id = OB_INVALID_ID;
        uint64_t column_id = OB_INVALID_ID;
        ObRow val_row;
        val_row.set_row_desc(row_desc);

        // add name
        if ((ret = row_desc.get_tid_cid(0, table_id, column_id)) != OB_SUCCESS)
        {
          TRANS_LOG("Get row desc failed");
          break;
        }
        int32_t name_len = static_cast<int32_t>(strlen(columns[i].get_name()));
        ObString name_val(name_len, name_len, columns[i].get_name());
        ObObj name;
        name.set_varchar(name_val);
        if ((ret = val_row.set_cell(table_id, column_id, name)) != OB_SUCCESS)
        {
          TRANS_LOG("Add name to ObRow failed");
          break;
        }

        // add type
        if ((ret = row_desc.get_tid_cid(1, table_id, column_id)) != OB_SUCCESS)
        {
          TRANS_LOG("Get row desc failed");
          break;
        }
        char type_str[OB_MAX_SYS_PARAM_NAME_LENGTH];
        int32_t type_len = OB_MAX_SYS_PARAM_NAME_LENGTH;
        switch (columns[i].get_type())
        {
          case ObNullType:
            type_len = snprintf(type_str, type_len, "null");
            break;
          case ObIntType:
            type_len = snprintf(type_str, type_len, "int");
            break;
          case ObFloatType:
            type_len = snprintf(type_str, type_len, "float");
            break;
          case ObDoubleType:
            type_len = snprintf(type_str, type_len, "double");
            break;
          case ObDateTimeType:
            type_len = snprintf(type_str, type_len, "datetime");
            break;
          case ObPreciseDateTimeType:
            type_len = snprintf(type_str, type_len, "timestamp");
            break;
          case ObVarcharType:
            type_len = snprintf(type_str, type_len, "varchar(%ld)", columns[i].get_size());
            break;
          case ObSeqType:
            type_len = snprintf(type_str, type_len, "seq");
            break;
          case ObCreateTimeType:
            type_len = snprintf(type_str, type_len, "createtime");
            break;
          case ObModifyTimeType:
            type_len = snprintf(type_str, type_len, "modifytime");
            break;
          case ObExtendType:
            type_len = snprintf(type_str, type_len, "extend");
            break;
          case ObBoolType:
            type_len = snprintf(type_str, type_len, "bool");
            break;
          case ObDecimalType:
            type_len = snprintf(type_str, type_len, "decimal");
            break;
          default:
            type_len = snprintf(type_str, type_len, "unknown");
            break;
        }
        ObString type_val(type_len, type_len, type_str);
        ObObj type;
        type.set_varchar(type_val);
        if ((ret = val_row.set_cell(table_id, column_id, type)) != OB_SUCCESS)
        {
          TRANS_LOG("Add type to ObRow failed");
          break;
        }

        // add nullable
        if ((ret = row_desc.get_tid_cid(2, table_id, column_id)) != OB_SUCCESS)
        {
          TRANS_LOG("Get row desc failed");
          break;
        }
        ObString nullable_val;
        ObObj nullable;
        nullable.set_varchar(nullable_val);
        if ((ret = val_row.set_cell(table_id, column_id, nullable)) != OB_SUCCESS)
        {
          TRANS_LOG("Add nullable to ObRow failed");
          break;
        }

        // add key_id
        if ((ret = row_desc.get_tid_cid(3, table_id, column_id) != OB_SUCCESS))
        {
          TRANS_LOG("Get row desc failed");
          break;
        }
        int64_t index = -1;
        rowkey_info.get_index(columns[i].get_id(), index, rowkey_column);
        ObObj key_id;
        key_id.set_int(index + 1); /* rowkey id is rowkey index plus 1 */
        if ((ret = val_row.set_cell(table_id, column_id, key_id)) != OB_SUCCESS)
        {
          TRANS_LOG("Add key_id to ObRow failed");
          break;
        }

        // add default
        if ((ret = row_desc.get_tid_cid(4, table_id, column_id) != OB_SUCCESS))
        {
          TRANS_LOG("Get row desc failed");
          break;
        }
        ObObj def;
        def.set_null();
        if ((ret = val_row.set_cell(table_id, column_id, def)) != OB_SUCCESS)
        {
          TRANS_LOG("Add default to ObRow failed");
          break;
        }

        // add extra
        if ((ret = row_desc.get_tid_cid(5, table_id, column_id) != OB_SUCCESS))
        {
          TRANS_LOG("Get row desc failed");
          break;
        }
        ObString extra_val;
        ObObj extra;
        extra.set_varchar(extra_val);
        if ((ret = val_row.set_cell(table_id, column_id, extra)) != OB_SUCCESS)
        {
          TRANS_LOG("Add extra to ObRow failed");
          break;
        }

        if (ret == OB_SUCCESS && (ret = values_op->add_values(val_row)) != OB_SUCCESS)
        {
          TRANS_LOG("Add value row failed");
          break;
        }
      }
    }
  }

  if (ret == OB_SUCCESS)
  {
    out_op = values_op;
  }

  return ret;
}

int ObTransformer::gen_phy_show_variables(
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObShowStmt *show_stmt,
    ObPhyOperator *&out_op)
  {
    int& ret = err_stat.err_code_ = OB_SUCCESS;
    if (!show_stmt->is_global_scope())
    {
      ObRowDesc row_desc;
      ObValues *values_op = NULL;
      CREATE_PHY_OPERRATOR(values_op, ObValues, physical_plan, err_stat);
      for (int32_t i = 0; ret == OB_SUCCESS && i < show_stmt->get_column_size(); i++)
      {
        const ColumnItem* column_item = show_stmt->get_column_item(i);
        if ((ret = row_desc.add_column_desc(column_item->table_id_,
                                            column_item->column_id_)) != OB_SUCCESS)
        {
          TRANS_LOG("Add row desc error, err=%d", ret);
        }
      }
      if (ret == OB_SUCCESS && (ret = values_op->set_row_desc(row_desc)) != OB_SUCCESS)
      {
        TRANS_LOG("Set row desc error, err=%d", ret);
      }
      uint64_t table_id = OB_INVALID_ID;
      uint64_t column_id = OB_INVALID_ID;
      ObSQLSessionInfo::SysVarNameValMap::const_iterator it_begin;
      ObSQLSessionInfo::SysVarNameValMap::const_iterator it_end;
      it_begin = sql_context_->session_info_->get_sys_var_val_map().begin();
      it_end = sql_context_->session_info_->get_sys_var_val_map().end();
      for(; ret == OB_SUCCESS && it_begin != it_end; it_begin++)
      {
        ObRow val_row;
        val_row.set_row_desc(row_desc);
        ObObj var_name;
        var_name.set_varchar(it_begin->first);
        // add Variable_name
        if ((ret = row_desc.get_tid_cid(0, table_id, column_id)) != OB_SUCCESS)
        {
          TRANS_LOG("Get row desc failed");
        }
        else if ((ret = val_row.set_cell(table_id, column_id, var_name)) != OB_SUCCESS)
        {
          TRANS_LOG("Add variable name to ObRow failed");
        }
        // add Value
        else if ((ret = row_desc.get_tid_cid(1, table_id, column_id)) != OB_SUCCESS)
        {
          TRANS_LOG("Get row desc failed");
        }
        else if ((ret = val_row.set_cell(table_id, column_id, *((it_begin->second).first))) != OB_SUCCESS)
        {
          TRANS_LOG("Add value to ObRow failed");
        }
        else if ((ret = values_op->add_values(val_row)) != OB_SUCCESS)
        {
          TRANS_LOG("Add value row failed");
        }
      }
      if (ret == OB_SUCCESS)
      {
        out_op = values_op;
      }
    }
    else
    {
      ObProject *project_op = NULL;
      ObTableRpcScan *rpc_scan_op = NULL;
      ObRpcScanHint hint;
      hint.read_method_ = ObSqlReadStrategy::USE_SCAN;
      if (CREATE_PHY_OPERRATOR(project_op, ObProject, physical_plan, err_stat) == NULL)
      {
        ret = OB_ERR_PARSER_MALLOC_FAILED;
        TRANS_LOG("Generate Project operator failed");
      }
      else if (CREATE_PHY_OPERRATOR(rpc_scan_op, ObTableRpcScan, physical_plan, err_stat) == NULL)
      {
        ret = OB_ERR_PARSER_MALLOC_FAILED;
        TRANS_LOG("Generate TableScan operator failed");
      }
      if ((ret = rpc_scan_op->set_table(OB_ALL_SYS_PARAM_TID, OB_ALL_SYS_PARAM_TID)) != OB_SUCCESS)
      {
        TRANS_LOG("ObTableRpcScan set table faild");
      }
      else if ((ret = rpc_scan_op->init(sql_context_, hint)) != OB_SUCCESS)
      {
        TRANS_LOG("ObTableRpcScan init faild");
      }
      else if ((ret = project_op->set_child(0, *rpc_scan_op)) != OB_SUCCESS)
      {
        TRANS_LOG("Set child of Project operator faild");
      }
      else
      {
        const ObSchemaManagerV2 *schema = sql_context_->schema_manager_;
        const ObColumnSchemaV2* none_concern_keys[1];
        const ObColumnSchemaV2 *name_column = NULL;
        const ObColumnSchemaV2 *value_column = NULL;
        if ((none_concern_keys[0] = schema->get_column_schema(OB_ALL_SYS_PARAM_TABLE_NAME,
                                                             "cluster_id")) == NULL
          || (name_column = schema->get_column_schema(OB_ALL_SYS_PARAM_TABLE_NAME,
                                                      "name")) == NULL
          || (value_column = schema->get_column_schema(OB_ALL_SYS_PARAM_TABLE_NAME,
                                                       "value")) == NULL)
        {
          ret = OB_ERR_COLUMN_UNKNOWN;
          TRANS_LOG("Get column of %s faild, ret = %d", OB_ALL_SYS_PARAM_TABLE_NAME, ret);
        }
        for (int32_t i = 0; ret == OB_SUCCESS && i < 1; i++)
        {
          ObObj val;
          val.set_int(0);
          ObConstRawExpr value(val, T_INT);
          ObBinaryRefRawExpr col(OB_ALL_SYS_PARAM_TID, none_concern_keys[i]->get_id(), T_REF_COLUMN);
          ObBinaryOpRawExpr equal_op(&col, &value, T_OP_EQ);
          ObSqlRawExpr col_expr(OB_INVALID_ID,
                                OB_ALL_SYS_PARAM_TID,
                                none_concern_keys[i]->get_id(),
                                &col);
          ObSqlRawExpr equal_expr(OB_INVALID_ID,
                                  OB_ALL_SYS_PARAM_TID,
                                  none_concern_keys[i]->get_id(),
                                  &equal_op);
          ObSqlExpression output_col;
          ObSqlExpression *filter = ObSqlExpression::alloc();
          if (NULL == filter)
          {
            ret = OB_ALLOCATE_MEMORY_FAILED;
            TRANS_LOG("no memory");
          }
          else if ((ret = col_expr.fill_sql_expression(output_col)) != OB_SUCCESS)
          {
            ObSqlExpression::free(filter);
            TRANS_LOG("Generate output column of TableScan faild, ret = %d", ret);
          }
          else if ((ret = rpc_scan_op->add_output_column(output_col)) != OB_SUCCESS)
          {
            ObSqlExpression::free(filter);
            TRANS_LOG("Add output column to TableScan faild, ret = %d", ret);
          }
          else if ((ret = equal_expr.fill_sql_expression(*filter)) != OB_SUCCESS)
          {
            ObSqlExpression::free(filter);
            TRANS_LOG("Generate filter faild, ret = %d", ret);
          }
          else if ((ret = rpc_scan_op->add_filter(filter)) != OB_SUCCESS)
          {
            TRANS_LOG("Add filter to TableScan faild, ret = %d", ret);
          }
        }
        if (ret == OB_SUCCESS)
        {
          ObBinaryRefRawExpr col(OB_ALL_SYS_PARAM_TID, name_column->get_id(), T_REF_COLUMN);
          ObSqlRawExpr expr(OB_INVALID_ID, OB_ALL_SYS_PARAM_TID, name_column->get_id(), &col);
          ObSqlExpression output_expr;
          const ColumnItem* column_item = NULL;
          if ((ret = expr.fill_sql_expression(output_expr)) != OB_SUCCESS)
          {
            TRANS_LOG("Generate output column faild, ret = %d", ret);
          }
          else if ((ret = rpc_scan_op->add_output_column(output_expr)) != OB_SUCCESS)
          {
            TRANS_LOG("Add output column to TableScan faild, ret = %d", ret);
          }
          else if ((column_item = show_stmt->get_column_item(0)) == NULL)
          {
            TRANS_LOG("Can not get column item of 'name'");
          }
          else
          {
            output_expr.set_tid_cid(column_item->table_id_, column_item->column_id_);
            if ((ret = project_op->add_output_column(output_expr)) != OB_SUCCESS)
            {
              TRANS_LOG("Add output column to Project faild, ret = %d", ret);
            }
          }
        }
        if (ret == OB_SUCCESS)
        {
          ObBinaryRefRawExpr col(OB_ALL_SYS_PARAM_TID, value_column->get_id(), T_REF_COLUMN);
          ObSqlRawExpr expr(OB_INVALID_ID, OB_ALL_SYS_PARAM_TID, value_column->get_id(), &col);
          ObSqlExpression output_expr;
          const ColumnItem* column_item = NULL;
          if ((ret = expr.fill_sql_expression(output_expr)) != OB_SUCCESS)
          {
            TRANS_LOG("Generate output column faild, ret = %d", ret);
          }
          else if ((ret = rpc_scan_op->add_output_column(output_expr)) != OB_SUCCESS)
          {
            TRANS_LOG("Add output column to TableScan faild, ret = %d", ret);
          }
          else if ((column_item = show_stmt->get_column_item(1)) == NULL)
          {
            TRANS_LOG("Can not get column item of 'value'");
          }
          else
          {
            output_expr.set_tid_cid(column_item->table_id_, column_item->column_id_);
            if ((ret = project_op->add_output_column(output_expr)) != OB_SUCCESS)
            {
              TRANS_LOG("Add output column to Project faild, ret = %d", ret);
            }
          }
        }
      }
      if (ret == OB_SUCCESS)
      {
        out_op = project_op;
      }
    }
    return ret;
  }

int ObTransformer::gen_phy_show_warnings(
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObShowStmt *show_stmt,
    ObPhyOperator *&out_op)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObRowDesc row_desc;
  ObValues *values_op = NULL;
  CREATE_PHY_OPERRATOR(values_op, ObValues, physical_plan, err_stat);

  if (sql_context_->session_info_ == NULL)
  {
    ret = OB_ERR_GEN_PLAN;
    TRANS_LOG("can not get current session info, err=%d", ret);
  }
  else
  {
    const tbsys::WarningBuffer& warnings_buf = sql_context_->session_info_->get_warnings_buffer();
    if (show_stmt->is_count_warnings())
    {
      /* show COUNT(*) warnings */
      if ((ret = row_desc.add_column_desc(OB_INVALID_ID, OB_APP_MIN_COLUMN_ID)) != OB_SUCCESS)
      {
        TRANS_LOG("add row desc error, err=%d", ret);
      }
      else if (ret == OB_SUCCESS && (ret = values_op->set_row_desc(row_desc)) != OB_SUCCESS)
      {
        TRANS_LOG("set row desc error, err=%d", ret);
      }
      else
      {
        ObRow val_row;
        val_row.set_row_desc(row_desc);
        ObObj num;
        num.set_int(warnings_buf.get_readable_warning_count());
        if ((ret = val_row.set_cell(OB_INVALID_ID, OB_APP_MIN_COLUMN_ID, num)) != OB_SUCCESS)
        {
          TRANS_LOG("Add 'code' to ObRow failed");
        }
        else if ((ret = values_op->add_values(val_row)) != OB_SUCCESS)
        {
          TRANS_LOG("Add value row failed");
        }
      }
    }
    else
    {
      /* show warnings [limit] */
      // add descriptor
      for (int32_t i = 0; ret == OB_SUCCESS && i < 3; i++)
      {
        if ((ret = row_desc.add_column_desc(OB_INVALID_ID, i + OB_APP_MIN_COLUMN_ID)) != OB_SUCCESS)
        {
          TRANS_LOG("add row desc error, err=%d", ret);
          break;
        }
      }
      if (ret == OB_SUCCESS && (ret = values_op->set_row_desc(row_desc)) != OB_SUCCESS)
      {
        TRANS_LOG("set row desc error, err=%d", ret);
      }
      // add values
      else
      {
        uint32_t j = 0;
        int64_t k = 0;
        for (; ret == OB_SUCCESS && j < warnings_buf.get_readable_warning_count()
            && (k < show_stmt->get_warnings_count() || show_stmt->get_warnings_count() < 0);
            j++, k++)
        {
          ObRow val_row;
          val_row.set_row_desc(row_desc);
          // can not get level, get it from string
          const char* warning_ptr = warnings_buf.get_warning(j);
          if (warning_ptr == NULL)
            continue;
          const char* separator = strchr(warning_ptr, ' ');
          if (separator == NULL)
          {
            TBSYS_LOG(WARN, "Wrong message in warnings buffer: %s", warning_ptr);
            continue;
          }
          ObObj level;
          level.set_varchar(ObString::make_string("Warning"));
          if ((ret = val_row.set_cell(OB_INVALID_ID, OB_APP_MIN_COLUMN_ID, level)) != OB_SUCCESS)
          {
            TRANS_LOG("Add 'level' to ObRow failed");
            break;
          }
          // code, can not get it
          ObObj code;
          code.set_int(99999);
          if ((ret = val_row.set_cell(OB_INVALID_ID, 1 + OB_APP_MIN_COLUMN_ID, code)) != OB_SUCCESS)
          {
            TRANS_LOG("Add 'code' to ObRow failed");
            break;
          }
          // message
          // pls see the warning format
          int32_t msg_len = static_cast<int32_t>(strlen(warning_ptr));
          ObString msg_str(msg_len, msg_len, warning_ptr);
          ObObj message;
          message.set_varchar(msg_str);
          if ((ret = val_row.set_cell(OB_INVALID_ID, 2 + OB_APP_MIN_COLUMN_ID, message)) != OB_SUCCESS)
          {
            TRANS_LOG("Add 'message' to ObRow failed");
            break;
          }
          else if ((ret = values_op->add_values(val_row)) != OB_SUCCESS)
          {
            TRANS_LOG("Add value row failed");
            break;
          }
        }
      }
    }
  }
  if (ret == OB_SUCCESS)
  {
    out_op = values_op;
  }
  return ret;
}

int ObTransformer::gen_phy_show_grants(
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObShowStmt *show_stmt,
    ObPhyOperator *&out_op)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObRowDesc row_desc;
  ObValues *values_op = NULL;
  CREATE_PHY_OPERRATOR(values_op, ObValues, physical_plan, err_stat);
  if ((ret = row_desc.add_column_desc(OB_INVALID_ID, OB_APP_MIN_COLUMN_ID)) != OB_SUCCESS)
  {
    TRANS_LOG("add row desc error, err=%d", ret);
  }
  else if ((ret = values_op->set_row_desc(row_desc)) != OB_SUCCESS)
  {
    TRANS_LOG("set row desc error, err=%d", ret);
  }
  else
  {
    out_op = values_op;
    const ObPrivilege **pp_privilege  = sql_context_->pp_privilege_;
    ObString user_name = show_stmt->get_user_name();
    int64_t pos = 0;
    char buf[512];
    if (show_stmt->get_user_name().length() == 0)
    {
      user_name = sql_context_->session_info_->get_user_name();
    }
    const common::ObSchemaManagerV2 *schema_manager = sql_context_->schema_manager_;
    const ObTableSchema* table_schema = NULL;
    hash::ObHashMap<ObString,ObPrivilege::User, hash::NoPthreadDefendMode> *username_map = (const_cast<ObPrivilege*>(*pp_privilege))->get_username_map();
    hash::ObHashMap<ObPrivilege::UserIdTableId, ObPrivilege::UserPrivilege, hash::NoPthreadDefendMode> *user_table_map = (const_cast<ObPrivilege*>(*pp_privilege))->get_user_table_map();
    ObPrivilege::User user;
    ret = username_map->get(user_name, user);
    if (-1 == ret || hash::HASH_NOT_EXIST == ret)
    {
      TBSYS_LOG(WARN, "username:%.*s 's not exist, ret=%d", user_name.length(), user_name.ptr(), ret);
      ret = OB_ERR_USER_NOT_EXIST;
    }
    else
    {
      ret = OB_SUCCESS;
      //全局权限如果有，则显示一行
      const ObBitSet<> &privileges = user.privileges_;
      // 没有全局权限
      if (privileges.is_empty())
      {
      }
      else
      {
        databuff_printf(buf, 512, pos, "GRANT ");
        if (privileges.has_member(OB_PRIV_ALL))
        {
          databuff_printf(buf, 512, pos, "ALL PRIVILEGES ");
          if (privileges.has_member(OB_PRIV_GRANT_OPTION))
          {
            databuff_printf(buf, 512, pos, ",GRANT OPTION ON * TO '%.*s'", user_name.length(), user_name.ptr());
          }
          else
          {
            databuff_printf(buf, 512, pos, "ON * TO '%.*s'", user_name.length(), user_name.ptr());
          }
        }
        else
        {
          ObPrivilege::privilege_to_string(privileges, buf, 512, pos);
          pos = pos - 1;
          databuff_printf(buf, 512, pos, " ON * TO '%.*s'", user_name.length(), user_name.ptr());
        }
        ObRow val_row;
        val_row.set_row_desc(row_desc);
        ObString grant_str;
        if (pos >= 511)
        {
          // overflow
          ret = OB_BUF_NOT_ENOUGH;
          TBSYS_LOG(WARN, "privilege buffer not enough, ret=%d", ret);
        }
        else
        {
          grant_str.assign_ptr(buf, static_cast<int32_t>(pos));
          ObObj grant_val;
          grant_val.set_varchar(grant_str);
          if (OB_SUCCESS != (ret = val_row.set_cell(OB_INVALID_ID, OB_APP_MIN_COLUMN_ID, grant_val)))
          {
            TBSYS_LOG(WARN, "set cell fail:ret[%d]", ret);
          }
          else if (OB_SUCCESS != (ret = values_op->add_values(val_row)))
          {
            TRANS_LOG("add value row failed");
          }
        }
      }
    }
    //显示局部权限
    if (OB_SUCCESS == ret)
    {
      uint64_t user_id = user.user_id_;
      hash::ObHashMap<ObPrivilege::UserIdTableId, ObPrivilege::UserPrivilege, hash::NoPthreadDefendMode>::iterator iter = user_table_map->begin();
      for (;iter != user_table_map->end();++iter)
      {
        pos = 0;
        databuff_printf(buf, 512, pos, "GRANT ");
        const ObPrivilege::UserIdTableId &user_id_table_id = iter->first;
        if (user_id_table_id.user_id_ == user_id)
        {
          const ObBitSet<> &privileges = (iter->second).table_privilege_.privileges_;
          if (privileges.is_empty())
          {
            continue;
          }
          else
          {
            ObPrivilege::privilege_to_string(privileges, buf, 512, pos);
            table_schema = schema_manager->get_table_schema(user_id_table_id.table_id_);
            if (NULL == table_schema)
            {
              //出现这种情况的原因可能是别的会话通过同一个用户新建了一张新表，权限信息已经更新到了本地，但是schema信息还没有更新到本地
              //不将其作为一种错误，目前仅仅不显示这张表的权限信息即可
              TBSYS_LOG(WARN, "table id=%lu not exist in schema manager", user_id_table_id.table_id_);
            }
            else
            {
              const char *table_name = table_schema->get_table_name();
              pos = pos - 1;
              databuff_printf(buf, 512, pos, " ON %s TO '%.*s'", table_name, user_name.length(), user_name.ptr());
              ObRow val_row;
              val_row.set_row_desc(row_desc);
              ObString grant_str;
              if (pos >= 511)
              {
                // overflow
                ret = OB_BUF_NOT_ENOUGH;
                TBSYS_LOG(WARN, "privilege buffer not enough, ret=%d", ret);
              }
              else
              {
                grant_str.assign_ptr(buf, static_cast<int32_t>(pos));
                ObObj grant_val;
                grant_val.set_varchar(grant_str);
                if (OB_SUCCESS != (ret = val_row.set_cell(OB_INVALID_ID, OB_APP_MIN_COLUMN_ID, grant_val)))
                {
                  TBSYS_LOG(WARN, "set cell fail:ret[%d]", ret);
                }
                else if (OB_SUCCESS != (ret = values_op->add_values(val_row)))
                {
                  TRANS_LOG("add value row failed");
                }
              }
            }
          }
        }
        else
        {
          continue;
        }
      }
    }
  }
  return ret;
}

int ObTransformer::gen_phy_show_table_status(
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObShowStmt *show_stmt,
    ObPhyOperator *&out_op)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  UNUSED(show_stmt);
  ObValues *values_op = NULL;
  if (NULL == CREATE_PHY_OPERRATOR(values_op, ObValues, physical_plan, err_stat))
  {
    ret = OB_ALLOCATE_MEMORY_FAILED;
  }
  else
  {
    // @todo empty
    out_op = values_op;
  }
  return ret;
}
int ObTransformer::gen_physical_show(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    int32_t* index)
{
  int &ret = err_stat.err_code_ = OB_SUCCESS;
  ObShowStmt *show_stmt = NULL;
  ObPhyOperator *result_op = NULL;

  /* get statement */
  if (ret == OB_SUCCESS)
  {
    get_stmt(logical_plan, err_stat, query_id, show_stmt);
  }

  if (ret == OB_SUCCESS)
  {
    switch (show_stmt->get_stmt_type())
    {
      case ObBasicStmt::T_SHOW_TABLES:
        ret = gen_phy_show_tables(physical_plan, err_stat, show_stmt, result_op);
        break;
      case ObBasicStmt::T_SHOW_COLUMNS:
        ret = gen_phy_show_columns(physical_plan, err_stat, show_stmt, result_op);
        break;
      case ObBasicStmt::T_SHOW_VARIABLES:
        ret = gen_phy_show_variables(physical_plan, err_stat, show_stmt, result_op);
        break;
      case ObBasicStmt::T_SHOW_TABLE_STATUS:
        ret = gen_phy_show_table_status(physical_plan, err_stat, show_stmt, result_op);
        break;
      case ObBasicStmt::T_SHOW_SCHEMA:
      case ObBasicStmt::T_SHOW_SERVER_STATUS:
        TRANS_LOG("This statment not support now!");
        break;
      case ObBasicStmt::T_SHOW_CREATE_TABLE:
        ret = gen_phy_show_create_table(physical_plan, err_stat, show_stmt, result_op);
        break;
      case ObBasicStmt::T_SHOW_WARNINGS:
        ret = gen_phy_show_warnings(physical_plan, err_stat, show_stmt, result_op);
        break;
      case ObBasicStmt::T_SHOW_GRANTS:
        ret = gen_phy_show_grants(physical_plan, err_stat, show_stmt, result_op);
        break;
      case ObBasicStmt::T_SHOW_PARAMETERS:
        ret = gen_phy_show_parameters(logical_plan, physical_plan, err_stat, show_stmt, result_op);
        break;
      default:
        ret = OB_ERR_GEN_PLAN;
        TRANS_LOG("Unknown show statment!");
        break;
    }
  }
  if (ret == OB_SUCCESS)
  {
    ObFilter *filter_op = NULL;
    if (show_stmt->get_like_pattern().length() > 0)
    {
      ObObj pattern_val;
      pattern_val.set_varchar(show_stmt->get_like_pattern());
      ObConstRawExpr pattern_expr(pattern_val, T_STRING);
      pattern_expr.set_result_type(ObVarcharType);
      ObBinaryRefRawExpr col_expr(show_stmt->get_sys_table_id(), OB_INVALID_ID, T_REF_COLUMN);
      const ObColumnSchemaV2* name_col = NULL;
      const ObColumnSchemaV2* columns = NULL;
      int32_t column_size = 0;
      ObSchemaChecker schema_checker;
      schema_checker.set_schema(*sql_context_->schema_manager_);
      if (show_stmt->get_stmt_type() == ObBasicStmt::T_SHOW_PARAMETERS)
      {
        if ((name_col = schema_checker.get_column_schema(
                                            show_stmt->get_table_item(0).table_name_,
                                            ObString::make_string("name")
                                            )) == NULL)
        {
        }
        else
        {
          col_expr.set_second_ref_id(name_col->get_id());
          col_expr.set_result_type(name_col->get_type());
        }
      }
      else
      {
        if ((columns = schema_checker.get_table_columns(
                                           show_stmt->get_sys_table_id(),
                                           column_size)) == NULL
          || column_size <= 0)
        {
          ret = OB_ERR_GEN_PLAN;
          TRANS_LOG("Get show table schema error!");
        }
        else
        {
          col_expr.set_second_ref_id(columns[0].get_id());
          col_expr.set_result_type(columns[0].get_type());
        }
      }
      if (ret == OB_SUCCESS)
      {
        ObBinaryOpRawExpr like_op_expr(&col_expr, &pattern_expr, T_OP_LIKE);
        like_op_expr.set_result_type(ObBoolType);
        ObSqlRawExpr raw_like_expr(OB_INVALID_ID, col_expr.get_first_ref_id(),
                                   col_expr.get_second_ref_id(), &like_op_expr);
        ObSqlExpression *like_expr = ObSqlExpression::alloc();
        if (NULL == like_expr
            || (ret = raw_like_expr.fill_sql_expression(*like_expr, this, logical_plan, physical_plan)) != OB_SUCCESS)
        {
          TRANS_LOG("Gen like filter failed!");
        }
        else if (CREATE_PHY_OPERRATOR(filter_op, ObFilter, physical_plan, err_stat) == NULL)
        {
          ObSqlExpression::free(like_expr);
        }
        else if ((ret = filter_op->set_child(0, *result_op)) != OB_SUCCESS)
        {
          ObSqlExpression::free(like_expr);
          TRANS_LOG("Add child of filter plan failed");
        }
        else if ((ret = filter_op->add_filter(like_expr)) != OB_SUCCESS)
        {
          TRANS_LOG("Add filter expression failed");
        }
      }
    }
    else if (show_stmt->get_condition_size() > 0)
    {
      CREATE_PHY_OPERRATOR(filter_op, ObFilter, physical_plan, err_stat);
      for (int32_t i = 0; ret == OB_SUCCESS && i < show_stmt->get_condition_size(); i++)
      {
        ObSqlRawExpr *cnd_expr = logical_plan->get_expr(show_stmt->get_condition_id(i));
        if (cnd_expr->is_apply() == true)
        {
          continue;
        }
        else
        {
          ObSqlExpression *filter = ObSqlExpression::alloc();
          if (NULL == filter)
          {
            ret = OB_ALLOCATE_MEMORY_FAILED;
            TBSYS_LOG(ERROR, "no memory");
            break;
          }
          else if ((ret = cnd_expr->fill_sql_expression(*filter, this, logical_plan, physical_plan)) != OB_SUCCESS
                   || (ret = filter_op->add_filter(filter)) != OB_SUCCESS)
          {
            ObSqlExpression::free(filter);
            TRANS_LOG("Add table filter condition faild");
            break;
          }
        }
      } // end for
      if (ret == OB_SUCCESS && (ret = filter_op->set_child(0, *result_op))!= OB_SUCCESS)
      {
        TRANS_LOG("Add child of filter plan failed");
      }
    }
    if (ret == OB_SUCCESS && filter_op != NULL)
    {
      result_op = filter_op;
    }
  }
  if (ret == OB_SUCCESS)
  {
    ret = add_phy_query(logical_plan, physical_plan, err_stat, query_id, show_stmt, result_op, index);
  }

  return ret;
}

int ObTransformer::gen_physical_prepare(
  ObLogicalPlan *logical_plan,
  ObPhysicalPlan *physical_plan,
  ErrStat& err_stat,
  const uint64_t& query_id,
  int32_t* index)
{
  int &ret = err_stat.err_code_ = OB_SUCCESS;
  ObPrepare *result_op = NULL;
  ObPrepareStmt *stmt = NULL;
  /* get prepare statement */
  get_stmt(logical_plan, err_stat, query_id, stmt);
  /* add prepare operator */
  if (ret == OB_SUCCESS)
  {
    CREATE_PHY_OPERRATOR(result_op, ObPrepare, physical_plan, err_stat);
    if (ret == OB_SUCCESS)
    {
      ret = add_phy_query(logical_plan, physical_plan, err_stat, query_id, stmt, result_op, index);
    }
  }

  if (ret == OB_SUCCESS)
  {
    ObPhyOperator* op = NULL;
    ObString stmt_name;
    int32_t idx = OB_INVALID_INDEX;
    if ((ret = ob_write_string(*mem_pool_, stmt->get_stmt_name(), stmt_name)) != OB_SUCCESS)
    {
      TRANS_LOG("Add prepare plan for stmt %.*s faild",
          stmt->get_stmt_name().length(), stmt->get_stmt_name().ptr());
    }
    else
    {
      result_op->set_stmt_name(stmt_name);

      if ((ret = generate_physical_plan(
                          logical_plan,
                          physical_plan,
                          err_stat,
                          stmt->get_prepare_query_id(),
                          &idx)) != OB_SUCCESS)
      {
        TBSYS_LOG(WARN, "Create physical plan for query statement failed, err=%d", ret);
      }
      else if ((op = physical_plan->get_phy_query(idx)) == NULL
        || (ret = result_op->set_child(0, *op)) != OB_SUCCESS)
      {
        ret = OB_ERR_ILLEGAL_INDEX;
        TRANS_LOG("Set child of Prepare Operator failed");
      }
    }
  }

  return ret;
}

int ObTransformer::gen_physical_variable_set(
  ObLogicalPlan *logical_plan,
  ObPhysicalPlan *physical_plan,
  ErrStat& err_stat,
  const uint64_t& query_id,
  int32_t* index)
{
  int &ret = err_stat.err_code_ = OB_SUCCESS;
  ObVariableSet *result_op = NULL;
  ObVariableSetStmt *stmt = NULL;
  /* get variable set statement */
  get_stmt(logical_plan, err_stat, query_id, stmt);
  /* generate operator */
  if (ret == OB_SUCCESS)
  {
    CREATE_PHY_OPERRATOR(result_op, ObVariableSet, physical_plan, err_stat);
    if (ret == OB_SUCCESS)
    {
      ret = add_phy_query(logical_plan, physical_plan, err_stat, query_id, stmt, result_op, index);
    }
  }
  if (ret == OB_SUCCESS)
  {
    const ObTableSchema *table_schema = NULL;
    const ObColumnSchemaV2* name_column = NULL;
    const ObColumnSchemaV2* type_column = NULL;
    const ObColumnSchemaV2* value_column = NULL;
    if ((table_schema = sql_context_->schema_manager_->get_table_schema(
      OB_ALL_SYS_PARAM_TID)) == NULL)
    {
      ret = OB_ERR_TABLE_UNKNOWN;
      TRANS_LOG("Fail to get table schema for table[%ld]", OB_ALL_SYS_PARAM_TID);
    }
    else if ((name_column = sql_context_->schema_manager_->get_column_schema(
      OB_ALL_SYS_PARAM_TABLE_NAME, "name")) == NULL)
    {
      ret = OB_ERR_COLUMN_NOT_FOUND;
      TRANS_LOG("Column name not found");
    }
    else if ((type_column = sql_context_->schema_manager_->get_column_schema(
      OB_ALL_SYS_PARAM_TABLE_NAME, "data_type")) == NULL)
    {
      ret = OB_ERR_COLUMN_NOT_FOUND;
      TRANS_LOG("Column type not found");
    }
    else if ((value_column = sql_context_->schema_manager_->get_column_schema(
      OB_ALL_SYS_PARAM_TABLE_NAME, "value")) == NULL)
    {
      ret = OB_ERR_COLUMN_NOT_FOUND;
      TRANS_LOG("Column value not found");
    }
    else
    {
      result_op->set_rpc_stub(sql_context_->merger_rpc_proxy_);
      result_op->set_table_id(OB_ALL_SYS_PARAM_TID);
      result_op->set_name_cid(name_column->get_id());
      result_op->set_rowkey_info(table_schema->get_rowkey_info());
      result_op->set_type_column(type_column->get_id(), type_column->get_type());
      result_op->set_value_column(value_column->get_id(), value_column->get_type());
    }
  }
  int64_t variables_num = stmt->get_variables_size();
  for (int64_t i = 0; ret == OB_SUCCESS && i < variables_num; i++)
  {
    const ObVariableSetStmt::VariableSetNode& var_stmt_node = stmt->get_variable_node(static_cast<int32_t>(i));
    ObVariableSet::VariableSetNode var_op_node;
    ObSqlRawExpr *expr = NULL;
    ObSqlExpression value;
    ObRow val_row;
    const ObObj *value_obj = NULL;
    ObObj tmp_value_obj;
    var_op_node.is_system_variable_ = var_stmt_node.is_system_variable_;
    var_op_node.is_global_ = (var_stmt_node.scope_type_ == ObVariableSetStmt::GLOBAL);
    if (var_stmt_node.is_system_variable_ &&
      !sql_context_->session_info_->sys_variable_exists(var_stmt_node.variable_name_))
    {
      ret = OB_ERR_VARIABLE_UNKNOWN;
      TRANS_LOG("System variable %.*s Unknown", var_stmt_node.variable_name_.length(),
          var_stmt_node.variable_name_.ptr());
    }
    else if ((ret = ob_write_string(*mem_pool_,
                                    var_stmt_node.variable_name_,
                                    var_op_node.variable_name_)) != OB_SUCCESS)
    {
      TRANS_LOG("Make place for variable name %.*s failed",
          var_stmt_node.variable_name_.length(), var_stmt_node.variable_name_.ptr());
    }
    else if ((expr = logical_plan->get_expr(var_stmt_node.value_expr_id_)) == NULL)
    {
      ret = OB_ERR_ILLEGAL_ID;
      TRANS_LOG("Wrong expression id, id=%lu", var_stmt_node.value_expr_id_);
    }
    else if ((ret = expr->fill_sql_expression(value, this, logical_plan, physical_plan)) != OB_SUCCESS)
    {
      TRANS_LOG("Add value expression failed");
    }
    else if (var_op_node.is_system_variable_
        &&
        expr->get_result_type() != ObNullType
        &&
        expr->get_result_type() != (sql_context_->session_info_->get_sys_variable_type(var_stmt_node.variable_name_))
        )
    {
      ret = OB_OBJ_TYPE_ERROR;
      TRANS_LOG("type not match");
      TBSYS_LOG(WARN, "type not match, ret=%d", ret);
    }
    else if ((ret = value.calc(val_row, value_obj)) != OB_SUCCESS
             || (ret = ob_write_obj(*mem_pool_, *value_obj, var_op_node.variable_value_)) != OB_SUCCESS)
    {
      TRANS_LOG("Calculate variable value failed");
    }
    else if ((ret = result_op->add_variable_node(var_op_node)) != OB_SUCCESS)
    {
      TRANS_LOG("Add variable entry failed");
    }
  }
  return ret;
}

int ObTransformer::gen_physical_execute(
  ObLogicalPlan *logical_plan,
  ObPhysicalPlan *physical_plan,
  ErrStat& err_stat,
  const uint64_t& query_id,
  int32_t* index)
{
  int &ret = err_stat.err_code_ = OB_SUCCESS;
  ObExecute *result_op = NULL;
  ObExecuteStmt *stmt = NULL;
  /* get execute statement */
  get_stmt(logical_plan, err_stat, query_id, stmt);
  /* generate operator */
  if (ret == OB_SUCCESS)
  {
    CREATE_PHY_OPERRATOR(result_op, ObExecute, physical_plan, err_stat);
    if (ret == OB_SUCCESS)
    {
      ret = add_phy_query(logical_plan, physical_plan, err_stat, query_id, stmt, result_op, index);
    }
  }

  ObSQLSessionInfo *session_info = NULL;
  if (ret == OB_SUCCESS
    && (sql_context_ == NULL || (session_info = sql_context_->session_info_) == NULL))
  {
    ret = OB_NOT_INIT;
    TRANS_LOG("Session info is not initiated");
  }

  if (ret == OB_SUCCESS)
  {
    uint64_t stmt_id = OB_INVALID_ID;
    if (session_info->plan_exists(stmt->get_stmt_name(), &stmt_id) == false)
    {
      ret = OB_ERR_PREPARE_STMT_UNKNOWN;
      TRANS_LOG("Can not find stmt %.*s ", stmt->get_stmt_name().length(), stmt->get_stmt_name().ptr());
    }
    else
    {
      result_op->set_stmt_id(stmt_id);
    }
    for (int64_t i = 0; ret == OB_SUCCESS && i < stmt->get_variable_size(); i++)
    {
      const ObString& var_name = stmt->get_variable_name(i);
      if (session_info->variable_exists(var_name))
      {
        ObString tmp_name;
        if ((ret = ob_write_string(*mem_pool_, var_name, tmp_name)) != OB_SUCCESS
          || (ret = result_op->add_param_name(var_name)) != OB_SUCCESS)
        {
          TRANS_LOG("add variable %.*s failed", var_name.length(), var_name.ptr());
        }
      }
      else
      {
        ret = OB_ERR_VARIABLE_UNKNOWN;
        TRANS_LOG("Variable %.*s Unknown", var_name.length(), var_name.ptr());
      }
    }
  }

  return ret;
}

int ObTransformer::gen_physical_deallocate(
  ObLogicalPlan *logical_plan,
  ObPhysicalPlan *physical_plan,
  ErrStat& err_stat,
  const uint64_t& query_id,
  int32_t* index)
{
  int &ret = err_stat.err_code_ = OB_SUCCESS;
  ObDeallocate *result_op = NULL;
  ObDeallocateStmt *stmt = NULL;
  /* get deallocate statement */
  get_stmt(logical_plan, err_stat, query_id, stmt);
  /* generate operator */
  if (ret == OB_SUCCESS)
  {
    CREATE_PHY_OPERRATOR(result_op, ObDeallocate, physical_plan, err_stat);
    if (ret == OB_SUCCESS)
    {
      ret = add_phy_query(logical_plan, physical_plan, err_stat, query_id, stmt, result_op, index);
    }
  }
  if (ret == OB_SUCCESS)
  {
    uint64_t stmt_id = OB_INVALID_ID;
    if (sql_context_== NULL || sql_context_->session_info_ == NULL)
    {
      ret = OB_NOT_INIT;
      TRANS_LOG("Session info is needed");
    }
    else if (sql_context_->session_info_->plan_exists(stmt->get_stmt_name(), &stmt_id) == false)
    {
      ret = OB_ERR_PREPARE_STMT_UNKNOWN;
      TRANS_LOG("Unknown prepared statement handler (%.*s) given to DEALLOCATE PREPARE",
          stmt->get_stmt_name().length(), stmt->get_stmt_name().ptr());
    }
    else
    {
      result_op->set_stmt_id(stmt_id);
    }
  }

  return ret;
}

int ObTransformer::gen_phy_static_data_scan(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const ObInsertStmt *insert_stmt,
    const ObRowDesc& row_desc,
    const ObSEArray<int64_t, 64> &row_desc_map,
    const uint64_t table_id,
    const ObRowkeyInfo &rowkey_info,
    ObTableRpcScan &table_scan)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  OB_ASSERT(logical_plan);
  OB_ASSERT(insert_stmt);
  ObSqlExpression *rows_filter = ObSqlExpression::alloc();
  if (NULL == rows_filter)
  {
    ret = OB_ALLOCATE_MEMORY_FAILED;
    TBSYS_LOG(WARN, "no memory");
  }
  ObSqlExpression column_ref;
  // construct left operand of IN operator
  // the same order with row_desc
  ExprItem expr_item;
  expr_item.type_ = T_REF_COLUMN;
  expr_item.value_.cell_.tid = table_id;
  int64_t rowkey_column_num = rowkey_info.get_size();
  uint64_t tid = OB_INVALID_ID;
  for (int i = 0; OB_SUCCESS == ret && i < row_desc.get_column_num(); ++i)
  {
    if (OB_UNLIKELY(OB_SUCCESS != (ret = row_desc.get_tid_cid(i, tid, expr_item.value_.cell_.cid))))
    {
      break;
    }
    else if (rowkey_info.is_rowkey_column(expr_item.value_.cell_.cid))
    {
      column_ref.reset();
      column_ref.set_tid_cid(table_id, expr_item.value_.cell_.cid);
      if (OB_SUCCESS != (ret = rows_filter->add_expr_item(expr_item)))
      {
        TBSYS_LOG(WARN, "failed to add expr item, err=%d", ret);
        break;
      }
      else if (OB_SUCCESS != (ret = column_ref.add_expr_item(expr_item)))
      {
        TBSYS_LOG(WARN, "failed to add expr_item, err=%d", ret);
        break;
      }
      else if (OB_SUCCESS != (ret = column_ref.add_expr_item_end()))
      {
        TBSYS_LOG(WARN, "failed to add expr item, err=%d", ret);
        break;
      }
      else if (OB_SUCCESS != (ret = table_scan.add_output_column(column_ref)))
      {
        TBSYS_LOG(WARN, "failed to add output column, err=%d", ret);
        break;
      }
    }
  } // end for
  // add action flag column
  if (OB_LIKELY(OB_SUCCESS == ret))
  {
    column_ref.reset();
    column_ref.set_tid_cid(OB_INVALID_ID, OB_ACTION_FLAG_COLUMN_ID);
    if (OB_SUCCESS != (ret = ObSqlExpressionUtil::make_column_expr(OB_INVALID_ID, OB_ACTION_FLAG_COLUMN_ID, column_ref)))
    {
      TBSYS_LOG(WARN, "fail to make column expr:ret[%d]", ret);
    }
    else if (OB_SUCCESS != (ret = table_scan.add_output_column(column_ref)))
    {
      TBSYS_LOG(WARN, "failed to add output column, err=%d", ret);
    }
  }
  if (OB_LIKELY(OB_SUCCESS == ret))
  {
    expr_item.type_ = T_OP_ROW;
    expr_item.value_.int_ = rowkey_column_num;
    if (OB_SUCCESS != (ret = rows_filter->add_expr_item(expr_item)))
    {
      TRANS_LOG("Failed to add expr item, err=%d", ret);
    }
  }
  if (OB_LIKELY(OB_SUCCESS == ret))
  {
    expr_item.type_ = T_OP_LEFT_PARAM_END;
    // a in (a,b,c) => 1 Dim;  (a,b) in ((a,b),(c,d)) =>2 Dim; ((a,b),(c,d)) in (...) =>3 Dim
    expr_item.value_.int_ = 2;
    if (OB_SUCCESS != (ret = rows_filter->add_expr_item(expr_item)))
    {
      TBSYS_LOG(WARN, "failed to add expr item, err=%d", ret);
    }
  }
  uint64_t column_id = OB_INVALID_ID;
  if (OB_LIKELY(OB_SUCCESS == ret))
  {
    int64_t row_num = insert_stmt->get_value_row_size();
    for (int64_t i = 0; ret == OB_SUCCESS && i < row_num; i++) // for each row
    {
      const ObArray<uint64_t>& value_row = insert_stmt->get_value_row(i);
      OB_ASSERT(value_row.count() == row_desc_map.count());
      for (int64_t j = 0; ret == OB_SUCCESS && j < row_desc_map.count(); j++)
      {
        ObSqlRawExpr *value_expr = logical_plan->get_expr(value_row.at(row_desc_map.at(j)));
        if (value_expr == NULL)
        {
          ret = OB_ERR_ILLEGAL_ID;
          TRANS_LOG("Get value failed");
        }
        else if (OB_SUCCESS != (ret = row_desc.get_tid_cid(j, tid, column_id)))
        {
          TRANS_LOG("Failed to get tid cid, err=%d", ret);
        }
        // success
        else if (rowkey_info.is_rowkey_column(column_id))
        {
          // add right oprands of the IN operator
          if (OB_SUCCESS != (ret = value_expr->get_expr()->fill_sql_expression(*rows_filter, this, logical_plan, physical_plan)))
          {
            TRANS_LOG("Failed to fill expr, err=%d", ret);
          }
        }
      } // end for
      if (OB_LIKELY(ret == OB_SUCCESS))
      {
        if (rowkey_column_num > 0)
        {
          expr_item.type_ = T_OP_ROW;
          expr_item.value_.int_ = rowkey_column_num;
          if (OB_SUCCESS != (ret = rows_filter->add_expr_item(expr_item)))
          {
            TRANS_LOG("Failed to add expr item, err=%d", ret);
          }
        }
      }
    } // end for

    if (OB_LIKELY(OB_SUCCESS == ret))
    {
      expr_item.type_ = T_OP_ROW;
      expr_item.value_.int_ = row_num;
      ExprItem expr_in;
      expr_in.type_ = T_OP_IN;
      expr_in.value_.int_ = 2;
      if (OB_SUCCESS != (ret = rows_filter->add_expr_item(expr_item)))
      {
        TRANS_LOG("Failed to add expr item, err=%d", ret);
      }
      else if (OB_SUCCESS != (ret = rows_filter->add_expr_item(expr_in)))
      {
        TRANS_LOG("Failed to add expr item, err=%d", ret);
      }
      else if (OB_SUCCESS != (ret = rows_filter->add_expr_item_end()))
      {
        TRANS_LOG("Failed to add expr item end, err=%d", ret);
      }
      else if (OB_SUCCESS != (ret = table_scan.add_filter(rows_filter)))
      {
        TRANS_LOG("Failed to add filter, err=%d", ret);
      }
    }
  }
  return ret;
}

int ObTransformer::wrap_ups_executor(
  ObPhysicalPlan *physical_plan,
  const uint64_t query_id,
  ObPhysicalPlan*& new_plan,
  int32_t *index,
  ErrStat& err_stat)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  OB_ASSERT(physical_plan);
  ObUpsExecutor *ups_executor = NULL;
  new_plan = (ObPhysicalPlan*)trans_malloc(sizeof(ObPhysicalPlan));
  if (NULL == new_plan)
  {
    TRANS_LOG("no memory");
    ret = OB_ALLOCATE_MEMORY_FAILED;
  }
  else
  {
    new_plan = new(new_plan) ObPhysicalPlan();
    TBSYS_LOG(DEBUG, "new wrapper physical plan, addr=%p", physical_plan);
    if (NULL == CREATE_PHY_OPERRATOR(ups_executor, ObUpsExecutor, physical_plan, err_stat))
    {
      ret = OB_ALLOCATE_MEMORY_FAILED;
    }
    else if (OB_SUCCESS != (ret = physical_plan->add_phy_query(ups_executor, index, OB_INVALID_ID == query_id)))
    {
      TBSYS_LOG(WARN, "failed to add query, err=%d", ret);
    }
    else if (NULL == sql_context_->merge_service_)
    {
      ret = OB_NOT_INIT;
      TBSYS_LOG(WARN, "merge_service_ is null");
    }
    else
    {
      ups_executor->set_rpc_stub(sql_context_->merger_rpc_proxy_);
      ups_executor->set_inner_plan(new_plan);
    }
    if (OB_SUCCESS != ret)
    {
      new_plan->~ObPhysicalPlan();
    }
  }
  return ret;
}

int ObTransformer::gen_physical_insert_new(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    int32_t* index)
{
  int &ret = err_stat.err_code_ = OB_SUCCESS;
  ObInsertStmt *insert_stmt = NULL;
  ObUpsModify *ups_modify = NULL;
  ObRowDesc row_desc;
  ObRowDescExt row_desc_ext;
  ObSEArray<int64_t, 64> row_desc_map;
  const ObRowkeyInfo *rowkey_info = NULL;
  ObPhysicalPlan* inner_plan = NULL;
  if (OB_SUCCESS != (ret = wrap_ups_executor(physical_plan, query_id, inner_plan, index, err_stat)))
  {
    TBSYS_LOG(WARN, "err=%d", ret);
  }
  else if (OB_SUCCESS != (ret = get_stmt(logical_plan, err_stat, query_id, insert_stmt)))
  {
  }
  else if (NULL == CREATE_PHY_OPERRATOR(ups_modify, ObUpsModify, inner_plan, err_stat))
  {
    ret = OB_ALLOCATE_MEMORY_FAILED;
  }
  else if (OB_SUCCESS != (ret = inner_plan->add_phy_query(ups_modify, NULL, true))) // always main query
  {
    TRANS_LOG("Failed to add phy query, err=%d", ret);
  }
  else if (OB_SUCCESS != (ret = cons_row_desc(insert_stmt->get_table_id(), insert_stmt,
                                              row_desc_ext, row_desc, rowkey_info, row_desc_map, err_stat)))
  {
    ret = OB_ERROR;
    TRANS_LOG("Fail to get table schema for table[%ld]", insert_stmt->get_table_id());
  }
  else
  {
    // check primary key columns
    uint64_t tid = insert_stmt->get_table_id();
    uint64_t cid = OB_INVALID_ID;
    for (int64_t i = 0; i < rowkey_info->get_size(); ++i)
    {
      if (OB_SUCCESS != (ret = rowkey_info->get_column_id(i, cid)))
      {
        TBSYS_LOG(USER_ERROR, "primary key can not be empty");
        ret = OB_ERR_INSERT_NULL_ROWKEY;
        break;
      }
      else if (OB_INVALID_INDEX == row_desc.get_idx(tid, cid))
      {
        TBSYS_LOG(USER_ERROR, "primary key can not be empty");
        ret = OB_ERR_INSERT_NULL_ROWKEY;
        break;
      }
    } // end for
  }
  if (OB_LIKELY(ret == OB_SUCCESS))
  {
    if (OB_LIKELY(insert_stmt->get_insert_query_id() == OB_INVALID_ID))
    {
      // INSERT ... VALUES ...
      if (OB_LIKELY(OB_SUCCESS == ret))
      {
        uint64_t tid = insert_stmt->get_table_id();
        const ObTableSchema *table_schema = NULL;
        if (NULL == (table_schema = sql_context_->schema_manager_->get_table_schema(tid)))
        {
          ret = OB_ERR_ILLEGAL_ID;
          TRANS_LOG("fail to get table schema for table[%ld]", tid);
        }
        else if (row_desc.get_idx(tid, table_schema->get_create_time_column_id()) != OB_INVALID_INDEX)
        {
          ret = OB_ERR_CREAT_MODIFY_TIME_COLUMN;
          ColumnItem *column_item = insert_stmt->get_column_item_by_id(tid, table_schema->get_create_time_column_id());
          if (column_item != NULL)
            TRANS_LOG("Column '%.*s' of type ObCreateTimeType can not be inserted",
                column_item->column_name_.length(), column_item->column_name_.ptr());
          else
            TRANS_LOG("Column '%ld' of type ObCreateTimeType can not be inserted",
                table_schema->get_create_time_column_id());
        }
        else if (row_desc.get_idx(tid, table_schema->get_modify_time_column_id()) != OB_INVALID_INDEX)
        {
          ret = OB_ERR_CREAT_MODIFY_TIME_COLUMN;
          ColumnItem *column_item = insert_stmt->get_column_item_by_id(tid, table_schema->get_modify_time_column_id());
          if (column_item != NULL)
            TRANS_LOG("Column '%.*s' of type ObModifyTimeType can not be inserted",
                column_item->column_name_.length(), column_item->column_name_.ptr());
          else
            TRANS_LOG("Column '%ld' of type ObModifyTimeType can not be inserted",
                table_schema->get_modify_time_column_id());
        }
      }
      ObTableRpcScan *table_scan = NULL;
      if (OB_LIKELY(OB_SUCCESS == ret))
      {
        ObRpcScanHint hint;
        hint.read_method_ = ObSqlReadStrategy::USE_GET;
        hint.is_get_skip_empty_row_ = false;
        hint.only_frozen_version_data_ = true;
        CREATE_PHY_OPERRATOR(table_scan, ObTableRpcScan, inner_plan, err_stat);
        if (OB_UNLIKELY(OB_SUCCESS != ret))
        {
        }
        else if (OB_SUCCESS != (ret = table_scan->set_table(insert_stmt->get_table_id(), insert_stmt->get_table_id())))
        {
          TRANS_LOG("failed to set table id, err=%d", ret);
        }
        else if (OB_SUCCESS != (ret = table_scan->init(sql_context_, hint)))
        {
          TRANS_LOG("failed to init table scan, err=%d", ret);
        }
        else if (OB_SUCCESS != (ret = gen_phy_static_data_scan(logical_plan, inner_plan, err_stat,
                                                               insert_stmt, row_desc, row_desc_map,
                                                               insert_stmt->get_table_id(), *rowkey_info, *table_scan)))
        {
          TRANS_LOG("err=%d", ret);
        }
        else
        {
          table_scan->set_rowkey_cell_count(row_desc.get_rowkey_cell_count());
        }
      }
      ObValues *tmp_table = NULL;
      if (OB_LIKELY(OB_SUCCESS == ret))
      {
        CREATE_PHY_OPERRATOR(tmp_table, ObValues, inner_plan, err_stat);
        if (OB_UNLIKELY(OB_SUCCESS != ret))
        {
        }
        else if (OB_SUCCESS != (ret = tmp_table->set_child(0, *table_scan)))
        {
          TBSYS_LOG(WARN, "failed to set child, err=%d", ret);
        }
        else if (OB_SUCCESS != (ret = inner_plan->add_phy_query(tmp_table)))
        {
          TBSYS_LOG(WARN, "failed to add phy query, err=%d", ret);
        }
      }
      ObMemSSTableScan *static_data = NULL;
      if (OB_LIKELY(OB_SUCCESS == ret))
      {
        CREATE_PHY_OPERRATOR(static_data, ObMemSSTableScan, inner_plan, err_stat);
        if (OB_LIKELY(OB_SUCCESS == ret))
        {
          static_data->set_tmp_table(tmp_table);
        }
      }
      ObIncScan *inc_scan = NULL;
      if (OB_LIKELY(OB_SUCCESS == ret))
      {
        CREATE_PHY_OPERRATOR(inc_scan, ObIncScan, inner_plan, err_stat);
        if (OB_LIKELY(OB_SUCCESS == ret))
        {
          inc_scan->set_scan_type(ObIncScan::ST_MGET);
          inc_scan->set_write_lock_flag();
        }
      }
      ObMultipleGetMerge *fuse_op = NULL;
      if (OB_LIKELY(OB_SUCCESS == ret))
      {
        CREATE_PHY_OPERRATOR(fuse_op, ObMultipleGetMerge, inner_plan, err_stat);
        if (OB_UNLIKELY(OB_SUCCESS != ret))
        {
        }
        else if ((ret = fuse_op->set_child(0, *static_data)) != OB_SUCCESS)
        {
          TRANS_LOG("Set child of fuse_op operator failed, err=%d", ret);
        }
        else if ((ret = fuse_op->set_child(1, *inc_scan)) != OB_SUCCESS)
        {
          TRANS_LOG("Set child of fuse_op operator failed, err=%d", ret);
        }
        else
        {
          fuse_op->set_is_ups_row(false);
        }
      }
      ObInsertDBSemFilter *insert_sem = NULL;
      ObEmptyRowFilter * empty_row_filter = NULL;
      if (OB_LIKELY(OB_SUCCESS == ret))
      {
        CREATE_PHY_OPERRATOR(empty_row_filter, ObEmptyRowFilter, inner_plan, err_stat);
        if (OB_UNLIKELY(OB_SUCCESS != ret))
        {
        }
        else if ((ret = empty_row_filter->set_child(0, *fuse_op)) != OB_SUCCESS)
        {
          TRANS_LOG("Failed to set child");
        }
      }
      if (OB_LIKELY(OB_SUCCESS == ret))
      {
        CREATE_PHY_OPERRATOR(insert_sem, ObInsertDBSemFilter, inner_plan, err_stat);
        if (OB_UNLIKELY(OB_SUCCESS != ret))
        {
        }
        else if ((ret = insert_sem->set_child(0, *empty_row_filter)) != OB_SUCCESS)
        {
          TRANS_LOG("Failed to set child");
        }
        else if ((ret = insert_sem->get_values().set_row_desc(row_desc, row_desc_ext)) != OB_SUCCESS)
        {
          TRANS_LOG("Set descriptor of value operator failed, err=%d", ret);
        }
        else if (OB_SUCCESS != (ret = gen_phy_values(logical_plan, inner_plan, err_stat, insert_stmt,
                                                     row_desc, row_desc_ext, &row_desc_map, insert_sem->get_values())))
        {
          TRANS_LOG("Failed to generate values, err=%d", ret);
        }
        else if (OB_SUCCESS != (ret = ups_modify->set_child(0, *insert_sem)))
        {
          TRANS_LOG("Set child of ups_modify operator failed, err=%d", ret);
        }
        else
        {
          inc_scan->set_values(&insert_sem->get_values(), true);
        }
      }
    }
    else
    {
      // @todo insert ... select ...
    }
  }

  return ret;
}

#if 0
int check_scan_get(const common::ObRpcScanHint &hint) {
//Added by Weiwei Jia
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  TBSYS_LOG(INFO, "999 enter func %s", __func__);
  ObSqlReadStrategy sql_read_strategy;

  
  int32_t read_method = ObSqlReadStrategy::USE_SCAN;
  ObArray<ObRowkey> rowkey_array;
  PageArena<ObObj,ModulePageAllocator> rowkey_objs_allocator(
      PageArena<ObObj, ModulePageAllocator>::DEFAULT_PAGE_SIZE,ModulePageAllocator(ObModIds::OB_SQL_TRANSFORMER));
  if (OB_SUCCESS != (ret = sql_read_strategy.get_read_method(rowkey_array, rowkey_objs_allocator, read_method))) {
    TBSYS_LOG(WARN, "999 fail to get read method:ret[%d]", ret);
  } else {
    TBSYS_LOG(INFO, "use [%s] method", read_method == ObSqlReadStrategy::USE_SCAN ? "SCAN" : "GET");
  }
  TBSYS_LOG(INFO, "999 enter func %s", __func__);
  hint.read_method_ = read_method;
  TBSYS_LOG(INFO, "999 hint.read_method_ is %d\n", read_method);
//End here
  return OB_SUCCESS;
}
#endif

int ObTransformer::gen_phy_table_for_update(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan*& physical_plan,
    ErrStat& err_stat,
    ObStmt *stmt,
    uint64_t table_id,
    const ObRowkeyInfo &rowkey_info,
    const ObRowDesc &row_desc,
    const ObRowDescExt &row_desc_ext,
    ObPhyOperator*& table_op)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  TableItem* table_item = NULL;
  ObTableRpcScan *table_rpc_scan_op = NULL;
  ObFilter *filter_op = NULL;
  ObIncScan *inc_scan_op = NULL;
  ObMultipleScanMerge *fuse_op = NULL; //Added by Weiwei Jia; ObMultipleGetMerge->ObMultipleScanMerge
  ObMemSSTableScan *static_data = NULL;
  ObValues *tmp_table = NULL;
  ObRowDesc rowkey_col_map;
  ObExprValues* get_param_values = NULL;
  ObObj rowkey_objs[OB_MAX_ROWKEY_COLUMN_NUMBER]; // used for constructing GetParam
  ModuleArena rowkey_alloc(OB_MAX_VARCHAR_LENGTH, ModulePageAllocator(ObModIds::OB_SQL_TRANSFORMER));
  ObCellInfo cell_info;
  cell_info.table_id_ = table_id;
  cell_info.row_key_.assign(rowkey_objs, rowkey_info.get_size());

  bool has_other_cond = false;
  ObRpcScanHint hint;
//Added by Weiwei Jia
//  hint.read_method_ = ObSqlReadStrategy::USE_GET;
  ObSqlReadStrategy sql_read_strategy;
  hint.only_frozen_version_data_ = true;
  hint.is_get_skip_empty_row_ = false;
#if 0
//Added by Weiwei Jia
  ObSqlReadStrategy sql_read_strategy;

  int32_t read_method = ObSqlReadStrategy::USE_SCAN;
  ObArray<ObRowkey> rowkey_array;
  TBSYS_LOG(INFO, "999 enter func %s", __func__);
  PageArena<ObObj,ModulePageAllocator> rowkey_objs_allocator(
      PageArena<ObObj, ModulePageAllocator>::DEFAULT_PAGE_SIZE,ModulePageAllocator(ObModIds::OB_SQL_TRANSFORMER));
  if (OB_SUCCESS != (ret = sql_read_strategy.get_read_method(rowkey_array, rowkey_objs_allocator, read_method))) {
    TBSYS_LOG(WARN, "999 fail to get read method:ret[%d]", ret);
  } else {
    TBSYS_LOG(INFO, "use [%s] method", read_method == ObSqlReadStrategy::USE_SCAN ? "SCAN" : "GET");
  }
  TBSYS_LOG(INFO, "999 enter func %s", __func__);
  hint.read_method_ = read_method;
  TBSYS_LOG(INFO, "999 hint.read_method_ is %d\n", read_method);
//End here
#endif //end if
  hint.only_frozen_version_data_ = true;
  hint.is_get_skip_empty_row_ = false;

  if (table_id == OB_INVALID_ID
      || (table_item = stmt->get_table_item_by_id(table_id)) == NULL
      || TableItem::BASE_TABLE != table_item->type_)
  {
    ret = OB_ERR_ILLEGAL_ID;
    TRANS_LOG("Wrong table id, tid=%lu", table_id);
  }
  else if (NULL == CREATE_PHY_OPERRATOR(table_rpc_scan_op, ObTableRpcScan, physical_plan, err_stat))
  {
    ret = OB_ALLOCATE_MEMORY_FAILED;
  }
  else if ((ret = table_rpc_scan_op->set_table(table_item->table_id_, table_item->ref_id_)) != OB_SUCCESS)
  {
    TRANS_LOG("ObTableRpcScan set table failed");
  } else { //added by Weiwei Jia, check get/scan protocol for delete statement
#if 1
     ObBitSet<> table_bitset;
    if (OB_SUCCESS == ret) {
      int32_t bit_index = stmt->get_table_bit_index(table_item->table_id_);
      table_bitset.add_member(bit_index);

      const ObTableSchema *table_schema = NULL;
      if (NULL == (table_schema = sql_context_->schema_manager_->get_table_schema(table_item->ref_id_))) {
        ret = OB_ERROR;
        TRANS_LOG("Fail to get table schema for table[%ld]", table_item->ref_id_);
      } else {
        sql_read_strategy.set_rowkey_info(table_schema->get_rowkey_info());
      }
     
    int32_t num = stmt->get_condition_size();
    for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++) {
      ObSqlRawExpr *cnd_expr = logical_plan->get_expr(stmt->get_condition_id(i));
      if (cnd_expr && table_bitset.is_superset(cnd_expr->get_tables_set())) {
        cnd_expr->set_applied(true);
        ObSqlExpression filter;
        if ((ret = cnd_expr->fill_sql_expression(filter, this, logical_plan, physical_plan)) != OB_SUCCESS) {
          TRANS_LOG("Add table filter condition faild");
          break;
        }
        else if (OB_SUCCESS != (ret = sql_read_strategy.add_filter(filter))) {
          TBSYS_LOG(WARN, "fail to add filter:ret[%d]", ret);
        }
      }
    }
        //Added by Weiwei Jia
    TBSYS_LOG(INFO, "999 enter func %s", __func__);
  
    int32_t read_method = ObSqlReadStrategy::USE_GET;
    ObArray<ObRowkey> rowkey_array;
    PageArena<ObObj,ModulePageAllocator> rowkey_objs_allocator(
        PageArena<ObObj, ModulePageAllocator>::DEFAULT_PAGE_SIZE,ModulePageAllocator(ObModIds::OB_SQL_TRANSFORMER));
    if (OB_SUCCESS != (ret = sql_read_strategy.get_read_method(rowkey_array, rowkey_objs_allocator, read_method))) {
      TBSYS_LOG(WARN, "999 fail to get read method:ret[%d]", ret);
    } else {
      TBSYS_LOG(INFO, "use [%s] method", read_method == ObSqlReadStrategy::USE_SCAN ? "SCAN" : "GET");
    }
    TBSYS_LOG(INFO, "999 enter func %s", __func__);
    hint.read_method_ = read_method;
    //hint.read_method_ = ObSqlReadStrategy::USE_GET;
    TBSYS_LOG(INFO, "999 hint.read_method_ is %d\n", read_method);
    //End here
#endif //end if
    }
  }
//End added by Weiwei Jia
//  else if (OB_SUCCESS != (ret = table_rpc_scan_op->init(sql_context_, hint)))
  if (OB_SUCCESS != (ret = table_rpc_scan_op->init(sql_context_, hint))) {
    TRANS_LOG("ObTableRpcScan init failed");
  }
  else if (NULL == CREATE_PHY_OPERRATOR(tmp_table, ObValues, physical_plan, err_stat))
  {
  }
  else if (OB_SUCCESS != (ret = tmp_table->set_child(0, *table_rpc_scan_op)))
  {
    TBSYS_LOG(WARN, "failed to set child op, err=%d", ret);
  }
  else if (OB_SUCCESS != (ret = physical_plan->add_phy_query(tmp_table)))
  {
    TBSYS_LOG(WARN, "failed to add sub query, err=%d", ret);
  }
  else if (NULL == CREATE_PHY_OPERRATOR(filter_op, ObFilter, physical_plan, err_stat))
  {
  }
  else if (NULL == CREATE_PHY_OPERRATOR(inc_scan_op, ObIncScan, physical_plan, err_stat))
  {
  } //Added by Weiwei Jia; ObMultipleGetMerge->ObMultipleScanMerge
  else if (NULL == CREATE_PHY_OPERRATOR(fuse_op, ObMultipleScanMerge, physical_plan, err_stat))
  {
  }
  else if (NULL == CREATE_PHY_OPERRATOR(static_data, ObMemSSTableScan, physical_plan, err_stat))
  {
  }
  else if (OB_SUCCESS != (ret = fuse_op->set_child(0, *static_data)))
  {
  }
  else if (OB_SUCCESS != (ret = fuse_op->set_child(1, *inc_scan_op)))
  {
  }
  else if (NULL == CREATE_PHY_OPERRATOR(get_param_values, ObExprValues, physical_plan, err_stat))
  {
    ret = OB_ALLOCATE_MEMORY_FAILED;
  }
  else if (OB_SUCCESS != (ret = physical_plan->add_phy_query(get_param_values)))
  {
    TBSYS_LOG(WARN, "failed to add sub query, err=%d", ret);
  }
  else
  {
    fuse_op->set_is_ups_row(false);

    inc_scan_op->set_scan_type(ObIncScan::ST_SCAN); //added by Weiwei Jia; ST_MGET->ST_SCAN
    inc_scan_op->set_write_lock_flag();
#if 1 //added by Weiwei Jia
    ObScanParam *scan_param = NULL;
    scan_param = OB_NEW(ObScanParam, ObModIds::OB_SCAN_PARAM);
    if (NULL == scan_param) {
      TBSYS_LOG(WARN, "no memory");
      ret = OB_ALLOCATE_MEMORY_FAILED;
    }
    ObNewRange range;
    ObVersionRange vrange;
    bool found;
    if (OB_SUCCESS != (ret = sql_read_strategy.find_scan_range(range, found, false))) {
      TBSYS_LOG(WARN, "failed to find_scan_range, err=%d", ret);
    }
/*
    const ObTableSchema *table_schema = NULL;
    if (NULL == (table_schema = sql_context_->schema_manager_->get_table_schema(table_item->ref_id_))) {
      ret = OB_ERROR;
      TRANS_LOG("Fail to get table schema for table[%ld]", table_item->ref_id_);
    } else {
      sql_read_strategy.set_rowkey_info(table_schema->get_rowkey_info());
    }
    const char *table_name = table_schema->get_table_name();
*/
    if (OB_SUCCESS != (ret = scan_param->set(table_id, cell_info.table_name_, range))) {
      TBSYS_LOG(WARN, "failed to set_table_id, err=%d", ret);
    }
    scan_param->set_range(range);
    inc_scan_op->set_scan_param(scan_param);
#endif //end added by Weiwei Jia
    //inc_scan_op->set_values(get_param_values, false);

    static_data->set_tmp_table(tmp_table);

    table_rpc_scan_op->set_rowkey_cell_count(row_desc.get_rowkey_cell_count());

    get_param_values->set_row_desc(row_desc, row_desc_ext);
    // set filters
    int32_t num = stmt->get_condition_size();
    uint64_t cid = OB_INVALID_ID;
    int64_t cond_op = T_INVALID;
    ObObj cond_val;
    int64_t rowkey_idx = OB_INVALID_INDEX;
    ObRowkeyColumn rowkey_col;
    for (int32_t i = 0; i < num; i++)
    {
      ObSqlRawExpr *cnd_expr = logical_plan->get_expr(stmt->get_condition_id(i));
      OB_ASSERT(cnd_expr);
      cnd_expr->set_applied(true);
      ObSqlExpression *filter = ObSqlExpression::alloc();
      if (NULL == filter)
      {
        TRANS_LOG("no memory");
        ret = OB_ALLOCATE_MEMORY_FAILED;
        break;
      }
      else if (OB_SUCCESS != (ret = cnd_expr->fill_sql_expression(*filter, this, logical_plan, physical_plan)))
      {
        ObSqlExpression::free(filter);
        TRANS_LOG("Failed to fill expression, err=%d", ret);
        break;
      }
      else if (filter->is_simple_condition(false, cid, cond_op, cond_val)
               && (T_OP_EQ == cond_op || T_OP_IS == cond_op)
               && rowkey_info.is_rowkey_column(cid))
      {
        if (OB_SUCCESS != (ret = table_rpc_scan_op->add_filter(filter)))
        {
          ObSqlExpression::free(filter);
          TRANS_LOG("Failed to add filter, err=%d", ret);
          break;
        }
        else if (OB_SUCCESS != (ret = rowkey_col_map.add_column_desc(OB_INVALID_ID, cid)))
        {
          ObSqlExpression::free(filter);
          TRANS_LOG("Failed to add column desc, err=%d", ret);
          break;
        }
        else if (OB_SUCCESS != (ret = rowkey_info.get_index(cid, rowkey_idx, rowkey_col)))
        {
          ObSqlExpression::free(filter);
          TRANS_LOG("Unexpected branch");
          ret = OB_ERR_UNEXPECTED;
          break;
        }
        else if (OB_SUCCESS != (ret = ob_write_obj(rowkey_alloc, cond_val, rowkey_objs[rowkey_idx]))) // deep copy
        {
          ObSqlExpression::free(filter);
          TRANS_LOG("failed to copy cell, err=%d", ret);
        }
        else
        {
          TBSYS_LOG(DEBUG, "rowkey obj, i=%ld val=%s", rowkey_idx, to_cstring(cond_val));
        }
      }
      else
      {
        // other condition
        has_other_cond = true;
        if (OB_SUCCESS != (ret = filter_op->add_filter(filter)))
        {
          TRANS_LOG("Failed to add filter, err=%d", ret);
          break;
        }
      }
    } // end for
    if (OB_LIKELY(OB_SUCCESS == ret))
    {
      int64_t rowkey_col_num = rowkey_info.get_size();
      uint64_t cid = OB_INVALID_ID;
      for (int64_t i = 0; i < rowkey_col_num; ++i)
      {
        if (OB_SUCCESS != (ret = rowkey_info.get_column_id(i, cid)))
        {
          TRANS_LOG("Failed to get column id, err=%d", ret);
          break;
        }
#if 0 //Added by Weiwei Jia, for delete statement
        else if (OB_INVALID_INDEX == rowkey_col_map.get_idx(OB_INVALID_ID, cid))
        {
          TRANS_LOG("Primary key column %lu not specified in the WHERE clause", cid);
          ret = OB_ERR_LACK_OF_ROWKEY_COL;
          break;
        }
#endif //End added by Weiwei Jia
      } // end for
    }
  }
  if (OB_LIKELY(OB_SUCCESS == ret))
  {
    // add output columns
    int32_t num = stmt->get_column_size();
    for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
    {
      const ColumnItem *col_item = stmt->get_column_item(i);
      if (col_item && col_item->table_id_ == table_item->table_id_)
      {
        ObBinaryRefRawExpr col_expr(col_item->table_id_, col_item->column_id_, T_REF_COLUMN);
        ObSqlRawExpr col_raw_expr(
          common::OB_INVALID_ID,
          col_item->table_id_,
          col_item->column_id_,
          &col_expr);
        ObSqlExpression output_expr;
        if ((ret = col_raw_expr.fill_sql_expression(
               output_expr,
               this,
               logical_plan,
               physical_plan)) != OB_SUCCESS
            || (ret = table_rpc_scan_op->add_output_column(output_expr)) != OB_SUCCESS)
        {
          TRANS_LOG("Add table output columns faild");
          break;
        }
        // for IncScan
        ObConstRawExpr col_expr2;
        if (i < rowkey_info.get_size()) // rowkey column
        {
          if (ObExtendType == rowkey_objs[i].get_type())
          {
            // convert address to index
            // @FIXME TERRIBLE BAD CODE here
            int64_t param_addr = 0;
            int64_t param_idx = -1;
            rowkey_objs[i].get_ext(param_addr);
            if (OB_SUCCESS != (ret = sql_context_->session_info_->get_current_result_set()->get_param_idx(param_addr, param_idx)))
            {
              TBSYS_LOG(ERROR, "failed to get param idx, err=%d addr=0x%lx", ret, param_addr);
              ret = OB_ERR_UNEXPECTED;
              break;
            }
            else
            {
              rowkey_objs[i].set_ext(param_idx);
              TBSYS_LOG(DEBUG, "convert param addr to idx, addr=%ld idx=%ld", param_addr, param_idx);
            }
          }
          if (OB_SUCCESS != (ret = col_expr2.set_value_and_type(rowkey_objs[i])))
          {
            TBSYS_LOG(WARN, "failed to set value, err=%d", ret);
            break;
          }
        }
        else
        {
          ObObj null_obj;
          col_expr2.set_value_and_type(null_obj);
        }
        ObSqlRawExpr col_raw_expr2(
          common::OB_INVALID_ID,
          col_item->table_id_,
          col_item->column_id_,
          &col_expr2);
        ObSqlExpression output_expr2;
        if ((ret = col_raw_expr2.fill_sql_expression(
               output_expr2,
               this,
               logical_plan,
               physical_plan)) != OB_SUCCESS)
        {
          TRANS_LOG("Add table output columns failed");
          break;
        }
        else if (OB_SUCCESS != (ret = get_param_values->add_value(output_expr2)))
        {
          TRANS_LOG("Failed to add cell into get param, err=%d", ret);
          break;
        }
      }
    } // end for
  }
  // add action flag column
  if (OB_LIKELY(OB_SUCCESS == ret))
  {
    ObSqlExpression column_ref;
    column_ref.set_tid_cid(OB_INVALID_ID, OB_ACTION_FLAG_COLUMN_ID);
    if (OB_SUCCESS != (ret = ObSqlExpressionUtil::make_column_expr(OB_INVALID_ID, OB_ACTION_FLAG_COLUMN_ID, column_ref)))
    {
      TBSYS_LOG(WARN, "fail to make column expr:ret[%d]", ret);
    }
    else if (OB_SUCCESS != (ret = table_rpc_scan_op->add_output_column(column_ref)))
    {
      TBSYS_LOG(WARN, "failed to add output column, err=%d", ret);
    }
  }

  if (ret == OB_SUCCESS)
  {
    if (has_other_cond)
    {
      if (OB_SUCCESS != (ret = filter_op->set_child(0, *fuse_op)))
      {
        TRANS_LOG("Failed to set child, err=%d", ret);
      }
      else
      {
        table_op = filter_op;
      }
    }
    else
    {
      table_op = fuse_op;
    }
  }
  return ret;
}

int ObTransformer::cons_row_desc(const uint64_t table_id,
                                 const ObStmt *stmt,
                                 ObRowDescExt &row_desc_ext,
                                 ObRowDesc &row_desc,
                                 const ObRowkeyInfo *&rowkey_info,
                                 ObSEArray<int64_t, 64> &row_desc_map,
                                 ErrStat& err_stat)
{
  OB_ASSERT(sql_context_);
  OB_ASSERT(sql_context_->schema_manager_);
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  const ObTableSchema *table_schema = NULL;
  if (NULL == (table_schema = sql_context_->schema_manager_->get_table_schema(table_id)))
  {
    ret = OB_ERR_ILLEGAL_ID;
    TRANS_LOG("fail to get table schema for table[%ld]", table_id);
  }
  else
  {
    rowkey_info = &table_schema->get_rowkey_info();
    int64_t rowkey_col_num = rowkey_info->get_size();
    row_desc.set_rowkey_cell_count(rowkey_col_num);

    int32_t column_num = stmt->get_column_size();
    const ColumnItem* column_item = NULL;
    row_desc_map.clear();
    row_desc_map.reserve(column_num);
    ObObj data_type;
    // construct rowkey columns first
    for (int64_t i = 0; OB_SUCCESS == ret && i < rowkey_col_num; ++i) // for each primary key
    {
      const ObRowkeyColumn *rowkey_column = rowkey_info->get_column(i);
      OB_ASSERT(rowkey_column);
      // find it's index in the input columns
      for (int32_t j = 0; ret == OB_SUCCESS && j < column_num; ++j)
      {
        column_item = stmt->get_column_item(j);
        OB_ASSERT(column_item);
        OB_ASSERT(table_id == column_item->table_id_);
        if (rowkey_column->column_id_ == column_item->column_id_)
        {
          if (OB_SUCCESS != (ret = row_desc_map.push_back(j)))
          {
            TRANS_LOG("failed to add index map, err=%d", ret);
          }
          else if (OB_SUCCESS != (ret = row_desc.add_column_desc(column_item->table_id_,
                                                                 column_item->column_id_)))
          {
            TRANS_LOG("failed to add row desc, err=%d", ret);
          }
          else
          {
            data_type.set_type(rowkey_column->type_);
            if (OB_SUCCESS != (ret = row_desc_ext.add_column_desc(column_item->table_id_,
                                                                  column_item->column_id_, data_type)))
            {
              TRANS_LOG("failed to add row desc, err=%d", ret);
            }
          }
          break;
        }
      } // end for
    }   // end for
    // then construct other columns
    const ObColumnSchemaV2* column_schema = NULL;
    for (int32_t i = 0; ret == OB_SUCCESS && i < column_num; ++i)
    {
      column_item = stmt->get_column_item(i);
      OB_ASSERT(column_item);
      OB_ASSERT(table_id == column_item->table_id_);
      if (!rowkey_info->is_rowkey_column(column_item->column_id_))
      {
        if (NULL == (column_schema = sql_context_->schema_manager_->get_column_schema(
                       column_item->table_id_, column_item->column_id_)))
        {
          ret = OB_ERR_COLUMN_NOT_FOUND;
          TRANS_LOG("Get column item failed");
          break;
        }
        else if (OB_SUCCESS != (ret = row_desc_map.push_back(i)))
        {
          TRANS_LOG("failed to add index map, err=%d", ret);
        }
        else if (OB_SUCCESS != (ret = row_desc.add_column_desc(column_item->table_id_,
                                                               column_item->column_id_)))
        {
          TRANS_LOG("failed to add row desc, err=%d", ret);
        }
        else
        {
          data_type.set_type(column_schema->get_type());
          if (OB_SUCCESS != (ret = row_desc_ext.add_column_desc(column_item->table_id_,
                                                                column_item->column_id_, data_type)))
          {
            TRANS_LOG("failed to add row desc, err=%d", ret);
          }
        }
      } // end if not rowkey column
    }   // end for
    if (OB_LIKELY(OB_SUCCESS == ret))
    {
      TBSYS_LOG(DEBUG, "row_desc=%s map_count=%ld", to_cstring(row_desc), row_desc_map.count());
    }
  }
  return ret;
}

int ObTransformer::gen_physical_update_new(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan*& physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    int32_t* index)
{
  int &ret = err_stat.err_code_ = OB_SUCCESS;
  ObUpdateStmt *update_stmt = NULL;
  ObUpsModify *ups_modify = NULL;
  ObProject *project_op = NULL;
  uint64_t table_id = OB_INVALID_ID;
  const ObRowkeyInfo *rowkey_info = NULL;
  ObRowDesc row_desc;
  ObRowDescExt row_desc_ext;
  ObSEArray<int64_t, 64> row_desc_map;
  ObPhysicalPlan* inner_plan = NULL;
  if (OB_SUCCESS != (ret = wrap_ups_executor(physical_plan, query_id, inner_plan, index, err_stat)))
  {
    TBSYS_LOG(WARN, "err=%d", ret);
  }
  else if (OB_SUCCESS != (ret = get_stmt(logical_plan, err_stat, query_id, update_stmt)))
  {
  }
  /* generate root operator */
  else if (NULL == CREATE_PHY_OPERRATOR(ups_modify, ObUpsModify, inner_plan, err_stat))
  {
    ret = OB_ALLOCATE_MEMORY_FAILED;
    TRANS_LOG("Failed to create phy operator");
  }
  else if (OB_SUCCESS != (ret = inner_plan->add_phy_query(ups_modify, NULL, true)))
  {
    TRANS_LOG("Add ups_modify operator failed");
  }
  else if (NULL == CREATE_PHY_OPERRATOR(project_op, ObProject, inner_plan, err_stat))
  {
    ret = OB_ALLOCATE_MEMORY_FAILED;
    TRANS_LOG("Failed to create phy operator");
  }
  else if (OB_SUCCESS != (ret = ups_modify->set_child(0, *project_op)))
  {
    TRANS_LOG("Failed to add child, err=%d", ret);
  }
  else if (OB_SUCCESS != (ret = cons_row_desc(update_stmt->get_update_table_id(), update_stmt,
                                              row_desc_ext, row_desc, rowkey_info, row_desc_map, err_stat)))
  {
  }
  else
  {
    table_id = update_stmt->get_update_table_id();
  }
  ObSqlExpression expr;
  // fill rowkey columns into the Project op
  if (OB_LIKELY(OB_SUCCESS == ret))
  {
    uint64_t tid = OB_INVALID_ID;
    uint64_t cid = OB_INVALID_ID;
    for (int64_t i = 0; i < row_desc.get_rowkey_cell_count(); ++i)
    {
      if (OB_SUCCESS != (ret = row_desc.get_tid_cid(i, tid, cid)))
      {
        TRANS_LOG("Failed to get tid cid");
        break;
      }
      else
      {
        ObBinaryRefRawExpr col_raw_ref(tid, cid, T_REF_COLUMN);
        expr.reset();
        expr.set_tid_cid(tid, cid);
        ObSqlRawExpr col_ref(0, tid, cid, &col_raw_ref);
        if (OB_SUCCESS != (ret = col_ref.fill_sql_expression(expr, this, logical_plan, inner_plan)))
        {
          TRANS_LOG("Failed to fill expression, err=%d", ret);
          break;
        }
        else if (OB_SUCCESS != (ret = project_op->add_output_column(expr)))
        {
          TRANS_LOG("Failed to add output column");
          break;
        }
      }
    }
  }
  /* check and fill set column=expr pairs */
  if (OB_LIKELY(OB_SUCCESS == ret))
  {
    ObSqlRawExpr *raw_expr = NULL;
    uint64_t column_id = OB_INVALID_ID;
    uint64_t expr_id = OB_INVALID_ID;
    const ObColumnSchemaV2* column_schema = NULL;

    for (int64_t column_idx = 0; column_idx < update_stmt->get_update_column_count(); column_idx++)
    {
      expr.reset();
      // valid check
      // 1. rowkey can't be updated
      // 2. joined column can't be updated
      if (OB_SUCCESS != (ret = update_stmt->get_update_column_id(column_idx, column_id)))
      {
        TRANS_LOG("fail to get update column id for table %lu column_idx=%lu", table_id, column_idx);
        break;
      }
      else if (NULL == (column_schema = sql_context_->schema_manager_->get_column_schema(table_id, column_id)))
      {
        ret = OB_ERR_COLUMN_NOT_FOUND;
        TRANS_LOG("Get column item failed");
        break;
      }
      else if (true == column_schema->is_join_column())
      {
        ret = OB_ERR_UPDATE_JOIN_COLUMN;
        TRANS_LOG("join column '%s' can not be updated", column_schema->get_name());
        break;
      }
      else if (rowkey_info->is_rowkey_column(column_id))
      {
        ret = OB_ERR_UPDATE_ROWKEY_COLUMN;
        TRANS_LOG("rowkey column '%s' can not be updated", column_schema->get_name());
        break;
      }
      else if (column_schema->get_type() == ObCreateTimeType || column_schema->get_type() == ObModifyTimeType)
      {
        ret = OB_ERR_CREAT_MODIFY_TIME_COLUMN;
        TRANS_LOG("Column '%s' of type ObCreateTimeType/ObModifyTimeType can not be updated", column_schema->get_name());
        break;
      }
      // get expression
      else if (OB_SUCCESS != (ret = update_stmt->get_update_expr_id(column_idx, expr_id)))
      {
        TBSYS_LOG(WARN, "fail to get update expr for table %lu column %lu. column_idx=%ld", table_id, column_id, column_idx);
        break;
      }
      else if (NULL == (raw_expr = logical_plan->get_expr(expr_id)))
      {
        TBSYS_LOG(WARN, "fail to get expr from logical plan for table %lu column %lu. column_idx=%ld", table_id, column_id, column_idx);
        ret = OB_ERR_UNEXPECTED;
        break;
      }
      else if (OB_SUCCESS != (ret = raw_expr->fill_sql_expression(expr, this, logical_plan, inner_plan)))
      {
        TBSYS_LOG(WARN, "fail to fill sql expression. ret=%d", ret);
        break;
      }
      else
      {
        expr.set_tid_cid(table_id, column_id);
        // add <column_id, expression> to project operator
        if (OB_SUCCESS != (ret = project_op->add_output_column(expr)))
        {
          TRANS_LOG("fail to add update expr to update operator");
          break;
        }
      }
    } // end for
  }
  if (OB_LIKELY(OB_SUCCESS == ret))
  {
    ObPhyOperator* table_op = NULL;
    if (OB_SUCCESS != (ret = gen_phy_table_for_update(logical_plan, inner_plan, err_stat,
                                                      update_stmt, table_id, *rowkey_info,
                                                      row_desc, row_desc_ext, table_op)))
    {
    }
    else if (OB_SUCCESS != (ret = project_op->set_child(0, *table_op)))
    {
      TRANS_LOG("Failed to set child, err=%d", ret);
    }
  }
  return ret;
}

int ObTransformer::gen_physical_delete_new(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan* physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    int32_t* index)
{
  int &ret = err_stat.err_code_ = OB_SUCCESS;
  OB_ASSERT(logical_plan);
  OB_ASSERT(physical_plan);
  ObDeleteStmt *delete_stmt = NULL;
  ObUpsModify *ups_modify = NULL;
  ObProject *project_op = NULL;
  uint64_t table_id = OB_INVALID_ID;
  const ObRowkeyInfo *rowkey_info = NULL;
  ObRowDesc row_desc;
  ObRowDescExt row_desc_ext;
  ObSEArray<int64_t, 64> row_desc_map;
  ObPhysicalPlan* inner_plan = NULL;
  if (OB_SUCCESS != (ret = wrap_ups_executor(physical_plan, query_id, inner_plan, index, err_stat)))
  {
    TBSYS_LOG(WARN, "err=%d", ret);
  }
  else if (OB_SUCCESS != (ret = get_stmt(logical_plan, err_stat, query_id, delete_stmt)))
  {
  }
  /* generate root operator */
  else if (NULL == CREATE_PHY_OPERRATOR(ups_modify, ObUpsModify, inner_plan, err_stat))
  {
    ret = OB_ALLOCATE_MEMORY_FAILED;
    TRANS_LOG("Failed to create phy operator");
  }
  else if (OB_SUCCESS != (ret = inner_plan->add_phy_query(ups_modify, NULL, true)))
  {
    TRANS_LOG("Add ups_modify operator failed");
  }
  else if (NULL == CREATE_PHY_OPERRATOR(project_op, ObProject, inner_plan, err_stat))
  {
    ret = OB_ALLOCATE_MEMORY_FAILED;
    TRANS_LOG("Failed to create phy operator");
  }
  else if (OB_SUCCESS != (ret = ups_modify->set_child(0, *project_op)))
  {
    TRANS_LOG("Failed to add child, err=%d", ret);
  }
  else if (OB_SUCCESS != (ret = cons_row_desc(delete_stmt->get_delete_table_id(), delete_stmt,
                                              row_desc_ext, row_desc, rowkey_info, row_desc_map, err_stat)))
  {
  }
  else
  {
    table_id = delete_stmt->get_delete_table_id();
  }
  ObSqlExpression expr;
  // fill rowkey columns into the Project op
  if (OB_LIKELY(OB_SUCCESS == ret))
  {
    uint64_t tid = OB_INVALID_ID;
    uint64_t cid = OB_INVALID_ID;
    for (int64_t i = 0; i < row_desc.get_rowkey_cell_count(); ++i)
    {
      if (OB_SUCCESS != (ret = row_desc.get_tid_cid(i, tid, cid)))
      {
        TRANS_LOG("Failed to get tid cid");
        break;
      }
      else
      {
        ObBinaryRefRawExpr col_raw_ref(tid, cid, T_REF_COLUMN);
        expr.reset();
        ObSqlRawExpr col_ref(OB_INVALID_ID, tid, cid, &col_raw_ref);
        if (OB_SUCCESS != (ret = col_ref.fill_sql_expression(expr, this, logical_plan, inner_plan)))
        {
          TRANS_LOG("Failed to fill expression, err=%d", ret);
          break;
        }
        else if (OB_SUCCESS != (ret = project_op->add_output_column(expr)))
        {
          TRANS_LOG("Failed to add output column");
          break;
        }
      }
    }
    // add ObActionFlag::OB_DEL_ROW cell
    if (OB_LIKELY(OB_SUCCESS == ret))
    {
      ObObj del_row;
      del_row.set_int(ObActionFlag::OP_DEL_ROW);
      ObConstRawExpr const_expr(del_row, T_INT);
      expr.reset();
      ObSqlRawExpr const_del(OB_INVALID_ID, table_id, OB_ACTION_FLAG_COLUMN_ID, &const_expr);
      if (OB_SUCCESS != (ret = const_del.fill_sql_expression(expr, this, logical_plan, inner_plan)))
      {
        TRANS_LOG("Failed to fill expression, err=%d", ret);
      }
      else if (OB_SUCCESS != (ret = project_op->add_output_column(expr)))
      {
        TRANS_LOG("Failed to add output column");
      }
    }
  }
//Added by Weiwei Jia
#if 0
  ObPhyOperator *result_op = NULL;
  if (ret == OB_SUCCESS) {
    ret = gen_phy_limit(logical_plan, physical_plan, err_stat, delete_stmt, result_op, result_op);
  }
#endif
//End added by Weiwei Jia
  if (OB_LIKELY(OB_SUCCESS == ret))
  {
    ObPhyOperator* table_op = NULL;
    if (OB_SUCCESS != (ret = gen_phy_table_for_update(logical_plan, inner_plan, err_stat,
                                                      delete_stmt, table_id, *rowkey_info,
                                                      row_desc, row_desc_ext, table_op)))
    {
    }
    else if (OB_SUCCESS != (ret = project_op->set_child(0, *table_op)))
    {
      TRANS_LOG("Failed to set child, err=%d", ret);
    }
  }
  return ret;
}

int ObTransformer::gen_physical_start_trans(
  ObLogicalPlan *logical_plan,
  ObPhysicalPlan* physical_plan,
  ErrStat& err_stat,
  const uint64_t& query_id,
  int32_t* index)
{
  int &ret = err_stat.err_code_ = OB_SUCCESS;
  OB_ASSERT(logical_plan);
  OB_ASSERT(physical_plan);
  ObStartTransStmt *stmt = NULL;
  ObStartTrans *start_trans = NULL;
  if (OB_SUCCESS != (ret = get_stmt(logical_plan, err_stat, query_id, stmt)))
  {
  }
  /* generate root operator */
  else if (NULL == CREATE_PHY_OPERRATOR(start_trans, ObStartTrans, physical_plan, err_stat))
  {
    ret = OB_ALLOCATE_MEMORY_FAILED;
    TRANS_LOG("Failed to create phy operator");
  }
  else if (OB_SUCCESS != (ret = add_phy_query(logical_plan, physical_plan, err_stat,
                                              query_id, stmt, start_trans, index)))
  {
    TRANS_LOG("Add ups_modify operator failed");
  }
  else
  {
    start_trans->set_rpc_stub(sql_context_->merger_rpc_proxy_);
    start_trans->set_trans_param(stmt->get_with_consistent_snapshot()?READ_ONLY_TRANS:READ_WRITE_TRANS);
  }
  return ret;
}

int ObTransformer::gen_physical_priv_stmt(
  ObLogicalPlan *logical_plan,
  ObPhysicalPlan* physical_plan,
  ErrStat& err_stat,
  const uint64_t& query_id,
  int32_t* index)
{
  int &ret = err_stat.err_code_ = OB_SUCCESS;
  OB_ASSERT(logical_plan);
  OB_ASSERT(physical_plan);
  ObBasicStmt * stmt = NULL;
  ObPrivExecutor *priv_executor = NULL;
  if (OB_SUCCESS != (ret = get_stmt(logical_plan, err_stat, query_id, stmt)))
  {
  }
  /* generate root operator */
  else if (NULL == CREATE_PHY_OPERRATOR(priv_executor, ObPrivExecutor, physical_plan, err_stat))
  {
    ret = OB_ALLOCATE_MEMORY_FAILED;
    TRANS_LOG("Failed to create phy operator");
  }
  else if (OB_SUCCESS != (ret = add_phy_query(logical_plan, physical_plan, err_stat,
                                              query_id, stmt, priv_executor, index)))
  {
    TRANS_LOG("Add create user operator failed");
  }
  else
  {
    ObBasicStmt * basic_stmt = NULL;
    // 这块内存是从transform mem pool中分配出来的
    if (stmt->get_stmt_type() == ObBasicStmt::T_CREATE_USER)
    {
      void *ptr = trans_malloc(sizeof(ObCreateUserStmt));
      if (ptr == NULL)
      {
        ret = OB_ALLOCATE_MEMORY_FAILED;
        TBSYS_LOG(ERROR, "malloc ObCreateUserStmt in transform mem pool failed, ret=%d", ret);
      }
      else
      {
        basic_stmt = new (ptr) ObCreateUserStmt(*(dynamic_cast<ObCreateUserStmt*>(stmt)));
      }
    }
    else if (stmt->get_stmt_type() == ObBasicStmt::T_DROP_USER)
    {
      void *ptr = trans_malloc(sizeof(ObDropUserStmt));
      if (ptr == NULL)
      {
        ret = OB_ALLOCATE_MEMORY_FAILED;
        TBSYS_LOG(ERROR, "malloc ObDropUserStmt in transform mem pool failed, ret=%d", ret);
      }
      else
      {
        basic_stmt = new (ptr) ObDropUserStmt(*(dynamic_cast<ObDropUserStmt*>(stmt)));
      }
    }
    else if (stmt->get_stmt_type() == ObBasicStmt::T_GRANT)
    {
      void *ptr = trans_malloc(sizeof(ObGrantStmt));
      if (ptr == NULL)
      {
        ret = OB_ALLOCATE_MEMORY_FAILED;
        TBSYS_LOG(ERROR, "malloc ObGrantStmt in transform mem pool failed, ret=%d", ret);
      }
      else
      {
        basic_stmt = new (ptr) ObGrantStmt(*(dynamic_cast<ObGrantStmt*>(stmt)));
      }
    }
    else if (stmt->get_stmt_type() == ObBasicStmt::T_REVOKE)
    {
      void *ptr = trans_malloc(sizeof(ObRevokeStmt));
      if (ptr == NULL)
      {
        ret = OB_ALLOCATE_MEMORY_FAILED;
        TBSYS_LOG(ERROR, "malloc ObRevokeStmt in transform mem pool failed, ret=%d", ret);
      }
      else
      {
        basic_stmt = new (ptr) ObRevokeStmt(*(dynamic_cast<ObRevokeStmt*>(stmt)));
      }
    }
    else if (stmt->get_stmt_type() == ObBasicStmt::T_RENAME_USER)
    {
      void *ptr = trans_malloc(sizeof(ObRenameUserStmt));
      if (ptr == NULL)
      {
        ret = OB_ALLOCATE_MEMORY_FAILED;
        TBSYS_LOG(ERROR, "malloc ObRenameUserStmt in transform mem pool failed, ret=%d", ret);
      }
      else
      {
        basic_stmt = new (ptr) ObRenameUserStmt(*(dynamic_cast<ObRenameUserStmt*>(stmt)));
      }
    }
    else if (stmt->get_stmt_type() == ObBasicStmt::T_SET_PASSWORD)
    {
      void *ptr = trans_malloc(sizeof(ObSetPasswordStmt));
      if (ptr == NULL)
      {
        ret = OB_ALLOCATE_MEMORY_FAILED;
        TBSYS_LOG(ERROR, "malloc ObSetPasswordStmt in transform mem pool failed, ret=%d", ret);
      }
      else
      {
        basic_stmt = new (ptr) ObSetPasswordStmt(*(dynamic_cast<ObSetPasswordStmt*>(stmt)));
      }
    }
    else if (stmt->get_stmt_type() == ObBasicStmt::T_LOCK_USER)
    {
      void *ptr = trans_malloc(sizeof(ObLockUserStmt));
      if (ptr == NULL)
      {
        ret = OB_ALLOCATE_MEMORY_FAILED;
        TBSYS_LOG(ERROR, "malloc ObGrantStmt in transform mem pool failed, ret=%d", ret);
      }
      else
      {
        basic_stmt = new (ptr) ObLockUserStmt(*(dynamic_cast<ObLockUserStmt*>(stmt)));
      }
    }
    priv_executor->set_stmt(basic_stmt);
    priv_executor->set_context(sql_context_);
  }
  return ret;
}
int ObTransformer::gen_physical_end_trans(
  ObLogicalPlan *logical_plan,
  ObPhysicalPlan* physical_plan,
  ErrStat& err_stat,
  const uint64_t& query_id,
  int32_t* index)
{
  int &ret = err_stat.err_code_ = OB_SUCCESS;
  OB_ASSERT(logical_plan);
  OB_ASSERT(physical_plan);
  ObEndTransStmt *stmt = NULL;
  ObEndTrans *end_trans = NULL;
  if (OB_SUCCESS != (ret = get_stmt(logical_plan, err_stat, query_id, stmt)))
  {
  }
  /* generate root operator */
  else if (NULL == CREATE_PHY_OPERRATOR(end_trans, ObEndTrans, physical_plan, err_stat))
  {
    ret = OB_ALLOCATE_MEMORY_FAILED;
    TRANS_LOG("Failed to create phy operator");
  }
  else if (OB_SUCCESS != (ret = add_phy_query(logical_plan, physical_plan, err_stat,
                                              query_id, stmt, end_trans, index)))
  {
    TRANS_LOG("Add ups_modify operator failed");
  }
  else
  {
    end_trans->set_rpc_stub(sql_context_->merger_rpc_proxy_);
    end_trans->set_trans_param(sql_context_->session_info_->get_trans_id(), stmt->get_is_rollback());
  }
  return ret;
}

int ObTransformer::gen_phy_select_for_update(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    int32_t* index)
{
  int &ret = err_stat.err_code_ = OB_SUCCESS;
  TBSYS_LOG(DEBUG, "999 enter func %s\n", __func__);
  ObSelectStmt *select_stmt = NULL;
  ObPhyOperator *result_op = NULL;
  //ObLockFilter *lock_op = NULL;
  ObProject *project_op = NULL;
  uint64_t table_id = OB_INVALID_ID;
  const ObRowkeyInfo *rowkey_info = NULL;
  ObPhysicalPlan *inner_plan = NULL;
  ObRowDesc row_desc;
  ObRowDescExt row_desc_ext;
  ObSEArray<int64_t, 64> row_desc_map;
  if ((ret = get_stmt(logical_plan, err_stat, query_id, select_stmt)) != OB_SUCCESS)
  {
  }
  else if (!select_stmt->is_for_update()
    || select_stmt->get_from_item_size() != 1
    || select_stmt->get_table_size() != 1
    || !(select_stmt->get_table_item(0).type_ == TableItem::BASE_TABLE
    || select_stmt->get_table_item(0).type_ == TableItem::ALIAS_TABLE)
    || select_stmt->get_group_expr_size() > 0
    || select_stmt->get_agg_fun_size() > 0)
  {
    TRANS_LOG("This select statement is not allowed by implement");
  }
  else if ((ret = wrap_ups_executor(physical_plan, query_id, inner_plan, index, err_stat)) != OB_SUCCESS)
  {
    TBSYS_LOG(WARN, "err=%d", ret);
  }
  /*
  else if (CREATE_PHY_OPERRATOR(lock_op, ObLockFilter, physical_plan, err_stat) == NULL)
  {
    ret = OB_ALLOCATE_MEMORY_FAILED;
    TRANS_LOG("Failed to ObLockFilter operator");
  }
  */
  else if (CREATE_PHY_OPERRATOR(project_op, ObProject, physical_plan, err_stat) == NULL)
  {
    ret = OB_ALLOCATE_MEMORY_FAILED;
    TRANS_LOG("Failed to create phy operator");
  }
  else if ((ret = inner_plan->add_phy_query(project_op, NULL, true)) != OB_SUCCESS)
  {
    TRANS_LOG("Add top operator failed");
  }
  else if ((ret = cons_row_desc(select_stmt->get_table_item(0).table_id_, select_stmt,
                                row_desc_ext, row_desc, rowkey_info, row_desc_map, err_stat))
      != OB_SUCCESS)
  {
  }
  else
  {
    table_id = select_stmt->get_table_item(0).table_id_;
    //lock_op->set_write_lock_flag();
  }
  // add output columns
  for (int32_t i = 0; ret == OB_SUCCESS && i < select_stmt->get_select_item_size(); i++)
  {
    const SelectItem& select_item = select_stmt->get_select_item(i);
    ObSqlExpression output_expr;
    ObSqlRawExpr *expr = NULL;
    if ((expr = logical_plan->get_expr(select_item.expr_id_)) == NULL)
    {
      ret = OB_ERR_ILLEGAL_ID;
      TRANS_LOG("Wrong expression id");
    }
    else if ((ret = expr->fill_sql_expression(
                              output_expr,
                              this,
                              logical_plan,
                              physical_plan)) != OB_SUCCESS)
    {
      TRANS_LOG("Generate post-expression faild");
    }
    else if ((ret = project_op->add_output_column(output_expr)) != OB_SUCCESS)
    {
      TRANS_LOG("Add output column to project operator faild");
    }
  }
  if (OB_LIKELY(OB_SUCCESS == ret))
  {
    if ((ret = gen_phy_table_for_update(logical_plan, inner_plan, err_stat,
                                        select_stmt, table_id, *rowkey_info, row_desc, row_desc_ext, result_op)
         ) != OB_SUCCESS)
    {
    }
    /*
    else if ((ret = lock_op->set_child(0, *result_op)) != OB_SUCCESS)
    {
      TRANS_LOG("Failed to set child, err=%d", ret);
    }
    else
    {
      result_op = lock_op;
    }
    */
  }
  // generate physical plan for order by
  if (ret == OB_SUCCESS && select_stmt->get_order_item_size() > 0)
    ret = gen_phy_order_by(logical_plan, physical_plan, err_stat, select_stmt, result_op, result_op);
  // generate physical plan for limit
  if (ret == OB_SUCCESS && select_stmt->has_limit())
  {
    ret = gen_phy_limit(logical_plan, physical_plan, err_stat, select_stmt, result_op, result_op);
  }
  if (ret == OB_SUCCESS && (ret = project_op->set_child(0, *result_op)) != OB_SUCCESS)
  {
    TRANS_LOG("Failed to add child, err=%d", ret);
  }
  return ret;
}

int ObTransformer::gen_physical_alter_system(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    const uint64_t& query_id,
    int32_t* index)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObAlterSysCnfStmt *alt_sys_stmt = NULL;
  ObAlterSysCnf     *alt_sys_op = NULL;

  /* get statement */
  if ((get_stmt(logical_plan, err_stat, query_id, alt_sys_stmt)) != OB_SUCCESS)
  {
  }
  /* generate operator */
  else if (CREATE_PHY_OPERRATOR(alt_sys_op, ObAlterSysCnf, physical_plan, err_stat) == NULL)
  {
  }
  else if ((ret = add_phy_query(logical_plan,
                                physical_plan,
                                err_stat,
                                query_id,
                                alt_sys_stmt,
                                alt_sys_op, index)
                                ) != OB_SUCCESS)
  {
    TRANS_LOG("Add physical operator failed, err=%d", ret);
  }
  else
  {
    alt_sys_op->set_sql_context(*sql_context_);
    hash::ObHashMap<ObSysCnfItemKey, ObSysCnfItem>::iterator iter;
    for (iter = alt_sys_stmt->sys_cnf_begin(); iter != alt_sys_stmt->sys_cnf_end(); iter++)
    {
      ObSysCnfItem cnf_item = iter->second;
      if ((ret = ob_write_string(*mem_pool_,
                                 iter->second.param_name_,
                                 cnf_item.param_name_)) != OB_SUCCESS)
      {
        TRANS_LOG("Failed to copy param name, err=%d", ret);
        break;
      }
      else if ((ret = ob_write_obj(*mem_pool_,
                                   iter->second.param_value_,
                                   cnf_item.param_value_)) != OB_SUCCESS)
      {
        TRANS_LOG("Failed to copy param value, err=%d", ret);
        break;
      }
      else if ((ret = ob_write_string(*mem_pool_,
                                      iter->second.comment_,
                                      cnf_item.comment_)) != OB_SUCCESS)
      {
        TRANS_LOG("Failed to copy comment, err=%d", ret);
        break;
      }
      else if ((ret = ob_write_string(*mem_pool_,
                                      iter->second.server_ip_,
                                      cnf_item.server_ip_)) != OB_SUCCESS)
      {
        TRANS_LOG("Failed to copy server ip, err=%d", ret);
        break;
      }
      else if ((ret = alt_sys_op->add_sys_cnf_item(cnf_item)) != OB_SUCCESS)
      {
        TRANS_LOG("Failed to add config item, err=%d", ret);
        break;
      }
    }
  }
  return ret;
}

int ObTransformer::gen_phy_show_parameters(
    ObLogicalPlan *logical_plan,
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObShowStmt *show_stmt,
    ObPhyOperator *&out_op)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObTableRpcScan *table_op = NULL;
  ObProject *project_op = NULL;
  ObRpcScanHint hint;
  hint.read_method_ = ObSqlReadStrategy::USE_SCAN;
  if (CREATE_PHY_OPERRATOR(table_op, ObTableRpcScan, physical_plan, err_stat) == NULL)
  {
  }
  else if (CREATE_PHY_OPERRATOR(project_op, ObProject, physical_plan, err_stat) == NULL)
  {
  }
  else if ((ret = project_op->set_child(0, *table_op)) != OB_SUCCESS)
  {
    TRANS_LOG("Set child of project failed, ret=%d", ret);
  }
  else if ((ret = table_op->set_table(
                                OB_ALL_SYS_CONFIG_STAT_TID,
                                OB_ALL_SYS_CONFIG_STAT_TID)
                                ) != OB_SUCCESS)
  {
    TRANS_LOG("ObTableRpcScan set table faild, table id = %lu", OB_ALL_SYS_CONFIG_STAT_TID);
  }
  else if ((ret = table_op->init(sql_context_, hint)) != OB_SUCCESS)
  {
    TRANS_LOG("ObTableRpcScan init faild");
  }
  else
  {
    ObString cnf_name = ObString::make_string(OB_ALL_SYS_CONFIG_STAT_TABLE_NAME);
    ObString ip_name = ObString::make_string("server_ip");
    ObString port_name = ObString::make_string("server_port");
    ObString type_name = ObString::make_string("server_type");
    for (int32_t i = 0; i < show_stmt->get_column_size(); i++)
    {
      const ColumnItem* column_item = show_stmt->get_column_item(i);
      ObString cname;
      if (column_item->column_name_ == ip_name)
      {
        cname = ObString::make_string("svr_ip");
      }
      else if (column_item->column_name_ == port_name)
      {
        cname = ObString::make_string("svr_port");
      }
      else if (column_item->column_name_ == type_name)
      {
        cname = ObString::make_string("svr_type");
      }
      else
      {
        cname = column_item->column_name_;
      }
      const ObColumnSchemaV2* column_schema = NULL;
      if ((column_schema = sql_context_->schema_manager_->get_column_schema(
                                cnf_name,
                                cname
                                )) == NULL)
      {
        ret = OB_ERR_COLUMN_UNKNOWN;
        TRANS_LOG("Can not get relative column %.*s from %s",
            column_item->column_name_.length(), column_item->column_name_.ptr(),
            OB_ALL_SYS_CONFIG_STAT_TABLE_NAME);
        break;
      }
      else
      {
        // add table scan columns
        ObBinaryRefRawExpr col_expr(OB_ALL_SYS_CONFIG_STAT_TID, column_schema->get_id(), T_REF_COLUMN);
        ObSqlRawExpr col_raw_expr(
            common::OB_INVALID_ID,
            OB_ALL_SYS_CONFIG_STAT_TID,
            column_schema->get_id(),
            &col_expr);
        ObSqlExpression output_expr;
        if ((ret = col_raw_expr.fill_sql_expression(
                                    output_expr,
                                    this,
                                    logical_plan,
                                    physical_plan)) != OB_SUCCESS
          || (ret = table_op->add_output_column(output_expr)) != OB_SUCCESS)
        {
          TRANS_LOG("Add table output columns faild");
          break;
        }

        // add project columns
        col_raw_expr.set_table_id(column_item->table_id_);
        col_raw_expr.set_column_id(column_item->column_id_);
        output_expr.reset();
        if ((ret = col_raw_expr.fill_sql_expression(
                                    output_expr,
                                    this,
                                    logical_plan,
                                    physical_plan)) != OB_SUCCESS
          || (ret = project_op->add_output_column(output_expr)) != OB_SUCCESS)
        {
          TRANS_LOG("Add project output columns faild");
          break;
        }
      }
    } // end for
  }
  if (ret == OB_SUCCESS)
  {
    out_op = project_op;
  }
  return ret;
}

int ObTransformer::gen_phy_show_create_table(
    ObPhysicalPlan *physical_plan,
    ErrStat& err_stat,
    ObShowStmt *show_stmt,
    ObPhyOperator *&out_op)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  ObRowDesc row_desc;
  ObValues *values_op = NULL;

  int32_t num = show_stmt->get_column_size();
  if (OB_UNLIKELY(num != 2))
  {
    ret = OB_ERR_COLUMN_SIZE;
    TRANS_LOG("wrong columns' number of %s", OB_CREATE_TABLE_SHOW_TABLE_NAME);
  }
  else if (CREATE_PHY_OPERRATOR(values_op, ObValues, physical_plan, err_stat) == NULL)
  {
  }
  else
  {
    for (int32_t i = 0; ret == OB_SUCCESS && i < num; i++)
    {
      const ColumnItem* column_item = show_stmt->get_column_item(i);
      if ((ret = row_desc.add_column_desc(column_item->table_id_, column_item->column_id_)) != OB_SUCCESS)
      {
        TRANS_LOG("Add row desc error, err=%d", ret);
        break;
      }
    }
    if ((ret = values_op->set_row_desc(row_desc)) != OB_SUCCESS)
    {
      TRANS_LOG("Set row desc error, err=%d", ret);
    }
  }

  const ObTableSchema *table_schema = NULL;
  if (ret != OB_SUCCESS)
  {
  }
  else if ((table_schema = sql_context_->schema_manager_->get_table_schema(
                                                               show_stmt->get_show_table_id()
                                                               )) == NULL)
  {
    ret = OB_ERR_TABLE_UNKNOWN;
    TRANS_LOG("Unknow table id = %lu, err=%d", show_stmt->get_show_table_id(), ret);
  }
  else
  {
    uint64_t table_id = OB_INVALID_ID;
    uint64_t column_id = OB_INVALID_ID;
    ObRow val_row;
    val_row.set_row_desc(row_desc);
    int64_t pos = 0;
    char buf[OB_MAX_VARCHAR_LENGTH];

    // add table_name
    int32_t name_len = static_cast<int32_t>(strlen(table_schema->get_table_name()));
    ObString name_val(name_len, name_len, table_schema->get_table_name());
    ObObj name;
    name.set_varchar(name_val);
    if ((ret = row_desc.get_tid_cid(0, table_id, column_id)) != OB_SUCCESS)
    {
      TRANS_LOG("Get table_name desc failed");
    }
    else if ((ret = val_row.set_cell(table_id, column_id, name)) != OB_SUCCESS)
    {
      TRANS_LOG("Add table_name to ObRow failed, ret=%d", ret);
    }
    // add table definition
    else if ((ret = row_desc.get_tid_cid(1, table_id, column_id)) != OB_SUCCESS)
    {
      TRANS_LOG("Get table definition desc failed");
    }
    else if ((ret = cons_table_definition(
                         *table_schema,
                         buf,
                         OB_MAX_VARCHAR_LENGTH,
                         pos,
                         err_stat)) != OB_SUCCESS)
    {
      TRANS_LOG("Generate table definition failed");
    }
    else
    {
      ObString value_str(static_cast<int32_t>(pos), static_cast<int32_t>(pos), buf);
      ObObj value;
      value.set_varchar(value_str);
      if ((ret = val_row.set_cell(table_id, column_id, value)) != OB_SUCCESS)
      {
        TRANS_LOG("Add table_definiton to ObRow failed, ret=%d", ret);
      }
    }
    // add final value row
    if (ret == OB_SUCCESS && (ret = values_op->add_values(val_row)) != OB_SUCCESS)
    {
      TRANS_LOG("Add value row failed");
    }
  }
  if (ret == OB_SUCCESS)
  {
    out_op = values_op;
  }
  return ret;
}

int ObTransformer::cons_table_definition(
    const ObTableSchema& table_schema,
    char* buf,
    const int64_t& buf_len,
    int64_t& pos,
    ErrStat& err_stat)
{
  int& ret = err_stat.err_code_ = OB_SUCCESS;
  const ObColumnSchemaV2* columns = NULL;
  int32_t column_size = 0;
  if ((columns = sql_context_->schema_manager_->get_table_schema(
                                                     table_schema.get_table_id(),
                                                     column_size)) == NULL
      || column_size <= 0)
  {
    ret = OB_ERR_TABLE_UNKNOWN;
    TRANS_LOG("Unknow table id = %lu, err=%d", table_schema.get_table_id(), ret);
  }
  else
  {
    databuff_printf(buf, buf_len, pos, "CREATE TABLE %s (\n",
                    table_schema.get_table_name());
  }

  // add columns
  for (int32_t i = 0; ret == OB_SUCCESS && i < column_size; i++)
  {
    if (i == 0)
    {
      databuff_printf(buf, buf_len, pos, "%s %s\n",
                      columns[i].get_name(), ObObj::get_sql_type(columns[i].get_type()));
    }
    else
    {
      databuff_printf(buf, buf_len, pos, ", %s %s\n",
                      columns[i].get_name(), ObObj::get_sql_type(columns[i].get_type()));
    }
  }

  // add rowkeys
  const ObRowkeyInfo& rowkey_info = table_schema.get_rowkey_info();
  databuff_printf(buf, buf_len, pos, ", PRIMARY KEY(");
  for (int64_t j = 0; ret == OB_SUCCESS && j < rowkey_info.get_size(); j++)
  {
    const ObColumnSchemaV2* col = NULL;
    if ((col = sql_context_->schema_manager_->get_column_schema(
                                                   table_schema.get_table_id(),
                                                   rowkey_info.get_column(j)->column_id_
                                                   )) == NULL)
    {
      ret = OB_ERR_COLUMN_UNKNOWN;
      TRANS_LOG("Get column %lu failed", rowkey_info.get_column(j)->column_id_);
      break;
    }
    else if (j != rowkey_info.get_size() - 1)
    {
      databuff_printf(buf, buf_len, pos, "%s, ", col->get_name());
    }
    else
    {
      databuff_printf(buf, buf_len, pos, "%s)\n", col->get_name());
    }
  }

  // add table options
  if (ret == OB_SUCCESS)
  {
    databuff_printf(buf, buf_len, pos, ") ");
    if (table_schema.get_max_sstable_size() >= 0)
    {
      databuff_printf(buf, buf_len, pos, "TABLET_MAX_SIZE = %ld, ",
                      table_schema.get_max_sstable_size());
    }
    if (table_schema.get_block_size() >= 0)
    {
      databuff_printf(buf, buf_len, pos, "TABLET_BLOCK_SIZE = %d, ",
                      table_schema.get_block_size());
    }
    if (*table_schema.get_expire_condition() != '\0')
    {
      databuff_printf(buf, buf_len, pos, "EXPIRE_INFO = '%s', ",
                      table_schema.get_expire_condition());
    }
    if (!table_schema.is_merge_dynamic_data())
    {
      databuff_printf(buf, buf_len, pos, "CONSISTENT_MODE = STATIC, ");
    }
    databuff_printf(buf, buf_len, pos,
                    // "REPLICA_NUM = %ld, "
                    "USE_BLOOM_FILTER = %s",
                    // table_schema.get_replica_num(),
                    table_schema.is_use_bloomfilter() ? "TRUE" : "FALSE");
  }
  return ret;
}
