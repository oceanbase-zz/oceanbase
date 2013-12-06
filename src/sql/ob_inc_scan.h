/**
 * (C) 2010-2012 Alibaba Group Holding Limited.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * version 2 as published by the Free Software Foundation.
 *
 * Version: $Id$
 *
 * ob_inc_scan.h
 *
 * Authors:
 *   Li Kai <yubai.lk@alipay.com>
 *
 */
#ifndef _OB_INC_SCAN_H
#define _OB_INC_SCAN_H 1

#include "ob_no_children_phy_operator.h"
#include "ob_husk_phy_operator.h"
#include "ob_phy_operator_type.h"
#include "ob_expr_values.h"
#include "ob_sql_session_info.h"
#include "common/ob_scan_param.h"
#include "common/ob_get_param.h"
#include "common/ob_range.h"
#include "common/ob_resource_pool.h"
#include "common/utility.h"

namespace oceanbase
{
  using namespace common;

  namespace sql
  {
    const int64_t DEFAULT_INC_GET_PARAM_NUM = 256;
    const int64_t DEFAULT_INC_SCAN_PARAM_NUM = 256;
    typedef ObResourcePool<ObGetParam, 0, DEFAULT_INC_GET_PARAM_NUM> ObGetParamPool;
    typedef ObResourcePool<ObScanParam, 0, DEFAULT_INC_SCAN_PARAM_NUM> ObScanParamPool;
    // 用于在ups端执行 读取指定版本的增量数据
    class ObIncScan: public ObNoChildrenPhyOperator
    {
      public:
        enum ScanType
        {
          ST_NONE = 0,
          ST_MGET = 1,
          ST_SCAN = 2,
          ST_END = 3,
        };
        static const char* st_repr(const ScanType type)
        {
          static const char* repr[] = {"None", "MGET", "SCAN", "UNKNOWN"};
          return repr[(type >= 0 && type < ST_END)? type: ST_END];
        }
      public:
        ObIncScan();
        virtual ~ObIncScan();
      public:
        // implement virtual function
        enum ObPhyOperatorType get_type() const
        {
          return PHY_INC_SCAN;
        }
        int open()
        {
          return OB_NOT_SUPPORTED;
        }

        int close()
        {
          return OB_NOT_SUPPORTED;
        }

        int get_next_row(const common::ObRow *&row)
        {
          UNUSED(row);
          return OB_NOT_SUPPORTED;
        }

        int get_row_desc(const common::ObRowDesc *&row_desc) const
        {
          UNUSED(row_desc);
          return OB_NOT_SUPPORTED;
        }

        int64_t to_string(char* buf, const int64_t buf_len) const
        {
          int64_t pos = 0;
          databuff_printf(buf, buf_len, pos, "IncScan(scan_type=%s[%d], lock=%x, ",
                          st_repr(scan_type_), scan_type_, lock_flag_);
          if (NULL != get_param_)
          {
            pos += get_param_->to_string(buf + pos, buf_len - pos);
          }
          else
          {
            databuff_printf(buf, buf_len, pos, "get_param=NULL ");
          }
          if (NULL != scan_param_)
          {
            //scan_param_->to_str(buf, buf_len, pos);
            databuff_printf(buf, buf_len, pos, "scan_param(NotImplement to_string() method)");
          }
          else
          {
            databuff_printf(buf, buf_len, pos, "scan_param=NULL");
          }
          databuff_printf(buf, buf_len, pos, ")\n");
          return pos;
        }
        void set_write_lock_flag() { lock_flag_ = (ObLockFlag)(lock_flag_ | LF_WRITE); }
        int serialize(char* buf, const int64_t buf_len, int64_t& pos) const;
        int deserialize(const char* buf, const int64_t data_len, int64_t& pos);
        int64_t get_serialize_size() const;
        void set_scan_type(const ScanType scan_type) { scan_type_ = scan_type; }
        void set_values(ObExprValues *values, bool with_only_rowkey) {values_ = values; cons_get_param_with_rowkey_ = with_only_rowkey;};
        void set_scan_param(ObScanParam *scan_param) {scan_param_ = scan_param;};
        common::ObGetParam* get_get_param();
        common::ObScanParam* get_scan_param();
      private:
        int create_get_param_from_values(common::ObGetParam* get_param);
      protected:
        ObLockFlag lock_flag_;
        ScanType scan_type_;
        ObGetParamPool::Guard get_param_guard_;
        ObScanParamPool::Guard scan_param_guard_;
        common::ObGetParam* get_param_;
        common::ObScanParam* scan_param_;
        ObExprValues *values_;
        bool cons_get_param_with_rowkey_;
    };
  } // end namespace sql
} // end namespace oceanbase

#endif /* _OB_INC_SCAN_H */
