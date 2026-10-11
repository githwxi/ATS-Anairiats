/***********************************************************************/
/*                                                                     */
/*                         Applied Type System                         */
/*                                                                     */
/***********************************************************************/

/* (*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-2012 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
** later version.
**
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
**
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*) */

/* ****** ****** */

/*
** Source:
** $PATSHOME/prelude/CATS/CODEGEN/mysql.atxt
** Time of generation: Sat Sep  1 15:33:21 2012
*/

/* ****** ****** */

/*
(* Author: Hongwei Xi *)
(* Authoremail: hwxi AT cs DOT bu DOT edu *)
(* Start time: May, 2012 *)
*/

/* ****** ****** */

#ifndef ATSHOME_CONTRIB_MYSQL_MYSQL_CATS
#define ATSHOME_CONTRIB_MYSQL_MYSQL_CATS

/* ****** ****** */

#include <mysql.h>

/* ****** ****** */

typedef MYSQL MYSQL_struct ;
typedef MYSQL_RES MYSQLRES_struct ;
typedef MYSQL_ROW MYSQLROW_struct ;
typedef MYSQL_FIELD MYSQLFIELD_struct ;

/* ****** ****** */

#define atsctrb_mysql_init_0() mysql_init(NULL)
#define atsctrb_mysql_init_1(conn) mysql_init(conn)

/* ****** ****** */

#define atsctrb_mysql_close mysql_close
#define atsctrb_mysql_real_connect mysql_real_connect
#define atsctrb_mysql_change_user mysql_change_user

/* ****** ****** */

#define atsctrb_mysql_ping mysql_ping
#define atsctrb_mysql_commit mysql_commit

/* ****** ****** */

#define atsctrb_mysql_query mysql_query
#define atsctrb_mysql_list_dbs mysql_list_dbs
#define atsctrb_mysql_list_fields mysql_list_fields

/* ****** ****** */

#define atsctrb_mysql_field_count mysql_field_count

/* ****** ****** */

#define atsctrb_mysql_num_rows mysql_num_rows
#define atsctrb_mysql_num_fields mysql_num_fields

/* ****** ****** */

#define atsctrb_mysql_field_tell mysql_field_tell
#define atsctrb_mysql_field_seek mysql_field_seek

/* ****** ****** */

#define atsctrb_mysql_affected_rows mysql_affected_rows

/* ****** ****** */

#define atsctrb_mysql_use_result mysql_use_result
#define atsctrb_mysql_store_result mysql_store_result

/* ****** ****** */

#define atsctrb_mysql_free_result mysql_free_result

/* ****** ****** */

#define atsctrb_mysql_data_seek mysql_data_seek

/* ****** ****** */

#define atsctrb_mysql_fetch_row mysql_fetch_row
#define atsctrb_mysql_fetch_lengths mysql_fetch_lengths

/* ****** ****** */

#define atsctrb_mysql_fetch_field mysql_fetch_field
#define atsctrb_mysql_fetch_field_direct mysql_fetch_field_direct
#define atsctrb_mysql_fetch_fields mysql_fetch_fields

/* ****** ****** */

ATSinline()
ats_ptr_type
atsctrb_mysqlrow_get_at
  (ats_ptr_type row, ats_int_type i) { return ((ats_ptr_type*)row)[i] ; }
// end of [atsctrb_mysqlrow_get_at]

ATSinline()
ats_ulint_type
atsctrb_mysqlrowlen_get_at
  (ats_ptr_type rowlen, ats_int_type i) { return ((ats_ulint_type*)rowlen)[i] ; }
// end of [atsctrb_mysqlrowlen_get_at]

/* ****** ****** */

ATSinline()
ats_ptr_type
atsctrb_mysqlfield_get_name
  (ats_ptr_type fld) { return ((MYSQLFIELD_struct*)fld)->name ; }
// end of [atsctrb_mysqlfield_get_name]

/* ****** ****** */

#define atsctrb_mysql_info(conn) ((char*)(mysql_info(conn)))
#define atsctrb_mysql_stat(conn) ((char*)(mysql_stat(conn)))
#define atsctrb_mysql_sqlstate(conn) ((char*)(mysql_sqlstate(conn)))

/* ****** ****** */

#define atsctrb_mysql_get_host_info(conn) ((char*)(mysql_get_host_info(conn)))
#define atsctrb_mysql_get_proto_info mysql_get_proto_info
#define atsctrb_mysql_get_client_info() ((char*)(mysql_get_client_info()))
#define atsctrb_mysql_get_client_version mysql_get_client_version
#define atsctrb_mysql_get_server_info(conn) ((char*)(mysql_get_server_info(conn)))
#define atsctrb_mysql_get_server_version mysql_get_server_version

/* ****** ****** */

#define atsctrb_mysql_errno mysql_errno
#define atsctrb_mysql_error(x) ((char*)(mysql_error(x)))

/* ****** ****** */

#define atsctrb_mysql_hex_string mysql_hex_string
#define atsctrb_mysql_escape_string mysql_escape_string
#define atsctrb_mysql_real_escape_string mysql_real_escape_string

/* ****** ****** */

#define atsctrb_mysql_warning_count mysql_warning_count

/* ****** ****** */

#endif // ifndef ATSHOME_CONTRIB_MYSQL_MYSQL_CATS

/* ****** ****** */

/* end of [mysql.cats] */
