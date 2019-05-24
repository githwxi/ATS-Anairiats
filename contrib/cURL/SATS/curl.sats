(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2009-2010 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
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
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: June, 2010
//
(* ****** ****** *)

%{#
#include "contrib/cURL/CATS/curl.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staloading at run-time

(* ****** ****** *)

absviewtype CURLptr (l:addr) // CURL*
viewtypedef CURLptr0 = [l:addr] CURLptr l
viewtypedef CURLptr1 = [l:addr | l > null] CURLptr l

(* ****** ****** *)

castfn ptr_of_curlptr {l:addr} (x: !CURLptr l):<> ptr l
overload ptr_of with ptr_of_curlptr

castfn curlptr_free_null (x: CURLptr null):<> ptr null

fun curlptr_is_null {l:addr}
  (x: !CURLptr l):<> bool (l == null) = "mac#atspre_ptr_is_null"
// end of [curlptr_is_null]

fun curlptr_isnot_null {l:addr}
  (x: !CURLptr l):<> bool (l > null) = "mac#atspre_ptr_isnot_null"
// end of [curlptr_isnot_null]
  
(* ****** ****** *)

// #define CURL_READFUNC_ABORT 0x10000000
macdef CURL_READFUNC_ABORT = $extval (int, "CURL_READFUNC_ABORT")
// #define CURL_READFUNC_PAUSE 0x10000001
macdef CURL_READFUNC_PAUSE = $extval (int, "CURL_READFUNC_PAUSE")

(* ****** ****** *)

abst@ype curlsocktype = $extype"curlsocktype" // enum type
macdef CURLSOCKTYPE_IPCXN =
  $extval (curlsocktype, "CURLSOCKTYPE_IPCXN") // for a specific IP connection
macdef CURLSOCKTYPE_LAST =
  $extval (curlsocktype, "CURLSOCKTYPE_LAST") // HX: it should never be used

(* ****** ****** *)

abst@ype curlioerr = $extype"curlioerr" // enum type
macdef CURLIOE_OK = $extval (curlioerr, "CURLIOE_OK")
macdef CURLIOE_UNKNOWNCMD = $extval (curlioerr, "CURLIOE_UNKNOWNCMD")
macdef CURLIOE_FAILRESTART = $extval (curlioerr, "CURLIOE_FAILRESTART")
macdef CURLIOE_LAST = $extval (curlioerr, "CURLIOE_LAST")

abst@ype curliocmd = $extype"curliocmd" // enum type
macdef CURLIOCMD_NOP = $extval (curliocmd, "CURLIOCMD_NOP")
macdef CURLIOCMD_RESTARTREAD = $extval (curliocmd, "CURLIOCMD_RESTARTREAD")
macdef CURLIOCMD_LAST = $extval (curliocmd, "CURLIOCMD_LAST")

(* ****** ****** *)

absview CURLerr_v (i:int)
prfun curlerr_elim_null (pf: CURLerr_v 0):<> void

abst@ype CURLcode
  (i:int) = $extype"CURLcode" // enum type
typedef CURLcode = [i:int] CURLcode (i)
macdef CURLE_OK = $extval (CURLcode 0, "CURLE_OK")
macdef CURLE_UNSUPPORTED_PROTOCOL = $extval (CURLcode, "CURLE_UNSUPPORTED_PROTOCOL")
macdef CURLE_FAILED_INIT = $extval (CURLcode, "CURLE_FAILED_INIT")
macdef CURLE_URL_MALFORMAT = $extval (CURLcode, "CURLE_URL_MALFORMAT")
macdef CURLE_OBSOLETE4 = $extval (CURLcode, "CURLE_OBSOLETE4")
macdef CURLE_COULDNT_RESOLVE_PROXY = $extval (CURLcode, "CURLE_COULDNT_RESOLVE_PROXY")
macdef CURLE_COULDNT_RESOLVE_HOST = $extval (CURLcode, "CURLE_COULDNT_RESOLVE_HOST")
macdef CURLE_COULDNT_CONNECT = $extval (CURLcode, "CURLE_COULDNT_CONNECT")
macdef CURLE_FTP_WEIRD_SERVER_REPLY = $extval (CURLcode, "CURLE_FTP_WEIRD_SERVER_REPLY")
macdef CURLE_REMOTE_ACCESS_DENIED = $extval (CURLcode, "CURLE_REMOTE_ACCESS_DENIED")
macdef CURLE_OBSOLETE10 = $extval (CURLcode, "CURLE_OBSOLETE10")
macdef CURLE_FTP_WEIRD_PASS_REPLY = $extval (CURLcode, "CURLE_FTP_WEIRD_PASS_REPLY")
macdef CURLE_OBSOLETE12 = $extval (CURLcode, "CURLE_OBSOLETE12")
macdef CURLE_FTP_WEIRD_PASV_REPLY = $extval (CURLcode, "CURLE_FTP_WEIRD_PASV_REPLY")
macdef CURLE_FTP_WEIRD_227_FORMAT = $extval (CURLcode, "CURLE_FTP_WEIRD_227_FORMAT")
macdef CURLE_FTP_CANT_GET_HOST = $extval (CURLcode, "CURLE_FTP_CANT_GET_HOST")
macdef CURLE_OBSOLETE16 = $extval (CURLcode, "CURLE_OBSOLETE16")
macdef CURLE_FTP_COULDNT_SET_TYPE = $extval (CURLcode, "CURLE_FTP_COULDNT_SET_TYPE")
macdef CURLE_PARTIAL_FILE = $extval (CURLcode, "CURLE_PARTIAL_FILE")
macdef CURLE_FTP_COULDNT_RETR_FILE = $extval (CURLcode, "CURLE_FTP_COULDNT_RETR_FILE")
macdef CURLE_OBSOLETE20 = $extval (CURLcode, "CURLE_OBSOLETE20")
macdef CURLE_QUOTE_ERROR = $extval (CURLcode, "CURLE_QUOTE_ERROR")
macdef CURLE_HTTP_RETURNED_ERROR = $extval (CURLcode, "CURLE_HTTP_RETURNED_ERROR")
macdef CURLE_WRITE_ERROR = $extval (CURLcode, "CURLE_WRITE_ERROR")
macdef CURLE_OBSOLETE24 = $extval (CURLcode, "CURLE_OBSOLETE24")
macdef CURLE_UPLOAD_FAILED = $extval (CURLcode, "CURLE_UPLOAD_FAILED")
macdef CURLE_READ_ERROR = $extval (CURLcode, "CURLE_READ_ERROR")
macdef CURLE_OUT_OF_MEMORY = $extval (CURLcode, "CURLE_OUT_OF_MEMORY")
macdef CURLE_OPERATION_TIMEDOUT = $extval (CURLcode, "CURLE_OPERATION_TIMEDOUT")
macdef CURLE_OBSOLETE29 = $extval (CURLcode, "CURLE_OBSOLETE29")
macdef CURLE_FTP_PORT_FAILED = $extval (CURLcode, "CURLE_FTP_PORT_FAILED")
macdef CURLE_FTP_COULDNT_USE_REST = $extval (CURLcode, "CURLE_FTP_COULDNT_USE_REST")
macdef CURLE_OBSOLETE32 = $extval (CURLcode, "CURLE_OBSOLETE32")
macdef CURLE_RANGE_ERROR = $extval (CURLcode, "CURLE_RANGE_ERROR")
macdef CURLE_HTTP_POST_ERROR = $extval (CURLcode, "CURLE_HTTP_POST_ERROR")
macdef CURLE_SSL_CONNECT_ERROR = $extval (CURLcode, "CURLE_SSL_CONNECT_ERROR")
macdef CURLE_BAD_DOWNLOAD_RESUME = $extval (CURLcode, "CURLE_BAD_DOWNLOAD_RESUME")
macdef CURLE_FILE_COULDNT_READ_FILE = $extval (CURLcode, "CURLE_FILE_COULDNT_READ_FILE")
macdef CURLE_LDAP_CANNOT_BIND = $extval (CURLcode, "CURLE_LDAP_CANNOT_BIND")
macdef CURLE_LDAP_SEARCH_FAILED = $extval (CURLcode, "CURLE_LDAP_SEARCH_FAILED")
macdef CURLE_OBSOLETE40 = $extval (CURLcode, "CURLE_OBSOLETE40")
macdef CURLE_FUNCTION_NOT_FOUND = $extval (CURLcode, "CURLE_FUNCTION_NOT_FOUND")
macdef CURLE_ABORTED_BY_CALLBACK = $extval (CURLcode, "CURLE_ABORTED_BY_CALLBACK")
macdef CURLE_BAD_FUNCTION_ARGUMENT = $extval (CURLcode, "CURLE_BAD_FUNCTION_ARGUMENT")
macdef CURLE_OBSOLETE44 = $extval (CURLcode, "CURLE_OBSOLETE44")
macdef CURLE_INTERFACE_FAILED = $extval (CURLcode, "CURLE_INTERFACE_FAILED")
macdef CURLE_OBSOLETE46 = $extval (CURLcode, "CURLE_OBSOLETE46")
macdef CURLE_TOO_MANY_REDIRECTS  = $extval (CURLcode, "CURLE_TOO_MANY_REDIRECTS ")
macdef CURLE_UNKNOWN_TELNET_OPTION = $extval (CURLcode, "CURLE_UNKNOWN_TELNET_OPTION")
macdef CURLE_TELNET_OPTION_SYNTAX  = $extval (CURLcode, "CURLE_TELNET_OPTION_SYNTAX ")
macdef CURLE_OBSOLETE50 = $extval (CURLcode, "CURLE_OBSOLETE50")
macdef CURLE_PEER_FAILED_VERIFICATION = $extval (CURLcode, "CURLE_PEER_FAILED_VERIFICATION")
macdef CURLE_GOT_NOTHING = $extval (CURLcode, "CURLE_GOT_NOTHING")
macdef CURLE_SSL_ENGINE_NOTFOUND = $extval (CURLcode, "CURLE_SSL_ENGINE_NOTFOUND")
macdef CURLE_SSL_ENGINE_SETFAILED = $extval (CURLcode, "CURLE_SSL_ENGINE_SETFAILED")
macdef CURLE_SEND_ERROR = $extval (CURLcode, "CURLE_SEND_ERROR")
macdef CURLE_RECV_ERROR = $extval (CURLcode, "CURLE_RECV_ERROR")
macdef CURLE_OBSOLETE57 = $extval (CURLcode, "CURLE_OBSOLETE57")
macdef CURLE_SSL_CERTPROBLEM = $extval (CURLcode, "CURLE_SSL_CERTPROBLEM")
macdef CURLE_SSL_CIPHER = $extval (CURLcode, "CURLE_SSL_CIPHER")
macdef CURLE_SSL_CACERT = $extval (CURLcode, "CURLE_SSL_CACERT")
macdef CURLE_BAD_CONTENT_ENCODING = $extval (CURLcode, "CURLE_BAD_CONTENT_ENCODING")
macdef CURLE_LDAP_INVALID_URL = $extval (CURLcode, "CURLE_LDAP_INVALID_URL")
macdef CURLE_FILESIZE_EXCEEDED = $extval (CURLcode, "CURLE_FILESIZE_EXCEEDED")
macdef CURLE_USE_SSL_FAILED = $extval (CURLcode, "CURLE_USE_SSL_FAILED")
macdef CURLE_SEND_FAIL_REWIND = $extval (CURLcode, "CURLE_SEND_FAIL_REWIND")
macdef CURLE_SSL_ENGINE_INITFAILED = $extval (CURLcode, "CURLE_SSL_ENGINE_INITFAILED")
macdef CURLE_LOGIN_DENIED = $extval (CURLcode, "CURLE_LOGIN_DENIED")
macdef CURLE_TFTP_NOTFOUND = $extval (CURLcode, "CURLE_TFTP_NOTFOUND")
macdef CURLE_TFTP_PERM = $extval (CURLcode, "CURLE_TFTP_PERM")
macdef CURLE_REMOTE_DISK_FULL = $extval (CURLcode, "CURLE_REMOTE_DISK_FULL")
macdef CURLE_TFTP_ILLEGAL = $extval (CURLcode, "CURLE_TFTP_ILLEGAL")
macdef CURLE_TFTP_UNKNOWNID = $extval (CURLcode, "CURLE_TFTP_UNKNOWNID")
macdef CURLE_REMOTE_FILE_EXISTS = $extval (CURLcode, "CURLE_REMOTE_FILE_EXISTS")
macdef CURLE_TFTP_NOSUCHUSER = $extval (CURLcode, "CURLE_TFTP_NOSUCHUSER")
macdef CURLE_CONV_FAILED = $extval (CURLcode, "CURLE_CONV_FAILED")
macdef CURLE_CONV_REQD = $extval (CURLcode, "CURLE_CONV_REQD")
macdef CURLE_SSL_CACERT_BADFILE = $extval (CURLcode, "CURLE_SSL_CACERT_BADFILE")
macdef CURLE_REMOTE_FILE_NOT_FOUND = $extval (CURLcode, "CURLE_REMOTE_FILE_NOT_FOUND")
macdef CURLE_SSH = $extval (CURLcode, "CURLE_SSH")
macdef CURLE_SSL_SHUTDOWN_FAILED = $extval (CURLcode, "CURLE_SSL_SHUTDOWN_FAILED")
macdef CURLE_AGAIN = $extval (CURLcode, "CURLE_AGAIN")
macdef CURLE_SSL_CRL_BADFILE = $extval (CURLcode, "CURLE_SSL_CRL_BADFILE")
macdef CURLE_SSL_ISSUER_ERROR = $extval (CURLcode, "CURLE_SSL_ISSUER_ERROR")
macdef CURL_LAST = $extval (CURLcode, "CURL_LAST") // HX: it should never be used!

castfn int_of_CURLcode {i:int} (x: CURLcode i) :<> int i
fun eq_CURLcode_CURLcode {i,j:int}
  (x: CURLcode i, y: CURLcode j):<> bool (i==j) = "mac#atspre_eq_int_int"
overload = with eq_CURLcode_CURLcode
fun neq_CURLcode_CURLcode {i,j:int}
  (x: CURLcode i, y: CURLcode j):<> bool (i <> j) = "mac#atspre_neq_int_int"
overload <> with neq_CURLcode_CURLcode

(* ****** ****** *)

abst@ype CURLoption = $extype"CURLoption"
macdef CURLOPT_FILE = $extval (CURLoption, "CURLOPT_FILE")
macdef CURLOPT_URL = $extval (CURLoption, "CURLOPT_URL")
macdef CURLOPT_PORT = $extval (CURLoption, "CURLOPT_PORT")
macdef CURLOPT_PROXY = $extval (CURLoption, "CURLOPT_PROXY")
macdef CURLOPT_USERPWD = $extval (CURLoption, "CURLOPT_USERPWD")
macdef CURLOPT_PROXYUSERPWD = $extval (CURLoption, "CURLOPT_PROXYUSERPWD")
macdef CURLOPT_RANGE = $extval (CURLoption, "CURLOPT_RANGE")
macdef CURLOPT_INFILE = $extval (CURLoption, "CURLOPT_INFILE")
macdef CURLOPT_ERRORBUFFER = $extval (CURLoption, "CURLOPT_ERRORBUFFER")
macdef CURLOPT_WRITEFUNCTION = $extval (CURLoption, "CURLOPT_WRITEFUNCTION")
macdef CURLOPT_READFUNCTION = $extval (CURLoption, "CURLOPT_READFUNCTION")
macdef CURLOPT_TIMEOUT = $extval (CURLoption, "CURLOPT_TIMEOUT")
macdef CURLOPT_INFILESIZE = $extval (CURLoption, "CURLOPT_INFILESIZE")
macdef CURLOPT_POSTFIELDS = $extval (CURLoption, "CURLOPT_POSTFIELDS")
macdef CURLOPT_REFERER = $extval (CURLoption, "CURLOPT_REFERER")
macdef CURLOPT_FTPPORT = $extval (CURLoption, "CURLOPT_FTPPORT")
macdef CURLOPT_USERAGENT = $extval (CURLoption, "CURLOPT_USERAGENT")
macdef CURLOPT_LOW_SPEED_LIMIT = $extval (CURLoption, "CURLOPT_LOW_SPEED_LIMIT")
macdef CURLOPT_LOW_SPEED_TIME = $extval (CURLoption, "CURLOPT_LOW_SPEED_TIME")
macdef CURLOPT_RESUME_FROM = $extval (CURLoption, "CURLOPT_RESUME_FROM")
macdef CURLOPT_COOKIE = $extval (CURLoption, "CURLOPT_COOKIE")
macdef CURLOPT_HTTPHEADER = $extval (CURLoption, "CURLOPT_HTTPHEADER")
macdef CURLOPT_HTTPPOST = $extval (CURLoption, "CURLOPT_HTTPPOST")
macdef CURLOPT_SSLCERT = $extval (CURLoption, "CURLOPT_SSLCERT")
macdef CURLOPT_KEYPASSWD = $extval (CURLoption, "CURLOPT_KEYPASSWD")
macdef CURLOPT_CRLF = $extval (CURLoption, "CURLOPT_CRLF")
macdef CURLOPT_QUOTE = $extval (CURLoption, "CURLOPT_QUOTE")
macdef CURLOPT_WRITEHEADER = $extval (CURLoption, "CURLOPT_WRITEHEADER")
macdef CURLOPT_COOKIEFILE = $extval (CURLoption, "CURLOPT_COOKIEFILE")
macdef CURLOPT_SSLVERSION = $extval (CURLoption, "CURLOPT_SSLVERSION")
macdef CURLOPT_TIMECONDITION = $extval (CURLoption, "CURLOPT_TIMECONDITION")
macdef CURLOPT_TIMEVALUE = $extval (CURLoption, "CURLOPT_TIMEVALUE")
macdef CURLOPT_CUSTOMREQUEST = $extval (CURLoption, "CURLOPT_CUSTOMREQUEST")
macdef CURLOPT_STDERR = $extval (CURLoption, "CURLOPT_STDERR")
macdef CURLOPT_POSTQUOTE = $extval (CURLoption, "CURLOPT_POSTQUOTE")
macdef CURLOPT_WRITEINFO = $extval (CURLoption, "CURLOPT_WRITEINFO")
macdef CURLOPT_VERBOSE = $extval (CURLoption, "CURLOPT_VERBOSE")
macdef CURLOPT_HEADER = $extval (CURLoption, "CURLOPT_HEADER")
macdef CURLOPT_NOPROGRESS = $extval (CURLoption, "CURLOPT_NOPROGRESS")
macdef CURLOPT_NOBODY = $extval (CURLoption, "CURLOPT_NOBODY")
macdef CURLOPT_FAILONERROR = $extval (CURLoption, "CURLOPT_FAILONERROR")
macdef CURLOPT_UPLOAD = $extval (CURLoption, "CURLOPT_UPLOAD")
macdef CURLOPT_POST = $extval (CURLoption, "CURLOPT_POST")
macdef CURLOPT_DIRLISTONLY = $extval (CURLoption, "CURLOPT_DIRLISTONLY")
macdef CURLOPT_APPEND = $extval (CURLoption, "CURLOPT_APPEND")
macdef CURLOPT_NETRC = $extval (CURLoption, "CURLOPT_NETRC")
macdef CURLOPT_FOLLOWLOCATION = $extval (CURLoption, "CURLOPT_FOLLOWLOCATION")
macdef CURLOPT_TRANSFERTEXT = $extval (CURLoption, "CURLOPT_TRANSFERTEXT")
macdef CURLOPT_PUT = $extval (CURLoption, "CURLOPT_PUT")
macdef CURLOPT_PROGRESSFUNCTION = $extval (CURLoption, "CURLOPT_PROGRESSFUNCTION")
macdef CURLOPT_PROGRESSDATA = $extval (CURLoption, "CURLOPT_PROGRESSDATA")
macdef CURLOPT_AUTOREFERER = $extval (CURLoption, "CURLOPT_AUTOREFERER")
macdef CURLOPT_PROXYPORT = $extval (CURLoption, "CURLOPT_PROXYPORT")
macdef CURLOPT_POSTFIELDSIZE = $extval (CURLoption, "CURLOPT_POSTFIELDSIZE")
macdef CURLOPT_HTTPPROXYTUNNEL = $extval (CURLoption, "CURLOPT_HTTPPROXYTUNNEL")
macdef CURLOPT_INTERFACE = $extval (CURLoption, "CURLOPT_INTERFACE")
macdef CURLOPT_KRBLEVEL = $extval (CURLoption, "CURLOPT_KRBLEVEL")
macdef CURLOPT_SSL_VERIFYPEER = $extval (CURLoption, "CURLOPT_SSL_VERIFYPEER")
macdef CURLOPT_CAINFO = $extval (CURLoption, "CURLOPT_CAINFO")
macdef CURLOPT_MAXREDIRS = $extval (CURLoption, "CURLOPT_MAXREDIRS")
macdef CURLOPT_FILETIME = $extval (CURLoption, "CURLOPT_FILETIME")
macdef CURLOPT_TELNETOPTIONS = $extval (CURLoption, "CURLOPT_TELNETOPTIONS")
macdef CURLOPT_MAXCONNECTS = $extval (CURLoption, "CURLOPT_MAXCONNECTS")
macdef CURLOPT_CLOSEPOLICY = $extval (CURLoption, "CURLOPT_CLOSEPOLICY")
macdef CURLOPT_FRESH_CONNECT = $extval (CURLoption, "CURLOPT_FRESH_CONNECT")
macdef CURLOPT_FORBID_REUSE = $extval (CURLoption, "CURLOPT_FORBID_REUSE")
macdef CURLOPT_RANDOM_FILE = $extval (CURLoption, "CURLOPT_RANDOM_FILE")
macdef CURLOPT_EGDSOCKET = $extval (CURLoption, "CURLOPT_EGDSOCKET")
macdef CURLOPT_CONNECTTIMEOUT = $extval (CURLoption, "CURLOPT_CONNECTTIMEOUT")
macdef CURLOPT_HEADERFUNCTION = $extval (CURLoption, "CURLOPT_HEADERFUNCTION")
macdef CURLOPT_HTTPGET = $extval (CURLoption, "CURLOPT_HTTPGET")
macdef CURLOPT_SSL_VERIFYHOST = $extval (CURLoption, "CURLOPT_SSL_VERIFYHOST")
macdef CURLOPT_COOKIEJAR = $extval (CURLoption, "CURLOPT_COOKIEJAR")
macdef CURLOPT_SSL_CIPHER_LIST = $extval (CURLoption, "CURLOPT_SSL_CIPHER_LIST")
macdef CURLOPT_HTTP_VERSION = $extval (CURLoption, "CURLOPT_HTTP_VERSION")
macdef CURLOPT_FTP_USE_EPSV = $extval (CURLoption, "CURLOPT_FTP_USE_EPSV")
macdef CURLOPT_SSLCERTTYPE = $extval (CURLoption, "CURLOPT_SSLCERTTYPE")
macdef CURLOPT_SSLKEY = $extval (CURLoption, "CURLOPT_SSLKEY")
macdef CURLOPT_SSLKEYTYPE = $extval (CURLoption, "CURLOPT_SSLKEYTYPE")
macdef CURLOPT_SSLENGINE = $extval (CURLoption, "CURLOPT_SSLENGINE")
macdef CURLOPT_SSLENGINE_DEFAULT = $extval (CURLoption, "CURLOPT_SSLENGINE_DEFAULT")
macdef CURLOPT_DNS_USE_GLOBAL_CACHE = $extval (CURLoption, "CURLOPT_DNS_USE_GLOBAL_CACHE")
macdef CURLOPT_DNS_CACHE_TIMEOUT = $extval (CURLoption, "CURLOPT_DNS_CACHE_TIMEOUT")
macdef CURLOPT_PREQUOTE = $extval (CURLoption, "CURLOPT_PREQUOTE")
macdef CURLOPT_DEBUGFUNCTION = $extval (CURLoption, "CURLOPT_DEBUGFUNCTION")
macdef CURLOPT_DEBUGDATA = $extval (CURLoption, "CURLOPT_DEBUGDATA")
macdef CURLOPT_COOKIESESSION = $extval (CURLoption, "CURLOPT_COOKIESESSION")
macdef CURLOPT_CAPATH = $extval (CURLoption, "CURLOPT_CAPATH")
macdef CURLOPT_BUFFERSIZE = $extval (CURLoption, "CURLOPT_BUFFERSIZE")
macdef CURLOPT_NOSIGNAL = $extval (CURLoption, "CURLOPT_NOSIGNAL")
macdef CURLOPT_SHARE = $extval (CURLoption, "CURLOPT_SHARE")
macdef CURLOPT_PROXYTYPE = $extval (CURLoption, "CURLOPT_PROXYTYPE")
macdef CURLOPT_ENCODING = $extval (CURLoption, "CURLOPT_ENCODING")
macdef CURLOPT_PRIVATE = $extval (CURLoption, "CURLOPT_PRIVATE")
macdef CURLOPT_HTTP200ALIASES = $extval (CURLoption, "CURLOPT_HTTP200ALIASES")
macdef CURLOPT_UNRESTRICTED_AUTH = $extval (CURLoption, "CURLOPT_UNRESTRICTED_AUTH")
macdef CURLOPT_FTP_USE_EPRT = $extval (CURLoption, "CURLOPT_FTP_USE_EPRT")
macdef CURLOPT_HTTPAUTH = $extval (CURLoption, "CURLOPT_HTTPAUTH")
macdef CURLOPT_SSL_CTX_FUNCTION = $extval (CURLoption, "CURLOPT_SSL_CTX_FUNCTION")
macdef CURLOPT_SSL_CTX_DATA = $extval (CURLoption, "CURLOPT_SSL_CTX_DATA")
macdef CURLOPT_FTP_CREATE_MISSING_DIRS = $extval (CURLoption, "CURLOPT_FTP_CREATE_MISSING_DIRS")
macdef CURLOPT_PROXYAUTH = $extval (CURLoption, "CURLOPT_PROXYAUTH")
macdef CURLOPT_FTP_RESPONSE_TIMEOUT = $extval (CURLoption, "CURLOPT_FTP_RESPONSE_TIMEOUT")
macdef CURLOPT_IPRESOLVE = $extval (CURLoption, "CURLOPT_IPRESOLVE")
macdef CURLOPT_MAXFILESIZE = $extval (CURLoption, "CURLOPT_MAXFILESIZE")
macdef CURLOPT_INFILESIZE_LARGE = $extval (CURLoption, "CURLOPT_INFILESIZE_LARGE")
macdef CURLOPT_RESUME_FROM_LARGE = $extval (CURLoption, "CURLOPT_RESUME_FROM_LARGE")
macdef CURLOPT_MAXFILESIZE_LARGE = $extval (CURLoption, "CURLOPT_MAXFILESIZE_LARGE")
macdef CURLOPT_NETRC_FILE = $extval (CURLoption, "CURLOPT_NETRC_FILE")
macdef CURLOPT_USE_SSL = $extval (CURLoption, "CURLOPT_USE_SSL")
macdef CURLOPT_POSTFIELDSIZE_LARGE = $extval (CURLoption, "CURLOPT_POSTFIELDSIZE_LARGE")
macdef CURLOPT_TCP_NODELAY = $extval (CURLoption, "CURLOPT_TCP_NODELAY")
macdef CURLOPT_FTPSSLAUTH = $extval (CURLoption, "CURLOPT_FTPSSLAUTH")
macdef CURLOPT_IOCTLFUNCTION = $extval (CURLoption, "CURLOPT_IOCTLFUNCTION")
macdef CURLOPT_IOCTLDATA = $extval (CURLoption, "CURLOPT_IOCTLDATA")
macdef CURLOPT_FTP_ACCOUNT = $extval (CURLoption, "CURLOPT_FTP_ACCOUNT")
macdef CURLOPT_COOKIELIST = $extval (CURLoption, "CURLOPT_COOKIELIST")
macdef CURLOPT_IGNORE_CONTENT_LENGTH = $extval (CURLoption, "CURLOPT_IGNORE_CONTENT_LENGTH")
macdef CURLOPT_FTP_SKIP_PASV_IP = $extval (CURLoption, "CURLOPT_FTP_SKIP_PASV_IP")
macdef CURLOPT_FTP_FILEMETHOD = $extval (CURLoption, "CURLOPT_FTP_FILEMETHOD")
macdef CURLOPT_LOCALPORT = $extval (CURLoption, "CURLOPT_LOCALPORT")
macdef CURLOPT_LOCALPORTRANGE = $extval (CURLoption, "CURLOPT_LOCALPORTRANGE")
macdef CURLOPT_CONNECT_ONLY = $extval (CURLoption, "CURLOPT_CONNECT_ONLY")
macdef CURLOPT_CONV_FROM_NETWORK_FUNCTION = $extval (CURLoption, "CURLOPT_CONV_FROM_NETWORK_FUNCTION")
macdef CURLOPT_CONV_TO_NETWORK_FUNCTION = $extval (CURLoption, "CURLOPT_CONV_TO_NETWORK_FUNCTION")
macdef CURLOPT_CONV_FROM_UTF8_FUNCTION = $extval (CURLoption, "CURLOPT_CONV_FROM_UTF8_FUNCTION")
macdef CURLOPT_MAX_SEND_SPEED_LARGE = $extval (CURLoption, "CURLOPT_MAX_SEND_SPEED_LARGE")
macdef CURLOPT_MAX_RECV_SPEED_LARGE = $extval (CURLoption, "CURLOPT_MAX_RECV_SPEED_LARGE")
macdef CURLOPT_FTP_ALTERNATIVE_TO_USER = $extval (CURLoption, "CURLOPT_FTP_ALTERNATIVE_TO_USER")
macdef CURLOPT_SOCKOPTFUNCTION = $extval (CURLoption, "CURLOPT_SOCKOPTFUNCTION")
macdef CURLOPT_SOCKOPTDATA = $extval (CURLoption, "CURLOPT_SOCKOPTDATA")
macdef CURLOPT_SSL_SESSIONID_CACHE = $extval (CURLoption, "CURLOPT_SSL_SESSIONID_CACHE")
macdef CURLOPT_SSH_AUTH_TYPES = $extval (CURLoption, "CURLOPT_SSH_AUTH_TYPES")
macdef CURLOPT_SSH_PUBLIC_KEYFILE = $extval (CURLoption, "CURLOPT_SSH_PUBLIC_KEYFILE")
macdef CURLOPT_SSH_PRIVATE_KEYFILE = $extval (CURLoption, "CURLOPT_SSH_PRIVATE_KEYFILE")
macdef CURLOPT_FTP_SSL_CCC = $extval (CURLoption, "CURLOPT_FTP_SSL_CCC")
macdef CURLOPT_TIMEOUT_MS = $extval (CURLoption, "CURLOPT_TIMEOUT_MS")
macdef CURLOPT_CONNECTTIMEOUT_MS = $extval (CURLoption, "CURLOPT_CONNECTTIMEOUT_MS")
macdef CURLOPT_HTTP_TRANSFER_DECODING = $extval (CURLoption, "CURLOPT_HTTP_TRANSFER_DECODING")
macdef CURLOPT_HTTP_CONTENT_DECODING = $extval (CURLoption, "CURLOPT_HTTP_CONTENT_DECODING")
macdef CURLOPT_NEW_FILE_PERMS = $extval (CURLoption, "CURLOPT_NEW_FILE_PERMS")
macdef CURLOPT_NEW_DIRECTORY_PERMS = $extval (CURLoption, "CURLOPT_NEW_DIRECTORY_PERMS")
macdef CURLOPT_POSTREDIR = $extval (CURLoption, "CURLOPT_POSTREDIR")
macdef CURLOPT_SSH_HOST_PUBLIC_KEY_MD5 = $extval (CURLoption, "CURLOPT_SSH_HOST_PUBLIC_KEY_MD5")
macdef CURLOPT_OPENSOCKETFUNCTION = $extval (CURLoption, "CURLOPT_OPENSOCKETFUNCTION")
macdef CURLOPT_OPENSOCKETDATA = $extval (CURLoption, "CURLOPT_OPENSOCKETDATA")
macdef CURLOPT_COPYPOSTFIELDS = $extval (CURLoption, "CURLOPT_COPYPOSTFIELDS")
macdef CURLOPT_PROXY_TRANSFER_MODE = $extval (CURLoption, "CURLOPT_PROXY_TRANSFER_MODE")
macdef CURLOPT_SEEKFUNCTION = $extval (CURLoption, "CURLOPT_SEEKFUNCTION")
macdef CURLOPT_SEEKDATA = $extval (CURLoption, "CURLOPT_SEEKDATA")
macdef CURLOPT_CRLFILE = $extval (CURLoption, "CURLOPT_CRLFILE")
macdef CURLOPT_ISSUERCERT = $extval (CURLoption, "CURLOPT_ISSUERCERT")
macdef CURLOPT_ADDRESS_SCOPE = $extval (CURLoption, "CURLOPT_ADDRESS_SCOPE")
macdef CURLOPT_CERTINFO = $extval (CURLoption, "CURLOPT_CERTINFO")
macdef CURLOPT_USERNAME = $extval (CURLoption, "CURLOPT_USERNAME")
macdef CURLOPT_PASSWORD = $extval (CURLoption, "CURLOPT_PASSWORD")
macdef CURLOPT_PROXYUSERNAME = $extval (CURLoption, "CURLOPT_PROXYUSERNAME")
macdef CURLOPT_PROXYPASSWORD = $extval (CURLoption, "CURLOPT_PROXYPASSWORD")
macdef CURLOPT_NOPROXY = $extval (CURLoption, "CURLOPT_NOPROXY")
macdef CURLOPT_TFTP_BLKSIZE = $extval (CURLoption, "CURLOPT_TFTP_BLKSIZE")
macdef CURLOPT_SOCKS5_GSSAPI_SERVICE = $extval (CURLoption, "CURLOPT_SOCKS5_GSSAPI_SERVICE")
macdef CURLOPT_SOCKS5_GSSAPI_NEC = $extval (CURLoption, "CURLOPT_SOCKS5_GSSAPI_NEC")
macdef CURLOPT_PROTOCOLS = $extval (CURLoption, "CURLOPT_PROTOCOLS")
macdef CURLOPT_REDIR_PROTOCOLS = $extval (CURLoption, "CURLOPT_REDIR_PROTOCOLS")
macdef CURLOPT_SSH_KNOWNHOSTS = $extval (CURLoption, "CURLOPT_SSH_KNOWNHOSTS")
macdef CURLOPT_SSH_KEYFUNCTION = $extval (CURLoption, "CURLOPT_SSH_KEYFUNCTION")
macdef CURLOPT_SSH_KEYDATA = $extval (CURLoption, "CURLOPT_SSH_KEYDATA")
macdef CURLOPT_LASTENTRY = $extval (CURLoption, "CURLOPT_LASTENTRY")

(* ****** ****** *)

macdef CURL_GLOBAL_SSL = $extval (lint, "CURL_GLOBAL_SSL")
macdef CURL_GLOBAL_WIN32 = $extval (lint, "CURL_GLOBAL_WIN32")
macdef CURL_GLOBAL_ALL = $extval (lint, "CURL_GLOBAL_ALL")
macdef CURL_GLOBAL_NOTHING = $extval (lint, "CURL_GLOBAL_NOTHING") 
macdef CURL_GLOBAL_DEFAULT = $extval (lint, "CURL_GLOBAL_DEFAULT") // = CURL_GLOBAL_ALL

(*
** curl_global_init() should be invoked exactly once for each application that
** uses libcurl and before any call of other libcurl functions.
**
** This function is not thread-safe!
*)
absview CURLglobal_v (i:int)
fun curl_global_init (
  flags: lint
) : [i:int] (
  CURLglobal_v i | CURLcode i
) = "mac#atsctrb_curl_global_init"
// end of [curl_global_init]

(* ****** ****** *)

fun curl_global_cleanup (
  pf: CURLglobal_v 0 | (*none*)
) : void
  = "mac#atsctrb_curl_global_cleanup"
// end of [curl_global_cleanup]

(* ****** ****** *)

#include "contrib/cURL/SATS/easy.sats"

(* ****** ****** *)

(* end of [curl.sats] *)
