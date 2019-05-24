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

staload "contrib/cURL/SATS/curl.sats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no need for dynloading at run-time

(* ****** ****** *)

staload "libc/SATS/stdarg.sats"

(* ****** ****** *)

%{^
//
// HX-2010-06-03: not sure if this is a good idea:
//
extern CURLcode Curl_setopt(ats_ptr_type, CURLoption, va_list);
#define atsctrb_Curl_setopt(curl, option, arg) Curl_setopt(curl, option, *(va_list*)arg)
%} // end of [%{^]

implement
curl_easy_setopt_exn {l} {ts}
  (curl, option, arg) = let
  extern fun Curl_setopt (
    curl: !CURLptr l, option: CURLoption, arg: &va_list ts >> va_list
  ) : CURLcode = "mac#atsctrb_Curl_setopt" // declared in lib/url.h
  val err = Curl_setopt (curl, option, arg)
  val () = va_end (arg) // a type error is reported if [va_end] is not called
  val () = if (err <> CURLE_OK) then let
    val () = fprintf (stderr_ref, "exit(ATS): [curl_easy_setopt] failed\n", @())
  in
    exit (1)
  end // end of [val]
in
  // nothing
end // end of [curl_easy_setopt_exn]

(* ****** ****** *)

(* end of [curl.dats] *)
