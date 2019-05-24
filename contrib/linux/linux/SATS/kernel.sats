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
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#
#include "contrib/linux/linux/CATS/kernel.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staloading at run-time

(* ****** ****** *)

(*
#define KERN_EMERG      "<0>"   /* system is unusable                   */
#define KERN_ALERT      "<1>"   /* action must be taken immediately     */
#define KERN_CRIT       "<2>"   /* critical conditions                  */
#define KERN_ERR        "<3>"   /* error conditions                     */
#define KERN_WARNING    "<4>"   /* warning conditions                   */
#define KERN_NOTICE     "<5>"   /* normal but significant condition     */
#define KERN_INFO       "<6>"   /* informational                        */
#define KERN_DEBUG      "<7>"   /* debug-level messages                 */
*)

fun KERN_EMERG {ts:types}
  (fmt: printf_c (ts)): printf_c (ts) = "mac#atsctrb_linux_KERN_EMERG"
// end of [KERN_EMERG]

fun KERN_ALERT {ts:types}
  (fmt: printf_c (ts)): printf_c (ts) = "mac#atsctrb_linux_KERN_ALERT"
// end of [KERN_ALERT]

fun KERN_CRIT {ts:types}
  (fmt: printf_c (ts)): printf_c (ts) = "mac#atsctrb_linux_KERN_CRIT"
// end of [KERN_CRIT]

fun KERN_ERR {ts:types}
  (fmt: printf_c (ts)): printf_c (ts) = "mac#atsctrb_linux_KERN_ERR"
// end of [KERN_ERR]

fun KERN_WARNING {ts:types}
  (fmt: printf_c (ts)): printf_c (ts) = "mac#atsctrb_linux_KERN_WARNING"
// end of [KERN_WARNING]

fun KERN_NOTICE {ts:types}
  (fmt: printf_c (ts)): printf_c (ts) = "mac#atsctrb_linux_KERN_NOTICE"
// end of [KERN_NOTICE]

fun KERN_INFO {ts:types}
  (fmt: printf_c (ts)): printf_c (ts) = "mac#atsctrb_linux_KERN_INFO"
// end of [KERN_INFO]

fun KERN_DEBUG {ts:types}
  (fmt: printf_c (ts)): printf_c (ts) = "mac#atsctrb_linux_KERN_DEBUG"
// end of [KERN_DEBUG]

(* ****** ****** *)

(*
// HX: [printf_c] is just an approximation
*)
fun printk {ts:types}
  (fmt: printf_c (ts), arg: ts): void = "mac#atsctrb_linux_printk"
// end of [printk]

(* ****** ****** *)

(* end of [kernel.sats] *)
