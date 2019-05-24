(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
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
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Feburary(?) 2011
//
(* ****** ****** *)

staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t
staload Lst = "ats_list.sats"
staload Sym = "ats_symbol.sats"
typedef sym_t = $Sym.symbol_t
overload = with $Sym.eq_symbol_symbol

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"
staload "ats_dynexp1_syndef.sats"

(* ****** ****** *)

(*
dynload "libatsyndef/atsyndef_main.dats"
*)

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

macdef list_sing (x) = list_cons (,(x), list_nil)

(* ****** ****** *)

fn prerr_loc_error1
  (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(1)")
// end of [prerr_loc_error1]

(* ****** ****** *)

implement
fprint_intlst
  (out, ns) = let
  fun loop (
    out: FILEref, ns: intlst, i: int
  ) : void =
    case+ ns of
    | list_cons (n, ns) => let
        val () = if i > 0 then
          fprint_string (out, ", ")
        val () = fprint_int (out, n)
      in
        loop (out, ns, i+1)
      end // end of [cons]
    | list_nil () => ()
  // end of [loop]
in
  loop (out, ns, 0)
end // end of [fprint_intlst]

(* ****** ****** *)

(*
//
// n >= 0 means exact n
// n <  0 means at least (~n-1)
//
*)

implement
match_intlst_intlst (ns1, ns2) =
  case+ ns1 of
  | list_cons (n1, ns1) => (case+ ns2 of
    | list_cons (n2, ns2) => (
        if n2 >= 0 then
          (if (n1 = n2) then match_intlst_intlst (ns1, ns2) else false)
        else if n2 <= ~2 then
          (if (n1 + 1 >= ~n2) then match_intlst_intlst (ns1, ns2) else false)
        else (
          match_intlst_intlst (ns1, ns2)
        ) // end of [if]
      ) // end of [list_cons]
    | list_nil () => false
    ) // end of [cons]
  | list_nil () => (
    case+ ns2 of list_cons _ => false | list_nil () => true
    ) // end of [list_nil]
// end of [match_intlst_intlst]

(* ****** ****** *)

implement
tmpqi0de_make_qid
  (loc, q, id) = '{
  tmpqi0de_loc= loc, tmpqi0de_qua= q, tmpqi0de_sym= id
} // end of [tmpqi0de_make_qid]

(* ****** ****** *)

implement
un_d1exp_ann_type
  (d1e) = case+ d1e.d1exp_node of
  | D1Eann_type (d1e, s1e) => (d1e, s1e)
  | _ => let
      val () = prerr_loc_error1 (d1e.d1exp_loc)
      val () = prerr ": the dynexp is expected be some annotated expression."
      val () = prerr_newline ()
    in
      $Err.abort ()
    end // end of [_]
// end of [un_d1exp_ann_type]

(* ****** ****** *)

implement
un_d1exp_idext (d1e) =
  case+ d1e.d1exp_node of
  | D1Eidextapp (id, _, _) => id
  | _ => let
      val () = prerr_loc_error1 (d1e.d1exp_loc)
      val () = prerr ": the dynexp is expected to be some external identifer."
      val () = prerr_newline ()
    in
      $Err.abort {sym_t} ()
    end // end of [_]
// end of [un_d1exp_idext]

implement
un_d1exp_idext_sym
  (d1e, sym0) = let
  val sym = un_d1exp_idext (d1e)
in
  if $Sym.eq_symbol_symbol
    (sym0, sym) then () else let
    val () = prerr_loc_error1 (d1e.d1exp_loc)
    val () = (
      prerr ": the external id ["; $Sym.prerr_symbol (sym0); prerr "] is expected."
    ) // end of [val]
    val () = prerr_newline ()
  in
    $Err.abort {void} ()
  end (* end of [if] *)
end // end of [un_d1exp_idext_sym]

(* ****** ****** *)

implement
un_d1exp_qid (d1e) =
  case+ d1e.d1exp_node of
  | D1Eqid (q, id) =>  (q, id)
  | _ => let
      val () = prerr_loc_error1 (d1e.d1exp_loc)
      val () = prerr ": the dynexp is expected be some (qualified) identifier."
      val () = prerr_newline ()
    in
      $Err.abort ()
    end // end of [_]
// end of [un_d1exp_qid]

implement
un_d1exp_qid_sym
  (d1e, sym0) = let
  val (q, sym) = un_d1exp_qid (d1e)
in
  if $Sym.eq_symbol_symbol
    (sym0, sym) then () else let
    val () = prerr_loc_error1 (d1e.d1exp_loc)
    val () = (
      prerr ": the symbol ["; $Sym.prerr_symbol (sym0); prerr "] is expected."
    ) // end of [val]
    val () = prerr_newline ()
  in
    $Err.abort {void} ()
  end (* end of [if] *)
end // end of [un_d1exp_qid_sym]

(* ****** ****** *)

implement
un_d1exp_sexparg (d1e) =
  case+ d1e.d1exp_node of
  | D1Esexparg s1a => s1a
  | _ => let
      val () = prerr_loc_error1 (d1e.d1exp_loc)
      val () = prerr ": the dynexp is expected to be a static argument."
      val () = prerr_newline ()
    in
      $Err.abort {s1exparg} ()
    end // end of [_]
// end of [un_d1exp_sexparg]

(* ****** ****** *)

implement
un_d1exp_decseq (d1e) =
  case+ d1e.d1exp_node of
  | D1Edecseq (d1cs) => d1cs
  | _ => let
      val () = prerr_loc_error1 (d1e.d1exp_loc)
      val () = prerr ": the dynexp is expected to be a list of declarations."
      val () = prerr_newline ()
    in
      $Err.abort {d1eclst} ()
    end // end of [_]
// end of [un_d1exp_decseq]

(* ****** ****** *)
//
// HX-2010-11-02:
// this function is implemented in
// $ATSHOME/libatsyndef/atsyndef_main.dats
//
typedef
atsyndef_search_all_type =
  (sym_t, intlst) -<fun1> Option_vt (fsyndef)
(*
//
// HX: this style is not supported in ATS/Geizella
//
extern
fun atsyndef_search_all : atsyndef_search_all_type
// end of [extern]
*)
extern
fun atsyndef_search_all
  (_: sym_t, _: intlst):<fun1> Option_vt (fsyndef)
// end of [extern]

(* ****** ****** *)

val _n1 = (~1 :: nil): intlst
val _n1_p1 = (~1 :: 1 :: nil): intlst // while ($test) ($body)
val _n1_p1_n1 =
  (~1 :: 1 :: ~1 :: nil): intlst // do ($body) while ($test)
val _n2 = (~2 :: nil): intlst
val _p3 = ( 3 :: nil): intlst

(* ****** ****** *)

macdef matii = match_intlst_intlst

(* ****** ****** *)

extern
fun search_IF (ns: intlst): fsyndefopt
extern
fun d1exp_if_p3 (loc: loc_t, d1es: d1explst): d1exp
implement
search_IF (ns) = let
(*
  val () = print "search_IF: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when ns \matii _p3 => Some_vt (d1exp_if_p3)
  | _ => None_vt ()
end // end of [search_IF]

(* ****** ****** *)

extern
fun search_DO (ns: intlst): fsyndefopt
extern
fun d1exp_do_n1_p1_n1
  (loc: loc_t, d1es: d1explst): d1exp
// end of [d1exp_do_n1_p1_n1]

implement
search_DO (ns) = let
(*
  val () = print "search_DO: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when ns \matii _n1_p1_n1 => Some_vt (d1exp_do_n1_p1_n1)
  | _ => None_vt ()
end // end of [search_DO]

(* ****** ****** *)

extern
fun search_WHILE
  (ns: intlst): fsyndefopt
extern
fun d1exp_while_n1_p1
  (loc: loc_t, d1es: d1explst): d1exp
// end of [d1exp_while_n1_p1]

implement
search_WHILE (ns) = let
(*
  val () = print "search_WHILE: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when ns \matii _n1_p1 => Some_vt (d1exp_while_n1_p1)
  | _ => None_vt ()
end // end of [search_WHILE]

(* ****** ****** *)

extern
fun search_PRINT (ns: intlst): fsyndefopt
extern
fun d1exp_print_n1 (loc: loc_t, d1es: d1explst): d1exp
implement
search_PRINT (ns) = let
(*
  val () = print "search_PRINT: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when ns \matii _n1 => Some_vt (d1exp_print_n1)
  | _ => None_vt ()
end // end of [search_PRINT]

extern
fun search_PRINTLN  (ns: intlst): fsyndefopt
extern
fun d1exp_println_n1 (loc: loc_t, d1es: d1explst): d1exp
implement
search_PRINTLN (ns) = let
(*
  val () = print "search_PRINTLN: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when ns \matii _n1 => Some_vt (d1exp_println_n1)
  | _ => None_vt ()
end // end of [search_PRINTLN]

extern
fun search_PRERR (ns: intlst): fsyndefopt
extern
fun d1exp_prerr_n1 (loc: loc_t, d1es: d1explst): d1exp
implement
search_PRERR (ns) = let
(*
  val () = print "search_PRERR: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when ns \matii _n1 => Some_vt (d1exp_prerr_n1)
  | _ => None_vt ()
end // end of [search_PRERR]

extern
fun search_PRERRLN  (ns: intlst): fsyndefopt
extern
fun d1exp_prerrln_n1 (loc: loc_t, d1es: d1explst): d1exp
implement
search_PRERRLN (ns) = let
(*
  val () = print "search_PRERRLN: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when ns \matii _n1 => Some_vt (d1exp_prerrln_n1)
  | _ => None_vt ()
end // end of [search_PRERRLN]

extern
fun search_FPRINT (ns: intlst): fsyndefopt
extern
fun d1exp_fprint_n2 (loc: loc_t, d1es: d1explst): d1exp
implement
search_FPRINT (ns) = let
(*
  val () = print "search_FPRINT: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when ns \matii _n2 => Some_vt (d1exp_fprint_n2)
  | _ => None_vt ()
end // end of [search_FPRINT]

extern
fun search_FPRINTLN (ns: intlst): fsyndefopt
extern
fun d1exp_fprintln_n2 (loc: loc_t, d1es: d1explst): d1exp
implement
search_FPRINTLN (ns) = let
(*
  val () = print "search_FPRINTLN: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when ns \matii _n2 => Some_vt (d1exp_fprintln_n2)
  | _ => None_vt ()
end // end of [search_FPRINTLN]

(* ****** ****** *)

val symbol_IF = $Sym.symbol_IF
val symbol_DO = $Sym.symbol_DO
val symbol_WHILE = $Sym.symbol_WHILE
val symbol_PRINT = $Sym.symbol_make_string ("print")
val symbol_PRINTLN = $Sym.symbol_make_string ("println")
val symbol_PRERR = $Sym.symbol_make_string ("prerr")
val symbol_PRERRLN = $Sym.symbol_make_string ("prerrln")
val symbol_FPRINT = $Sym.symbol_make_string ("fprint")
val symbol_FPRINTLN = $Sym.symbol_make_string ("fprintln")

implement
atsyndef_search_all_default
  (id, ns) = let
(*
  val () = print "atsyndef_search_all_default: id = "
  val () = $Sym.print_symbol (id)
  val () = print_newline ()
  val () = print "atsyndef_search_all_default: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when id = symbol_IF => search_IF (ns)
  | _ when id = symbol_DO => search_DO (ns)
  | _ when id = symbol_WHILE => search_WHILE (ns)
//
  | _ when id = symbol_PRINT => search_PRINT (ns)
  | _ when id = symbol_PRINTLN => search_PRINTLN (ns)
//
  | _ when id = symbol_PRERR => search_PRERR (ns)
  | _ when id = symbol_PRERRLN => search_PRERRLN (ns)
//
  | _ when id = symbol_FPRINT => search_FPRINT (ns)
  | _ when id = symbol_FPRINTLN => search_FPRINTLN (ns)
//
(*
// HX-2010-11-15:
// how should I judge whether a new external symbol should be supported?
*)
  | _ => None_vt ()
end // end of [atsyndef_search_all_default]

(* ****** ****** *)

(*
// HX: compile with the -DATS_SYNDEFATS flag
#define _SYNDEFATS 1
*)
#if defined(_SYNDEFATS) #then
//
local
//
staload "libc/SATS/dlfcn.sats"
//
val finit_name = "atsyndef_initialize"
var finit_ptr: ptr = null
//
val fsrch_name = "atsyndef_search_all"
var fsrch_ptr: ptr = null
//
val (pfopt_lib | p_lib) =
  dlopen ("libatsyndef.so", RTLD_LAZY)
// end of [val]
val () = if
p_lib > null then let
  val () = (prerr "\
ATS/Anairiats: [libatsyndef.so] is available to support syndef-loaded external ids.\n\
"
  ) // end of [val]
  prval Some_v (pf_lib) = pfopt_lib
  val () = dlerror_clr ()
  val () = finit_ptr := dlsym (pf_lib | p_lib, finit_name)
(*
  val (fpf_msg | msg) = dlerror () // clearing any existing error
  val () = (
    print "atsyndef_search_all: finit: "; print msg; print_newline ()
  ) // end of [val]
  prval () = fpf_msg (msg)
*)
  val () = dlerror_clr ()
  val () = fsrch_ptr := dlsym (pf_lib | p_lib, fsrch_name)
(*
  val (fpf_msg | msg) = dlerror () // see if there is any error
  val () = (
    print "atsyndef_search_all: fsrch = "; print msg; print_newline ()
  ) // end of [val]
  prval () = fpf_msg (msg)
*)
  val () = dlclose_exn (pf_lib | p_lib)
in
  // nothing
end else let
  val () = (prerr "\
ATS/Anairiats: [libatsyndef.so] is not available to support syndef-loaded external ids.\n\
"
  ) // end of [val]
  prval None_v () = pfopt_lib
in
  // nothing
end // end of [if]
//
val finit_ptr = finit_ptr
val fsrch_ptr = fsrch_ptr
//
val () = if
  finit_ptr > null then let
  val finit = __cast (finit_ptr) where {
    extern castfn __cast (x: ptr):<> ((*none*)) -<fun1> void
  } // end of [val]
in
  finit ()
end // end of [val]

in // in of [local]

implement
atsyndef_search_all
  (id, ns) = let
  val ans = atsyndef_search_all_default (id, ns)
in
  case+ ans of
  | ~None_vt _ => (case+ 0 of
    | _ when fsrch_ptr > null => let
        val fsrch = __cast (fsrch_ptr) where {
          extern castfn __cast (x: ptr):<> atsyndef_search_all_type
        } // end of [_ when ...]
      in
        fsrch (id, ns)
      end // end of [_ when ...]
    | _ => None_vt ()
    ) // end of [None_vt]
  | Some_vt _ => (fold@ ans; ans)
end // end of [atsyndef_search_all]

end  // end of [local]

#else // else of [_SYNDEFATS]

implement
atsyndef_search_all
  (id, ns) = atsyndef_search_all_default (id, ns)
// end of [atsyndef_search_all]

#endif // end of [_SYNDEFATS]

(* ****** ****** *)

implement
d1exp_idextapp_resolve
  (loc0, d1e) = begin
  case+ d1e.d1exp_node of
  | D1Eidextapp (
      id, _(*ns*), d1es_arg
    ) => begin case+ 0 of
    | _ when id = $Sym.symbol_TUPZ =>
        d1exp_list (loc0, $Lst.list_reverse (d1es_arg))
      // end of [_ when ...]
    | _ => d1e
    end // end of [D1Eidextapp]
  | _ => d1e // end of [_]
end // end of [d1exp_idextapp_resolve]

(* ****** ****** *)

implement
d1exp_app_syndef (
  loc0, d1e_fun, d1e_arg
) =
  case+ d1e_fun.d1exp_node of
  | D1Eidextapp
      (id, ns, arglst) => let
      val n = (
        case+ d1e_arg.d1exp_node of
        | D1Elist (_(*npf*), d1es) => $Lst.list_length (d1es) | _ => 1
      ) : int // end of [val]
      val ns = cons (n, ns)
      val arglst = cons (d1e_arg, arglst)
      val opt = atsyndef_search_all (id, ns)
    in
      case+ opt of
      | ~Some_vt (fsyndef) => fsyndef (loc0, arglst)
      | ~None_vt () => d1exp_idextapp (loc0, id, ns, arglst)
    end // end of [D1Eidexpapp]
  | _ => (case+ d1e_arg.d1exp_node of
    | D1Elist (npf, d1es) => begin
        d1exp_app_dyn (loc0, d1e_fun, d1e_arg.d1exp_loc, npf, d1es)
      end // end of [D1Elist]
    | D1Esexparg s1a => (case+ d1e_fun.d1exp_node of
      | D1Eapp_sta (d1e_fun, s1as) => begin
          d1exp_app_sta (loc0, d1e_fun, $Lst.list_extend (s1as, s1a))
        end // end of [D1Eapp_sta]
      | _ => let
          val s1as =  cons (s1a, nil ()) in d1exp_app_sta (loc0, d1e_fun, s1as)
        end // end of [_]
      ) // end of [D1Esexparg]
    | _ => let
        val npf = 0 and d1es = cons (d1e_arg, nil ()) in
        d1exp_app_dyn (loc0, d1e_fun, d1e_arg.d1exp_loc, npf, d1es)
      end // end of [_]    
    ) // end of [_]
// end of [d1exp_app_syndef]

(* ****** ****** *)

fun d1exp_applstseq (
  loc0: loc_t
, d1es: d1explst
, f: !(d1exp) -<cloptr1> d1exp
) : d1exp = let
  fun mapf (
    d1es: d1explst, f: !(d1exp) -<cloptr1> d1exp
  ) : d1explst =
    case+ d1es of
    | list_cons (d1e, d1es) => list_cons (f (d1e), mapf (d1es, f))
    | list_nil () => list_nil ()
  // end of [mapf]
in
  d1exp_seq (loc0, mapf (d1es, f))
end // end of [d1exp_applstseq]

fun d1exp_appseq (
  loc0: loc_t
, d1e: d1exp
, f: !(d1exp) -<cloptr1> d1exp
) : d1exp = begin
  case+ d1e.d1exp_node of
  | D1Elist (_(*npf*), d1es) => d1exp_applstseq (loc0, d1es, f)
  | _ => f (d1e)
end // end of [d1exp_appseq]

(* ****** ****** *)

implement
d1exp_if_p3
  (loc0, arg) = let
  val- cons (d1e1, _) = arg
  val- D1Elist (_, d1es) = d1e1.d1exp_node
  val- cons (d1e11, d1es) = d1es
  val- cons (d1e12, d1es) = d1es
  val- cons (d1e13, d1es) = d1es
  val ifhead = i1nvresstate_nil
in
  d1exp_if (loc0, ifhead, d1e11, d1e12, Some (d1e13))
end // end of [d1exp_if_p3]

(* ****** ****** *)

implement
d1exp_do_n1_p1_n1
  (loc0, d1es) = let
//
  val- cons (d1e3, d1es) = d1es
//
  val- cons (d1e2, d1es) = d1es
  val () = un_d1exp_idext_sym (d1e2, $Sym.symbol_WHILE)
//
  val- cons (d1e1, d1es) = d1es
//
  val _then = d1exp_loopexn (loc0, 1) // continue
  val _else = Some (d1exp_loopexn (loc0, 0)) // break
//
  val loc3 = d1e3.d1exp_loc
  val _ifexp = d1exp_if (loc3, i1nvresstate_nil, d1e3, _then, _else)
//
  val _inv = loopi1nv_nil (loc0)
  val _true = d1exp_bool (loc0, true)
//
  val _body = d1exp_seq (loc0, d1e1 :: _ifexp :: nil)
//
in
  d1exp_while (loc0, _inv, _true, _body)
end // end of [do_n1_p1_n1]

(* ****** ****** *)

implement
d1exp_while_n1_p1
  (loc0, d1es) = let
//
  val- cons (d1e2, d1es) = d1es
  val _body = d1e2
//
  val- cons (d1e1, d1es) = d1es
  val _test = d1e1
//
  val _inv = loopi1nv_nil (loc0)
//
in
  d1exp_while (loc0, _inv, _test, _body)
end // end of [d1exp_while_n1_p1]

(* ****** ****** *)

implement
d1exp_print_n1
  (loc0, d1es) = let
  val- cons (d1e1, _) = d1es
  val q = $Syn.d0ynq_none ()
  val fqid = d1exp_qid (loc0, q, symbol_PRINT)
  val f = lam
    (d1e: d1exp)
    : d1exp =<cloptr1> let
    val loc = d1e.d1exp_loc
  in
    d1exp_app_dyn (loc, fqid, loc, 0(*npf*), list_sing (d1e))
  end // end of [_]
  val d1eseq = d1exp_appseq (loc0, d1e1, f)
  val () = cloptr_free (f)
in
  d1eseq
end // end of [print_n1]

implement
d1exp_println_n1
  (loc0, d1es) = let
//
  val q = $Syn.d0ynq_none ()
  val println_id = $Sym.symbol_make_string ("print_newline")
  val println_qid = d1exp_qid (loc0, q, println_id)
//
  val d1eseq = d1exp_print_n1 (loc0, d1es)
  val d1eln = d1exp_app_dyn (loc0, println_qid, loc0, 0(*npf*), list_nil)
//
in
  d1exp_seq (loc0, d1eseq :: d1eln :: list_nil)
end // end of [println_n1]

implement
d1exp_prerr_n1
  (loc0, d1es) = let
  val- cons (d1e1, _) = d1es
  val q = $Syn.d0ynq_none ()
  val fqid = d1exp_qid (loc0, q, symbol_PRERR)
  val f = lam
    (d1e: d1exp)
    : d1exp =<cloptr1> let
    val loc = d1e.d1exp_loc
  in
    d1exp_app_dyn (loc, fqid, loc, 0(*npf*), list_sing (d1e))
  end // end of [_]
  val d1eseq = d1exp_appseq (loc0, d1e1, f)
  val () = cloptr_free (f)
in
  d1eseq
end // end of [prerr_n1]

implement
d1exp_prerrln_n1
  (loc0, d1es) = let
//
  val q = $Syn.d0ynq_none ()
  val prerrln_id = $Sym.symbol_make_string ("prerr_newline")
  val prerrln_qid = d1exp_qid (loc0, q, prerrln_id)
//
  val d1eseq = d1exp_prerr_n1 (loc0, d1es)
  val d1eln = d1exp_app_dyn (loc0, prerrln_qid, loc0, 0(*npf*), list_nil)
//
in
  d1exp_seq (loc0, d1eseq :: d1eln :: list_nil)
end // end of [prerrln_n1]

(* ****** ****** *)

implement
d1exp_fprint_n2
  (loc0, d1es) = let
  val- cons (d1e1, _) = d1es
  val q = $Syn.d0ynq_none ()
  val fqid = d1exp_qid (loc0, q, symbol_FPRINT)
  val (d1e_out, d1es_arg) = (case+ d1e1.d1exp_node of
    | D1Elist (_(*npf*), d1e :: d1es) => (d1e, d1es) | _ => (d1e1, list_nil)
  ) : (d1exp, d1explst)
  val f = lam
    (d1e_arg: d1exp)
    : d1exp =<cloptr1> let
    val loc = d1e_arg.d1exp_loc in
    d1exp_app_dyn (loc, fqid, loc, 0(*npf*), d1e_out :: d1e_arg :: list_nil)
  end // end of [_]
  val d1eseq = d1exp_applstseq (loc0, d1es_arg, f)
  val () = cloptr_free (f)
in
  d1eseq
end // end of [fprint_n2]

(* ****** ****** *)

implement
d1exp_fprintln_n2
  (loc0, d1es) = let
  val- cons (d1e1, _) = d1es
  val q = $Syn.d0ynq_none ()
  val fqid = d1exp_qid (loc0, q, symbol_FPRINT)
  val (d1e_out, d1es_arg) = (case+ d1e1.d1exp_node of
    | D1Elist (_(*npf*), d1e :: d1es) => (d1e, d1es) | _ => (d1e1, list_nil)
  ) : (d1exp, d1explst)
  val f = lam
    (d1e_arg: d1exp)
    : d1exp =<cloptr1> let
    val loc = d1e_arg.d1exp_loc in
    d1exp_app_dyn (loc, fqid, loc, 0(*npf*), d1e_out :: d1e_arg :: list_nil)
  end // end of [_]
  val d1eseq = d1exp_applstseq (loc0, d1es_arg, f)
  val () = cloptr_free (f)
//
  val fprintln_id = $Sym.symbol_make_string ("fprint_newline")
  val fprintln_qid = d1exp_qid (loc0, q, fprintln_id)
  val d1eln = d1exp_app_dyn (loc0, fprintln_qid, loc0, 0(*npf*), list_sing (d1e_out))
//
in
  d1exp_seq (loc0, d1eseq :: d1eln :: list_nil)
end // end of [fprintln_n2]

(* ****** ****** *)

(* end of [ats_dynexp1_syndef.dats] *)
