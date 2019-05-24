(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Power of Types!
**
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
**
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
*)

(* ****** ****** *)

// February 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload STDIO = "libc/SATS/stdio.sats"

(* ****** ****** *)

staload Loc = "location.sats"
staload Sym = "symbol.sats"
staload Tok = "token.sats"
staload Gra = "grammar.sats"

(* ****** ****** *)

typedef symbol = $Sym.symbol_t
typedef symlst = List (symbol)
typedef symopt = Option (symbol)
viewtypedef symlst_vt = List_vt (symbol)

typedef token = $Tok.token
typedef tokenlst = $Tok.tokenlst
typedef tokenopt = $Tok.tokenopt
viewtypedef tokenlst_vt = List_vt (token)

(* ****** ****** *)

staload "atsyacc_top.sats"

(* ****** ****** *)

staload _(*anonymois*) = "prelude/DATS/array.dats"
staload _(*anonymois*) = "prelude/DATS/list_vt.dats"
staload _(*anonymois*) = "prelude/DATS/pointer.dats"
staload _(*anonymois*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

extern fun the_token_get (): token
extern fun the_token_update (): void
extern fun the_token_update_get (): token
extern fun the_token_get_update (): token

extern fun the_assocval_getinc (): int

local

val theTokenRef = let
  val tok = $Tok.token_none_make () in ref_make_elt<token> (tok)
end // end of [val]

val theAssocValRef = ref_make_elt<int> (0)

in // in of [loca]

implement the_token_get () = !theTokenRef

implement the_token_update () = let
  val tok = atsyacc_lexer_token_get () in !theTokenRef := tok
end // end of [the_token_update]

implement the_token_get_update () = let
  val tok0 = !theTokenRef
  val tok1 = atsyacc_lexer_token_get () in !theTokenRef := tok1; tok0
end // end of [the_token_update]

implement the_token_update_get () = let
  val tok = atsyacc_lexer_token_get () in !theTokenRef := tok; tok
end // end of [the_token_update]

implement the_assocval_getinc () = let
  val n = !theAssocValRef in !theAssocValRef := n+1; n
end // end of [the_assoc_getinc]

end // end of [local]

(* ****** ****** *)

fn parse_percperc (): void = let
  val tok = the_token_get () in
  case+ tok.token_node of
  | $Tok.TOKpercperc () => the_token_update ()
  | _ => begin
      $Loc.prerr_location tok.token_loc;
      prerr ": error(ATSYACC)";
      prerr ": the token should be [%%] but it is not.";
      prerr_newline ();
      exit {void} (1)
    end // end of [_]
end // end of [parse_percperc]

fn parse_percpercopt (): void = let
  val tok = the_token_get () in
  case+ tok.token_node of
  | $Tok.TOKpercperc () => the_token_update ()
  | _ => ()
end // end of [parse_percpercopt]

(* ****** ****** *)

fun parse_type (): token = let
  val tok = the_token_get ()
in
  case+ tok.token_node of
  | $Tok.TOKptbrackstr _ => let
      val () = the_token_update () in tok
    end // end of [TOKptbrackstr]
  | _ => begin
      $Loc.prerr_location tok.token_loc;
      prerr ": error(ATSYACC)";
      prerr ": the token should represent a type but it does not.";
      prerr_newline ();
      exit {token} (1)
    end // end of [_]
end // end of [parse_typeopt]

fun parse_typeopt (): tokenopt = let
  val tok = the_token_get ()
in
  case+ tok.token_node of
  | $Tok.TOKptbrackstr _ => let
      val () = the_token_update () in Some (tok)
    end // end of [TOKptbrackstr]
  | _ => None ()
end // end of [parse_typeopt]

(* ****** ****** *)

fun parse_tokenlst
  (knd: $Sym.symkind, tpopt: tokenopt): void = let
  val tok = the_token_get ()
in
  case+ tok.token_node of
  | $Tok.TOKident name => let
      val () = the_token_update ()
      val isnew = $Sym.name_is_new (name)
    in
      if isnew then let
        val _(*sym*) = $Sym.symbol_make_newname (knd, name)
      in
        parse_tokenlst (knd, tpopt)
      end else begin
        $Loc.prerr_location tok.token_loc;
        prerr ": error(ATSYACC)";
        prerr ": the token is introduced repeatedly.";
        prerr_newline ();
        exit {void} (1)
      end // end of [if]
    end // end of [parse_tokenlst]
  | _ => ()
end // end of [parse_tokenlst] 

(* ****** ****** *)

fun parse_assoclst (assoc: int): void = let
  val tok = the_token_get ()
in
  case+ tok.token_node of
  | $Tok.TOKident name => let
      val () = the_token_update ()
      val knd = $Sym.SYMKINDterm ()
      val sym = $Sym.symbol_make_name (knd, name)
      val () = if $Sym.symbol_is_nonterm sym then begin
        $Loc.prerr_location tok.token_loc;
        prerr ": error(ATSYACC): the symbol [";
        prerr name;
        prerr "] is already introduced as a nonterminal.";
        prerr_newline ();
        exit {void} (1)
      end // end of [val]
      val () = $Sym.symbol_assoc_set (sym, assoc)
    in
      parse_assoclst (assoc)
    end // end of [parse_assoclst]
  | _ => ()
end // end of [parse_assoclst]

(* ****** ****** *)

fun parse_start (): void = let
  val tok = the_token_get ()
in
  case+ tok.token_node of
  | $Tok.TOKident name => let
      val () = the_token_update ()
      val knd = $Sym.SYMKINDnonterm ()
      val sym = $Sym.symbol_make_name (knd, name)
      val () = if $Sym.symbol_is_term sym then begin
        $Loc.prerr_location tok.token_loc;
        prerr ": error(ATSYACC): the symbol [";
        prerr name;
        prerr "] is already introduced as a terminal.";
        prerr_newline ();
        exit {void} (1)
      end // end of [val]
    in
      $Gra.the_start_symbol_set (sym)
    end // end of [TOKident]
  | _ => ()
end // end of [parse_start]

(* ****** ****** *)

fn name_is_leftassoc (name: string): bool =
  case+ name of
  | "%left" => true
  | "%leftassoc" => true
  | _ => false
// end of [name_is_leftassoc]

fn name_is_rightassoc (name: string): bool =
  case+ name of
  | "%right" => true
  | "%rightassoc" => true
  | _ => false
// end of [name_is_rightassoc]

fn parse_keyword_line (flag: &int): void = let
  val tok = the_token_get ()
in
  case+ tok.token_node of
  | $Tok.TOKkeyword name => let
      val () = flag := flag + 1
      val () = the_token_update ()
    in
      case+ name of
      | _ when (name = "%token") => let
          val otp = parse_typeopt ()
          val knd = $Sym.SYMKINDterm ()
        in
          parse_tokenlst (knd, otp)
        end // end of ["%token"]
      | _ when (name = "%nonassoc") => let
          val n = the_assocval_getinc () in
          parse_assoclst (3 * n)
        end
      | _ when (name_is_leftassoc name) => let
          val n = the_assocval_getinc () in
          parse_assoclst (3 * n + 1)
        end
      | _ when (name_is_rightassoc name) => let
          val n = the_assocval_getinc () in
          parse_assoclst (3 * n + 2)
        end
      | _ when (name = "%type") => let
          val tp = parse_type ()
          val knd = $Sym.SYMKINDnonterm ()
        in
          parse_tokenlst (knd, Some tp)
        end
      | _ when (name = "%start") => parse_start ()
      | _ => begin
          $Loc.prerr_location tok.token_loc;
          prerr ": error(ATSYACC)";
          prerr ": the keyword ["; prerr name; prerr "] is unrecognized.";
          prerr_newline ();
          exit {void} (1)
        end // end of [_]
    end // end of [TOKkeyword]
  | _ => ()
end // end of [parse_keyword_line]

(* ****** ****** *)

fun parse_identlst (): tokenlst_vt = let
  val tok = the_token_get () in case+ tok.token_node of
  | $Tok.TOKident _ => let
      val () = the_token_update () in
      list_vt_cons (tok, parse_identlst ())
    end // end of [TOKident]
  | _ => list_vt_nil ()
end // end of [parse_identlst]

fn parse_prec_ident (): tokenopt = let
  val tok0 = the_token_get () in case+ tok0.token_node of
  | $Tok.TOKkeyword "%prec" => let
      val tok1 = the_token_update_get () in
      case+ tok1.token_node of
      | $Tok.TOKident _ => let
          val () = the_token_update () in Some (tok1)
        end // end of [TOKident]
      | _ => begin
          $Loc.prerr_location tok1.token_loc;
          prerr ": error(ATSYACC)";
          prerr "the token should be an identifier but it is not.";
          prerr_newline ();
          exit {tokenopt} (1)
        end // end of [_]
    end // end of [TOKkeyword "%prec"]
  | _ => None ()
end // end of [parse_prec_ident]

fn parse_extcode (): tokenopt = let
  val tok = the_token_get () in case+ tok.token_node of
  | $Tok.TOKextcode _ => let
      val () = the_token_update () in Some (tok)
    end // end of [TOKextcode]
  | _ => None ()
end // end of [parse_extcode]

(* ****** ****** *)

viewtypedef prerulerhs = @(
  tokenlst_vt (*symseq*), tokenopt (*prec*), tokenopt (*extcode*)
) // end of [rulerhs]

viewtypedef prerulerhslst = List_vt (prerulerhs)

viewtypedef prerule = @($Sym.symbol_t, prerulerhslst)

viewtypedef prerulelst_vt = List_vt (prerule)
viewtypedef preruleopt_vt = Option_vt (prerule)

(* ****** ****** *)

fn parse_rulerhs (): prerulerhs = let
  val ids = parse_identlst ()
  val prec = parse_prec_ident ()
  val ext = parse_extcode ()
in
  @(ids, prec, ext)
end // end of [parse_rulerhs]

fun parse_rulerhslst (): prerulerhslst = let
  val tok = the_token_get () in case+ tok.token_node of
  | $Tok.TOKkeychar '|' => let
      val () = the_token_update ()
      val rhs = parse_rulerhs (); val rhss = parse_rulerhslst ()
    in
      list_vt_cons (rhs, rhss)
    end // end of [TOKkeychar '|']
  | $Tok.TOKkeychar ';' => let // ';' is optional
      val () = the_token_update () in list_vt_nil ()
    end // end of [TOKkeychar ';']
(*
  | _ => begin
      $Loc.prerr_location tok.token_loc;
      prerr ": error(ATSYACC)";
      prerr ": the token at should be a semicolon [;] but it is not.";
      prerr_newline ();
      exit {rulerhslst} (1)
    end // end of [_]
*)
  | _ => list_vt_nil ()
end // end of [parse_rulerhslst]

(* ****** ****** *)

fun parse_rule (): prerule = let
  val tok0 = the_token_get () in case+ tok0.token_node of
  | $Tok.TOKident name => let
      val knd = $Sym.SYMKINDnonterm ()
      val sym0 = $Sym.symbol_make_name (knd, name)
      val tok1 = the_token_update_get () in case+ tok1.token_node of
      | $Tok.TOKkeychar c
          when (c = ':' orelse c = '|') => let
          val () = the_token_update ()
          val rhs = parse_rulerhs (); val rhss = parse_rulerhslst ()
        in
          (sym0, list_vt_cons (rhs, rhss))
        end // end of [TOKkeychar when ...]
      | _ => begin
          $Loc.prerr_location tok1.token_loc;
          prerr ": error(ATSYACC)";
          prerr ": the token should be a colon [:] or a bar [|] but it is neither.";
          prerr_newline ();
          exit (1)
        end // end of [_]
    end // end of [TOKident]
  | _ => begin
      $Loc.prerr_location tok0.token_loc;
      prerr ": error(ATSYACC)";
      prerr ": the token should an identifer but it is not.";
      prerr_newline ();
      exit (1)
    end // end of [_]
end // end of [parse_rule]

fun parse_ruleopt (): preruleopt_vt = let
  val tok0 = the_token_get () in case+ tok0.token_node of
  | $Tok.TOKident _ => Some_vt (parse_rule ())
  | _ => None_vt ()
end // end of [parse_ruleopt]

(* ****** ****** *)

fn prerulerhs_process (
    nrhs: int, rhs: prerulerhs
  ) : $Gra.rulerhs_t = let
  val xs = rhs.0 and prec = rhs.1 and ext = rhs.2
  val nsym = list_vt_length<token> (xs)
  val asz = size1_of_int1 nsym // array size
  val symarr = array_make_arrsz {T}
    @(pf_gc, pf_arr | p_arr, asz) where {
    typedef T = symbol
    val (pf_gc, pf_arr | p_arr) =
      array_ptr_alloc<T> (asz) // end of [val]
    val () = loop (pf_arr | p_arr, xs) where {
      fun loop {n:nat} {l:addr} (
          pf: !array_v (T?, n, l) >> array_v (T, n, l)
        | p: ptr l, xs: list_vt (token, n)
        ) : void =
        case+ xs of
        | ~list_vt_cons (x, xs) => let
            val- $Tok.TOKident (name) = x.token_node
(*
            val () = begin
              prerr "prerulerhs_process: name = "; prerr name; prerr_newline ()
            end // end of [val]
*)
            val symopt = $Sym.symbol_find_name (name)
            val sym = (case+ symopt of
              | ~Some_vt sym => sym | ~None_vt () =>
                  $Sym.symbol_make_newname (knd, name) where {
(*
                  val () = begin
                    $Loc.prerr_location x.token_loc;
                    prerr ": warning(ATSYACC)";
                    prerr ": the symbol ["; prerr name;
                    prerr "] is nonterminal";
                    prerr ", but there are no production rules for it.";
                    prerr_newline ();
                  end // end of [None_vt]
*)
                  val knd = $Sym.SYMKINDnonterm ()
                } // end of [None_vt]
            ) : T // end of [val]
            prval (pf1, pf2) = array_v_uncons {T?} (pf)
            val () = !p := sym
            val () = loop (pf2 | p + sizeof<T>, xs)
          in
            pf := array_v_cons {T} (pf1, pf2)
          end // end of [list_vt_cons]
        | ~list_vt_nil () => let
            prval () = array_v_unnil {T?} (pf) in pf := array_v_nil ()
          end // end of [list_vt_nil]
      // end of [loop]
    } // end of [val]
  } (* end of [val symarr] *)
in
  $Gra.rulerhs_make (nrhs, nsym, symarr, prec, ext)
end // end of [prerulerhs_process]

fun prerulerhslst_process
  (nrhs_r: &int, rhss: prerulerhslst)
  : $Gra.rulerhslst = case+ rhss of
  | ~list_vt_cons (rhs, rhss) => let
      val nrhs = nrhs_r
      val () = nrhs_r := nrhs + 1
      val rhs = prerulerhs_process (nrhs, rhs)
      val rhss = prerulerhslst_process (nrhs_r, rhss)
    in
      list_cons (rhs, rhss)
    end // end of [list_vt_cons]
  | ~list_vt_nil () => list_nil ()
// end of [prerulerhslst_process]

(* ****** ****** *)

staload Q = "LIB/linqueuelst.dats"

(* ****** ****** *)

local

typedef rulelhsrhss =
  @($Sym.symbol_t, $Gra.rulerhslst)

viewtypedef rulelhsrhssque =
  [n:nat] $Q.linqueuelst_vt (rulelhsrhss, n)

val theRulelhsrhssqueRef =
  ref_make_elt<rulelhsrhssque> ($Q.linqueuelst_nil<> ())

in

fn the_rulelhsrhssque_insert
  (lhs: $Sym.symbol_t, rhss: $Gra.rulerhslst): void = let
  val (vbox pf | p) =
    ref_get_view_ptr (theRulelhsrhssqueRef) in
  $Q.linqueuelst_enqueue (!p, @(lhs, rhss))
end // end of [the_rulelhsrhssque_insert]

fn the_rulelhsrhssque_takeout (): List_vt (rulelhsrhss) = let
  val (vbox pf | p) =
    ref_get_view_ptr (theRulelhsrhssqueRef)
  val xs = !p; val () = !p := $Q.linqueuelst_nil<> ()
in
  $Q.list_vt_of_linqueuelst (xs)
end // end of [the_rulelhsrhssque_insert]

end

(* ****** ****** *)

implement the_rulelhsrhsslst_get () = begin
  list_of_list_vt (the_rulelhsrhssque_takeout ())
end // end of [the_rulelhsrhsslst_get]

(* ****** ****** *)

fn prerule_process
  (nrhs_r: &int, rl: prerule): void = let
  val lhs = rl.0 and rhss = rl.1
  val rhss = prerulerhslst_process (nrhs_r, rhss)
  val () = the_rulelhsrhssque_insert (lhs, rhss)
in
  // note that [postpend] is used here:
  $Gra.symbol_rulerhslst_postpend (lhs, rhss)
end // end of [val]

(* ****** ****** *)

extern fun the_preruleque_takeout (): prerulelst_vt
extern fun the_preruleque_insert (rl: prerule): void

local

viewtypedef preruleque =
  [n:nat] $Q.linqueuelst_vt (prerule, n)

val thePrerulequeRef =
  ref_make_elt<preruleque> ($Q.linqueuelst_nil<> ())

in // in of [local]

implement the_preruleque_insert (rl) = let
  val (vbox pf | p) =
    ref_get_view_ptr (thePrerulequeRef) in
  $Q.linqueuelst_enqueue (!p, rl)
end // end of [the_preruleque_insert]

implement the_preruleque_takeout () = let
  val (vbox pf | p) =
    ref_get_view_ptr (thePrerulequeRef)
  val xs = !p; val () = !p := $Q.linqueuelst_nil<> () in
  $Q.list_vt_of_linqueuelst (xs)
end // end of [the_preruleque_takeout]

end // end of [local]

(* ****** ****** *)

#define NRHS_FIRST 1

extern fun parse_main (): void

local

val thePreambleRef = ref_make_elt<tokenopt> (None)
val thePostambleRef = ref_make_elt<tokenopt> (None)

in // in of [local]

implement parse_main () = let
  val () = the_token_update () // flush out a junk value
  val () = let // processing preamble
    val tok = the_token_get () in case+ tok.token_node of
    | $Tok.TOKpreamble _ => let
        val () = the_token_update () in !thePreambleRef := Some tok
      end // end of [TOKpreamble]
    | _ => ()
  end // end of [val]

  val () = loop () where { // processing keyword lines
    fun loop (): void = let
      var flag: int = 0
      val () = parse_keyword_line (flag)
    in
      if flag > 0 then loop () else ()
    end // end of [loop]
  } // end of [val]

  val () = parse_percperc ()

  val () = loop () where { // processing production rules
    fun loop (): void = let
      val rlopt = parse_ruleopt ()
    in
      case+ rlopt of
      | ~Some_vt (rl) => let
          val () = the_preruleque_insert (rl) in loop ()
        end // end of [Some_vt]
      | ~None_vt () => () // loop exists
    end // end of [loop]
  } // end of [val]

  val () = let // processing postamble
    val tok = the_token_get () in case+ tok.token_node of
    | $Tok.TOKeof () => ()
    | $Tok.TOKpercperc () => let
        val tok = the_token_update_get () in
        case+ tok.token_node of
        | $Tok.TOKpostamble _ => let
            val () = the_token_update () in !thePostambleRef := Some tok
          end // end of [TOKpostamble]
        | _ => ()
      end // end of [TOKpercperc]
    | _ => ()
  end // end of [val]
  
  val () = let
    val tok = the_token_get ()
  in
    case+ tok.token_node of
    | $Tok.TOKeof () => () | _ => begin
        $Loc.prerr_location tok.token_loc;
        prerr ": error(ATSYACC)";
        prerr ": the token should have been consumed but it is not.";
        prerr_newline ();
      end // end of [_]
  end // end of [val]
  
  val () = () where { // processing the production rules
    val rls = the_preruleque_takeout ()
    val lhss0 = loop
      (nrhs_r, rls, list_vt_nil ()) where {
      fun loop (
          nrhs_r: &int, rls: prerulelst_vt, lhss: symlst_vt
        ) : symlst_vt = case+ rls of
        | ~list_vt_cons (rl, rls) => let
            val lhs = rl.0
            val () = prerule_process (nrhs_r, rl) in
            loop (nrhs_r, rls, list_vt_cons (lhs, lhss))
          end // end of [list_vt_cons]
        | ~list_vt_nil () => let
(*
            val () = begin
              prerr "The next number of rhs = "; prerr nrhs_r; prerr_newline ()
            end // end of [val]
*)
          in
            lhss // loop exists
          end // end of [list_vt_nil]
      // end of [loop]
      var nrhs_r: int = NRHS_FIRST
    } // end of [val]
    val lhss1 = loop (lhss0, list_nil ()) where {
      fun loop (
          lhss0: symlst_vt, lhss1: symlst
        ) : symlst = case+ lhss0 of
        | ~list_vt_cons (lhs, lhss0) =>
             loop (lhss0, list_cons (lhs, lhss1))
        | ~list_vt_nil () => lhss1
      // end of [loop]
    } // end of [val]
    val () = $Gra.the_rulelhslst_set (lhss1)
  } // end of [val]

// (*
  val () = begin
    prerrf ("The total number of terminals is %i\n", @(nsym))
  end where {
    val nsym = $Sym.symbol_term_total_get ()
  } // end of [val]

  val () = begin
    prerrf ("The total number of nonterminals is %i\n", @(nsym))
  end where {
    val nsym = $Sym.symbol_nonterm_total_get ()
  } // end of [val]
// *)

in
  // empty
end // end of [parse_main]

end // end of [local]

(* ****** ****** *)

staload LEXING = "libats/lex/lexing.sats"

implement parse_from_filename (filename) = let
(*
  val () = begin
    prerr "parse_from_filename: "; prerr filename; prerr_newline ()
  end // end of [val]
*)
  val file_mode_r = $extval (file_mode r, "\"r\"")
  val (pf_fil | p_fil) =
    $STDIO.fopen_exn (filename, file_mode_r)
  val (pf_infil | p_infil) =
    $LEXING.infile_make_file (pf_fil, file_mode_lte_r_r | p_fil)
  val (pf_lexbuf | lexbuf) =
    $LEXING.lexbuf_make_infile (pf_infil | p_infil)
  val () = $LEXING.lexing_lexbuf_set (pf_lexbuf | lexbuf)
  val ans = parse_main ()
in
  $LEXING.lexing_lexbuf_free (); ans
end // end of [parse_from_filename]

implement parse_from_stdin () = let
  val (pf_infil | p_infil) =
    $LEXING.infile_make_stdin ()
  val (pf_lexbuf | lexbuf) =
    $LEXING.lexbuf_make_infile (pf_infil | p_infil)
  val () = $LEXING.lexing_lexbuf_set (pf_lexbuf | lexbuf)
  val ans = parse_main ()
in
  $LEXING.lexing_lexbuf_free (); ans
end // end of [parse_from_stdin]

(* ****** ****** *)

(* end of [parser.dats] *)
