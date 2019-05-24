(*
**
** For documenting the grammar of ATS
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Sylvain Nahas (sylvain.nahas AT googlemail DOT com)
**
** Time: November, 2010
**
*)

(* ****** ****** *)

staload _(*anon*) =
  "prelude/DATS/reference.dats"
// end of [staload]

(* ****** ****** *)

staload "atsgrammar.sats"

(* ****** ****** *)

assume
tyname = '{
  tyname_nam= Stropt, tyname_def= Stropt
} // end of [tyname]

(* ****** ****** *)

implement
theTynameNone = '{
  tyname_nam= stropt_none, tyname_def= stropt_none
} // end of [theTynameNone]

(* ****** ****** *)

implement
tyname_make_namdef
  (nam, def) = let
  val nam = string1_of_string (nam)
  val def = string1_of_string (def)
in '{
  tyname_nam= stropt_some (nam), tyname_def= stropt_some (def)
} end // end of [tyname_make_string]

(* ****** ****** *)

implement tyname_is_some (x) = stropt_is_some (x.tyname_nam)
implement tyname_get_nam (x) = x.tyname_nam
implement tyname_get_def (x) = x.tyname_def

(* ****** ****** *)

implement
fprint_tyname (out, x) = let
  val nam = x.tyname_nam
in
  if stropt_is_some (nam) then let
    val nam = stropt_unsome (nam) in fprint_string (out, nam)
  end else ()
end // end of [fprint_tyname]

implement print_tyname (x) = fprint_tyname (stdout_ref, x)
implement prerr_tyname (x) = fprint_tyname (stderr_ref, x)

(* ****** ****** *)

(* end of [atsgrammar_tyname.dats] *)
