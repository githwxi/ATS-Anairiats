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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
**
*)

(* ****** ****** *)

// February 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload Loc = "location.sats"

(* ****** ****** *)

staload "token.sats"

(* ****** ****** *)

implement token_none_make () = '{
  token_loc= $Loc.location_none, token_node= TOKeof
}

implement token_eof_make (loc) = '{
  token_loc=loc, token_node= TOKeof ()
}

implement token_extcode_make (loc, code) = '{
  token_loc=loc, token_node= TOKextcode (code)
}

implement token_ident_make (loc, name) = '{
  token_loc=loc, token_node= TOKident (name)
}

implement token_keychar_make (loc, name) = '{
  token_loc=loc, token_node= TOKkeychar (name)
}

implement token_keyword_make (loc, name) = '{
  token_loc=loc, token_node= TOKkeyword (name)
}

implement token_percperc_make (loc) = '{
  token_loc=loc, token_node= TOKpercperc ()
}

implement token_preamble_make (loc, code) = '{
  token_loc=loc, token_node= TOKpreamble (code)
}

implement token_postamble_make (loc, code) = '{
  token_loc=loc, token_node= TOKpostamble (code)
}

implement token_ptbrackstr_make (loc, code) = '{
  token_loc=loc, token_node= TOKptbrackstr (code)
}

(* ****** ****** *)

implement fprint_token (pf | out, tok) = let
  macdef strpr (str) = fprint1_string (pf | out, ,(str))
in
  case+ tok.token_node of
  | TOKextcode _ => strpr "TOKextcode(...)"
  | TOKident name => begin
      strpr "TOKident("; fprint1_string (pf | out, name); strpr ")"
    end // end of [TOKident]
  | TOKkeychar name => begin
      strpr "TOKkeychar("; fprint1_char (pf | out, name); strpr ")"
    end // end of [TOKkeyword]
  | TOKkeyword name => begin
      strpr "TOKkeyword("; fprint1_string (pf | out, name); strpr ")"
    end // end of [TOKkeyword]
  | TOKpercperc () => strpr "TOKpercperc()"
  | TOKpostamble _ => strpr "TOKpostamble(...)"
  | TOKpreamble _ => strpr "TOKpreamble(...)"
  | TOKptbrackstr (name) => begin
      strpr "TOKptbrackstr("; fprint1_string (pf | out, name); strpr ")"
    end // end of [TOKptbrackstr]
  | TOKeof () => strpr "TOKeof()"
end // end of [fprint_token]

implement print_token (tok) = print_mac (fprint_token, tok)
implement prerr_token (tok) = prerr_mac (fprint_token, tok)

(* ****** ****** *)

viewtypedef charlst_vt (n:int) = list_vt (c1har, n)

(* ****** ****** *)

(* end of [atsyacc_token.dats] *)
