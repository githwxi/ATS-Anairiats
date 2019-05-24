(*
** HX: this is a standard way to do systems programming in ATS
*)

(* ****** ****** *)

%{#
#define FUSE_USE_VERSION 26
#include "prelude/CATS/basics.cats"
#include "prelude/CATS/bool.cats"
#include "prelude/CATS/char.cats"
#include "prelude/CATS/integer.cats"
#include "prelude/CATS/pointer.cats"
#include "prelude/CATS/sizetype.cats"
#include "prelude/CATS/string.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staloading at run-time

(* ****** ****** *)

(* end of [myheader.sats] *)
