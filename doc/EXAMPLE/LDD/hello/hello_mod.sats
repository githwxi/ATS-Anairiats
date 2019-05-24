//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0

(* ****** ****** *)

%{#
//
#include "contrib/linux/include/ats_types.h"
#include "contrib/linux/include/ats_basics.h"
//
// for handling a call like: printk (KERN_INFO "...")
//
#ifdef ATSstrcst
#undef ATSstrcst
#endif
#define ATSstrcst(x) x
//

%} // end of [%{#]

(* ****** ****** *)

(* end of [hello_mod.sats] *)
