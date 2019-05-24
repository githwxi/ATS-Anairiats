(*
**
** An interface
** for ATS to interact with FUSE (fuse.sourceforge.net)
**
** Contributed by Zhiqian Ren (aren AT cs DOT bu DOT edu)
** Contributed by Mark Reynolds (markreyn AT cs DOT bu DOT edu)
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** Start Time: September, 2010
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

%{#
#include "contrib/FUSE/CATS/fuse.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staloading at run-time

(* ****** ****** *)

#include "contrib/FUSE/SATS/fuse_common.sats"

(* ****** ****** *)

staload STAT = "libc/sys/SATS/stat.sats"
typedef stat = $STAT.stat
staload TYPES = "libc/sys/SATS/types.sats"
typedef off_t = $TYPES.off_t

(* ****** ****** *)

absviewt@ype
fuse_struct = $extype"ats_fuse_type"
viewtypedef fuse = fuse_struct // HX: creating a shorthand

(* ****** ****** *)

typedef
fuse_fill_dir_t = (ptr, string, &stat, off_t) -> int
// end of [fuse_fill_dir_t]

(* ****** ****** *)

(* end of [fuse.sats] *)
