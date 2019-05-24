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
#include "contrib/linux/linux/CATS/fs.cats"
%} // end of [%{#]

(* ****** ****** *)

staload "contrib/linux/basics.sats"

(* ****** ****** *)

staload TYPES = "contrib/linux/linux/SATS/types.sats"
typedef dev_t = $TYPES.dev_t
typedef fmode_t = $TYPES.fmode_t
typedef loff_t = $TYPES.loff_t
//
typedef uid_t = $TYPES.uid_t
typedef gid_t = $TYPES.gid_t
//
typedef uint64= $TYPES.uint64

(* ****** ****** *)

viewtypedef
inode_struct =
$extype_struct "inode_struct" of {
  empty= empty
(*
, i_count= atomic_t
*)
, i_nlink= uint
, i_uid= uid_t
, i_gid= gid_t
, i_rdev= dev_t
, i_blkbits= uint
, i_version= uint64
, i_size= loff_t
//
, i_state= ulint
, dirtied_when= ulint (* jiffies or first dirtying *)
, i_flags= uint
//
, _rest= undefined_vt
} // end of [inode]
viewtypedef inode = inode_struct

(*
//
// HX: it is in cdev.sats
//
fun inode_get_i_cdev
  (inode: &inode): [l:agz] (cdev_ref (l) -<lin,prf> void | cdev_ref (l))
// end of [inode_get_i_cdev]
*)

(* ****** ****** *)

absview inode_v (l:addr)
prfun inode_v_takeout
  : {l:addr} ftakeout (inode_v l, inode @ l)
// end of [inode_v_takeout]

//
// HX-2011-03-18: [ref] means ref-counted
//
absviewtype inode_ref (l:addr) = ptr
viewtypedef inode_ref0 = [l:agez] inode_ref (l)
viewtypedef inode_ref1 = [l:addr | l > null] inode_ref (l)
//
prfun
inode_ref_unfold
  {l:agz} (
  x: !inode_ref (l) >> ptr l
) : (
  inode_v l | void
) // end of [inode_ref_unfold]
//
prfun
inode_ref_fold
  {l:addr} (
  pf: inode_v l | x: !ptr l >> inode_ref l
) : void // end of [inode_ref_fold]
//
castfn ptr_of_inode {l:addr} (x: inode_ref (l)):<> ptr (l)
overload ptr_of with ptr_of_inode
//
(* ****** ****** *)

viewtypedef
file_struct =
$extype_struct "file_struct" of {
  empty= empty
(*
, f_count= atomic_long_t
*)
, f_flags= uint
, f_mode= fmode_t
, f_pos= loff_t
} // end of [file_struct]
viewtypedef file = file_struct

(* ****** ****** *)

viewtypedef
super_block =
$extype_struct "super_block_struct" of {
  empty= empty
, s_dev= dev_t
, s_blocksize= ulint
, s_blocksize_bits= uchar
, s_dirt= uchar
, s_maxbytes= ullint
, _rest= undefined_vt
} // end of [super_block]

(* ****** ****** *)

fun new_inode (
  sb: &super_block
) : inode_ref0 = "mac#atsctrb_linux_new_inode"
// end of [new_inode]

(* ****** ****** *)

(* end of [fs.sats] *)
