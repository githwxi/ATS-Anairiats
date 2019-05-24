/*
** HFUSE: FUSE file system (modular) for AWS S3
** Mark Reynolds
*/

(* ****** ****** *)

(*
** HX: adapting Mark's C code to ATS
*)

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staloading at run-time

(* ****** ****** *)

staload TYPES = "libc/sys/SATS/types.sats"
typedef dev_t = $TYPES.dev_t
typedef mode_t = $TYPES.mode_t

(* ****** ****** *)

staload "contrib/FUSE/SATS/fuse.sats"

(* ****** ****** *)

absview hfuselog_v
fun hfuselog_lock ():<> (hfuselog_v | void)
fun hfuselog_unlock (pf: hfuselog_v | (*none*)):<> void

(* ****** ****** *)

fun tfprintf {ts:types}
  (pf: !hfuselog_v | fmt: printf_c (ts), arg: ts): int = "tfprintf"
// end of [tfprintf]

(* ****** ****** *)

fun dologtime(pf: !hfuselog_v | (*none*)): void  = "dologtime"

(* ****** ****** *)

fun parts {n:pos} (
  path: string n, n: size_t n
, bname: &strptr0? >> strptr0, rname: &strptr0? >> strptr0
) : void = "parts"

(* ****** ****** *)

fun hfuse_open (path: string, fi: &fuse_file_info): int = "hfuse_open"

(* ****** ****** *)

fun hfuse_read
  {n1,n2:nat | n2 <= n1} {l:addr} (
    pf: !bytes n1 @ l
  | path: string, p_buf: ptr l, size: size_t n2, ofs: off_t, fi: &fuse_file_info
) : int = "hfuse_read"

(* ****** ****** *)

fun hfuse_release
  (path: string, fi: &fuse_file_info): int = "hfuse_release"
// end of [hfuse_release]

(* ****** ****** *)

fun hfuse_create
  (path: string, mode: mode_t, fi: &fuse_file_info): int = "hfuse_create"
// end of [hfuse_create]

(* ****** ****** *)

fun hfuse_mknod
  (path: string, mode: mode_t, dev: dev_t): int = "hfuse_mknod"
// end of [hfuse_mknod]

(* ****** ****** *)

fun hfuse_unlink (path: string): int = "hfuse_unlink"

(* ****** ****** *)

(* end of [hfuse.sats] *)
