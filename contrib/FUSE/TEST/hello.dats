/*
    FUSE: Filesystem in Userspace
    Copyright (C) 2001-2005  Miklos Szeredi <miklos@szeredi.hu>

    This program can be distributed under the terms of the GNU GPL.
    See the file COPYING.
*/

(* ****** ****** *)

//
// Modified from C into ATS by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%} // end of [%{^]

(* ****** ****** *)

staload "myheader.sats"
staload "libc/SATS/errno.sats"
staload "libc/SATS/fcntl.sats"
staload "libc/SATS/printf.sats"
staload "libc/SATS/stdarg.sats"
staload "libc/SATS/stdio.sats"
staload "libc/SATS/string.sats"
staload "libc/sys/SATS/stat.sats"
staload "libc/sys/SATS/types.sats"

staload "contrib/FUSE/SATS/fuse.sats"

(* ****** ****** *)

%{^
static char *hello_str = "Hello, world!\n" ;
static char *hello_path = "/hello" ;
%} // end of [%{^]
extern val hello_str : string = "mac#hello_str"
extern val hello_path : string = "mac#hello_path"

(* ****** ****** *)

absview hellolog_v

%{^
#include <pthread.h>
static pthread_mutex_t
theMutex_hellolog = PTHREAD_MUTEX_INITIALIZER ;
ats_void_type
hellolog_lock () {
  (void)pthread_mutex_lock (&theMutex_hellolog) ; return ;
} // end of [hellolog_lock]
ats_void_type
hellolog_unlock () {
  (void)pthread_mutex_unlock (&theMutex_hellolog) ; return ;
} // end of [hellolog_unlock]
%} // end of [{%{^]
extern
fun hellolog_lock ():<> (hellolog_v | void) = "mac#hellolog_lock"
extern
fun hellolog_unlock (pf: hellolog_v | (*none*)):<> void = "mac#hellolog_unlock"

(* ****** ****** *)

#define LOGFILENAME "/tmp/hello_log"

extern
fun hellolog_reset
  (pflock: !hellolog_v | (*none*)): int = "hellolog_reset"
implement
hellolog_reset
  (pflock | (*none*)) = let
  var res: int = 0
  val (pfopt | p) = fopen_err (LOGFILENAME, file_mode_w)
  val () = (
//
if p > null then let
  prval Some_v (pf) = pfopt
  val _err = fclose1_loop (pf | p) // HX: error is ignored if there is one
in
  // nothing
end else let
  prval None_v () = pfopt
  val () = res := ~1
in
  // nothing
end // end of [if]
//
  ) : void // end of [val]
in
  res
end // end of [hellolog_reset]

(* ****** ****** *)

extern
fun tfprintf {ts:types}
  (pf: !hellolog_v | fmt: printf_c (ts), arg: ts): int = "tfprintf"
implement
tfprintf
  (pflock | fmt, arg) = let
  val (pfopt | p) = fopen_err (LOGFILENAME, file_mode_aa)
  val ntot = (
//
if p > null then let
  prval Some_v (pf) = pfopt
  // [va_start (arg, fmt)] is emitted by 'atsopt'
  val ntot = vfprintf (file_mode_lte_rw_w | !p, fmt, arg)
//
  val _err = fclose1_loop (pf | p) // HX: error is ignored if there is one
//
in
  ntot
end else let
  prval None_v () = pfopt
  prval () = va_clear (arg)
in
  0 // nothing is output
end // end of [if]
//
  ) : int // end of [val]
  val () = va_end (arg)
in
  ntot // the number of bytes in the output
end // end of [tfprintf]

(* ****** ****** *)

/*
static
int hello_getattr (
  const char *path, struct stat *stbuf
) {
    int res = 0;
//
    memset (stbuf, 0, sizeof(struct stat));
//
    if (strcmp(path, "/") == 0) {
      stbuf->st_mode = (S_IFDIR | 0755) ;
      stbuf->st_nlink = 2 ;
    } else if (strcmp(path, hello_path) == 0) {
      stbuf->st_mode = (S_IFREG | 0444) ;
      stbuf->st_nlink = 1 ;
      stbuf->st_size = strlen (hello_str) ;
    } else {
      res = -ENOENT;
    } // end of [if]
//
    return res;
} // end of [hello_getattr]
*/
extern
fun hello_getattr (
  path: string, stbuf: &stat? >> opt (stat, i==0)
) : #[i:int | i <= 0] int i = "hello_getattr"
implement
hello_getattr
  (path, stbuf) = let
  var res: int = 0
  val () = ptr_zero_tsz {stat} (
    __assert () | stbuf, sizeof<stat>
  ) where {
    extern praxi __assert (): NULLABLE (stat)
  } // end of [val]
in
  case+ 0 of
  | _ when (
      path = "/"
    ) => res where {
      val _0755 = mode_of_uint (0755U)
      val () = stbuf.st_mode := (S_IFDIR lor _0755)
      val _2 = nlink_of_int (2)
      val () = stbuf.st_nlink := _2
      prval () = opt_some {stat} (stbuf)
    } // end of [_ when ...]
  | _ when (
      path = hello_path
    )  => res where {
      val _0444 = mode_of_uint (0444U)
      val () = stbuf.st_mode := (S_IFREG lor _0444)
      val _1 = nlink_of_int (1)
      val () = stbuf.st_nlink := _1
      val n = string0_length (hello_str)
      val () = stbuf.st_size := off_of_size (n)
      prval () = opt_some {stat} (stbuf)
    } // end of [_ when ...]
  | _ => res where {
      val () = res := ~int_of(ENOENT)
      prval () = __assert (res) where {
        extern prfun __assert {i:int} (x: int i): [i < 0] void
      } // end of [prval]
      prval () = opt_none {stat} (stbuf)
    } // end of [_]
end // end of [hello_getattr]

(* ****** ****** *)

/*
%{^
static
int hello_readdir (
  const char *path
, void *buf
, fuse_fill_dir_t filler
, off_t offset
, struct fuse_file_info *fi
) {
  (void)offset; (void)fi;
  if (strcmp(path, "/") != 0) return -ENOENT;
  filler (buf, ".", NULL, 0) ;
  filler (buf, "..", NULL, 0) ;
  filler (buf, hello_path + 1, NULL, 0) ;
  return 0;
} // end of [hello_readdir]
%}
*/
extern
fun hello_readdir (
  path: string
, buf: ptr, filler: fuse_fill_dir_t, ofs: off_t
, fi: &fuse_file_info
) : int = "hello_readdir" // 0/1: succ/fail
implement
hello_readdir (
  path, buf, filler, ofs, fi
) = let
//
  val (pflock | ()) = hellolog_lock ()
  val _err = tfprintf (pflock | "hello_readdir: path = \"%s\"\n", @(path))
  val () = hellolog_unlock (pflock | (*none*))
//
  var res: int = 0
  val () = while (true) let
    val test = (path = "/")
    val () = if ~test then
      (res := ~int_of(ENOENT); break)
    val filler = __cast (filler) where {
      // HX: [off_t] cannot be changed to [int]!!!
      extern castfn __cast (x: fuse_fill_dir_t): (ptr, string, ptr, off_t) -> int
    } // end of [val]
    val _0 = (off_of_lint)0L
    val _err = filler (buf, ".", null, _0)
    val _err = filler (buf, "..", null, _0)
    val hpath1 = __tail (hello_path) where {
      extern fun __tail (x: string):<> string = "atspre_psucc"
    } // end of [val]
    val _err = filler (buf, hpath1, null, _0)
  in
    break
  end // end of [val]
//
  val (pflock | ()) = hellolog_lock ()
  val _err = tfprintf (pflock | "hello_readdir: res = %i\n", @(res))
  val () = hellolog_unlock (pflock | (*none*))
//
in
  res (* 0/neg : succ/fail *)
end // end of [hello_readdir]

(* ****** ****** *)

/*
static
int hello_open (
  const char *path
, struct fuse_file_info *fi
) {
//
    if (strcmp(path, hello_path)) return -ENOENT ;
//
    if ((fi->flags & 3) != O_RDONLY) return -EACCES ;
//
    return 0;
//
} // end of [hello_open]
*/
extern
fun hello_open
  (path: string, fi: &fuse_file_info): int = "sta#hello_open"
// end of [hello_open]
implement
hello_open (path, fi) = let
  var res: int = 0
  val () = while (true) let
    val test =  path = hello_path
    val () = if ~test then (res := ~(int_of)ENOENT; break)
    val test = ((fi.flags land 0x3U) = (uint_of)O_RDONLY)
    val () = if ~test then (res := ~(int_of)EACCES; break)
  in
    break
  end // end of [val]
in
  res (* 0/neg : succ/fail *)
end // end of [hello_open]

(* ****** ****** *)

/*
static
int hello_read (
  const char *path
, char *buf
, size_t size
, off_t offset
, struct fuse_file_info *fi
) {
    size_t len; (void) fi;
//
    if (strcmp(path, hello_path) != 0) return -ENOENT;
//
    len = strlen (hello_str);
//
    if (offset < len) {
      if (offset + size > len) size = len - offset;
      memcpy (buf, hello_str + offset, size);
    } else
      size = 0;
    // end of [if]
//
    return size;
} // end of [hello_read]
*/
//
// HX-2010-09-30:
// this is really an overkill, but the idea is demonstrated ...
//
extern
fun hello_read_main {n1,n2:nat} {l:addr} (
  pf: !bytes n1 @ l
| path: string
, p_buf: ptr l, n1: size_t n1, ofs: size_t n2
, fi: &fuse_file_info
) : sizeLte (n1) = "hello_read_main"
implement
hello_read_main {n1,n2}
  (pf | path, p_buf, n1, ofs, fi) = let
  val [len:int] str = (string1_of_string)hello_str
  val len = string1_length (str)
in
//
if ofs <= len then let
  stavar len1: int
  val len1: size_t (len1) = min (n1, len-ofs)
  val (pf_ofs, fpf_ofs | p_ofs) = __takeout (str, ofs) where {
     extern fun __takeout
       {n2 + len1 <= len} (
       x: string len, ofs: size_t n2
     ) :<> [l_ofs:addr] (
       bytes len1 @ l_ofs, bytes len1 @ l_ofs -<lin,prf> void | ptr l_ofs
     ) = "mac#atspre_padd_size"
     // end of [__takeout]
  } // end of [val]
  val _err = memcpy (pf | p_buf, !p_ofs, len1)
  var i: natLte len1
  #define b2c char_of_byte
  #define c2b byte_of_char
  val () = for (i := 0; i < len1; i := i+1) let
    val c = b2c(p_buf->[i]) in p_buf->[i] := c2b (char_toupper(c)) // turning into uppercase
  end // end of [val]
  prval () = fpf_ofs (pf_ofs)
in
  len1
end else (size1_of_int1)0
//
end // end of [hello_read_main]
extern
fun hello_read {n:nat} {l:addr} (
    pf: !bytes n @ l
  | path: string, p_buf: ptr l, n: size_t n, ofs: off_t, fi: &fuse_file_info
) : int = "hello_read"
implement hello_read
  (pf | path, p_buf, n, ofs, fi) = let
  var res: errno_t = ENONE
  val () = if res = ENONE then (
    if (path <> hello_path) then res := ENOENT
  ) // end of [if]
  val ofs = lint_of_off (ofs)
  val () = if res = ENONE then (if ofs < 0L then res := EINVAL)
  val ofs = ulint_of_lint (ofs)
  val ofs = size_of_ulint (ofs)
  val ofs = size1_of_size (ofs)
in
  if res = ENONE then
    int_of_size(hello_read_main (pf | path, p_buf, n, ofs, fi))
  else ~int_of_errno(res)
end // end of [hello_read]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$

static
struct fuse_operations
hello_oper = {
  .getattr= (fuse_getattr_t)hello_getattr,
  .readdir= (fuse_readdir_t)hello_readdir,
  .open= (fuse_open_t)hello_open,
  .read= (fuse_read_t)hello_read,
} ; // end of [fuse_operations]

ats_void_type
mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  (void)hellolog_reset () ;
  fuse_main (argc, (char**)argv, &hello_oper, NULL) ;
  return ;
} // end of [mainats]
%} // end of [%{$]

(* ****** ****** *)

(* end of [hello.dats] *)
