/*
** HFUSE: FUSE file system (modular) for AWS S3
** Mark Reynolds
*/

(* ****** ****** *)

(*
** HX-2010-10-01: adapting Mark's C code to ATS
*)

(* ****** ****** *)

staload "myheader.sats"
staload "libc/SATS/errno.sats"
staload "libc/SATS/printf.sats"
staload "libc/SATS/stdarg.sats"
staload "libc/SATS/stdio.sats"
staload "libc/sys/SATS/types.sats"

(* ****** ****** *)

staload "hfuse.sats"

(* ****** ****** *)

%{^
#include "personality.h"
#define F_SIZEval (*f_sizep)
#define F_READval (*f_readp)
#define F_WRITEval (*f_writep)
#define F_UNLINKval (*f_unlinkp)
%} // end of [%{^]

extern
fun F_SIZE {l1,l2:addr}
  (b: !strptr l1, r: !strptr l2): int = "#F_SIZEval"
extern
fun F_READ {n1,n2:nat | n2 <= n1} {l:addr} (
  pfbuf: !bytes(n1) @ l
| b: !strptr0, rest: !strptr0, pbuf: ptr l, ofs: off_t, nbyte: size_t n2
) : int = "#F_READval"
extern
fun F_WRITE {n1,n2:nat | n2 <= n1} {l:addr} (
  pfbuf: !bytes(n1) @ l
| b: !strptr0, rest: !strptr0, pbuf: ptr l, nbyte: size_t n2
) : int = "#F_WRITEval"
extern
fun F_UNLINK
  (b: !strptr0, rest: !strptr0): int = "#F_UNLINKval"
// end of [F_UNLINK]

(* ****** ****** *)

%{^
#include <pthread.h>
static pthread_mutex_t
theMutex_hfuselog = PTHREAD_MUTEX_INITIALIZER ;
ats_void_type
hfuselog_lock () {
  (void)pthread_mutex_lock (&theMutex_hfuselog) ; return ;
} // end of [hfuselog_lock]
ats_void_type
hfuselog_unlock () {
  (void)pthread_mutex_unlock (&theMutex_hfuselog) ; return ;
} // end of [hfuselog_unlock]
%} // end of [{%{^]
(*
extern
fun hfuselog_lock ():<> (hfuselog_v | void) = "#hfuselog_lock"
extern
fun hfuselog_unlock (pf: hfuselog_v | (*none*)):<> void = "#hfuselog_unlock"
*)

(* ****** ****** *)

/*
static int tfprintf(const char *fmt, ...)
{
  va_list ap;
  FILE *fout;
  int   r = 0;

  pthread_mutex_lock(&mutex);
  va_start(ap, fmt);
  fout = fopen("/var/log/hfuselog", "a+");
  if ( fout != NULL )
    {
      r = vfprintf(fout, fmt, ap);
      (void)fclose(fout);
    }
  va_end(ap);
  pthread_mutex_unlock(&mutex);
  return r;
}
*/
implement
tfprintf
  (pflock | fmt, arg) = let
  val (pfopt | p) = fopen_err ("/var/log/hfuselog", file_mode_aa)
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
static void dologtime(void)
{
  memset((void *)&ts, 0, sizeof(ts));
  if ( clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts) >= 0 )
    tfprintf("TIME: %d %ld\n", ts.tv_sec, ts.tv_nsec);
}
*/

(* ****** ****** *)

/*
static int parts(const char *path, char **bname, char **rname)
{
  const char *sla;
  const char *p;
  int   leen;

  if ( path == NULL || path[0] == 0 || bname == NULL || rname == NULL )
    return -EINVAL;
  *bname = NULL;
  *rname = NULL;
  if ( strcmp(path, "/") == 0 )
    return 0;
  p = path+1;
  sla = strchr(p, '/');
  if ( sla == NULL )
    {
      *bname = strdup(p);
      return 0;
    }
  leen = (int)(sla - p);
  *bname = (char *)calloc(leen+1, sizeof(char));
  if ( *bname != NULL )
    memcpy(*bname, p, leen);
  *rname = strdup(sla+1);
  return 0;
}
*/
implement
parts {n} (
  path, n, bname, rname
) = let
  // nothing
in
  case+ 0 of
  | _ when n >= 2 => let
      val path1 = __tail (path) where {
        extern fun __tail
          (x: string n):<> string (n-1) = "atspre_psucc"
      } // end of [val]
      val n1 = n - 1
      val n2 = string_index_of_char_from_left (path1, '/')
    in
      if n2 >= 0 then let
        val n2 = size1_of_ssize1 (n2)
        val sbuf = string_make_substring (path1, 0, n2)
        val () = bname := strptr_of_strbuf (sbuf)
        val sbuf = string_make_substring (path1, n2+1, n1-n2-1)
        val () = rname := strptr_of_strbuf (sbuf)
      in
        // nothing
      end else let (* not found *)
        val sbuf = string_make_substring (path1, 0, n1)
        val () = bname := strptr_of_strbuf (sbuf)
        val () = rname := strptr_null ()
      in
        // nothing
      end // end of [if]
    end // end of [_ when ...]
  | _ (*n = 1*) => let
      val () = bname := strptr_null ()
      val () = rname := strptr_null ()
    in
      // nothing
    end // end of [_]
end // end of [parts]

(* ****** ****** *)

/*
static
int hfuse_open (
  const char *path
, struct fuse_file_info *fi
) {
  tfprintf("open(%s, 0x%x)\n", path, fi->flags);
  dologtime();
  tfprintf("open success\n");
  dologtime();
  return 0;
}
*/
implement
hfuse_open
  (path, fi) = 0 where {
//
  val (pflock | ()) = hfuselog_lock ()
  val _err = tfprintf (pflock | "open(%s, 0x%x)\n", @(path, fi.flags))
  val _err = dologtime (pflock | (*none*))
  val () = hfuselog_unlock (pflock | (*none*))
//
  val (pflock | ()) = hfuselog_lock ()
  val _err = tfprintf(pflock | "open success\n", @())
  val _err = dologtime (pflock | (*none*))
  val () = hfuselog_unlock (pflock | (*none*))
//
} // end of [hfuse_open]

(* ****** ****** *)

/*
static int hfuse_read(const char *path, char *buf, size_t size, off_t offset,
		      struct fuse_file_info *fi)
{
  char  *b = NULL;
  char  *rest = NULL;
  size_t len;
  int    res;

  UNREF(fi);
  tfprintf("read(%s, 0x%x, %d, %d)\n", path, buf, size, offset);
  dologtime();
  res = parts(path, &b, &rest);
  if ( res < 0 )
    return res;
  res = (*f_sizep)(b, rest);
  if ( res < 0 )
    {
      if ( b != NULL )
	free((void *)b);
      if ( rest != NULL )
	free((void *)rest);
      return res;
    }
  len = (size_t)res;
  res = 0;
  if ( offset < len )
    {
      if ( (offset + size) > len)
	size = len - offset;
      res = (*f_readp)(b, rest, buf, offset, size);
    }
  else {} // do nothing
  if ( b != NULL )
    free((void *)b);
  if ( rest != NULL )
    free((void *)rest);
  tfprintf("read success\n");
  dologtime();
  return res;
}
*/
implement
hfuse_read (
  pfbuf | path, pbuf, size, ofs, fi
) = let
//
  val (pflock | ()) = hfuselog_lock ()
  val _err = tfprintf
    (pflock | "read(%s, 0x%p, %ld, %ld)\n", @(path, pbuf, _size, _ofs)) where {
    val _ofs = lint_of_off (ofs)
    val _size = lint_of_size (size)
  } // end of [val]
  val _err = dologtime (pflock | (*none*))
  val () = hfuselog_unlock (pflock | (*none*))
//
  var res: int = 0
  val [n:int] path = string1_of_string (path)
  val () =
//
while (true) let
  val n = string1_length (path)
  val () = (if (n = 0) then
    (res := ~(int_of)EINVAL; break; assertfalse())
  ) : [n>0] void
  var b: strptr0 and rest: strptr0
  val () = parts (path, n, b, rest)
  val () =
//
while (true) let
  val () = res := F_SIZE (b, rest)
  val () = if (res < 0) then break
  val () = res := F_READ (pfbuf | b, rest, pbuf, ofs, size)
  val () = if (res < 0) then break
in
  break
end // end of [while]
//
  val () = strptr_free (b) and () = strptr_free (rest)
in
  break
end // end of [while]
//
  val () = if res >= 0 then let
    val (pflock | ()) = hfuselog_lock ()
    val _err = tfprintf(pflock | "read success: res = %i\n", @(res))
    val _err = dologtime (pflock | (*none*))
    val () = hfuselog_unlock (pflock | (*none*))
  in
    // nothing
  end // end of [val]
in
  res
end // end of [hfuse_read]

(* ****** ****** *)

implement
hfuse_release
  (path, fi) = 0 where {
//
  val (pflock | ()) = hfuselog_lock ()
  val _err = tfprintf (pflock | "release(%s)\n", @(path))
  val _err = dologtime (pflock | (*none*))
  val () = hfuselog_unlock (pflock | (*none*))
//
  val (pflock | ()) = hfuselog_lock ()
  val _err = tfprintf(pflock | "release success\n", @())
  val _err = dologtime (pflock | (*none*))
  val () = hfuselog_unlock (pflock | (*none*))
//
} // end of [hfuse_release]

(* ****** ****** *)

/*
static int hfuse_create(const char *path, mode_t mode,
			struct fuse_file_info *fi)
{
  char *b = NULL;
  char *rest = NULL;
  char  dum;
  int   res;

  tfprintf("create(%s, 0%o)\n", path, mode);
  dologtime();
  res = parts(path, &b, &rest);
  if ( res < 0 )
    return res;
  res = (*f_writep)(b, rest, &dum, 0);
  if ( b != NULL )
    free((void *)b);
  if ( rest != NULL )
    free((void *)rest);
  if ( res < 0 )
    {
      tfprintf("create failed with code %d\n", res);
      return res;
    }
// GAGNON: change the acl
  res = hfuse_open(path, fi);
  if ( res >= 0 )
    {
      tfprintf("create success\n");
      dologtime();
    }
  return res;
}
*/
implement
hfuse_create
  (path, mode, fi) = let
//
  val (pflock | ()) = hfuselog_lock ()
  val _err = tfprintf
    (pflock | "create(%s, 0%o)\n", @(path, _mode)) where {
    val _mode = uint_of_mode (mode)
  } // end of [val]
  val _err = dologtime (pflock | (*none*))
  val () = hfuselog_unlock (pflock | (*none*))
//
  var res: int = 0
  val [n:int] path = string1_of_string (path)
  val () =
//
while (true) let
  val n = string1_length (path)
  val () = (if (n = 0) then
    (res := ~(int_of)EINVAL; break; assertfalse())
  ) : [n>0] void
  var b: strptr0 and rest: strptr0
  val () = parts (path, n, b, rest)
  var !p_dummy with pf_dummy = @[byte][0]()
  val () = pf_dummy := bytes_v_of_b0ytes_v (pf_dummy)
  val () = res := F_WRITE (pf_dummy | b, rest, p_dummy, 0)
  val () =
//
while (true) let
  val () = if res < 0 then break
  val () = res := hfuse_open (path, fi)
in
  break
end // end of [val]
//
  val () = strptr_free (b) and () = strptr_free (rest)
in
  break
end // end of [val]
//
  val () = if res >= 0 then let
    val (pflock | ()) = hfuselog_lock ()
    val _err = tfprintf(pflock | "create success\n", @())
    val _err = dologtime (pflock | (*none*))
    val () = hfuselog_unlock (pflock | (*none*))
  in
    // nothing
  end // end of [val]
//
in
  res
end // end of [hfuse_create]

(* ****** ****** *)

/*
static int hfuse_mknod(const char *path, mode_t mode, dev_t dev)
{
  char *b = NULL;
  char *rest = NULL;
  char  dum;
  int   res;

  tfprintf("mknod(%s, 0%o, 0%o)\n", path, mode, dev);
  dologtime();
  res = parts(path, &b, &rest);
  if ( res < 0 )
    return res;
  res = (*f_writep)(b, rest, &dum, 0);
  // GAGNON: change modes
  if ( b != NULL )
    free((void *)b);
  if ( rest != NULL )
    free((void *)rest);
  if ( res < 0 )
    tfprintf("mknod failed with code %d\n", res);
  else
    {
      tfprintf("mknod success\n");
      dologtime();
    }
  return res;
}
*/
implement
hfuse_mknod (path, mode, dev) = let
  val (pflock | ()) = hfuselog_lock ()
  val _err = tfprintf
    (pflock | "mknod(%s, 0%o, 0%o)\n", @(path, _mode, _dev)) where {
    val _dev = uint_of_dev (dev)
    val _mode = uint_of_mode (mode)
  } // end of [val]
  val _err = dologtime (pflock | (*none*))
  val () = hfuselog_unlock (pflock | (*none*))
//
  var res: int = 0
  val [n:int] path = string1_of_string (path)
  val () =
//
while (true) let
  val n = string1_length (path)
  val () = (if (n = 0) then
    (res := ~(int_of)EINVAL; break; assertfalse())
  ) : [n>0] void
  var b: strptr0 and rest: strptr0
  val () = parts (path, n, b, rest)
//
  val _0 = byte_of_int (0)
  var !p_dummy with pf_dummy = @[byte][0](_0)
  val () = res := F_WRITE (pf_dummy | b, rest, p_dummy, 0)
//
  val () = strptr_free (b) and () = strptr_free (rest)
in
  break
end // end of [while]
//
  val (pflock | ()) = hfuselog_lock ()
  val () = if res >= 0 then let
    val _err = tfprintf(pflock | "mknod success\n", @())
    val _err = dologtime(pflock | (*none*))
  in
    // nothing
  end else let
    val _err = tfprintf(pflock | "mknod failed with code %d\n", @(res))
  in
    // nothing
  end // end of [val]
  val () = hfuselog_unlock (pflock | (*none*))
in
  res
end // end of [hfuse_mknod]

(* ****** ****** *)

/*
static int hfuse_unlink(const char *path)
{
  char *b = NULL;
  char *rest = NULL;
  int   res;

  tfprintf("unlink(%s)\n", path);
  dologtime();
  res = parts(path, &b, &rest);
  if ( res < 0 )
    return res;
  if ( b == NULL || rest == NULL ) // trying to unlink a directory
    return -EISDIR;
  res = (*f_unlinkp)(b, rest);
  free((void *)b);
  free((void *)rest);
  if ( res >= 0 )
    {
      tfprintf("unlink success\n");
      dologtime();
    }
  return res;
}
*/
implement
hfuse_unlink (path) = let
  val (pflock | ()) = hfuselog_lock ()
  val _err = tfprintf (pflock | "unlink(%s)\n", @(path))
  val _err = dologtime (pflock | (*none*))
  val () = hfuselog_unlock (pflock | (*none*))
//
  var res: int = 0
  val [n:int] path = string1_of_string (path)
  val () =
//
while (true) let
  val n = string1_length (path)
  val () = (if (n = 0) then
    (res := ~(int_of)EINVAL; break; assertfalse())
  ) : [n>0] void
  var b: strptr0 and rest: strptr0
  val () = parts (path, n, b, rest)  
  val isdir = strptr_is_null (b) orelse strptr_is_null (rest)
  val () = if isdir then res := ~(int_of)EISDIR
  val () = res := F_UNLINK (b, rest)
//
  val () = strptr_free (b) and () = strptr_free (rest)
in
  break
end // end of [while]
//
  val (pflock | ()) = hfuselog_lock ()
  val () = if res >= 0 then let
    val _err = tfprintf(pflock | "unlink success\n", @())
    val _err = dologtime(pflock | (*none*))
  in
    // nothing
  end else let
    val _err = tfprintf(pflock | "unlink failed with code %d\n", @(res))
  in
    // nothing
  end // end of [val]
  val () = hfuselog_unlock (pflock | (*none*))
//
in
  res
end // end of [hfuse_unlink]

(* ****** ****** *)

(* end of [hfuse.dats] *)
