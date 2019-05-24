(*
** for highlighting/xreferencing ATS code
*)

(* ****** ****** *)

staload
UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload
F = "libc/SATS/fcntl.sats"
stadef fildes_v = $F.fildes_v
staload
S = "libc/SATS/stdlib.sats"
staload
W = "libc/sys/SATS/wait.sats"
staload
UNI = "libc/SATS/unistd.sats"

(* ****** ****** *)

staload "libatsdoc/SATS/libatsdoc_atext.sats"

(* ****** ****** *)

staload "utils/atsyntax/SATS/ats2xhtml.sats"

(* ****** ****** *)

extern
fun atsopt_get
  (): string = "atsopt_get"
implement
atsopt_get () = let
  val (fpf | x) = $S.getenv ("ATSHOME")
in
//
if strptr_isnot_null (x) then let
  val res = sprintf ("%s/bin/atsopt", @($UN.castvwtp1{string}(x)))
  prval () = fpf (x)
in
  string_of_strptr (res)
end else let
  prval () = fpf (x) in "atsopt"
end (* end of [if] *)
//
end // end of [atsopt_get]

(* ****** ****** *)

extern
fun string2filename
  (pfx: string, content: string): strptr0
implement
string2filename
  (pfx, content) = let
  val tmp = sprintf ("%sXXXXXX", @(pfx))
  val [m,n:int] tmp = strbuf_of_strptr (tmp)
  prval () = __assert () where {
    extern prfun __assert (): [n >= 6] void
  }
  prval pfstr = tmp.1
  val (pfopt | fd) = $S.mkstemp !(tmp.2) // create it!
  prval () = tmp.1 := pfstr
in
//
if fd >= 0 then let
  prval $F.open_v_succ (pffil) = pfopt
  val [n:int] content = string1_of_string (content)
  val n = string1_length (content)
  val (pf, fpf | p) = __cast (content) where {
    extern castfn __cast {n:nat}
      (x: string n): [l:addr] (bytes(n)@l, bytes(n)@l -<lin,prf> void | ptr l)
    // end of [extern]
  }
  val () = $F.write_all_exn (pffil | fd, !p, n)
  prval () = fpf (pf)
  val () = $F.close_exn (pffil | fd)
in
  strptr_of_strbuf (tmp)
end else let
  prval $F.open_v_fail () = pfopt
  val () = strbufptr_free (tmp)
in
  strptr_null ()
end // end of [if]
//
end // end of [string2filename]

(* ****** ****** *)

extern
fun atscc_posmark_html_body_exec (
  stadyn: int, out: string, path: string
) : void = "atscc_posmark_html_body_exec"
// end of [atscc_posmark_html_body_exec]

(* ****** ****** *)

implement
ats2xhtml_strcode
  (stadyn, code) = let
  val [l:addr] path =
    string2filename ("libatsdoc_ats2xhtmlinp", code)
  prval () = addr_is_gtez {l} ()
in
//
if strptr_isnot_null (path) then let
  val res =
    ats2xhtml_filcode (stadyn, $UN.castvwtp1(path))
  val _err = $UNI.unlink ($UN.castvwtp1 (path))  
  val () = strptr_free (path)
in
  res
end else let
  prval () = strptr_free_null (path) in strptr_null ()
end // end of [if]
//
end // end of [ats2xhtml_strcode]

(* ****** ****** *)

implement
ats2xhtml_filcode
  (stadyn, path) = let
//
  val tmp = sprintf
    ("%sXXXXXX", @("libatsdoc_ats2xhtmlout"))
  // end of [val]
  val [m,n:int] tmp = strbuf_of_strptr (tmp)
  prval () = __assert () where {
    extern prfun __assert (): [n >= 6] void
  }
  prval pfstr = tmp.1
  val (pfopt | fd) = $S.mkstemp !(tmp.2) // create it!
  prval () = tmp.1 := pfstr
  val tmp = strptr_of_strbuf (tmp)
//
in
//
if fd >= 0 then let
  prval $F.open_v_succ (pffil) = pfopt
  val () = $F.close_exn (pffil | fd)
//
  val _tmp =
    $UN.castvwtp1{string}(tmp)
  // end of [val]
  val cmd = lam (): void =<cloptr1>
    atscc_posmark_html_body_exec (stadyn, _tmp, path)
  // end of [val]
  val status = $UNI.fork_exec_and_wait_cloptr_exn (cmd)
//
  val status = int1_of_int (status)
  val (pf_ifexited | ifexited) = $W.WIFEXITED (status)
  val () = if ifexited then let
    val code = $W.WEXITSTATUS (pf_ifexited | status) in
    if code <> 0 then
      prerrf ("exit(ATS): [ats2xhtml_filcode(%s)] failed.\n", @(path))
    // end of [if]
  end // end of [val]
  val () = if ~ifexited
    then prerr ("[ats2xhtml_filcode] is sigtermed\n")
  // end of [if]
//
  val (pffil | fd) = $F.open_flag_exn ($UN.castvwtp1(tmp), $F.O_RDONLY)
  val res = file2strptr (pffil | fd)
  val () = $F.close_exn (pffil | fd)
  val _err = $UNI.unlink ($UN.castvwtp1(tmp)) // HX: may save it for debugging
  val () = strptr_free (tmp)
in
  res
end else let
  prval $F.open_v_fail () = pfopt; val () = strptr_free (tmp) in strptr_null ()
end // end of [if]
//
end // end of [ats2xhtml_filcode]

(* ****** ****** *)

%{$

ats_void_type
atscc_posmark_html_body_exec (
  ats_int_type stadyn, ats_ptr_type out, ats_ptr_type path
) {
  ats_ptr_type atsopt = atsopt_get () ;
  char *stadynflg = (stadyn > 0 ? "--dynamic" : "--static") ;
  int err = execl (
    (char*)atsopt
  , (char*)atsopt
  , "--posmark_html_body"
  , "--output", out, stadynflg, (char*)path
  , (char*)0
  ) ; // end of [execl]
  if (err < 0) perror("atscc_posmark_html_body: [execl] failed: ") ;
  exit(EXIT_FAILURE) ;
} // end of [atscc_posmark_html_body]

%} // end of [%{$]

(* ****** ****** *)

(* end of [ats2xhtml.dats] *)
