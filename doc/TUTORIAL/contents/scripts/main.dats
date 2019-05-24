//
//
//

(* ****** ****** *)

staload "libc/SATS/fcntl.sats"
staload "libc/SATS/unistd.sats"
staload "libc/sys/SATS/stat.sats"
staload "libc/sys/SATS/types.sats"

(* ****** ****** *)

// overload lor with lor_flag_orflag
// overload lor with lor_mode_mode

(* ****** ****** *)

extern fun fildescopy
  {fd1,fd2:int} (
  pf1_fd: !fildes_v (fd1), pf2_fd: !fildes_v (fd2)
| fd1: int fd1, fd2: int fd2
) : int (*err*) = "fildescopy"
// end of [fildescopy]

(* ****** ****** *)

#define PROLOG_one "\
<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"
\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">
<html xmlns=\"http://www.w3.org/1999/xhtml\">
<head>
  <title></title>
  <meta http-equiv=\"Content-Type\" content=\"text/html;charset=utf-8\"/>
  <style type=\"text/css\">
    .atsyntax {color:#E80000;background-color:#E0E0E0}
    .atsyntax span.comment {color:#787878;font-style:italic}
    .atsyntax span.extern  {color:#A52A2A}
    .atsyntax span.keyword {color:#000000;font-weight:bold}
    .atsyntax span.neuexp  {color:#800080}
    .atsyntax span.staexp  {color:#0000FF}
    .atsyntax span.dynexp  {color:#E80000}
    .atsyntax span.prfexp  {color:#009000}
    .atsyntax span.stacstdec  {text-decoration:none}
    .atsyntax span.stacstuse  {color:#0000CF;text-decoration:underline}
    .atsyntax span.dyncstdec  {text-decoration:none}
    .atsyntax span.dyncstimp  {color:#B80000;text-decoration:underline}
    .atsyntax span.dyncstuse  {color:#B80000;text-decoration:underline}
  </style>
</head>
<!--
<html>\n\
<head>\n\
<style type=\"text/css\">\n\
span.comment {color:787878;font-style:italic}\n\
span.extern  {color:A52A2A}\n\
span.keyword {color:000000;font-weight:bold}\n\
span.neuexp  {color:800080}\n\
span.staexp  {color:0000FF}\n\
span.dynexp  {color:E80000}\n\
span.prfexp  {color:009000}\n\
</style>\n\
</head>\n\
-->
<body text=\"#000000\" bgcolor=\"#ffffff\" link=\"#0000FF\" vlink=\"#CC00CC\" alink=\"#ff0000\">\n\
"

#define EPILOG_one "\
\n\
</body>\n\
</html>\n\
"

val nPROLOG_one = string1_length (PROLOG_one)
val nEPILOG_one = string1_length (EPILOG_one)

(* ****** ****** *)

#define DIR "./"
#define DIR_OUTPUT "./OUTPUT/"

(* ****** ****** *)

fn copy_one (name: string): void = let
  val iname = DIR + name
(*
  val () = (prerr "iname = "; prerr iname; prerr_newline ())
*)
  val oname = DIR_OUTPUT + name
(*
  val () = (prerr "oname = "; prerr oname; prerr_newline ())
*)
  val (pf1_fd | fd1) =
    open_flag_exn (iname, O_RDONLY)
  val flag2 = O_WRONLY lor O_CREAT lor O_TRUNC
  val mode2 = S_IRUSR lor S_IWUSR
  val (pf2_fd | fd2) =
    open_flag_mode_exn (oname, flag2, mode2)
  val _(*nwrite*) = write_substring_exn
    (pf2_fd | fd2, PROLOG_one, 0, nPROLOG_one)
  // end of [val]
  val err = fildescopy (pf1_fd, pf2_fd | fd1, fd2)
  val _(*nwrite*) = write_substring_exn
    (pf2_fd | fd2, EPILOG_one, 0, nEPILOG_one)
  // end of [val]
  val () = close_loop_exn (pf1_fd | fd1)
  val () = close_loop_exn (pf2_fd | fd2)
  val () = if err <> 0 then begin
    prerr "[copy_one] failed.\n"; exit {void} (1)
  end // end of [if]
in
  // empty
end // end of [copy_one]

(* ****** ****** *)

#define PROLOG_many "\
<HTML>\n\
<HEAD>\n\
<TITLE>Home Page for ATS-tutorial-all</TITLE>\n\
<META name=\"description\" content=\"Home Page for ATS-tutorial-all\">\n\
<META name=\"keywords\" content=\"\">\n\
<STYLE TYPE=\"text/css\">\n\
.atsyntax {color:#E80000;background-color:#E0E0E0}
.atsyntax span.comment {color:787878;font-style:italic}\n\
.atsyntax span.extern  {color:A52A2A}\n\
.atsyntax span.keyword {color:000000;font-weight:bold}\n\
.atsyntax span.neuexp  {color:800080}\n\
.atsyntax span.staexp  {color:0000FF}\n\
.atsyntax span.dynexp  {color:E80000}\n\
.atsyntax span.prfexp  {color:009000}\n\
</STYLE>\n\
</HEAD>\n\
<BODY text=\"#000000\" bgcolor=\"#ffffff\" link=\"#0000FF\" vlink=\"#CC00CC\" alink=\"#ff0000\">\n\
\n\
<CENTER>\n\
<H1><A id=\"top\" name=\"top\">Tutorial on ATS/Anairiats</A></H1>\n\
<H4>(all topics in one file)</H4>\n\
</CENTER>\n
<HR SIZE=6 ALIGN=LEFT COLOR=\"000000\">\n\
\n\
<H2>Primary Tutorial Topics</H2>\n\
<MENU>\n\
<LI> <A href=\"#syntax-coloring\">Syntax Coloring</A>\n\
<LI> <A href=\"#basics\">Basics</A>\n\
<LI> <A href=\"#file-inclusion\">File Inclusion</A>\n\
<LI> <A href=\"#filename-extensions\">Filename Extensions</A>\n\
<LI> <A href=\"#compilation\">Compilation</A>\n\
<LI> <A href=\"#ats-main\">The Main Function in ATS</A>\n\
<LI> <A href=\"#fixity\">Fixity Declaration</A>\n\
<LI> <A href=\"#overloading\">Overloading</A>\n\
<LI> <A href=\"#macros\">Macros</A>\n\
<LI> <A href=\"#function-or-closure\">Function or Closure?</A>\n\
<LI> <A href=\"#variadicity\">Variadic Functions</A>\n\
<LI> <A href=\"#tailrecfun\">Tail-Recursive Functions</A>\n\
<LI> <A href=\"#termination-metrics\">Termination Metrics</A>\n\
<LI> <A href=\"#types-with-effects\">Types with Effects</A>\n\
<LI> <A href=\"#templates\">Parametric Polymorphism and Templates</A>\n\
<LI> <A href=\"#lists\">(Persistent) Lists</A>\n\
<LI> <A href=\"#val-and-var\">Val(ue) and Var(iable) Declarations</A>\n\
<LI> <A href=\"#call-by-reference\">Call-By-Reference</A>\n\
<LI> <A href=\"#pointers\">Pointers</A>\n\
<LI> <A href=\"#references\">References</A>\n\
<LI> <A href=\"#arrays-and-matrices\">Arrays and Matrices</A>\n\
<LI> <A href=\"#linear-arrays\">Linear Arrays</A>\n\
<LI> <A href=\"#strings\">Strings and String Bufferes</A>\n\
<LI> <A href=\"#datatypes\">Datatypes</A>\n\
<LI> <A href=\"#dataprops\">Dataprops</A>\n\
<LI> <A href=\"#dataviews\">Dataviews</A>\n\
<LI> <A href=\"#dataviewtypes\">Dataviewtypes</A>\n\
<LI> <A href=\"#pattern-matching\">Pattern Matching</A>\n\
<LI> <A href=\"#exceptions\">Exceptions</A>\n\
<LI> <A href=\"#lazy-evaluation\">Lazy Evaluation</A>\n\
<LI> <A href=\"#llazy-evaluation\">Linear Lazy Evaluation</A>\n\
<LI> <A href=\"#input-and-output\">Input and Output</A>\n\
<LI> <A href=\"#ats-and-c\">Combining ATS and C</A>\n\
<LI> <A href=\"#PwTP\">Programming with Theorem Proving</A>\n\
</MENU>\n\
<H2>Secondary Tutorial Topics</H2>\n\
<MENU>\n\
<LI> <A href=\"#castingfun\">Casting Functions</A>\n\
<LI> <A href=\"#stackalloc\">Allocation in Stack Frames</A>\n\
<LI> <A href=\"#statetypes\">State Types</A>\n\
<LI> <A href=\"#looping\">Looping Constructs</A>\n\
</MENU>\n\
"

#define EPILOG_many "\
\n\
</BODY>\n\
</HTML>\n\
"

val nPROLOG_many = string1_length (PROLOG_many)
val nEPILOG_many = string1_length (EPILOG_many)

//

#define FILESEP "\
\n\
<HR SIZE=2 ALIGH=LEFT COLOR=\"000000\">\n\
"

val nFILESEP = string1_length (FILESEP)

(* ****** ****** *)

fn copy_many {n:nat} {st:nat | st <= n} (
   oname: string, names: &(@[string][n]), n: int n, st: int st
  ) : void = let
  var err: int = 0
  fun loop {ofd: int} {i:nat | i <= n} (
      pf_ofd: !fildes_v (ofd)
    | ofd: int ofd, names: &(@[string][n]), n: int n, i: int i, err: &int
    ) : void =
    if i < n then let
      val iname = DIR + names.[i]
      val (pf_ifd | ifd) = open_flag_exn (iname, O_RDONLY)
      val _(*nwrite*) = write_substring_exn (pf_ofd | ofd, FILESEP, 0, nFILESEP)
      val () = err := fildescopy (pf_ifd, pf_ofd | ifd, ofd)
      val () = close_loop_exn (pf_ifd | ifd)
    in
      loop (pf_ofd | ofd, names, n, i+1, err)
    end else begin
      // empty
    end // end of [if]
  // end of [loop]

  val (pf_ofd | ofd) = open_flag_mode_exn (oname, flag, mode) where {
    val flag = O_WRONLY lor O_CREAT lor O_TRUNC; val mode = S_IRUSR lor S_IWUSR
  } // end of [val]

  val _(*nwrite*) =
    write_substring_exn (pf_ofd | ofd, PROLOG_many, 0, nPROLOG_many)
  val () = loop (pf_ofd | ofd, names, n, st, err)
  val _(*nwrite*) =
    write_substring_exn (pf_ofd | ofd, EPILOG_many, 0, nEPILOG_many)
  // end of [val]
  val () = close_exn (pf_ofd | ofd)
in
  // empty
end // end of [copy_many]

(* ****** ****** *)

fn prerr_usage (cmd: string): void = let
  val () = prerr ("Usage:\n")
  val () = prerrf ("  %s -one <filename>\n", @(cmd));
  val () = prerrf ("  %s -many <filename> ... <filename>\n", @(cmd));
in
  // empty
end // end of [prerr_usage]

(* ****** ****** *)

dynload "fildescopy.dats"

implement main (argc, argv) = let
  val () = if (argc < 2) then prerr_usage (argv.[0])
  val () = assert (argc >= 2)
in
  case+ argv.[1] of
  | "-one" => let
      val () = assert (argc >= 3)
    in
      copy_one (argv.[2])
    end // end of ["-one"]
  | "-many" => let
      val oname = DIR_OUTPUT + "tutorial_all.html"
      val oname = string1_of_strbuf (oname)
    in
      copy_many (oname, argv, argc, 2)
    end // end of ["-many"]
  | flag => let
      val () = prerrf ("The flag [%s] is unrecognized.\n", @(flag))
    in
      prerr_usage (argv.[0])
    end // end of [_]
end // end of [main]

(* ****** ****** *)

(* end of [main.dats] *)
