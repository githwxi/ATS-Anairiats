(*
**
** A simple graphviz example
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2011
**
*)

(* ****** ****** *)

staload
"contrib/graphviz/SATS/types.sats"
staload "contrib/graphviz/SATS/gvc.sats"

(* ****** ****** *)

implement
main (argc, argv) = {
  val filr = stdin_ref
//
  val () = aginit ()
  val gvc = gvContext_exn ()
//
  var fmt: string = "plain"
  val () = if argc >= 2 then fmt := argv.[1]
//
  val g = agread_exn (filr)
  val (pfopt | err) = gvLayout (gvc, g, "dot")
  val () = assert (err = 0)
  prval Some_v (pf) = pfopt
  val err = gvRender (pf | gvc, g, fmt, stdout_ref)
  val _0 = gvFreeLayout (pf | gvc, g)
  val () = agclose (g)
//
  val nerr = gvFreeContext1 (gvc)
} // end of [main]

(* ****** ****** *)

#if(0)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}
implement main_dummy () = ()

%{$

#include <gvc.h>
#include <stdio.h>

ats_void_type
mainats (
  ats_int_type argc0, ats_ptr_type argv0
) {
  int argc = argc0 ;
  char **argv = (char**)argv0 ;
  GVC_t *gvc ;
  graph_t *g ;
  FILE *filp ;
  gvc = gvContext() ;
  filp = stdin ;
//
  if (argc > 1) {
    filp = fopen (argv[1], "r") ;
    if (!filp) {
      perror("File can't be opened for read") ; exit (EXIT_FAILURE) ;
    } // end of [if]
  } // end of [if]
//
  g = agread (filp) ;
  gvLayout (gvc, g, "dot") ;
  gvRender (gvc, g, "plain", stdout) ;
  gvFreeLayout (gvc, g) ;
  agclose (g) ;
  gvFreeContext (gvc) ;
  return ;
} // end of [main]

%} // end of [%{$]

#endif // end of [if(0)]

(* ****** ****** *)

(* end of [graphviz-test01.dats] *)
