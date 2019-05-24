(*
**
** A simple OpenGL example: stippled lines
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2009
**
*)

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

(* ****** ****** *)

staload "contrib/GL/SATS/gl.sats"
staload "contrib/GL/SATS/glu.sats"
staload "contrib/GL/SATS/glut.sats"

(* ****** ****** *)

typedef dbl = double

(* ****** ****** *)

extern
fun initialize (): void = "initialize"
implement initialize () = let
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glMatrixMode (GL_PROJECTION)
in
  // empty
end // end of [initialize]

(*
extern
fun initialize (): void = "initialize"
implement initialize () = let
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glShadeModel (GL_FLAT)
  val () = glLoadIdentity ()
  val () = glOrtho (0.0, 1.0, 0.0, 1.0, ~1.0, 1.0)
in
  // empty
end // end of [initialize]
*)

(* ****** ****** *)

fn drawOneLine (
    x1: dbl, y1: dbl, x2: dbl, y2: dbl
  ) : void = () where {
  val (pf | ()) = glBegin (GL_LINES)
  val () = glVertex2d (x1, y1); val () = glVertex2d (x2, y2)
  val () = glEnd (pf | (*none*))
} // end of [drawOneLine]

extern
fun display (): void = "display"
implement display () = let
  val () = glClear (GL_COLOR_BUFFER_BIT)
//
  val () = glColor3d (1.0, 1.0, 1.0)
//
  val () = glEnable(GL_LINE_STIPPLE)
//
  val () = glLineStipple(1, (GLushort)0x0101) (* dotted *)
  val () = drawOneLine (50.0, 125.0, 150.0, 125.0)
  val () = glLineStipple(1, (GLushort)0x00FF) (* dashed *)
  val () = drawOneLine (150.0, 125.0, 250.0, 125.0)
  val () = glLineStipple(1, (GLushort)0x1C47) (* dash/dot/dash *)
  val () = drawOneLine (250.0, 125.0, 350.0, 125.0)
//
  val () = glLineWidth (5.0)
  val () = glLineStipple(1, (GLushort)0x0101) (* dotted *)
  val () = drawOneLine (50.0, 100.0, 150.0, 100.0)
  val () = glLineStipple(1, (GLushort)0x00FF) (* dashed *)
  val () = drawOneLine (150.0, 100.0, 250.0, 100.0)
  val () = glLineStipple(1, (GLushort)0x1C47) (* dash/dot/dash *)
  val () = drawOneLine (250.0, 100.0, 350.0, 100.0)
  val () = glLineWidth (1.0)
//
  var i : int // uninitialized
//
  val () = glLineStipple(1, (GLushort)0x1C47) (* dotted *)
  val (pf_beg | ()) = glBegin (GL_LINE_STRIP)
  val () = for (i := 0; i < 7; i := i+1) begin
    glVertex2d (50.0 + (double_of_int)i * 50.0, 75.0)
  end // end of [val]
  val () = glEnd (pf_beg | (*none*))
//
  val (pf_beg | ()) = glBegin (GL_LINE_STRIP)
  val () = for (i := 0; i < 6; i := i+1) begin
    drawOneLine (
      50.0 + (double_of_int)i * 50.0, 50.0
    , 50.0 + (double_of_int)(i+1) * 50.0, 50.0
    ) // end of [drawOneLine]
  end // end of [val]
  val () = glEnd (pf_beg | (*none*))
//
  val () = glLineStipple(5, (GLushort)0x1C47) (* dash/dot/dash *)
  val () = drawOneLine (50.0, 25.0, 350.0, 25.0)
//
  val () = glDisable(GL_LINE_STIPPLE)
  val () = glFlush ()
//
in
  // empty
end // end of [display]

(* ****** ****** *)

extern
fun reshape (w: int, h: int): void = "reshape"
implement reshape (w, h) = let
  val () = glViewport (0, 0, w, h)
  val w = double_of w and h = double_of h
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = gluOrtho2D (0.0, w, 0.0, h)
in
  // empty
end // end of [reshape]

(* ****** ****** *)

extern
fun main_work (): void = "main_work"
implement main_work () = let
  val () = initialize ()
  val () = glutDisplayFunc (display)
  val () = glutReshapeFunc (reshape)
in
  glutMainLoop ()
end // end of [main_work]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$

ats_void_type mainats
  (ats_int_type argc, ats_ptr_type argv) {
  glutInit ((int*)&argc, (char**)argv) ;
  glutInitDisplayMode (GLUT_SINGLE | GLUT_RGB) ;
  glutInitWindowSize (400, 150) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow(((char**)argv)[0]) ;
  main_work () ;
  return ; /* deadcode as [main_work] never returns */
} /* end of [mainats] */

%} // end of [%{$]

(* ****** ****** *)

(* end of [GL-test03-1.dats] *)
