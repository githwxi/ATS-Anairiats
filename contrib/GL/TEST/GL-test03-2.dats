(*
**
** A simple OpenGL example:
**   a circling dashed loop in the shape of a square
** 
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: January, 2010
**
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/reference.dats"
val theStipplePattern = ref_make_elt<uint> (0U) // updated by the timer

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

(* ****** ****** *)

staload MATH = "libc/SATS/math.sats"
macdef PI = $MATH.M_PI
macdef sin = $MATH.sin
macdef cos = $MATH.cos

(* ****** ****** *)

staload "contrib/GL/SATS/gl.sats"
staload "contrib/GL/SATS/glut.sats"

(* ****** ****** *)

extern
fun initialize (): void = "initialize"
implement initialize () = let
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glShadeModel (GL_FLAT)
  val () = glLineWidth (2.0)
in
  // empty
end // end of [initialize]

(* ****** ****** *)

typedef dbl = double

fn draw_regpgn
  {n:int | n >= 3}
  (pf_beg: !glBegin_v | n: int n): void = let
  val delta = 2*PI/n
  fun loop {i:nat | i <= n} .<n-i>.
    (i: int i, t: dbl):<cloref1> void =
    if i < n then let
      val t1 = t + delta
      val () = glVertex2d (cos t1, sin t1)
    in
      loop (i+1, t1)
    end else ()
  // end of [loop]
in
  glVertex2d (1.0, 0.0); loop (0, 0.0)
end // end of [draw_regpgn]

extern
fun display (): void = "display"
implement display () = let
  val () = glClear (GL_COLOR_BUFFER_BIT)
//
  val () = glEnable(GL_LINE_STIPPLE)
  val (pf_mat | ()) = glPushMatrix ()
  val () = glRotated (45.0, 0.0, 0.0, 1.0)
  val () = glScaled (0.5, 0.5, 1.0)
//
  #define N 4
  val pat = !theStipplePattern
  val () = glLineStipple(1, (GLushort)pat) (* dashed *)
  val () = glColor3d (1.0, 1.0, 1.0)
  val (pf_beg | ()) = glBegin (GL_LINE_STRIP)
  val () = draw_regpgn (pf_beg | N)
  val () = glEnd (pf_beg | (*none*))
//
  val pat = ~pat
  val () = glLineStipple(1, (GLushort)pat) (* dashed *)
  val () = glColor3d (1.0, 0.0, 0.0)
  val (pf_beg | ()) = glBegin (GL_LINE_STRIP)
  val () = draw_regpgn (pf_beg | N)
  val () = glEnd (pf_beg | (*none*))
//
  val () = glPopMatrix (pf_mat | (*none*))
  val () = glDisable(GL_LINE_STIPPLE)
//
  val () = glutSwapBuffers ()
in
  // empty
end // end of [display]

(* ****** ****** *)

extern
fun reshape (w: int, h: int): void = "reshape"
implement reshape (w, h) = let
  val wh = min (w, h)
  val () = glViewport (0, 0, w, h)
  val w = double_of w and h = double_of h
  val wh = double_of wh
  val r_w = w/wh and r_h = h/wh
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = glOrtho (~r_w, r_w, ~r_h, r_h, ~1.0, 1.0)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
in
  // empty
end // end of [reshape]

(* ****** ****** *)

#define INTERVAL 50
#define i2u uint_of_int

extern fun timer (flag: natLt 16): void = "timer"

implement timer (flag) = () where {
(*
  val () = printf ("timer: flag = %i\n", @(flag))
*)
  var pat: uint = (0xffU << flag)
  val () = if (flag > 8) then pat := pat + (0xffU >> (16 - flag))
  val () = !theStipplePattern := pat
  val flag = (if flag < 15 then flag + 1 else 0): int
  extern fun _timer (flag: int): void = "timer"
  val () = glutTimerFunc ((i2u)INTERVAL, _timer, flag)
  val () = glutPostRedisplay ()
}

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$

ats_void_type mainats
  (ats_int_type argc, ats_ptr_type argv) {
  glutInit ((int*)&argc, (char**)argv) ;
  glutInitDisplayMode (GLUT_DOUBLE | GLUT_RGB) ;
  glutInitWindowSize (500, 500) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow(((char**)argv)[0]) ;
  initialize () ;
  glutDisplayFunc (display) ;
  glutReshapeFunc (reshape) ;
  // glutMouseFunc (mouse) ;
  timer (0) ;
  glutMainLoop () ;
  return ; // deadcode as [glutMainLoop] never returns
} /* end of [mainats] */

%} // end of [%{$]

(* ****** ****** *)

(* end of [GL-test03-2.dats] *)
