(*
**
** A simple OpenGL example
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
staload "contrib/GL/SATS/glut.sats"

(* ****** ****** *)

var spin: double = 0.0
val spin_r = ref_make_view_ptr {double} (view@ spin | &spin)

extern
fun initialize (): void = "initialize"
implement initialize () = let
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glShadeModel (GL_FLAT)
in
  // empty
end // end of [initialize]

extern
fun display (): void = "display"
implement display () = let
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val (pf | ()) = glPushMatrix ()
  val () = glRotated (!spin_r, 0.0, 0.0, 1.0)
  val () = glColor3d (1.0, 1.0, 1.0)
  val () = glRectd (~25.0, ~25.0, 25.0, 25.0)
  val () = glPopMatrix (pf | (*none*))
  val () = glutSwapBuffers ()
in
  // empty
end // end of [display]

extern
fun spinDisplay (): void = "spinDisplay"
implement spinDisplay () = let
  val () = !spin_r := !spin_r + 2.0
  val () = if !spin_r > 360.0 then !spin_r := !spin_r - 360.0
in
  glutPostRedisplay ()
end // end of [spinDisplay]

extern
fun reshape (w: int, h: int): void = "reshape"
implement reshape (w, h) = let
  val () = glViewport (0, 0, w, h)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = glOrtho (~50.0, 50.0, ~50.0, 50.0, ~1.0, 1.0)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
in
  // empty
end // end of [reshape]

(* ****** ****** *)

symintr int
overload int with int_of_GLenum

extern fun mouse
  (button: int, state: int, x: int, y: int): void = "mouse"
// end of [mouse]

implement mouse (button, state, x, y) = begin
  case+ 0 of
  | _ when (button = (int)GLUT_LEFT_BUTTON) => begin
      if (state = (int)GLUT_DOWN) then glutIdleFunc (spinDisplay)
    end // end of [GLUT_LEFT_BUTTON]
  | _ when (button = (int)GLUT_RIGHT_BUTTON) => begin
      if (state = (int)GLUT_DOWN) then glutIdleFunc_null ()
    end // end of [GLUT_RIGHT_BUTTON]
  | _ => () // ignored
end // end of [mouse]

extern
fun main_work (): void = "main_work"
implement main_work () = let
  val () = initialize ()
  val () = glutDisplayFunc (display)
  val () = glutReshapeFunc (reshape)
  val () = glutMouseFunc (mouse)
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
  glutInitDisplayMode (GLUT_DOUBLE | GLUT_RGB) ;
  glutInitWindowSize (500, 500) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow(((char**)argv)[0]) ;
  main_work () ;
  return ; /* deadcode as [main_work] never returns */
} /* end of [mainats] */

%} // end of [%{$]

(* ****** ****** *)

(* end of [GL-test02.dats] *)
