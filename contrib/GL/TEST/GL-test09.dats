(*
**
** A simple OpenGL example: antialiasing
** 
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: January, 2010
**
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/reference.dats"
val rotAngleRef = ref_make_elt<double> (0.0)

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

#define float float_of_GLfloat

extern
fun initialize (): void = "initialize"
implement initialize () = let
  var !p_values = @[GLfloat][2]()
  val () = glGetFloatv (GL_LINE_WIDTH_GRANULARITY, !p_values)
  val v0 = double_of (float_of_GLfloat (p_values->[0]))
  val () = printf ("GL_LINE_WIDTH_GRANULARITY = %3.1f\n", @(v0))
  val () = glGetFloatv (GL_LINE_WIDTH_RANGE, !p_values)
  val v0 = double_of (float_of_GLfloat (p_values->[0]))
  and v1 = double_of (float_of_GLfloat (p_values->[1]))
  val () = printf
    ("GL_LINE_WIDTH_RANGE = %3.1f and %3.1f\n", @(v0, v1))
  // end of [val]
  val () = glEnable (GL_LINE_SMOOTH)
  val () = glEnable (GL_BLEND)
  val () = glBlendFunc (GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
  val () = glHint (GL_LINE_SMOOTH_HINT, GL_DONT_CARE)
  val () = glLineWidth (1.5)
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glShadeModel (GL_FLAT)
in
  // empty
end // end of [initialize]

(* ****** ****** *)

extern fun display (): void = "display"
implement display () = () where {
  val () = glClear (GL_COLOR_BUFFER_BIT)
//
  val rotAngle = !rotAngleRef
//
  val () = glColor3d (0.0, 1.0, 0.0)
  val (pf_mat | ()) = glPushMatrix ()
  val () = glRotated (~rotAngle, 0.0, 0.0, 0.1)
  val (pf_beg | ()) = glBegin (GL_LINES)
  val () = glVertex2d (~0.5,  0.5)
  val () = glVertex2d ( 0.5, ~0.5)
  val () = glEnd (pf_beg | (*none*))
  val () = glPopMatrix (pf_mat | (*none*))
//
  val () = glColor3d (0.0, 0.0, 1.0)
  val (pf_mat | ()) = glPushMatrix ()
  val () = glRotated (rotAngle, 0.0, 0.0, 0.1)
  val (pf_beg | ()) = glBegin (GL_LINES)
  val () = glVertex2d ( 0.5,  0.5)
  val () = glVertex2d (~0.5, ~0.5)
  val () = glEnd (pf_beg | (*none*))
  val () = glPopMatrix (pf_mat | (*none*))
//
  val () = glFlush ()
} // end of [display]

(* ****** ****** *)

extern
fun reshape (w: int, h: int): void = "reshape"
implement reshape (w, h) = () where {
  val () = glViewport (0, 0, w, h)
  val w = double_of w and h = double_of h
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = if (w <= h) then
    gluOrtho2D (~1.0, 1.0, ~h/w, h/w)
  else
    gluOrtho2D (~w/h, w/h, ~1.0, 1.0)
  // end of [val]
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
} // end of [reshape]

(* ****** ****** *)

extern
fun keyboard (key: uchar, x: int, y: int): void = "keyboard"
implement keyboard (key, x, y) = let
  val key = char_of_uchar (key)
in
  case+ key of
  | _ when (key = 'r' orelse key = 'R') => () where {
      val rotAngle = !rotAngleRef + 20
      val () = if rotAngle >= 360.0
        then !rotAngleRef := 0.0 else !rotAngleRef := rotAngle
      // end of [val]
      val () = glutPostRedisplay ()
    } // end of [_ when ...]
  | _ when (int_of_char key = 27) => exit (0)
  | _ => () // ignored
end // end of [keyboard]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$

ats_void_type mainats
  (ats_int_type argc, ats_ptr_type argv) {
  glutInit ((int*)&argc, (char**)argv) ;
  glutInitDisplayMode (GLUT_SINGLE | GLUT_RGB) ;
  glutInitWindowSize (200, 200) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow(((char**)argv)[0]) ;
  initialize () ;
  glutDisplayFunc (display) ;
  glutReshapeFunc (reshape) ;
  glutKeyboardFunc (keyboard) ;
  glutMainLoop () ;
  return ; // deadcode as [glutMainLoop] never returns
} /* end of [mainats] */

%} // end of [%{$]

(* ****** ****** *)

(* end of [GL-test09.dats] *)
