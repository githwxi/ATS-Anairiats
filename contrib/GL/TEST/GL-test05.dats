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
staload "contrib/GL/SATS/glu.sats"
staload "contrib/GL/SATS/glut.sats"

(* ****** ****** *)

typedef dbl = double

(* ****** ****** *)

extern
fun display (): void = "display"
implement display () = () where {
  val () = glClear (GL_COLOR_BUFFER_BIT)
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
  val () = gluPerspective (45.0, w/h, 1.0, 100.0)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
} // end of [reshape]

(* ****** ****** *)

symintr int
overload int with int_of_GLenum

extern
fun mouse
  (button: int, state: int, x: int, y: int): void
  = "mouse"
implement mouse (button, state, x, y) = () where {
  var !p_viewport = @[GLint?][4]()
  var !p_mvmatrix = @[GLdouble?][16]()
  var !p_projmatrix = @[GLdouble?][16]()
  var wx = (GLdouble)0.0 and wy = (GLdouble)0.0 and wz = (GLdouble)0.0
  val () = case+ 0 of
    | _ when (button = (int)GLUT_LEFT_BUTTON) => begin
        if (state = (int)GLUT_DOWN) then let
          val () = glGetIntegerv (GL_VIEWPORT, !p_viewport)
          val () = glGetDoublev (GL_MODELVIEW_MATRIX, !p_mvmatrix)
          val () = glGetDoublev (GL_PROJECTION_MATRIX, !p_projmatrix)
          val realy = (int1_of_GLint)p_viewport->[3] - y - 1
          val () = printf
            ("The coordinates at the cursor is (%4d, %4d)\n", @(x, realy))
          // end of [val]
          val x = double_of x
          val realy = double_of realy
          val ret = gluUnProject
            ((GLdouble)x, (GLdouble)realy, (GLdouble)0.0, !p_mvmatrix, !p_projmatrix, !p_viewport, wx, wy, wz)
          // end of [val]
          val () = printf ("gluUnProject(1): ret = %d\n", @(int1_of_GLint ret))
          val _wx = double_of wx and _wy = double_of wy and _wz = double_of wz
          val () = printf
            ("The world coordinates at z=0.0 is (%f, %f, %f)\n", @(_wx, _wy, _wz))
          // end of [val]
          val ret = gluUnProject
            ((GLdouble)x, (GLdouble)realy, (GLdouble)1.0, !p_mvmatrix, !p_projmatrix, !p_viewport, wx, wy, wz)
          // end of [val]
          val () = printf ("gluUnProject(2): ret = %d\n", @(int1_of_GLint ret))
          val _wx = double_of wx and _wy = double_of wy and _wz = double_of wz
          val () = printf
            ("The world coordinates at z=1.0 is (%f, %f, %f)\n", @(_wx, _wy, _wz))
          // end of [val]
        in
          // nothing
        end // end of [if]
      end // end of [_ when ...]
    | _ when (button = (int)GLUT_RIGHT_BUTTON) => (if (state = (int)GLUT_DOWN) then exit 0)
    | _ => () // ignored
} // end of [mouse]

(* ****** ****** *)

//

implement main_dummy () = ()

//

%{$

ats_void_type mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  glutInit ((int*)&argc, (char**)argv) ;
  glutInitDisplayMode (GLUT_SINGLE | GLUT_RGB) ;
  glutInitWindowSize (500, 500) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow(((char**)argv)[0]) ;
  glutDisplayFunc (display) ;
  glutReshapeFunc (reshape) ;
  glutMouseFunc (mouse) ;
  glutMainLoop () ;
  return ; /* deadcode */
} // end of [mainats]

%} // end of [%{$]

(* ****** ****** *)

(* end of [GL-test05.dats] *)
