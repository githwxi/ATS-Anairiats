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

extern
fun initialize (): void = "initialize"
implement initialize () = let
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = glOrtho (0.0, 1.0, 0.0, 1.0, ~1.0, 1.0)
  val () = glMatrixMode (GL_MODELVIEW)
in
  // empty
end // end of [initialize]

//

extern
fun display (): void = "display"
implement display () = let
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (1.0, 1.0, 1.0)
  val (pf | ()) = glBegin (GL_POLYGON)
//
  var !p =
    @[GLfloat]((GLfloat)0.25, (GLfloat)0.25, (GLfloat)0.00)
  // end of [var]
  val () = glVertex3fv (!p)
//
  val () = p->[0] := (GLfloat)0.75
  val () = glVertex3fv (!p)
//
  val () = p->[1] := (GLfloat)0.75
  val () = glVertex3fv (!p)
//
  val () = p->[0] := (GLfloat)0.25
  val () = glVertex3fv (!p)
//
  val () = glEnd (pf | (*none*))
  val () = glFlush ()
in
  // empty
end // end of [display]

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
  glutCreateWindow("Hello!") ;
  initialize () ;
  glutDisplayFunc (display) ;
  glutMainLoop () ;
  return ; /* deadcode */
} // end of [mainats]

%} // end of [%{$]

(* ****** ****** *)

(* end of [GL-test01.dats] *)
