(*
**
** A simple OpenGL example: 5 fogged spheres
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: August, 2010
**
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "contrib/GL/SATS/gl.sats"
staload "contrib/GL/SATS/glu.sats"
staload "contrib/GL/SATS/glut.sats"

(* ****** ****** *)

%{^
extern
ats_void_type mainats (ats_int_type argc, ats_ptr_type argv) ;
%} // end of [%{^]

(* ****** ****** *)

val fogMode = ref_make_elt<GLint> ((GLint)0)

(* ****** ****** *)

extern fun initialize (): void = "initialize"
implement initialize () = () where {
//
  val _0 = GLfloat(0.0)
  var !p_position = @[GLfloat]((GLfloat)0.5f, (GLfloat)0.5f, (GLfloat)3.0f, (GLfloat)0.0f)
//
  val () = glEnable (GL_DEPTH_TEST)
//
  val () = glLightfv (GL_LIGHT0, GL_POSITION, !p_position)
  val () = glEnable (GL_LIGHTING)
  val () = glEnable (GL_LIGHT0)
//
  val () = () where {
    var !p_mat = @[GLfloat]((GLfloat)0.1745, (GLfloat)0.01175, (GLfloat)0.01175)
    val () = glMaterialfv (GL_FRONT, GL_AMBIENT, !p_mat)
    val () = p_mat->[0] := (GLfloat)0.61424
    val () = p_mat->[1] := (GLfloat)0.04136
    val () = p_mat->[2] := (GLfloat)0.04136
    val () = glMaterialfv (GL_FRONT, GL_DIFFUSE, !p_mat)
    val () = p_mat->[0] := (GLfloat)0.727811
    val () = p_mat->[1] := (GLfloat)0.626959
    val () = p_mat->[2] := (GLfloat)0.626959
    val () = glMaterialfv (GL_FRONT, GL_SPECULAR, !p_mat)
    val () = glMaterialf (GL_FRONT, GL_SHININESS, GLfloat(0.6*128))
  } // end of [val]
//
  val () = glEnable (GL_FOG)
  val () = () where {
    var !p_fogColor = @[GLfloat]((GLfloat)0.5, (GLfloat)0.5, (GLfloat)0.5, (GLfloat)1.0)
    val () = !fogMode := (GLint)GL_EXP
    val () = glFogi (GL_FOG_MODE, !fogMode)
    val () = glFogfv (GL_FOG_COLOR, !p_fogColor)
    val () = glFogf (GL_FOG_DENSITY, (GLfloat)0.35f)
    val () = glHint (GL_FOG_HINT, GL_DONT_CARE)
    val () = glFogf (GL_FOG_START, (GLfloat)1.0f)
    val () = glFogf (GL_FOG_END, (GLfloat)5.0f)
  } // end of [val]
//
  val () = glClearColor (0.5, 0.5, 0.5, 1.0) // fog color
//
} // end of [initialize]

(* ****** ****** *)

fun renderSphere
  (x: GLfloat, y: GLfloat, z: GLfloat): void = () where {
  val (pf | ()) = glPushMatrix ()
  val () = glTranslatef (x, y, z)
  val () = glutSolidSphere ((GLdouble)0.4, (GLint)16, (GLint)16)
  val () = glPopMatrix (pf | (*none*))
} // end of [renderSphere]

(* ****** ****** *)

extern fun display (): void = "display"
implement display () = () where {
  val () = glClear (GL_COLOR_BUFFER_BIT lor GL_DEPTH_BUFFER_BIT)
  val () = renderSphere ((GLfloat)~2.0, (GLfloat)~0.5, (GLfloat)~1.0)
  val () = renderSphere ((GLfloat)~1.0, (GLfloat)~0.5, (GLfloat)~2.0)
  val () = renderSphere ((GLfloat)0.0, (GLfloat)~0.5, (GLfloat)~3.0)
  val () = renderSphere ((GLfloat)1.0, (GLfloat)~0.5, (GLfloat)~4.0)
  val () = renderSphere ((GLfloat)2.0, (GLfloat)~0.5, (GLfloat)~5.0)
  val () = glFlush ()
} // end of [display]

(* ****** ****** *)

extern fun reshape (w: int, h: int): void = "reshape"
implement reshape (w, h) = () where {
  val () = glViewport (0, 0, w, h)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val r = (if (w <= h) then (double_of)h/w else (double_of)w/h): double
  val () = glOrtho (~2.5, 2.5, ~2.5*r, 2.5*r, ~10.0, 10.0)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
} // end of [reshape]

(* ****** ****** *)

extern fun keyboard (key: uchar, x: int, y: int): void = "keyboard"
implement
keyboard (key, x, y) = let
  val key = (char_of_uchar)key
in
  case+ key of
  | _ when (key = 'f' orelse key = 'F') => let
      val m = (int_of_GLint)!fogMode
//
      val () = case+ 0 of
      | _ when m = (int_of)GL_EXP => let
          val () = !fogMode := (GLint)GL_EXP2 in printf ("fogMode is set to GL_EXP2\n", @())
        end // end of ...
      | _ when m = (int_of)GL_EXP2 => let
          val () = !fogMode := (GLint)GL_LINEAR in printf ("fogMode is set to GL_LINEAR\n", @())
        end // end of ...
      | _ when m = (int_of)GL_LINEAR => let
          val () = !fogMode := (GLint)GL_EXP in printf ("fogMode is set to GL_EXP\n", @())
        end // end ...
      | _ => ()
//
      val () = glFogi (GL_FOG_MODE, !fogMode)
      val () = glutPostRedisplay ()
    in
      // nothing
    end // end of ...
  | _ when (key = (char_of_uint)27U) => exit (0)
  | _ => ()
end // end of [keyboard]

(* ****** ****** *)

implement main_dummy () = () // [mainats] is implemented externally

(* ****** ****** *)

%{$

ats_void_type mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  glutInit ((int*)&argc, (char**)argv) ;
  glutInitWindowSize (500, 500) ;
  glutInitDisplayMode (GLUT_SINGLE | GLUT_RGB | GLUT_DEPTH) ;
  glutCreateWindow(((char**)argv)[0]) ;
  initialize () ;
  glutDisplayFunc (display) ;
  glutReshapeFunc (reshape) ;
  glutKeyboardFunc (keyboard) ;
  glutMainLoop () ;
  return ; /* deadcode */
} // end of [mainats]

%} // end of [%{$]

(* ****** ****** *)

(* end of [GL-test15.dats] *)
