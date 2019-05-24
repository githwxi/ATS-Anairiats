(*
**
** A simple OpenGL example: bitmap
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: January, 2010
**
*)

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%} // end of [%{^]

(* ****** ****** *)

staload "contrib/GL/SATS/gl.sats"
staload "contrib/GL/SATS/glu.sats"
staload "contrib/GL/SATS/glut.sats"

(* ****** ****** *)

%{^
GLubyte
bitmap[24] = {
  0xc0, 0x00
, 0xc0, 0x00
, 0xc0, 0x00
, 0xc0, 0x00
, 0xc0, 0x00
, 0xff, 0x00
, 0xff, 0x00
, 0xc0, 0x00
, 0xc0, 0x00
, 0xc0, 0x00
, 0xff, 0xc0
, 0xff, 0xc0
} ; // end of [bitmap]

%} // end of [%{^]

sta bitmap : addr
val p_bitmap = $extval (ptr bitmap, "&bitmap[0]")
viewdef bitmap_v = array_v (GLubyte, 24, bitmap)

(* ****** ****** *)

extern
fun initialize (): void = "initialize"
implement initialize () = () where {
  val () = glPixelStorei (GL_UNPACK_ALIGNMENT, (GLint)1)
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
} // end of ...

(* ****** ****** *)

extern
fun display (pf: !bitmap_v | (*none*)): void = "display"
implement display
  (pf | (*none*)) = () where {
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (1.0, 1.0, 1.0)
  val () = glRasterPos2i ((GLint)20, (GLint)20)
  #define W8 2; #define W 10; #define H 12
  prval pf_mul = mul_make {W8,H} ()
  val () = glBitmap {W8} (pf_mul |
    (GLsizei)W, (GLsizei)H, (GLfloat)0.0, (GLfloat)0.0, (GLfloat)11.0, (GLfloat)0.0, !p_bitmap
  ) // end of [glBitmap]
  val () = glBitmap {W8} (pf_mul |
    (GLsizei)W, (GLsizei)H, (GLfloat)0.0, (GLfloat)0.0, (GLfloat)11.0, (GLfloat)0.0, !p_bitmap
  ) // end of [glBitmap]
  val () = glBitmap {W8} (pf_mul |
    (GLsizei)W, (GLsizei)H, (GLfloat)0.0, (GLfloat)0.0, (GLfloat)11.0, (GLfloat)0.0, !p_bitmap
  ) // end of [glBitmap]
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
  val () = glOrtho (0.0, w, 0.0, h, ~1.0, 1.0)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
} // end of [reshape]

(* ****** ****** *)

extern
fun keyboard
  (key: uchar, x: int, y: int): void = "keyboard"
// end of [keyboard]
implement keyboard (key, x, y) = let
  val key = char_of_uchar key
in
  case+ 0 of
  | _ when (key = (char_of_int)27) => exit (0)
  | _ => () // ignored
end // end of [keyboard]

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
  glutInitWindowSize (100, 100) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow(((char**)argv)[0]) ;
  initialize () ;
  glutReshapeFunc (reshape) ;
  glutKeyboardFunc (keyboard) ;
  glutDisplayFunc (display) ;
  glutMainLoop () ;
  return ; /* deadcode */
} // end of [mainats]

%} // end of [%{$]

(* ****** ****** *)

(* end of [GL-test10.dats] *)
