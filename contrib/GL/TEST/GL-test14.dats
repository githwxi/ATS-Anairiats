(*
**
** A simple OpenGL example: drawing, copying and zooming pixel data
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
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%} // end of [%{^]

(* ****** ****** *)

%{^
#define checkImageWidth 64
#define checkImageHeight 64
GLubyte checkImage[checkImageHeight][checkImageWidth][3] ;
%} // end of [%{^]
#define checkImageWidth 64
#define checkImageHeight 64
sta l_image : addr
viewdef image_v = GLarray3 (GLubyte, checkImageWidth, checkImageHeight, 3) @ l_image
extern val p_checkImage : ptr l_image = "mac#checkImage"
extern prfun checkImage_get (): (image_v, image_v -<lin,prf> void)

(* ****** ****** *)

%{^
void makeCheckImage () {
  int i, j, c ;
  for (i = 0; i < checkImageHeight ; i += 1) {
    for (j = 0; j < checkImageWidth ; j += 1) {
      c = ((((i&0x8)==0)^((j&0x8))==0))*255 ;
      checkImage[i][j][0] = (GLubyte)c ;
      checkImage[i][j][1] = (GLubyte)c ;
      checkImage[i][j][2] = (GLubyte)c ;
    } // end of [for]
  } // end of [for]
} // end of [makeCheckImage]
%} // end of [%{^]

extern fun makeCheckImage (): void = "makeCheckImage"

(* ****** ****** *)

extern fun initialize (): void = "initialize"
implement
initialize () = () where {
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glShadeModel (GL_FLAT)
  val () = makeCheckImage ()
  val () = glPixelStorei (GL_UNPACK_ALIGNMENT, (GLint)1)
} // end of [initialize]

(* ****** ****** *)

extern fun display (): void = "display"
implement
display () = () where {
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glRasterPos2i ((GLint)0, (GLint)0)
  prval (pf, fpf) = checkImage_get ()
  val () = glDrawPixels {GLubyte} (
    (GLsizei)checkImageWidth, (GLsizei)checkImageHeight, GL_RGB_format, GL_UNSIGNED_BYTE, !p_checkImage
  ) // end of [val]
  prval () = fpf (pf)
  val () = glFlush ()
} // end of [display]

(* ****** ****** *)

val theHeight = ref<int> (0)

extern fun reshape {w,h:nat} (w: int w, h: int h): void = "reshape"
implement
reshape (w, h) = () where {
  val () = !theHeight := h
  val () = glViewport (0, 0, w, h)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = gluOrtho2D (0.0, (double_of)w, 0.0, (double_of)h)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
} // end of [reshape]

(* ****** ****** *)

val zoomFactor = ref<double> (1.0)

extern fun motion (x: int, y: int): void = "motion"
implement
motion (x, y) = () where {
  val screeny = !theHeight - y
  val () = glRasterPos2i ((GLint)x, (GLint)screeny)
  val zf = (GLfloat)!zoomFactor; val () = glPixelZoom (zf, zf)
  val () = glCopyPixels ((GLint)0, (GLint)0, (GLsizei)checkImageWidth, (GLsizei)checkImageHeight, GL_COLOR)
  val () = glPixelZoom ((GLfloat)1.0, (GLfloat)1.0)
  val () = glFlush ()
} // end of [motion]

(* ****** ****** *)

extern fun keyboard (key: uchar, x: int, y: int): void = "keyboard"
implement
keyboard (key, x, y) = let
  val key = (char_of_uchar)key
in
  case+ key of
  | _ when (key = 'r' orelse key = 'R') => let
      val () = !zoomFactor := 1.0
      val () = glutPostRedisplay ()
    in
      printf ("zoomFactor reset to 1.0\n", @())
    end // end of [_]
  | _ when (key = 'z') => let
      val () = !zoomFactor := !zoomFactor + 0.5
      val () = if !zoomFactor >= 3.0 then !zoomFactor := 3.0
    in
      printf ("zoomFactor is now %4.1f\n", @(!zoomFactor))
    end // end of ['z']
  | _ when (key = 'Z') => let
      val () = !zoomFactor := !zoomFactor - 0.5
      val () = if !zoomFactor <= 0.5 then !zoomFactor := 0.5
    in
      printf ("zoomFactor is now %4.1f\n", @(!zoomFactor))
    end // end of ['Z']
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
  glutInitWindowSize (250, 250) ;
  glutInitDisplayMode (GLUT_SINGLE | GLUT_RGB) ;
  glutCreateWindow(((char**)argv)[0]) ;
  initialize () ;
  glutDisplayFunc (display) ;
  glutReshapeFunc (reshape) ;
  glutKeyboardFunc (keyboard) ;
  glutMotionFunc (motion) ;
  glutMainLoop () ;
  return ; /* deadcode */
} // end of [mainats]

%} // end of [%{$]

(* ****** ****** *)

(* end of [GL-test14.dats] *)
