(*
**
** A simple OpenGL example involving texturing
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

%{^

#define checkImageWidth 64
#define checkImageHeight 64
static GLubyte checkImage[checkImageWidth][checkImageHeight][4] ;
static GLuint texName ;

ats_void_type
makeCheckImage () {
  int i, j, c ;
  for (i = 0; i < checkImageHeight; i += 1) {
    for (j = 0; j < checkImageWidth; j += 1) {
      c = (((i&0x8) == 0) ^ ((j&0x8) == 0)) * 255 ;
      checkImage[i][j][0] = (GLubyte)c ;
      checkImage[i][j][1] = (GLubyte)c ;
      checkImage[i][j][2] = (GLubyte)c ;
      checkImage[i][j][3] = (GLubyte)255 ;
    } // end of [for]
  } // end of [for]
  return ;
} // end of [makeCheckImage]

%} // end of [%{^]

#define checkImageWidth 64
#define checkImageHeight 64
extern fun makeCheckImage (): void = "makeCheckImage"

typedef checkImage_t =
  GLarray3 (GLubyte, checkImageWidth, checkImageHeight, 4)

(* ****** ****** *)

extern
fun initialize {l1,l2:addr} (
    pf_texName: !array_v (GLtexture?, 1, l1) >> array_v (GLtexture, 1, l1)
  , pf_checkImage: ! checkImage_t @ l2
  | p_texName : ptr l1
  , p_checkImage: ptr l2
  ) : void = "initialize"

implement initialize (
    pf_texName
  , pf_checkImage
  | p_texName
  , p_checkImage
  ) = () where {
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glShadeModel (GL_FLAT)
  val () = glEnable (GL_DEPTH_TEST)
  val () = makeCheckImage ()
  val () = glPixelStorei (GL_UNPACK_ALIGNMENT, (GLint)1)
  val () = glGenTextures ((GLsizei)1, !p_texName)
  prval (pf1, pf2) = array_v_uncons {GLtexture} (pf_texName)
  val () = glBindTexture (GL_TEXTURE_2D, !p_texName)
  prval () = pf_texName := array_v_cons {GLtexture} (pf1, pf2)
  val () = glTexParameteri (GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, (GLint)GL_REPEAT)
  val () = glTexParameteri (GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, (GLint)GL_REPEAT)
  val () = glTexParameteri (GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, (GLint)GL_NEAREST)
  val () = glTexParameteri (GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, (GLint)GL_NEAREST)
  val () = glTexImage2D (
    GL_TEXTURE_2D
  , (GLint)0, (GLint)GL_RGBA
  , (GLsizei)checkImageWidth
  , (GLsizei)checkImageHeight
  , 0(*border*), GL_RGBA_format, GL_UNSIGNED_BYTE
  , !p_checkImage
  ) // end of [val]
(*
  val () = printf ("GL-test4: [initialize] is done\n", @())
*)
} // end of [initialize]

(* ****** ****** *)

val texName = $extval (GLuint, "texName")

extern
fun display (): void = "display"
implement display () = () where {
  val () = glClear (GL_COLOR_BUFFER_BIT lor GL_DEPTH_BUFFER_BIT)
  val () = glEnable (GL_TEXTURE_2D)
  val () = glTexEnvi (GL_TEXTURE_ENV, GL_TEXTURE_ENV_MODE, (GLint)GL_REPLACE)
//
  extern castfn __cast (x: GLuint) : [i:int] (GLtexture i -<lin,prf> void | GLtexture i)
  val (fpf_x | x) = __cast (texName)
  val () = glBindTexture (GL_TEXTURE_2D, x)
  prval () = fpf_x (x)
//
  val (pf | ()) = glBegin (GL_QUADS)
//
  val () = glTexCoord2d (0.0, 0.0)
  val () = glVertex3d (~2.0, ~1.0, 0.0)
  val () = glTexCoord2d (0.0, 1.0)
  val () = glVertex3d (~2.0,  1.0, 0.0)
  val () = glTexCoord2d (1.0, 1.0)
  val () = glVertex3d ( 0.0,  1.0, 0.0)
  val () = glTexCoord2d (1.0, 0.0)
  val () = glVertex3d ( 0.0, ~1.0, 0.0)
//
  val () = glTexCoord2d (0.0, 0.0)
  val () = glVertex3d ( 1.0, ~1.0, 0.0)
  val () = glTexCoord2d (0.0, 1.0)
  val () = glVertex3d ( 1.0,  1.0, 0.0)
  val () = glTexCoord2d (1.0, 1.0)
  val () = glVertex3d ( 2.41421,  1.0, ~1.41421)
  val () = glTexCoord2d (1.0, 0.0)
  val () = glVertex3d ( 2.41421, ~1.0, ~1.41421)
//
  val () = glEnd (pf | (*none*))
  val () = glFlush ()
  val () = glDisable (GL_TEXTURE_2D)
} // end of [display]

(* ****** ****** *)

extern
fun reshape {w,h:nat}
  (w: int w, h: int h): void = "reshape"
// end of [reshape]

implement reshape (w, h) = () where {
  val () = glViewport (0, 0, w, h)
  val w = double_of w and h = double_of h
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = gluPerspective (60.0, w/h, 1.0, 30.0)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
  val () = glTranslated (0.0, 0.0, ~3.6)
} // end of [reshape]

(* ****** ****** *)

extern
fun keyboard
  (key: uchar, x: int, y: int): void = "keyboard"
// end of [keyboard]

implement keyboard (key, x, y) = case+ 0 of
  | _ when (int_of key = 27) => exit (0) | _ => ()
// end of [keyboard]

(* ****** ****** *)

//

implement main_dummy () = ()

//

%{$

ats_void_type mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  glutInit ((int*)&argc, (char**)argv) ;
  glutInitDisplayMode (GLUT_SINGLE | GLUT_RGB | GLUT_DEPTH) ;
  glutInitWindowSize (250, 250) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow(((char**)argv)[0]) ;
//
  initialize (&texName, &checkImage) ;
  glutDisplayFunc (display) ;
  glutReshapeFunc (reshape) ;
  glutKeyboardFunc (keyboard) ;  
  glutMainLoop () ;
  return ; /* deadcode */
} // end of [mainats]

%} // end of [%{$]

(* ****** ****** *)

(* end of [GL-test04.dats] *)
