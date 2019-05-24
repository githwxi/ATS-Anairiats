(*
**
** A simple OpenGL example: multiple display lists for font definition
** 
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: August, 2010
**
*)

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

#define PT 1
#define STROKE 2
#define END 3

typedef struct { GLfloat x, y ; int type ; } CP ;

CP Adata[] = {
  {0, 0, PT}, {0, 9, PT}, {1, 10, PT}, {4, 10, PT}, {5, 9, PT}, {5, 0, STROKE}, {0, 5, PT}, {5, 5, END}
} ; // end of [Adata]

CP Edata[] = {
  {5, 0, PT}, {0, 0, PT}, {0, 10, PT}, {5, 10, STROKE}, {0, 5, PT}, {4, 5, END}
} ; // end of [Edata]

CP Pdata[] = {
  {0, 0, PT}, {0, 10, PT}, {4, 10, PT}, {5, 9, PT}, {5, 6, PT}, {4, 5, PT}, {0, 5, END}
} ; // end of [Pdata]

CP Rdata[] = {
  {0, 0, PT}, {0, 10, PT}, {4, 10, PT}, {5, 9, PT}, {5, 6, PT}, {4, 5, PT}, {0, 5, STROKE}, {3, 5, PT}, {5, 0, END}
} ; // end of [Rdata]

CP Sdata[] = {
  {0, 1, PT}, {1, 0, PT}, {4, 0, PT}, {5, 1, PT}, {5, 4, PT}, {4, 5, PT}, {1, 5, PT}, {0, 6, PT}, {0, 9, PT}, {1, 10, PT}, {4, 10, PT}, {5, 9, END}
} ; // end of [Sdata]

void
drawLetter (CP *A) {
  int MAX = 1024 ;
  glBegin (GL_LINE_STRIP) ;
  while (1) {
    switch (A->type) {
    case PT: glVertex2fv(&A->x) ; break ;
    case STROKE:
      glVertex2fv(&A->x) ; glEnd() ; glBegin(GL_LINE_STRIP) ; break ;
    case END:
      glVertex2fv(&A->x) ; glEnd() ; glTranslatef (8.0f, 0.0f, 0.0f) ; return ;
    } // end of [switch]
    A += 1 ; MAX -= 1 ; if (!MAX) break ;
  } // end of [while]
  return ; /* deadcode */
} // end of [drawLetter]

%} // end of [%{^]

(* ****** ****** *)

abstype CPref
extern castfn ptr_of_CPref (x: CPref): ptr
extern val Adata : CPref = "mac#Adata"
extern val Edata : CPref = "mac#Edata"
extern val Pdata : CPref = "mac#Pdata"
extern val Rdata : CPref = "mac#Rdata"
extern val Sdata : CPref = "mac#Sdata"
extern fun drawLetter (x: CPref): void = "mac#drawLetter"

val test1 = "A SPARE SERAPE APPEARS AS"
val test2 = "APES PREPARE RARE PEPPERS"

(* ****** ****** *)

%{^
GLuint theFontOffset = 0 ;
GLuint theFontOffset_get () { return theFontOffset ; }
void theFontOffset_set (GLuint base) { theFontOffset = base ; return ; }
%} // end of [%{^]
extern fun theFontOffset_get (): GLuint = "theFontOffset_get"
extern fun theFontOffset_set (base: GLuint): void = "theFontOffset_set"

(* ****** ****** *)

extern fun initialize (): void = "initialize"
implement
initialize () = () where {
  val () = glShadeModel (GL_FLAT)
  val base = glGenLists ((GLsizei)128) where {
    extern fun glGenLists (range: GLsizei): GLuint = "atsctrb_glGenLists"
  } // end of [val]
  val () = theFontOffset_set (base)
  val base = (uint_of_GLuint)base
  val () = assert (base <> 0U)
  extern fun glNewList
    (lst: uint, mode: GLenum): (glNewList_v | void) = "mac#glNewList"
  (* end of [extern] *)
//
  val (pf | ()) = glNewList (base+(uint_of)'A', GL_COMPILE)
  val () = drawLetter (Adata)
  val () = glEndList (pf | (*none*))
//
  val (pf | ()) = glNewList (base+(uint_of)'E', GL_COMPILE)
  val () = drawLetter (Edata)
  val () = glEndList (pf | (*none*))
//
  val (pf | ()) = glNewList (base+(uint_of)'P', GL_COMPILE)
  val () = drawLetter (Pdata)
  val () = glEndList (pf | (*none*))
//
  val (pf | ()) = glNewList (base+(uint_of)'R', GL_COMPILE)
  val () = drawLetter (Rdata)
  val () = glEndList (pf | (*none*))
//
  val (pf | ()) = glNewList (base+(uint_of)'S', GL_COMPILE)
  val () = drawLetter (Sdata)
  val () = glEndList (pf | (*none*))
//
  val (pf | ()) = glNewList (base+(uint_of)' ', GL_COMPILE)
  val () = glTranslated (8.0, 0.0, 0.0)
  val () = glEndList (pf | (*none*))
//
} // end of [initialize]

(* ****** ****** *)

fun printStrokedString
  {n:nat} (txt: string n) = let
  val len = string_length (txt)
  val () = glListBase (theFontOffset_get ())
(*
  val () = (print "printStrokenString: len = "; print len; print_newline ())
*)
  val () = glCallLists (len, GL_BYTE, txt) where {
    extern fun glCallLists {n:nat}
      (_: size_t n, _: GLenum_type GLbyte, _: string n): void = "mac#glCallLists"
  } // end of [val]
in
  // nothing
end // end of [printStrokedString]

(* ****** ****** *)

extern fun display (): void = "display"
implement
display () = () where {
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (1.0, 1.0, 1.0)
  val (pf_pm | ()) = glPushMatrix ()
  val () = glScaled (2.0, 2.0, 2.0)
  val () = glTranslated (10.0, 30.0, 0.0)
  val () = printStrokedString (test1)
  val () = glPopMatrix (pf_pm | (*none*))
  val (pf_pm | ()) = glPushMatrix ()
  val () = glScaled (2.0, 2.0, 2.0)
  val () = glTranslated (10.0, 13.0, 0.0)
  val () = printStrokedString (test2)
  val () = glPopMatrix (pf_pm | (*none*))
  val () = glFlush ()
} // end of [display]

(* ****** ****** *)

extern fun reshape {w,h:nat} (w: int w, h: int h): void = "reshape"
implement
reshape (w, h) = () where {
  val () = glViewport (0, 0, w, h)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = gluOrtho2D (0.0, (double_of)w, 0.0, (double_of)h)
} // end of [reshape]

(* ****** ****** *)

extern fun keyboard (key: uchar, x: int, y: int): void = "keyboard"
implement
keyboard (key, x, y) = let
  val key = (char_of_uchar)key
in
  case+ key of
  | ' ' => glutPostRedisplay ()
  | _ when (key = (char_of_uint)27U) => exit (0)
  | _ => ()
end // end of [keyboard]

(* ****** ****** *)

//

implement main_dummy () = () // [mainats] is implemented externally

//

%{$

ats_void_type mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  glutInit ((int*)&argc, (char**)argv) ;
  glutInitWindowSize (440, 120) ;
  glutInitDisplayMode (GLUT_SINGLE | GLUT_RGB) ;
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

(* end of [GL-test12.dats] *)
