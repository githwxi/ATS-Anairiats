(*
**
** A simple OpenGL example: display list
** 
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: June, 2010
**
*)

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%} // end of [%{^]

(* ****** ****** *)

staload "libc/SATS/math.sats"
macdef _2PI = 2 * M_PI
staload "contrib/GL/SATS/gl.sats"
staload "contrib/GL/SATS/glu.sats"
staload "contrib/GL/SATS/glut.sats"

(* ****** ****** *)

fun draw_torus {nc,nt:pos}
  (numc: int nc, numt: int nt): void = let
//
  fun loop2
    {i,j:nat | i < nc; j <= nt} .<nt-j>.
    (i: int i, j: int j):<cloref1> void =
    if j < numt then let
      var k: int 
      val () = for (k := 1; k >= 0; k := k-1) let
        val s = (i+k) mod numc + 0.5
        val t = j mod numt
        val alpha = 0.2
        val xy = (1+alpha*cos(_2PI*s/numc))
        val x = xy*cos(_2PI*t/numt)
        val y = xy*sin(_2PI*t/numt)
        val z = alpha * sin(_2PI*s/numc)
      in
        glVertex3d (x, y, z)
      end // end of [val]
    in
      loop2 (i, j+1)
    end // end of [if]
  // end of [loop2]
//
  fun loop1
    {i:nat | i <= nc} .<nc-i>.
    (i: int i):<cloref1> void =
    if i < numc then let
      val (pf_beg | ()) = glBegin (GL_QUAD_STRIP)
      val () = loop2 (i, 0(*j*))
      val () = glEnd (pf_beg | (*none*))
    in
      loop1 (i + 1)
    end // end of [if]
  // of [loop1]
//
in
  loop1 (0)
end // end of [draw_torus]

(* ****** ****** *)

%{^
GLuint theTorus = 0 ;
void theTorus_initset
  (GLuint n) { theTorus = n ; return ; }
GLuint theTorus_get () { return theTorus ; }
%} // end of [%{$]
extern
fun theTorus_initset {n:int}
  (n: GLlist n): void = "mac#theTorus_initset"
extern
fun theTorus_get (): [n:pos]
  (GLlist n -<lin,prf> void | GLlist n) = "mac#theTorus_get"
// end of [fun]

(* ****** ****** *)

extern
fun initialize (): void = "initialize"
implement
initialize () = () where {
  val (pf_torus | torus) = glGenList_exn ()
  val (pf_new | torus) = glNewList_new (pf_torus | torus, GL_COMPILE)
  val () = draw_torus (16, 25)
  val () = glEndList (pf_new | (*none*))
  val () = theTorus_initset (torus)
  val () = glShadeModel (GL_FLAT)
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
} // end of [initialize]

(* ****** ****** *)

extern
fun display (): void = "display"
implement display () = () where {
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3f ((GLfloat)1.0, (GLfloat)1.0, (GLfloat)1.0)
  val (fpf | lst) = theTorus_get ()
  val () = glCallList (lst)
  prval () = fpf (lst)
  val () = glFlush ()
} // end of [display]

(* ****** ****** *)

extern
fun reshape (w: int, h: int): void = "reshape"
implement reshape (w, h) = () where {
  val () = glViewport (0, 0, w, h)
  val () = glMatrixMode (GL_PROJECTION)
  val w = double_of w and h = double_of h
  val () = glLoadIdentity ()
  val () = gluPerspective (30.0, w/h, 1.0, 100.0)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
  val () = gluLookAt (0., 0., 10., 0., 0., 0., 0., 1., 0.)
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
  | _ when (key = 'x' orelse key = 'X') => () where {
      val () = glRotated (30., 1., 0., 0.); val () = glutPostRedisplay ()
    } // end of [...]
  | _ when (key = 'y' orelse key = 'Y') => () where {
      val () = glRotated (30., 0., 1., 0.); val () = glutPostRedisplay ()
    } // end of [...]
  | _ when (key = 'i' orelse key = 'I') => () where {
      val () = glLoadIdentity ()
      val () = gluLookAt (0., 0., 10., 0., 0., 0., 0., 1., 0.)
      val () = glutPostRedisplay ()
    } // end of [...]
  | _ => () // ignored
end // end of [keyboard]

(* ****** ****** *)

//

implement main_dummy () = () // [mainats] is implemented externally

//

%{$

ats_void_type mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  glutInitWindowSize (200, 200) ;
  glutInit ((int*)&argc, (char**)argv) ;
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

(* end of [GL-test11.dats] *)
