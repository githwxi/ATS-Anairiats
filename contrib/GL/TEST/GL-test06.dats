(*
**
** A simple OpenGL example: starfields
** 
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2009
**
** Note: This implementation is based on the following
** C code by Nate Robins
**
*)

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

typedef star = @{
  star_x= double, star_y= double, star_vx= double
} // end of [star]

abst@ype star_t = star
viewtypedef starlst = List_vt star_t

extern fun star_make ():<> star_t
extern fun star_x (x: &star_t):<> double
extern fun star_x_set (x: &star_t, _x: double):<> void
extern fun star_y (x: &star_t):<> double
extern fun star_y_set (x: &star_t, _y: double):<> void
extern fun star_vx (x: &star_t):<> double
extern fun star_vx_set (x: &star_t, _vx: double):<> void

(* ****** ****** *)

staload RAND = "libc/SATS/random.sats"
extern fun drand48 ():<> double = "atslib_drand48"

local

assume star_t = star

in

implement star_x (x) = x.star_x
implement star_x_set (x, _x) = x.star_x := _x
implement star_y (x) = x.star_y
implement star_y_set (x, _y) = x.star_y := _y
implement star_vx (x) = x.star_vx
implement star_vx_set (x, _vx) = x.star_vx := _vx

implement star_make () = let
  val _x = drand48 ()
  val _y = drand48 ()
  val _vx = drand48 ()
in
  @{ star_x=_x, star_y=_y, star_vx=_vx }
end // end of [star_make]

end // end of [local]

(* ****** ****** *)

var theStarLst: starlst = list_vt_nil ()
val (pf_theStarLst | ()) =
  vbox_make_view_ptr {starlst} (view@ theStarLst | &theStarLst)
// end of [prval]

(* ****** ****** *)

#define NSTAR 100

(* ****** ****** *)

fn theStarLst_add
  {n:nat} (n: int n): void = let
  fun loop {n:nat} {l:addr} .<n>.
    (xs: starlst, n: int n):<> starlst =
    if n > 0 then let
      val x = star_make () in loop (list_vt_cons (x, xs), n - 1)
    end else xs
  // end of [loop]
  prval vbox pf = pf_theStarLst
in
  theStarLst := loop (theStarLst, n)
end // end of [theStarLst_add]

fn theStarLst_del
  {n:nat} (n: int n) = let
  fun loop {n:nat} {l:addr} .<n>.
    (xs: starlst, n: int n):<> starlst =
    if n > 0 then case+ xs of
      | ~list_vt_cons (_, xs) => loop (xs, n-1)
      | ~list_vt_nil () => list_vt_nil ()
    else xs
  // end of [loop]
  prval vbox pf = pf_theStarLst
in
  theStarLst := loop (theStarLst, n)
end // end of [theStarLst_del]

fn theStarLst_free () = let
  prval vbox pf = pf_theStarLst in
  list_vt_free (theStarLst); theStarLst := list_vt_nil ()
end // end of [theStarLst_free]

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

extern
fun initialize
  {n:nat} (n: int n): void = "initialize"
// end of [initialize]
implement initialize (n) = () where {
  val () = $RAND.srand48_with_time ()
  val n = (if n >= 0 then n else NSTAR) : Nat
  val () = theStarLst_add (n)
} // end of [initialize]
  
(* ****** ****** *)

extern fun finalize (): void = "finalize"
implement finalize () = () where {
  val () = theStarLst_free (); val () = exit (0)
} // end of [finalize]

(* ****** ****** *)

extern
fun display (): void = "display"
implement display () = () where {
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val w_win = glutGet (GLUT_WINDOW_WIDTH)
  val w_win = double_of w_win
  var !p_f = @lam
    (pf_unit: !unit_v | x: &star_t): void =<clo> let
    val _vx = 5 * (star_vx x) + 2
    val _x = (star_x x) * w_win + _vx
  in
    if _x < w_win then $effmask_all let
      val _y = (star_y x) * w_win
      val () = star_x_set (x, _x / w_win)
      val (pf | ()) = glBegin (GL_LINE_STRIP)
      val () = glColor3ub ((GLubyte)0, (GLubyte)0, (GLubyte)0)
      val () = glVertex2d (_x - 4 * _vx, _y)
      val () = glColor3ub ((GLubyte)255, (GLubyte)255, (GLubyte)234)
      val () = glVertex2d (_x, _y)
      val () = glEnd (pf | (*none*))
    in
      // nothing
    end else let
      val () = star_x_set (x, 0.0)
      val () = star_y_set (x, drand48 ())
      val () = star_vx_set (x, drand48 ())
    in
      // nothing
    end // end of [if]
  end // end of [var]
  val () = () where {
    prval pf_unit = unit_v ()
    prval vbox pf = pf_theStarLst
    val () =
      list_vt_foreach_vclo<star_t> {unit_v} (pf_unit | theStarLst, !p_f)
    // end of [val]
    prval unit_v () = pf_unit
  } // end of [val]
  val () = glutSwapBuffers ()
} // end of [display]

(* ****** ****** *)

extern
fun reshape
  (w: int, h: int): void = "reshape"
// end of [reshape]
implement reshape (w, h) = () where {
  val () = glViewport (0, 0, w, h)
  val w = double_of w and h = double_of h
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = glOrtho (0., w, 0., h, ~1., 1.)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
  val () = glColor3ub ((GLubyte)255, (GLubyte)255, (GLubyte)255)
} // end of [reshape]

(* ****** ****** *)

var old_x: int = 50
var old_y: int = 50
var old_w: int = 320
var old_h: int = 320

viewdef old_v = @(
  int @ old_x, int @ old_y, int @ old_w, int @ old_h
) // end of [old_v]

extern
fun keyboard (
  pf: !old_v | key: uchar, x: int, y: int
) : void = "keyboard" // end of [keyboard]
implement keyboard
  (pf | key, x, y) = let
  prval (pf1, pf2, pf3, pf4) = pf
  val key = char_of_uchar key
  val () = case+ 0 of
  | _ when key = (char_of_int)27 => finalize ()
  | _ when key = 'q' => finalize () 
  | _ when key = 'a' => theStarLst_add (1)
  | _ when key = 'A' => theStarLst_add (10)
  | _ when key = 'd' => theStarLst_del (1)
  | _ when key = 'D' => theStarLst_del (10)
  | _ when key = 'f' => let
      val win_w = glutGet (GLUT_WINDOW_WIDTH)
      val scr_w = glutGet (GLUT_SCREEN_WIDTH)
    in
      if win_w < scr_w then let
        val () = old_x := glutGet (GLUT_WINDOW_X)
        val () = old_y := glutGet (GLUT_WINDOW_Y)
        val () = old_w := glutGet (GLUT_WINDOW_WIDTH)
        val () = old_h := glutGet (GLUT_WINDOW_HEIGHT)
      in
        glutFullScreen ()
      end // end of [if]
    end // end of [_ when ...]
  | _ when key = 'w' => () where {
      val () = glutPositionWindow (old_x, old_y)
      val () = glutReshapeWindow (old_w, old_h)
    } // end of [_ when ...]
  | _ => () // ignored
in
  pf := (pf1, pf2, pf3, pf4)
end // end of [keyboard]

(* ****** ****** *)

macdef TIME_INTERVAL = 50U

extern
fun timer (flag: int): void = "timer"
implement timer (flag) = let
  val () = glutPostRedisplay ()
in
  glutTimerFunc (TIME_INTERVAL, timer, 0)
end // end of [timer]

(* ****** ****** *)

extern
fun idle (): void = "idle"
implement idle
  () = () where {
  val () = glutPostRedisplay ()
} // end of [idle]

(* ****** ****** *)

extern
fun ss_keyboard
  (key: uchar, x: int, y: int): void = "ss_keyboard"
// end of [ss_keyboard]
implement ss_keyboard (key, x, y) = finalize ()

extern
fun ss_mouse
  (button: int, state: int, x: int, y: int): void = "ss_mouse"
// end of [ss_mouse]
implement ss_mouse(button, state, x, y) = finalize ()

(* ****** ****** *)

extern
fun fprint_usage (out: FILEref, cmd: string): void
  = "fprint_usage"

implement fprint_usage
  (out, cmd) = () where {
  val () = fprintf (out, "%s -h : for help message\n", @(cmd))
  val () = fprintf (out, "%s <nstar> : start with [nstar] stars\n", @(cmd))
  macdef prstr (str) = fprint_string (out, ,(str))
  val () = prstr "The following keys are supported:\n"
  val () = prstr "  'esc': exit\n"
  val () = prstr "  'a': add 1 stars\n"
  val () = prstr "  'A': add 10 stars\n"
  val () = prstr "  'd': delete 1 stars\n"
  val () = prstr "  'D': delete 10 stars\n"
  val () = prstr "  'w': norm screen\n"
  val () = prstr "  'f': full screen\n"
} // end of [fprint_usage]

(* ****** ****** *)

//

implement main_dummy () = ()

//

%{$

#define SCREEN_SAVER_MODE 0

void
ss_passive(int x, int y) {
  static int been_here = 0;
/*
** for some reason, GLUT sends an initial passive motion callback when a
** window is initialized, so this would immediately terminate the program;
** to get around this, see if we've been here before. (actually if we've
** been here twice.)
*/
  if (been_here > 1) finalize (); else been_here += 1 ;
  return ;
} // end of [ss_passive]

ats_void_type mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  char *arg1 ;
  int nstar = -1;
  if (argc >= 2) {
    arg1 = ((char**)argv)[1] ;
    if (!strcmp(arg1, "-h")) {
      fprint_usage (stdout, ((char**)argv)[0]); exit (0) ;
    }
    nstar = atoi(arg1) ;
  } 
  glutInit ((int*)&argc, (char**)argv) ;
  glutInitDisplayMode (GLUT_SINGLE | GLUT_RGB) ;
  glutInitWindowSize (500, 500) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow("Starfield") ;
  initialize (nstar) ;
  glutDisplayFunc (display) ;
  glutReshapeFunc (reshape) ;

#if (SCREEN_SAVER_MODE)
  glutPassiveMotionFunc(ss_passive);
  glutKeyboardFunc(ss_keyboard);
  glutMouseFunc(ss_mouse);
  glutSetCursor(GLUT_CURSOR_NONE);
  glutFullScreen(); 
#else
  glutKeyboardFunc (keyboard) ;
#endif // end of [#if SCREEN_SAVER_MODE]
/*
  glutIdleFunc (idle) ;
*/
  timer (0) ;
  glutMainLoop () ;
  return ; /* deadcode */
} // end of [mainats]

%} // end of [%{$]

(* ****** ****** *)

(* end of [GL-test06.dats] *)

////

/* 
   starfield.c
   Nate Robins, 1997

   An example of starfields in OpenGL.

*/


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if defined (__APPLE__) || defined (MACOSX)
#include <GLUT/glut.h>
#else
#include <GL/glut.h>
#endif


/* #define SCREEN_SAVER_MODE */


enum {
    SCROLL_LEFT = 1,
    SCROLL_RIGHT,
    SCROLL_UP,
    SCROLL_DOWN
} type = SCROLL_RIGHT;


typedef struct _star {
    float x, y;
    float vx, vy;
} star;


star* stars = NULL;
int num_stars = 150;


void
reshape(int width, int height)
{
    int i = 0;

    glViewport(0, 0, width, height);
    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    glOrtho(0, width, 0, height, -1, 1);
    glMatrixMode(GL_MODELVIEW);
    glLoadIdentity();
    glColor3ub(255, 255, 255);

    for (i = 0; i < num_stars; i++) {
        stars[i].x = rand() % width;
        stars[i].y = rand() % height;
        stars[i].vx = rand() / (float)RAND_MAX * 5 + 2;
        stars[i].vy = 0;
    }
}

void
display(void)
{
    int i;

    glClear(GL_COLOR_BUFFER_BIT);

    for (i = 0; i < num_stars; i++) {
        stars[i].x += stars[i].vx;
        if (stars[i].x < glutGet(GLUT_WINDOW_WIDTH)) {
            glBegin(GL_LINE_STRIP);
            glColor3ub(0, 0, 0);
            glVertex2i(stars[i].x-stars[i].vx*4, stars[i].y);
            glColor3ub(255, 255, 255);
            glVertex2i(stars[i].x, stars[i].y);
            glEnd();
        } else {
            stars[i].x = 0;
        }
    }
    
    glutSwapBuffers();
}

void
idle(void)
{
    glutPostRedisplay();
}

void
bail(int code)
{
    free(stars);
    exit(code);
}

#ifdef SCREEN_SAVER_MODE
void
ss_keyboard(char key, int x, int y)
{
    bail(0);
}

void
ss_mouse(int button, int state, int x, int y)
{
    bail(0);
}

void
ss_passive(int x, int y)
{
    static int been_here = 0;

    /* for some reason, GLUT sends an initial passive motion callback
       when a window is initialized, so this would immediately
       terminate the program.  to get around this, see if we've been
       here before. (actually if we've been here twice.) */

    if (been_here > 1)
        bail(0);
    been_here++;
}

#else

void
keyboard(unsigned char key, int x, int y)
{
    static int old_x = 50;
    static int old_y = 50;
    static int old_width = 320;
    static int old_height = 320;

    switch (key) {
    case 27:
        bail(0);
        break;
    case 'w':
        glutPositionWindow(old_x, old_y);
        glutReshapeWindow(old_width, old_height);
        break;
    case 'f':
        if (glutGet(GLUT_WINDOW_WIDTH) < glutGet(GLUT_SCREEN_WIDTH)) {
            old_x = glutGet(GLUT_WINDOW_X);
            old_y = glutGet(GLUT_WINDOW_Y);
            old_width = glutGet(GLUT_WINDOW_WIDTH);
            old_height = glutGet(GLUT_WINDOW_HEIGHT);
            glutFullScreen();
        }
        break;
    }
}

#endif

int
main(int argc, char** argv)
{
    glutInitDisplayMode(GLUT_DOUBLE | GLUT_RGBA);
    glutInitWindowPosition(50, 50);
    glutInitWindowSize(320, 320);
    glutInit(&argc, argv);

    glutCreateWindow("Starfield");
    glutDisplayFunc(display);
    glutReshapeFunc(reshape);
#ifdef SCREEN_SAVER_MODE
    glutPassiveMotionFunc(ss_passive);
    glutKeyboardFunc(ss_keyboard);
    glutMouseFunc(ss_mouse);
    glutSetCursor(GLUT_CURSOR_NONE);
    glutFullScreen(); 
#else
    glutKeyboardFunc(keyboard);
#endif

    if (argc > 1) {
        if (strcmp(argv[1], "-h") == 0) {
            fprintf(stderr, "%s [stars]\n", argv[0]);
            exit(0);
        }
        sscanf(argv[1], "%d", &num_stars);
    }      

    stars = (star*)malloc(sizeof(star) * num_stars);

    glutIdleFunc(idle);
    glutMainLoop();
    return 0;
}
