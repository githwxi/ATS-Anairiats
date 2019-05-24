(*
**
** A simple OpenGL example: a clock
** 
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
%}

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload MATH = "libc/SATS/math.sats"
macdef PI = $MATH.M_PI
macdef sin = $MATH.sin
macdef cos = $MATH.cos

(* ****** ****** *)

staload "contrib/GL/SATS/gl.sats"
staload "contrib/GL/SATS/glu.sats"
staload "contrib/GL/SATS/glut.sats"

(* ****** ****** *)

fn glColor_clock_base () = // white color
  glColor3ub ((GLubyte)255, (GLubyte)255, (GLubyte)255)
// end of [glColor_clock_base]

fn glColor_clock_decor () = // gree color
  glColor3ub ((GLubyte)0, (GLubyte)255, (GLubyte)0)
// end of [glColor_clock_decor]

(* ****** ****** *)

#define RAD1 0.35
#define RAD2 0.30

fn draw_clock_face
  {n:int | n >= 3} (n: int n): void = () where {
  val delta = 2*PI / n
  #define ANGLE_INIT PI/2
  fun loop {i:nat | i < n} .<n-i>. (
      i: int i
    , x1: double, y1: double
    , x2: double, y2: double
    , angle: double
    ) :<cloref1> void = let
    val i = i + 1
    val angle = (
      if i < n then angle + delta else ANGLE_INIT
    ) : double
    val sin_ = sin angle and cos_ = cos angle
//
    val (pf_beg | ()) = glBegin (GL_POLYGON)
    val () = glColor_clock_base ()
    val () = glVertex2d (0.0, 0.0)
    val () = glVertex2d (x2, y2)
    val x2_new = RAD2 * cos_ and y2_new = RAD2 * sin_
    val () = glVertex2d (x2_new, y2_new)
    val () = glEnd (pf_beg | (*none*))
//
    val (pf_beg | ()) = glBegin (GL_POLYGON)
    val () = glColor_clock_decor ()
    val () = glVertex2d (x2, y2)
    val () = glVertex2d (x1, y1)
    val x1_new = RAD1 * cos_ and y1_new = RAD1 * sin_
    val () = glVertex2d (x1_new, y1_new)
    val () = glVertex2d (x2_new, y2_new)
    val () = glEnd (pf_beg | (*none*))
  in
    if i < n then loop (i, x1_new, y1_new, x2_new, y2_new, angle)
  end // end of [loop]
  val () = loop (0, 0.0, RAD1, 0.0, RAD2, ANGLE_INIT)
} // end of [draw_clock_face]

(* ****** ****** *)

val SQRT2 = 2 * sin (PI/4)

macdef RAD_DECOR = 0.70*(RAD2*SQRT2)

fn draw_clock_decor () = let
  fun fdraw {n:nat | n >= 1}
    (n: int n) = loop
    (0, SQRT2/2, ~SQRT2/2, ~PI/4) where {
    val delta = 0.5*PI/n
    fun loop {i:nat | i <= n} .<n-i>. (
        i: int i, x: double, y: double, angle: double
      ) :<cloref1> void =
      if i < n then let
        val (pf_beg | ()) = glBegin (GL_POLYGON)
        val () = glVertex2d (0.0, 0.0)
        val () = glVertex2d (x * RAD_DECOR, y * RAD_DECOR)
        val angle = angle + delta
        val sin_ = sin angle and cos_ = cos angle
        val x = SQRT2 - cos_ and y = sin_
        val () = glVertex2d (x * RAD_DECOR, y * RAD_DECOR)
        val () = glEnd (pf_beg | (*none*))
      in
        loop (i+1, x, y, angle)
      end else ()
    // end of [loop]
  } // end of [fdraw]
  val () = glColor_clock_decor ()
  val (pf_mat | ()) = glPushMatrix ()
  val () = glRotated (45.0, 0.0, 0.0, 1.0)
  val () = fdraw (128)
  val () = glPopMatrix (pf_mat | (*none*))
  val (pf_mat | ()) = glPushMatrix ()
  val () = glRotated (135.0, 0.0, 0.0, 1.0)
  val () = fdraw (128)
  val () = glPopMatrix (pf_mat | (*none*))
  val (pf_mat | ()) = glPushMatrix ()
  val () = glRotated (225.0, 0.0, 0.0, 1.0)
  val () = fdraw (128)
  val () = glPopMatrix (pf_mat | (*none*))
  val (pf_mat | ()) = glPushMatrix ()
  val () = glRotated (315.0, 0.0, 0.0, 1.0)
  val () = fdraw (128)
  val () = glPopMatrix (pf_mat | (*none*))
in
  // nothing
end // end of [draw_clock_decor]

(* ****** ****** *)

fn draw_clock_center (): void = () where {
  val () = glColor3d (0.0, 0.0, 0.0)
  val (pf_obj | p_obj) = gluNewQuadric_exn ()
  val () = gluDisk (!p_obj, (GLdouble)0.0, (GLdouble)0.025, 8, 1)
  val () = gluDeleteQuadric (pf_obj | p_obj)
} // end of [draw_clock_center]

(* ****** ****** *)

#define HAND_H_BOT 0.016
#define HAND_H_MID 0.025
#define HAND_H_TOP 0.010
#define HAND_H_LEN1 0.18
#define HAND_H_LEN2 0.05
fn draw_clock_hand_h (): void = () where {
  val () = glEnable (GL_POLYGON_SMOOTH)
  val (pf_beg | ()) = glBegin (GL_POLYGON)
  val () = glColor3ub ((GLubyte)0, (GLubyte)0, (GLubyte)0)
//
  val () = glVertex2d (0.0,  HAND_H_MID/2)
  val () = glVertex2d (HAND_H_LEN1,  HAND_H_TOP/2)
  val () = glVertex2d (HAND_H_LEN1, ~HAND_H_TOP/2)
  val () = glVertex2d (0.0, ~HAND_H_MID/2)  
//
  val () = glVertex2d (0.0,  HAND_H_MID/2)
  val () = glVertex2d (~HAND_H_LEN2,  HAND_H_BOT/2)
  val () = glVertex2d (~HAND_H_LEN2, ~HAND_H_BOT/2)
  val () = glVertex2d (0.0, ~HAND_H_MID/2)  
//
  val () = glEnd (pf_beg | (*none*))
  val () = glDisable (GL_POLYGON_SMOOTH)
} // end of [draw_clock_hand_h]

#define HAND_M_BOT 0.012
#define HAND_M_MID 0.020
#define HAND_M_TOP 0.008
#define HAND_M_LEN1 0.25
#define HAND_M_LEN2 0.05
fn draw_clock_hand_m (): void = () where {
  val () = glEnable (GL_POLYGON_SMOOTH)
  val (pf_beg | ()) = glBegin (GL_POLYGON)
  val () = glColor3ub ((GLubyte)0, (GLubyte)0, (GLubyte)0)
//
  val () = glVertex2d (0.0,  HAND_M_MID/2)
  val () = glVertex2d (HAND_M_LEN1,  HAND_M_TOP/2)
  val () = glVertex2d (HAND_M_LEN1, ~HAND_M_TOP/2)
  val () = glVertex2d (0.0, ~HAND_M_MID/2)  
//
  val () = glVertex2d (0.0,  HAND_M_MID/2)
  val () = glVertex2d (~HAND_M_LEN2,  HAND_M_BOT/2)
  val () = glVertex2d (~HAND_M_LEN2, ~HAND_M_BOT/2)
  val () = glVertex2d (0.0, ~HAND_M_MID/2)  
//
  val () = glEnd (pf_beg | (*none*))
  val () = glDisable (GL_POLYGON_SMOOTH)
} // end of [draw_clock_hand_m]

(* ****** ****** *)

extern
fun initialize (): void = "initialize"
implement initialize () = let
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glEnable (GL_BLEND)
  val () = glBlendFunc (GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
  val () = glHint (GL_POLYGON_SMOOTH_HINT, GL_DONT_CARE)
  val () = glShadeModel (GL_FLAT)
in
  // empty
end // end of [initialize]

(* ****** ****** *)

val theHourRef: ref int = ref_make_elt<int> (~1)
val theMinuteRef : ref int = ref_make_elt<int> (~1)

extern
fun display (): void = "display"
implement display () = let
  val h = !theHourRef
  val h = (if h >= 12 then h - 12 else h): int
  val m = !theMinuteRef
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = draw_clock_face (128)
  val () = draw_clock_decor ()
//
  val () = draw_clock_center ()
//
  val (pf_mat | ()) = glPushMatrix ()
  val h_angle = 90 - (30.0*h + 0.50*m)
  val () = glRotated (h_angle, 0.0, 0.0, 1.0)
  val () = draw_clock_hand_h ()
  val () = glPopMatrix (pf_mat | (*none*))
//
  val (pf_mat | ()) = glPushMatrix ()
  val m_angle = 90 - 6.0*m
  val () = glRotated (m_angle, 0.0, 0.0, 1.0)
  val () = draw_clock_hand_m ()
  val () = glPopMatrix (pf_mat | (*none*))
  val () = glutSwapBuffers ()
in
  // empty
end // end of [display]

(* ****** ****** *)

extern
fun reshape (w: int, h: int): void = "reshape"
implement reshape (w, h) = let
  val wh = min (w, h)
  val () = glViewport (0, 0, w, h)
  val w = double_of w and h = double_of h
  val wh = double_of wh
  val r_w = w/wh and r_h = h/wh
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = glOrtho (~r_w, r_w, ~r_h, r_h, ~1.0, 1.0)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
in
  // empty
end // end of [reshape]

(* ****** ****** *)

staload "libc/SATS/time.sats"

#define INTERVAL 1000
#define i2u uint_of_int

extern fun clock_timer (flag: int): void = "clock_timer"

implement clock_timer (flag) = let
(*
  val () = begin
    prerr "timer: flag = "; prerr flag; prerr_newline ()
  end // end of [va]
*)
  var changed: bool = false
  var t: time_t // unintialized
  val () = assertloc (time_get_and_set (t))
  prval () = opt_unsome {time_t} (t)
  var tm: tm_struct // unintialized
  val _ptr = localtime_r (t, tm)
  val () = assert_errmsg (_ptr > null, #LOCATION)
  prval () = opt_unsome {tm_struct} (tm)
  val m_new = tm.tm_min
  val m_old = !theMinuteRef
  val () = if (m_new <> m_old) then let
    val () = changed := true
    val () = !theHourRef := tm.tm_hour
    val () = !theMinuteRef := m_new
  in
    // nothing
  end // end of [val]
  val () = if changed then glutPostRedisplay ()
in
  glutTimerFunc ((i2u)INTERVAL, clock_timer, 0) ;
end // end of [timer]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$

ats_void_type mainats
  (ats_int_type argc, ats_ptr_type argv) {
  glutInit ((int*)&argc, (char**)argv) ;
  glutInitDisplayMode (GLUT_DOUBLE | GLUT_RGB) ;
  glutInitWindowSize (500, 500) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow(((char**)argv)[0]) ;
  initialize () ;
  glutDisplayFunc (display) ;
  glutReshapeFunc (reshape) ;
  // glutMouseFunc (mouse) ;
  clock_timer (0) ;
  glutMainLoop () ;
  return ; // deadcode as [glutMainLoop] never returns
} /* end of [mainats] */

%} // end of [%{$]

(* ****** ****** *)

(* end of [GL-test08.dats] *)
