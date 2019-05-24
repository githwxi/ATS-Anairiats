(*
**
** A simple OpenGL example:
**   randomly generated polygons purturbing around
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: January, 2010
**
*)

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

typedef point = @{
  x= double, y= double
, r= double, b= double, g= double, a= double
} // end of [point]

viewtypedef pgn (n:int) = @{
  nvrtx= int n
, cntr_x= double, cntr_y = double
, pgn_z= double
, vrtxlst= list_vt (point, n)
, zrot_v= double // rotating velocity
, angle= double // current angle
} // end of [pgn]

viewtypedef pgn0 = pgn 0
viewtypedef pgn = [n:nat] pgn (n)
viewtypedef pgnlst = List_vt (pgn)

(* ****** ****** *)

staload MATH = "libc/SATS/math.sats"

macdef PI = $MATH.M_PI
macdef PI2 = 2 * PI
macdef sin = $MATH.sin
macdef cos = $MATH.cos

(* ****** ****** *)

staload RAND = "libc/SATS/random.sats"
macdef drand48 = $RAND.drand48
val () = $RAND.srand48_with_time () // generating a new seed

(* ****** ****** *)

#define NSIDE_MAX 8.0
#define ROT_V_MAX 30.0

fun pgn_make (pgn: &pgn0? >> pgn): void = let
  val n = 3 + int_of_double ((NSIDE_MAX - 3.000001) * drand48 ())
  val n = if n >= 7 then 128 else n
  val [n:int] n = int1_of_int (n)
  val () = assert (n >= 3)
(*
  val () = printf ("pgn_make: n = %i\n", @(n))
*)
  val theta0 = drand48 () * PI2
  val delta = PI2 / n
  val pts = loop (n, theta0) where {
    fun loop {n:nat}
      (n: int n, theta: double):<cloref1> list_vt (point, n) =
      if n > 0 then let
        val xs1 = loop (n-1, theta + delta)
        val xs = list_vt_cons {point} (?, xs1)
        val list_vt_cons (!p_x, _) = xs
        val () = p_x->x := cos theta
        val () = p_x->y := sin theta
        val () = p_x->r := drand48 ()
        val () = p_x->g := drand48 ()
        val () = p_x->b := drand48 ()
        val () = p_x->a := drand48 ()
      in
        fold@ xs; xs
      end else list_vt_nil ()
  } // end of [loop]
in
  pgn.nvrtx := n;
  pgn.cntr_x := drand48 () - 0.5;
  pgn.cntr_y := drand48 () - 0.5;
  pgn.pgn_z := 0.0 ; // pgn.pgn_z := drand48 () - 0.5;
  pgn.vrtxlst := pts;
  pgn.zrot_v := ROT_V_MAX * (drand48 () - 0.5);
  pgn.angle := 360 * drand48 ()
end // end of [pgn_make]

fn pgn_free
  (pgn: &pgn >> pgn?):<> void = list_vt_free (pgn.vrtxlst)
// end of [pgn_free]
fun pgnlst_free {n:nat} .<n>. (pgns: list_vt (pgn, n)):<> void =
  case+ pgns of
  | list_vt_cons (!p_pgn, pgns1) => (
      pgn_free !p_pgn; free@ {pgn} {0} pgns; pgnlst_free pgns1
    ) // end of [list_vt_cons]
  | ~list_vt_nil () => ()
// end of [pgnlst_free]

fun pgnlst_add {k0,k:nat} .<k>.
  (k: int k, res: &list_vt (pgn, k0) >> list_vt (pgn, k0+k)): void =
  if k > 0 then let
    val res_new =
      list_vt_cons {pgn0} {k0} (?, ?)
    val list_vt_cons (!p_x, !p_xs1) = res_new
    val () = pgn_make (!p_x)
    val () = !p_xs1 := res
  in
    fold@ res_new; res := res_new; pgnlst_add (k-1, res)
  end // end of [if]
// end of [pgnlst_add]

(* ****** ****** *)

var thePgnLst: pgnlst = let
  var res = list_vt_nil (); val () = pgnlst_add (32, res)
in
  res
end // end of [var]

val (pf_thePgnLst | ()) =
  vbox_make_view_ptr {pgnlst} (view@ thePgnLst | &thePgnLst)
// end of [prval]

(* ****** ****** *)

fn thePgnLst_add {k:nat}
  (k: int k): void = let
  prval vbox pf = pf_thePgnLst
in
  $effmask_ref (pgnlst_add (k, thePgnLst))
end // end of [thePgnLst_add]

fn thePgnLst_del {k:nat}
  (k: int k): void = let
  fun loop {k:nat} .<k>.
    (pgns: pgnlst, k: int k):<> pgnlst =
    if k > 0 then begin case+ pgns of
      | list_vt_cons (!p_pgn, pgns1) => let
          val () =  pgn_free (!p_pgn)
          val () = free@ {pgn} {0} (pgns)
        in
          loop {k-1} (pgns1, k-1)
        end // end of [list_vt_cons]
      | list_vt_nil () => (fold@ pgns; pgns)
    end else pgns
  // end of [loop]
  prval vbox pf = pf_thePgnLst
in
  thePgnLst := loop (thePgnLst, k)
end // end of [thePgnLst_del]

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

#define RADIUS 0.1

(* ****** ****** *)

#define PERTURB_COEFF 1.0/10
fn perturb (x: double): double = let
  val alpha = (drand48 () - 0.5)
in
  x + PERTURB_COEFF * alpha
end // end of [perturb]

(* ****** ****** *)

extern fun draw_pgn (pgn: &pgn): void = "draw_pgn"

implement draw_pgn (pgn) = let
  fun loop {n:nat} .<n>. (
      pts: !list_vt (point, n), pgn_z: double
    ) : void =
    case+ pts of
    | list_vt_cons (pt, !p_pts1) => let
        val () = glColor4d (pt.r, pt.g, pt.b, pt.a)
        val () = glVertex3d (pt.x, pt.y, pgn_z)
        val () = loop (!p_pts1, pgn_z)
      in
        fold@ pts
      end // end of [list_vt_cons]
    | list_vt_nil () => fold@ pts
  // end of [loop]
  val (pf_pushmat | ()) = glPushMatrix ()
  val xc = perturb (pgn.cntr_x) and yc = perturb (pgn.cntr_y)
  val () = glTranslated (xc, yc, 0.0)
  val () = glRotated (pgn.angle, 0.0, 0.0, 1.0)
  val () = glScaled (RADIUS, RADIUS, 1.0)
  val () = glPolygonMode (GL_FRONT, GL_FILL)
  val (pf_begin | ()) = glBegin (GL_POLYGON)
  val () = loop (pgn.vrtxlst, pgn.pgn_z)
  val () = glEnd (pf_begin | (*none*))
  val () = glPopMatrix (pf_pushmat | (*none*))
in
  // nothing
end // end of [draw_pgn]

(* ****** ****** *)

(*
fun draw_pgnlst (pgns: !pgnlst): void =
  case+ pgns of
  | list_vt_cons (!p_pgn, !p_pgns1) => begin
      draw_pgn (!p_pgn); draw_pgnlst (!p_pgns1); fold@ pgns
    end // end of [list_vt_cons]
  | list_vt_nil () => fold@ pgns
// end of [draw_pgnlst]
*)

extern fun{a:t@ype} array_ptr_shuffle 
  {n:nat} {l:addr} (pf: !array_v (a, n, l) | p: ptr l, n: size_t n):<> void
// end of [extern]

implement{a} array_ptr_shuffle
  (pf | p, n) = loop (pf | p, n) where {
  #define i2sz size1_of_int1; #define sz2i int1_of_size1
  fun loop {n:nat} {l:addr} .<n>.
    (pf: !array_v (a, n, l) | p: ptr l, n: size_t n):<> void =
    if n >= 2 then let
      val i = $effmask_ref ($RAND.randint (sz2i n))
      val () = if i <> 0 then array_ptr_exch<a> (!p, 0, i2sz i)
      prval (pf1, pf2) = array_v_uncons {a} (pf)
      val () = loop (pf2 | p + sizeof<a>, n-1)
      prval () = pf := array_v_cons {a} (pf1, pf2)
    in
      // nothing
    end // end of [if]
  // end of [loop]  
} (* end of [array_ptr_shuffle] *)

fn draw_pgnlst {n:nat}
  (pgns: !list_vt (pgn, n)): void = let
  val n = list_vt_length<pgn> (pgns)
  abst@ype a = pgn?
  val xs = __cast pgns where {
    extern castfn __cast
      (xs: !list_vt (pgn, n) >> list_vt (pgn, n)):<> list (a, n)
  } // end of [val]
  var !p_arr with pf_arr = @[a][n]() // stack allocation
  val () = array_ptr_initialize_lst<a> (!p_arr, xs)
  val asz = size1_of_int1 n
  val () = array_ptr_shuffle<a> (pf_arr | p_arr, asz)
//  
  val () = let
    extern fun f (x: &a):<> void = "draw_pgn"
  in
    array_ptr_foreach_fun<a> (!p_arr, f, asz)
  end // end of [val]
//
  fn f (pgn: &pgn): void = pgn.angle := pgn.angle + pgn.zrot_v
  val () = list_vt_foreach_fun (pgns, f)
in
  // nothing
end // end of [draw_pgnlst]

(* ****** ****** *)

extern
fun initialize (): void = "initialize"
implement initialize () = let
(*
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = glOrtho (0.0, 1.0, 0.0, 1.0, ~1.0, 1.0)
*)
in
  // empty
end // end of [initialize]

(* ****** ****** *)

extern
fun finalize (): void = "finalize"
implement finalize () = () where {
  val () = () where {
    prval vbox pf = pf_thePgnLst
    val () = pgnlst_free (thePgnLst)
    val () = thePgnLst := list_vt_nil ()
  } // end of [val]
  val () = exit (0) // normal exit
} // end of [finalize]

(* ****** ****** *)

(*
#define THE_YROT_V 5.0
var the_yrot_angle = 0.0
*)

extern
fun display (): void = "display"
implement display () = let
  val () = glClear (GL_COLOR_BUFFER_BIT)
(*
  val (pf_mat | ()) = glPushMatrix ()
  val t0 = the_yrot_angle
  val t1 = t0 + THE_YROT_V
  val t1 = (if t1 >= 360.0 then t1 - 360.0 else t1): double
  val () = the_yrot_angle := t1
  val () = glRotated (t0, 0., 1., 0.)
*)
  val () = let
    prval vbox pflst = pf_thePgnLst
  in
    $effmask_ref (draw_pgnlst thePgnLst)
  end // end of [val]
(*
  val () = glPopMatrix (pf_mat | (*none*))
*)
  val () = glutSwapBuffers ()
in
  // nothing
end // end of [display]

(* ****** ****** *)

extern
fun reshape (w: int, h: int): void = "reshape"
implement reshape (w, h) = let
  val wh = min (w, h)
  val () = glViewport (0, 0, w, h)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val a = 2.0 / 3
  val w = double_of w and h = double_of h
  val wh = double_of wh
  val r_w = w/wh and r_h = h/wh
  val () = glOrtho (~a*r_w, a*r_w, ~a*r_h, a*r_h, ~1.0, 1.0)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
in
  // empty
end // end of [reshape]

(* ****** ****** *)

extern fun keyboard (
  key: uchar, x: int, y: int
) : void = "keyboard"
implement keyboard
  (key, x, y) = let
  val key = char_of_uchar key
in
  case+ key of
  | 'a' => thePgnLst_add (1)
  | 'A' => thePgnLst_add (5)
  | 'd' => thePgnLst_del (1)
  | 'D' => thePgnLst_del (5)
  | 'q' => finalize ()
  | _ when (int_of (key) = 27) => finalize ()
  | _ => () // ignored
end // end of [keyboard]

(* ****** ****** *)

macdef TIME_INTERVAL = 150U

extern
fun timer (flag: int): void = "timer"
implement timer (flag) = let
  val () = glutPostRedisplay ()
in
  glutTimerFunc (TIME_INTERVAL, timer, 0)
end // end of [timer]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$

ats_void_type mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  glutInit ((int*)&argc, (char**)argv) ;
  glutInitDisplayMode (GLUT_DOUBLE | GLUT_RGB) ;
  glutInitWindowSize (500, 500) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow("Fidgeting Shapes") ;
  initialize () ;
  glutDisplayFunc (display) ;
  glutReshapeFunc (reshape) ;
  glutKeyboardFunc (keyboard) ;
  timer (0) ;
  glutMainLoop () ;
  return ; /* deadcode */
} // end of [mainats]

%} // end of [%{$]

(* ****** ****** *)

(* end of [GL-test07.dats] *)
