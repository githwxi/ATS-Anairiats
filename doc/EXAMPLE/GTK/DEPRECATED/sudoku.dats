(*******************************************************************)
(*                                                                 *)
(*                        Applied Type System                      *)
(*                                                                 *)
(*                          (c) Hongwei Xi                         *)
(*                                                                 *)
(*                            2002 - 2007                          *)
(*                                                                 *)
(*                         Boston University                       *)
(*                                                                 *)
(*                   Distributed by permission only.               *)
(*                                                                 *)
(*******************************************************************)

(*
**
** Author: Hongwei Xi (September 2007)
**
*)

(* ****** ****** *)

//
// HX: please do not "prettify" the code; please keep it as it is (10/20/2009)
//

(* ****** ****** *)

%{^

#include "prelude/CATS/array.cats"
#include "libc/sys/CATS/types.cats"
#include "libc/CATS/random.cats"
#include "libc/CATS/unistd.cats"

#include "gtk.cats"
#include "glib.cats"

extern void mainats (ats_int_type argc, ats_ptr_type argv) ;

%}

staload "gtk.sats"
staload "glib.sats"
staload "libc/SATS/random.sats"

(* ****** ****** *)

staload "prelude/DATS/array.dats"
staload "prelude/DATS/matrix.dats"
staload "prelude/DATS/reference.dats"

(* ****** ****** *)

#define GTRUE GBOOLEAN_TRUE
#define GFALSE GBOOLEAN_FALSE

(* ****** ****** *)

#define NMAX 10
#define NMAX1 9
#define NMAX12 81 // NMAX1 * NMAX1

val the_digits: array (int, NMAX) =
  array_make_arrpsz{int}($arrpsz(0, 0, 0, 0, 0, 0, 0, 0, 0, 0))

fn digits_initialize () = let
  fun loop (i: natLte NMAX): void =
    if (i < NMAX) then (the_digits[i] := 0; loop (i+1))
  in
    loop 0
  end // end of [loop]

val the_labels: array (string, 10) =
  array_make_arrpsz{string}($arrpsz("", "1", "2", "3", "4", "5", "6", "7", "8", "9"))

val the_ulabels: array (string, 10) =
  array_make_arrpsz{string}($arrpsz("", "_1", "_2", "_3", "_4", "_5", "_6", "_7", "_8", "_9"))

typedef digit = [i:nat | i < NMAX] int i

val the_puzzle_ori = matrix_make_elt<digit> (NMAX1, NMAX1, 0)
val the_puzzle_cur = matrix_make_elt<digit> (NMAX1, NMAX1, 0)

//

extern fun error_value_read (): int = "error_value_read"
extern fun error_value_write (ans: int): void = "error_value_write"

%{

int the_error_value = 0 ;

ats_int_type error_value_read () {
  return the_error_value;
 }

ats_void_type error_value_write (ats_int_type ans) {
  the_error_value = ans ; return ;
}

%}

//

fn puzzle_row_verify_one (i: natLt NMAX1): int =
  let
    fun loop (j: natLte NMAX1):<cloptr1> int =
      if j < NMAX1 then let
        val ij = the_puzzle_cur[i, NMAX1, j]
(*
        val () = printf
          ("puzzle_row_verify_one: loop: i = %i and j = %i and ij = %i\n", @(i, j, ij))
*)
      in
        if ij > 0 then
          if the_digits[ij] > 0 then ij (* repeated entry *)
          else (the_digits[ij] := 1; loop (j+1))
        else loop (j+1)
      end else begin
        0 (* free of conflict *)
      end
  in
    digits_initialize (); loop (0)
  end

fn puzzle_row_verify_all (): int (* row number *) =
  let
    fun loop (i: natLte NMAX1): int =
      if i < NMAX1 then let
        val ans = puzzle_row_verify_one i
(*
        val () =
          printf ("puzzle_row_verify_all: loop: i = %i and ans = %i\n", @(i, ans))
*)
      in
        if ans = 0 then loop (i+1) else (error_value_write ans; i+1)
      end else begin
        0 (* free of conflict *)
      end
  in
    loop 0
  end

//

fn puzzle_col_verify_one (j: natLt NMAX1): int =
  let
    fun loop (i: natLte NMAX1):<cloptr1> int =
      if i < NMAX1 then let
        val ij = the_puzzle_cur[i, NMAX1, j]
(*
        val () = printf
          ("puzzle_col_verify_one: loop: i = %i and j = %i and ij = %i\n", @(i, j, ij))
*)
      in
        if ij > 0 then
          if the_digits[ij] > 0 then ij (* repeated entry *)
          else (the_digits[ij] := 1; loop (i+1))
        else loop (i+1)
      end else begin
        0 (* free of conflict *)
      end
  in
    digits_initialize (); loop (0)
  end

fn puzzle_col_verify_all (): int (* row number *) =
  let
    fun loop (j: natLte NMAX1):<cloptr1> int =
      if j < NMAX1 then let
        val ans = puzzle_col_verify_one j
      in
        if ans = 0 then loop (j+1) else (error_value_write ans; j+1)
      end else begin
        0 (* free of conflict *)
      end
  in
    loop 0
  end

//

fn puzzle_squ_verify_one (i0: natLte (NMAX1-3), j0: natLte (NMAX1-3)): int =
  let
    fun loop1 (i: natLte NMAX1):<cloptr1> int =
      if (i < i0 + 3) then loop2 (i, j0) else 0
    and loop2 (i: natLt NMAX1, j: natLte NMAX1):<cloptr1> int =
      if (j < j0 + 3) then let
        val ij = the_puzzle_cur[i, NMAX1, j]
      in
        if ij > 0 then
          if the_digits[ij] > 0 then ij (* repeated entry *)
          else (the_digits[ij] := 1; loop2 (i, j+1))
        else loop2 (i, j+1)
      end else begin
        loop1 (i+1)
      end
  in
    digits_initialize (); loop1 (i0)
  end

fn puzzle_squ_verify_all (): int =
  let
    fun loop1 (i: Nat): int =
      if i + 3 <= NMAX1 then loop2 (i, 0) else 0
    and loop2 (i: natLte (NMAX1-3), j:Nat): int =
      if j + 3 <= NMAX1 then let
        val ans = puzzle_squ_verify_one (i, j)
      in
        if ans = 0 then loop2 (i, j + 3)
        else begin
          error_value_write ans; i + j / 3 + 1
        end
      end else begin
        loop1 (i + 3)
      end
  in
    loop1 (0)
  end

fn puzzle_ent_verify_all (): int =
  let
    fun loop1 (i: natLte NMAX1): int =
      if i < NMAX1 then loop2 (i, 0) else 0
    and loop2 (i: natLt NMAX1, j: natLte NMAX1): int =
      if j < NMAX1 then let
        val ij = the_puzzle_cur[i, NMAX1, j]
      in
        if ij > 0 then loop2 (i, j+1) else
          (error_value_write 0; i * NMAX1 + j + 1)
      end else begin
        loop1 (i+1)
      end
  in
    loop1 (0)
  end

(* ****** ****** *)

#define nil list_vt_nil
#define cons list_vt_cons

fun gtk_box_pack_start_buttons {c:gcls} {n:nat} {l:addr}
  (pf: gcls_lte (c, GtkBox) | box: &gobj c, bts: list_vt (gobjptr GtkButton, n))
  : void =
  case+ bts of
    | ~cons (bt, bts) => let
        val (pf_but | p_but) = bt
      in
        gtk_box_pack_start
          (pf, GtkButtonIsGtkWidget, pf_but | box, p_but, GTRUE, GFALSE, 0);
        gtk_box_pack_start_buttons (pf | box, bts)
      end
    | ~nil () => ()

(* ****** ****** *)

fn window_message_make_with_window_buttons {n:pos}
  (msg: string, r_win: gobjref GtkWindow, bts: list_vt (gobjptr GtkButton, n))
  : void = let

val (pf_lab | p_lab) = gtk_label_new (msg)
val () = gtk_widget_show (GtkLabelIsGtkWidget | !p_lab)

//

val (pf_hsep | p_hsep) = gtk_hseparator_new ()
val () = gtk_widget_show (GtkHSeparatorIsGtkWidget | !p_hsep)

//

val (pf_hbox | p_hbox) = gtk_hbox_new (GFALSE, 0)
val () = gtk_widget_show (GtkHBoxIsGtkWidget | !p_hbox)

val () = gtk_box_pack_start_buttons (GtkHBoxIsGtkBox | !p_hbox, bts)

//

val (pf_vbox | p_vbox) = gtk_vbox_new (GFALSE, 0)
val () = gtk_widget_show (GtkVBoxIsGtkWidget | !p_vbox)

val () = gtk_box_pack_start
  (GtkVBoxIsGtkBox, GtkLabelIsGtkWidget, pf_lab |
   !p_vbox, p_lab, GTRUE, GFALSE, 0)

val () = gtk_box_pack_start
  (GtkVBoxIsGtkBox, GtkHSeparatorIsGtkWidget, pf_hsep |
   !p_vbox, p_hsep, GFALSE, GFALSE, 2)

val () = gtk_box_pack_end
  (GtkVBoxIsGtkBox, GtkHBoxIsGtkWidget, pf_hbox |
   !p_vbox, p_hbox, GFALSE, GFALSE, 0)

val () = let
    val (pf_win | p_win) = g_objref_get (r_win)
 in
    gtk_container_add
     (GtkWindowIsGtkContainer, GtkVBoxIsGtkWidget, pf_vbox | !p_win, p_vbox);
    g_objref_set (pf_win | r_win, p_win)
 end

in

()

end

//

fn window_message_ok_make (msg: string): void = let

val (pf_win | p_win) = gtk_window_new (GTK_WINDOW_TOPLEVEL)
val () = gtk_widget_set_size_request
  (GtkWindowIsGtkWidget | !p_win, 250, 50)
val () = gtk_widget_show (GtkWindowIsGtkWidget | !p_win)

val r_win = g_objref_make_some (pf_win | p_win)

val (pf_but | p_but) = gtk_button_new_with_label ("OK")
val () = gtk_widget_show (GtkButtonIsGtkWidget | !p_but)
fn action {c:gcls}
  (wid: &gobj GtkButton, r_win: gobjref GtkWindow): void =
 let
    val (pf_win | p_win) = g_objref_get (r_win)
 in
    gtk_widget_destroy (GtkWindowIsGtkWidget, pf_win | p_win)
 end
val () = g_signal_connect
  {gobjref GtkWindow} (!p_but, GSIGNAL_CLICKED, action, r_win)

val bts = cons ((pf_but | p_but), nil ())

in

window_message_make_with_window_buttons (msg, r_win, bts)

end

//

typedef thunk_t = () -<cloref1> void

val the_quit_yes_action = ref_make_elt<thunk_t> (lam () => ())

fn window_message_yesno_make
  (msg: string, yes_lab: string, no_lab: string): void = let

val (pf_win | p_win) = gtk_window_new (GTK_WINDOW_TOPLEVEL)
val () = gtk_widget_set_size_request
  (GtkWindowIsGtkWidget | !p_win, 150, 50)
val () = gtk_widget_show (GtkWindowIsGtkWidget | !p_win)

val r_win = g_objref_make_some (pf_win | p_win)

val (pf_yes_but | p_yes_but) = gtk_button_new_with_label (yes_lab)
val () = gtk_widget_show (GtkButtonIsGtkWidget | !p_yes_but)
fn yes_action {c:gcls}
  (wid: &gobj GtkButton, r_win: gobjref GtkWindow): void =
 let
   val (pf_win | p_win) = g_objref_get (r_win)
 in
   gtk_widget_destroy (GtkWindowIsGtkWidget, pf_win | p_win);
   !the_quit_yes_action ()
 end
val () = g_signal_connect
  {gobjref GtkWindow} (!p_yes_but, GSIGNAL_CLICKED, yes_action, r_win)

val (pf_no_but | p_no_but) = gtk_button_new_with_label (no_lab)
val () = gtk_widget_show (GtkButtonIsGtkWidget | !p_no_but)
fn no_action {c:gcls}
  (wid: &gobj GtkButton, r_win: gobjref GtkWindow): void =
 let
    val (pf_win | p_win) = g_objref_get (r_win)
 in
    gtk_widget_destroy (GtkWindowIsGtkWidget, pf_win | p_win)
 end
val () = g_signal_connect
  {gobjref GtkWindow} (!p_no_but, GSIGNAL_CLICKED, no_action, r_win)

val bts = nil ()
val bts = cons ((pf_yes_but | p_yes_but), bts)
val bts = cons ((pf_no_but | p_no_but), bts)

in

window_message_make_with_window_buttons (msg, r_win, bts)

end

//

(* ****** ****** *)

#define p2s string_of_strptr

fn button_verify_make (): [l:addr] (gobj GtkButton @ l | ptr l) =
  let
    fn msg_gen (loc: string, ans: int, err: int): string =
      if err > 0 then begin
        p2s (tostringf ("The %s(%i) is incorrect: repeated entry(%i)", @(loc, ans, err)))
      end else let
         val xpos = (ans - 1) / NMAX1
         val ypos = (ans - 1) - xpos * NMAX1
      in
         p2s (tostringf ("The %s(%i,%i) is unfinished", @(loc, xpos+1, ypos+1)))
      end

    fn action {c:gcls} (wid: &gobj GtkButton, data: &void): void =
      let
        var ans_row: int = (~1: int)
        var ans_col: int = (~1: int)
        var ans_squ: int = (~1: int)
        var ans_ent: int = (~1: int)
        val () = ans_row := puzzle_row_verify_all ()
(*
	val () = (print "ans_row = "; print ans_row; print_newline ())
*)
        val () =
          if ans_row = 0 then ans_col := puzzle_col_verify_all ()
(*
	val () = (print "ans_col = "; print ans_col; print_newline ())
*)
        val () =
          if ans_col = 0 then ans_squ := puzzle_squ_verify_all ()
        val () =
          if ans_squ = 0 then ans_ent := puzzle_ent_verify_all ()
        val err = error_value_read ()
(*
        val () = printf ("button_verify_action: action: err = %i\n", @(err))
*)
        val msg: string =
          if ans_row > 0 then msg_gen ("row", ans_row, err)
          else if ans_col > 0 then msg_gen ("column", ans_col, err)
          else if ans_squ > 0 then msg_gen ("square", ans_squ, err)
          else if ans_ent > 0 then msg_gen ("entry", ans_ent, err)
          else begin
            "A solution is found!"
          end
      in
        window_message_ok_make msg
      end
    val dummy: ref void = ref_void_make ()
    val (pf_button | p_button) = gtk_button_new_with_label ("verify")
    val () = gtk_widget_show (GtkButtonIsGtkWidget | !p_button)
    val () = g_signal_connect_ref {void}
      (!p_button, GSIGNAL_CLICKED, action, dummy)
  in
    (pf_button | p_button)
  end

(* ****** ****** *)

fn button_quit_make (r_win: gobjref GtkWindow)
  : [l:addr] (gobj GtkButton @ l | ptr l) =
  let
    fn action {c:gcls}
      (wid: &gobj GtkButton, dummy: &void): void =
      window_message_yesno_make
        ("please confirm", "quit", "cancel")

    val dummy: ref void = ref_void_make ()
    val (pf_button | p_button) = gtk_button_new_with_label ("quit")
    val () = gtk_widget_show (GtkButtonIsGtkWidget | !p_button)
    val () = g_signal_connect_ref {void} (!p_button, GSIGNAL_CLICKED, action, dummy)
  in
    (pf_button | p_button)
  end

(* ****** ****** *)

fn window_delete_event
  (wid: &gobj GtkWindow, evt: &gevent, data: &void): gboolean =
  GFALSE (* [window_destroy] is to be called subsequently *)

fn window_destroy (wid: &gobj GtkWindow, data: &void): void =
  gtk_main_quit ()

extern fun menu_button_press_event (
    button: &gobj GtkButton
  , evt: &gevent
  , is_fixed: bool
  , menu: &gobj GtkMenu
  ) : gboolean
  = "menu_button_press_event"

fn menu_button_press_event_ref
  (button: &gobj GtkButton, evt: &gevent,
   data: &(natLt NMAX1, natLt NMAX1, gobjref GtkMenu))
  : gboolean = let
  val (i, j, r_menu) = data
  val (pf_menu | p_menu) = g_objref_get r_menu
  val is_fixed: bool = the_puzzle_ori[i, NMAX1, j] > 0
  val ans = menu_button_press_event (button, evt, is_fixed, !p_menu)
  val () = g_objref_set (pf_menu | r_menu, p_menu)
in
  ans
end // end of [menu_button_press_event_ref]

fn menu_item_response
  (mi: &gobj (GtkMenuItem),
   data: &(digit, natLt NMAX1, natLt NMAX1, gobjref GtkButton))
  : void = let
  val (digit, i, j, r_button) = data
  val () = the_puzzle_cur[i, NMAX1, j] := digit
  val lab: string = if digit > 0 then the_labels[digit] else "X"
  val (pf_button | p_button) = g_objref_get r_button
  val () = gtk_button_set_label (GtkButtonIsGtkButton | !p_button, lab)
in
  g_objref_set (pf_button | r_button, p_button)
end // end of [menu_item_response]

fun menu_items_append {n:nat | n <= NMAX}
  (menu: &gobj GtkMenu, n: int n,
   i: natLt NMAX1, j: natLt NMAX1, button: gobjref GtkButton): void =
  if n < NMAX then let
    val lab: string = if n > 0 then the_labels[n] else "X"
    val (pf_mi | p_mi) = gtk_menu_item_new_with_label (lab)
    val () = gtk_widget_show (GtkMenuItemIsGtkWidget | !p_mi)
    val () = g_signal_connect_ref
      {@(digit, natLt NMAX1, natLt NMAX1, gobjref GtkButton)}
      (!p_mi, GSIGNAL_ACTIVATE, menu_item_response, ref_make_elt @(n, i, j, button))
    val () = gtk_menu_shell_append
      (GtkMenuIsGtkMenuShell, GtkMenuItemIsGtkMenuItem, pf_mi | menu, p_mi)
  in
    menu_items_append (menu, n + 1, i, j, button) 
  end

(* ****** ****** *)

#define npuzzle 15

val the_puzzles
  : array (string(NMAX12), npuzzle) =
array_make_arrpsz{string(NMAX12)}$arrpsz (
// easy
"....12.7.....6.95.87.4.....4.7......1.......5.6....1.2.....1.36.18.5.....4.68....",
// easy
".762.534.2.94.76.851.6.3.29652...137.........387...96416.3.4.927.39.84.6.981.257.",
// medium
"7.2..8.3..8.2.......96.12.......91.885.....791.38.......73.58.44..7...1......4..2",
// hard
"........1.8.71......9...485.3...2......1..7.6..5.6..39.4.3.........9.5.4.2.......",
// super hard
".2........7.18..9...3...257...2...1..6.5.7.3..9...8.....2...9...37.51.2...6....4.",
// impossible
"4...3.......6..8..........1....5..9..8....6...7.2........1.27..5.3....4.9........",
"7.8...3.....2.1...5.........4.....263...8.......1...9..9.6....4....7.5...........",
"3.7.4...........918........4.....7.....16.......25..........38..9....5...2.6.....",
"7.8...3.....6.1...5.........4.....263...8.......1...9..9.2....4....7.5...........",
"5..7..6....38...........2..62.4............917............35.8.4.....1......9....",
"4..7..6....38...........2..62.5............917............43.8.5.....1......9....",
".4..1.2.......9.7..1..........43.6..8......5....2.....7.5..8......6..3..9........",
"7.5.....2...4.1...3.........1.6..4..2...5...........9....37.....8....6...9.....8.",
".8..1......5....3.......4.....6.5.7.89....2.....3.....2.....1.9..67........4.....",
"......41.9..3.....3...5.....48..7..........62.1.......6..2....5.7....8......9...."
)

(* ****** ****** *)

extern fun natrand48 {n:pos} (range: int n):<!ref> natLt n
  = "natrand48"

%{

ats_int_type natrand48 (ats_int_type range) {
  return (range * atslib_drand48 ()) ;
}

%}

fn puzzle_string_get (): string (NMAX12) = let
  val n = natrand48 (npuzzle)
in
  the_puzzles[n]
end // end of [puzzle_string_get]

extern fun digit_of_char (_: char): digit = "digit_of_char"

%{

ats_int_type digit_of_char (ats_char_type c) {
  if ('0' <= c && c <= '9') return (c - '0') ;
  return 0 ;
}

%}

val the_button_matrix =
  let val r_button = g_objref_make_none () in
    matrix_make_elt<gobjref GtkButton> (NMAX, NMAX, r_button)
  end

fn puzzle_update (): void = let
  val s = puzzle_string_get ()
(*
  val () = (print "puzzle_update: "; print s; print_newline ())
*)
  fun loop1 (i: natLte NMAX1):<cloptr1> void =
    if i < NMAX1 then loop2 (i, 0) else ()

  and loop2 (i: natLt NMAX1, j: natLte NMAX1):<cloptr1> void =
    if j < NMAX1 then let
      val digit = digit_of_char (s[i * NMAX1 + j])
    in
      matrix_set_elt_at__intsz (the_puzzle_ori, i, NMAX1, j, digit);
      matrix_set_elt_at__intsz (the_puzzle_cur, i, NMAX1, j, digit);
      loop2 (i,j+1)
    end else begin
      loop1 (i+1)
    end
in
  loop1 (0)
end // end of [loop2]

fn button_matrix_update (): void = let
  fun loop1 (i: natLte NMAX1): void =
    if i < NMAX1 then loop2 (i, 0) else ()

  and loop2 (i: natLt NMAX1, j: natLte NMAX1): void =
    if j < NMAX1 then let
      val is_fixed: bool = the_puzzle_ori[i, NMAX1, j] > 0
      val r_button = matrix_get_elt_at__intsz (the_button_matrix, i, NMAX, j)
      val lab = let
        val ij = the_puzzle_cur[i, NMAX1, j]
      in
        if is_fixed then the_ulabels[ij] else the_labels[ij]
      end // end of [val]
      val (pf_button | p_button) = g_objref_get r_button
      val () = gtk_button_set_label (GtkButtonIsGtkButton | !p_button, lab)
      val () = g_objref_set (pf_button | r_button, p_button)
    in
      loop2 (i, j+1)
    end else begin
      loop1 (i+1)
    end
in
  loop1 (0)
end // end of [button_matrix_update]

extern fun pause_button_is_on (): bool = "pause_button_is_on"
extern fun pause_button_on (): void = "pause_button_on"
extern fun pause_button_off (): void = "pause_button_off"

%{

int the_pause_param = 0 ;

ats_bool_type pause_button_is_on () {
  return (the_pause_param > 0 ? ats_true_bool : ats_false_bool) ;
}

ats_void_type pause_button_on () { the_pause_param = 1 ; return ; }
ats_void_type pause_button_off () { the_pause_param = 0 ; return ; }

%}

fn pause_update (): void = let
  fun loop1 (i: natLte NMAX1): void =
    if i < NMAX1 then loop2 (i, 0) else ()

  and loop2 (i: natLt NMAX1, j: natLte NMAX1): void =
    if j < NMAX1 then let
      val r_button = the_button_matrix[i, NMAX, j]
      val (pf_button | p_button) = g_objref_get r_button
      val () = gtk_button_set_label (GtkButtonIsGtkButton | !p_button, "X")
      val () = g_objref_set (pf_button | r_button, p_button)
    in
      loop2 (i, j+1)
    end else begin
      loop1 (i+1)
    end // end of [if]
in
  loop1 (0)
end // end of [pause_update]

(* ****** ****** *)

fn button_new_game_make ()
  : [l:addr] (gobj GtkButton @ l | ptr l) = let
  fn action {c:gcls} (wid: &gobj GtkButton, data: &void): void =
    (pause_button_off (); puzzle_update (); button_matrix_update ())

  val dummy: ref void = ref_void_make ()
  val (pf_button | p_button) = gtk_button_new_with_label ("new game")
  val () = gtk_widget_show (GtkButtonIsGtkWidget | !p_button)
  val () = g_signal_connect_ref {void}
    (!p_button, GSIGNAL_CLICKED, action, dummy)
in
  (pf_button | p_button)
end // end of [button_new_game_make]

(* ****** ****** *)

fn button_pause_make ()
  : [l:addr] (gobj GtkButton @ l | ptr l) = let
  fn action {c:gcls}
    (wid: &gobj GtkButton, data: &void): void =
    if pause_button_is_on () then begin
      button_matrix_update (); pause_button_off ()
    end else begin
      pause_update (); pause_button_on ()
    end

  val dummy: ref void = ref_void_make ()
  val (pf_button | p_button) = gtk_button_new_with_label ("pause")
  val () = gtk_widget_show (GtkButtonIsGtkWidget | !p_button)
  val () = g_signal_connect_ref {void}
    (!p_button, GSIGNAL_CLICKED, action, dummy)
in
  (pf_button | p_button)
end // end of [button_pause_make]

(* ****** ****** *)

fn button_matrix_make_with_menu ()
  : [l:addr] (gobj GtkTable @ l | ptr l) = let
  fun loop1 (table: &gobj GtkTable, i: natLte NMAX): void =
    if i < NMAX1 then begin
      if (i + 1) mod 3 = 0 then
        gtk_table_set_row_spacing (GtkTableIsGtkTable | table, i, 3);
      loop2 (table, i, 0)
    end

  and loop2 (table: &gobj GtkTable, i: natLt NMAX1, j: natLte NMAX1): void =
    if j < NMAX1 then let
      val () =
        if (j + 1) mod 3 = 0 then
          gtk_table_set_col_spacing (GtkTableIsGtkTable | table, j, 3)
        else ()
      val (pf_button | p_button) = gtk_button_new_with_mnemonic ("")
      val () = gtk_widget_show (GtkButtonIsGtkWidget | !p_button)
      val r_button = g_objref_make_some (pf_button | p_button)
      val () = the_button_matrix[i, NMAX, j] := r_button

      val (pf_menu | p_menu) = gtk_menu_new ()
      val () = menu_items_append (!p_menu, 0, i, j, r_button)
      val r_menu = g_objref_make_some (pf_menu | p_menu)
      val data: ref @(natLt NMAX1, natLt NMAX1, gobjref GtkMenu) =
        ref_make_elt @(i, j, r_menu)

      val (pf_button | p_button) = g_objref_get r_button
      val () = g_signal_connect_event_ref
        {@(natLt NMAX1, natLt NMAX1, gobjref GtkMenu)}
        (!p_button, GSIGNAL_EVENT, menu_button_press_event_ref, data)
      val (pf_button1 | p_button1) = g_object_ref (pf_button | p_button)
      val () = g_objref_set (pf_button | r_button, p_button)
      val () = gtk_table_attach_defaults
        (GtkTableIsGtkTable, GtkButtonIsGtkWidget, pf_button1 |
         table, p_button1, j, j+1, i, i+1)
    in
      loop2 (table, i, j+1)
    end else begin
      loop1 (table, i+1)
    end

  val (pf_table | p_table) =
    gtk_table_new (NMAX1, NMAX1, GTRUE (*is_homogeneous*))

  val () = loop1 (!p_table, 0)
in
  (pf_table | p_table)
end // end of [button_matrix_make_with_menu]

(* ****** ****** *)

implement main_dummy () = () // [mainats] is implemented in C

(* ****** ****** *)

extern fun main_sudoku (): void = "main_sudoku"

implement main_sudoku () = let

val dummy: ref void = ref_void_make ()

val (pf_window | p_window) = gtk_window_new (GTK_WINDOW_TOPLEVEL)

val () = g_signal_connect_ref {void}
  (!p_window, GSIGNAL_DESTROY, window_destroy, dummy)
val () = g_signal_connect_event_ref {void}
  (!p_window, GSIGNAL_DELETE_EVENT, window_delete_event, dummy)

val () = gtk_widget_set_size_request
  (GtkWindowIsGtkWidget | !p_window, 400, 400)

val r_window = g_objref_make_some (pf_window | p_window)

//

val (pf_vbox | p_vbox) = gtk_vbox_new (GFALSE, 0)
val () = gtk_widget_show (GtkVBoxIsGtkWidget | !p_vbox)

//

val (pf_hbox | p_hbox) = gtk_hbox_new (GFALSE, 0)
val () = gtk_widget_show (GtkHBoxIsGtkWidget | !p_hbox)

val (pf_button_new_game | p_button_new_game) = button_new_game_make ()
val () = gtk_box_pack_start
  (GtkHBoxIsGtkBox, GtkButtonIsGtkWidget, pf_button_new_game |
   !p_hbox, p_button_new_game, GTRUE, GTRUE, 0)

val (pf_button2 | p_button2) = gtk_button_new_with_label ("level")
val () = gtk_widget_show (GtkButtonIsGtkWidget | !p_button2)

val () = gtk_box_pack_start
  (GtkHBoxIsGtkBox, GtkButtonIsGtkWidget, pf_button2 |
   !p_hbox, p_button2, GTRUE, GTRUE, 0)

val (pf_button_pause | p_button_pause) = button_pause_make ()
val () = gtk_box_pack_start
  (GtkHBoxIsGtkBox, GtkButtonIsGtkWidget, pf_button_pause |
   !p_hbox, p_button_pause, GTRUE, GTRUE, 0)

val (pf_button_verify | p_button_verify) = button_verify_make ()
val () = gtk_box_pack_start
  (GtkHBoxIsGtkBox, GtkButtonIsGtkWidget, pf_button_verify |
   !p_hbox, p_button_verify, GTRUE, GTRUE, 0)

val (pf_button_quit | p_button_quit) = button_quit_make (r_window)

val () = gtk_box_pack_start
  (GtkHBoxIsGtkBox, GtkButtonIsGtkWidget, pf_button_quit |
   !p_hbox, p_button_quit, GTRUE, GTRUE, 0)

//

val () = let // initializing [the_quit_yes_action]

  fn yes_act ():<cloref1> void = let
    val (pf_win | p_win) = g_objref_get (r_window)
  in
    gtk_widget_destroy (GtkWindowIsGtkWidget, pf_win | p_win)
  end

in

!the_quit_yes_action := yes_act

end

//

val () = gtk_box_pack_start
  (GtkVBoxIsGtkBox, GtkHBoxIsGtkWidget, pf_hbox |
   !p_vbox, p_hbox, GFALSE, GFALSE, 0)

val (pf_table | p_table) = button_matrix_make_with_menu ()
val () = gtk_widget_show (GtkTableIsGtkWidget | !p_table)
val () = gtk_box_pack_end
  (GtkVBoxIsGtkBox, GtkTableIsGtkWidget, pf_table |
   !p_vbox, p_table, GTRUE, GTRUE, 0)

val (pf_windown | p_window) = g_objref_get (r_window)
val () = gtk_container_add
  (GtkWindowIsGtkContainer, GtkVBoxIsGtkWidget, pf_vbox | !p_window, p_vbox)
val () = gtk_widget_show (GtkWindowIsGtkWidget | !p_window)
val () = g_objref_set (pf_windown | r_window, p_window)

val () = srand48_with_time () // seeding the random number generator

in

gtk_main ()

end

(* ****** ****** *)

%{

void mainats (ats_int_type argc, ats_ptr_type argv) {

gtk_init ((int*)&argc, (char***)&argv) ;
main_sudoku () ;
return ;

}

%}

(* ****** ****** *)

%{^

static gboolean menu_button_press_event
  (ats_ptr_type button, ats_ptr_type event,
   ats_bool_type is_fixed, ats_ptr_type menu)
{
  GdkEventButton *bevent ;

  if ((((GdkEvent*)event)->type) == GDK_BUTTON_PRESS) {

    bevent = (GdkEventButton *) event ;

    if (is_fixed) return TRUE ;

    gtk_menu_popup (menu, NULL, NULL, NULL, NULL, bevent->button, bevent->time) ;

    /* Tell calling code that we have handled this event; the buck stops here. */
    return TRUE;
  }

  /* Tell calling code that we have not handled this event; pass it on. */
  return FALSE;
}

%} // end of [%{^]

(* ****** ****** *)

(* end of [sudoku.dats] *)
