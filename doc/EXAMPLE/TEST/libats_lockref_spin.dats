(*
** some testing code for functions declared in
** libats/SATS/parworkshop.sats
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: March, 2010
//

(* ****** ****** *)

staload UNISTD = "libc/SATS/unistd.sats"

(* ****** ****** *)

staload "libc/SATS/pthread.sats"
staload "libats/SATS/lockref_spin.sats"
staload "libats/SATS/parworkshop.sats"
staload _(*anon*) = "libats/DATS/parworkshop.dats"

(* ****** ****** *)

#define QSZ 1 // extreme testing condition!

(* ****** ****** *)

dynload "libats/DATS/parworkshop.dats"

(* ****** ****** *)

local

var X: int with pf_X = 0
viewdef V = int @ X
val lock = lockref_create_unlocked {V} (pf_X | 0(*pshared*))
val () = assertloc (ptr_of_lock(lock) > null)

in // in of [local]

fun getincX () = res where {
  val (pf | ()) = lockref_acquire (lock)
  val res = X
  val () = X := X + 1
  val () = lockref_release (pf | lock)
} // end of [getincX]

end // end of [local]

(* ****** ****** *)

implement
main () = () where {
  typedef work = int
  val fwork = lam {l:addr} (
    ws: !WORKSHOPptr (work, l), res: &work
  ) : int =<fun> $effmask_all let
    val tid = pthread_self ()
    val tid = lint_of_pthread (tid)
    val () = (print "tid = "; print tid)
    val X = getincX ()
    val () = (print ": X = "; print X; print_newline ())
    // val () = $UNISTD.usleep (1)
  in
    res
  end // end of [val]
  val ws = workshop_make<work> (QSZ, fwork)
//
  val status = workshop_add_worker (ws)
  val () = (print "status = "; print status; print_newline ())
  val nworker = workshop_get_nworker (ws)
  val () = (print "nworker = "; print nworker; print_newline ())
//
  val status = workshop_add_worker (ws)
  val () = (print "status = "; print status; print_newline ())
  val nworker = workshop_get_nworker (ws)
  val () = (print "nworker = "; print nworker; print_newline ())
//
  var i: Nat = 1
  val () = while (i <= 10) let
    val () = workshop_insert_work (ws, i)
  in
    i := i + 1
  end // end of [val]
//
  val () = workshop_insert_work (ws, 0) // quit ticket
  val () = workshop_insert_work (ws, 0) // quit ticket
//
  val () = workshop_free (ws)
//
} // end of [main]

(* ****** ****** *)

(* end of [libats_lockref_spin.dats] *)
