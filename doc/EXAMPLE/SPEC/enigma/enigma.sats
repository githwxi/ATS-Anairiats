(*
// HX-2011-08: an implementation of ENIGMA
*)

(* ****** ****** *)

abst@ype abrange = int
fun abrange_of_int (n: int): abrange
fun int_of_abrange (n: abrange): int

(* ****** ****** *)

abstype plugboard
//
// HX: [encode] and [decode] are inverse
// HX: they should be the same in a valid plugboard
//
fun plugboard_encode (x: plugboard, n: abrange): abrange
fun plugboard_decode (x: plugboard, n: abrange): abrange

(* ****** ****** *)

abstype rotor
//
// HX: [encode] and [decode] are inverse
//
fun rotor_encode (x: rotor, n: abrange): abrange
fun rotor_decode (x: rotor, n: abrange): abrange
//
// HX:
// the shift of a rotor indicates how far the rotor is from its init position
//
fun rotor_get_shift (x: rotor): abrange
fun rotor_set_shift (x: rotor, shift: abrange): void
//
fun rotor_get_notch (x: rotor): abrange
fun rotor_get_touched (x: rotor): bool
fun rotor_set_touched (x: rotor, touched: bool): void
//
fun rotor_rotate (x: rotor): void
fun rotor_rotate_delta (x: rotor, delta: abrange): void
//
(* ****** ****** *)

typedef rotorseq = List (rotor)
fun rotorseq_encode (xs: rotorseq, n: abrange): abrange
fun rotorseq_decode (xs: rotorseq, n: abrange): abrange
fun rotorseq_rotate (xs: rotorseq): void

(* ****** ****** *)

abstype reflector
//
// HX: [encode] and [decode] are the same
//
fun reflector_encode (x: reflector, n: abrange): abrange
(*
fun reflector_decode (x: reflector, n: abrange): abrange // HX: the same as reflector_encode
*)

(* ****** ****** *)

abstype enigma
//
fun enigma_encode (x: enigma, n: abrange): abrange
//
fun enigma_init_rotorseq (x: enigma, ns: List (abrange)): void
//
fun enigma_make_rand {n:pos} (nrotor: int n): enigma

(* ****** ****** *)

(* end of [enigma.sats] *)
