(*
// HX-2011-08: an implementation of ENIGMA
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/array.dats"
staload _(*anon*) = "prelude/DATS/pointer.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "enigma.sats"

(* ****** ****** *)

#define N 26
assume abrange = natLt (N)

(* ****** ****** *)

implement
abrange_of_int (n) = let
  val n = int1_of_int (n)
  val () = assert (n >= 0); val () = assert (n < N) in n
end // end of [abrange_of_int]

implement int_of_abrange (n) = n

(* ****** ****** *)

fn addNN
  (x: abrange, y: abrange):<> abrange = let
  val s = x + y in if s >= N then s - N else s
end // end of [addNN]

fn subNN
  (x: abrange, y: abrange):<> abrange = let
  val s = x - y in if s >= 0 then s else s + N
end // end of [subNN]

(* ****** ****** *)

abstype permmap (n: int)

extern
fun permmap_get {n:nat} (map: permmap n, i: natLt (n)): natLt (n)

extern fun fprint_permmap {n:nat} (out: FILEref, map: permmap (n), n: int n): void

extern fun permmap_make_rand {n:pos} (n: int n): permmap (n)
extern fun permmap_make_revmap {n:pos} (map: permmap (n), n: int n): permmap (n)
extern fun permmap_make_reflect {n:pos} (n: int n): permmap (n)

local

staload "libc/SATS/random.sats"
assume permmap (n:int) = array (natLt (n), n)

in // in of [local]

implement
fprint_permmap {n}
  (out, map, n) = let
  fun loop {i:nat | i <= n} (i: int i):<cloref1> void =
    if i < n then
      (if i > 0 then fprint (out, ", "); fprintf (out, "%2.2d", @(map[i])); loop (i+1))
    else () // end of [loop]
in
  loop (0)
end // end of [fprint_permmap]

implement permmap_get (map, i) = map[i]

implement
permmap_make_rand
  {n} (n) = let
  typedef elt = natLt (n)
  val asz = size1_of_int1 (n)
  val map = array_make_elt<elt> (asz, 0)
//
  fun loop1
    {i:nat | i <= n} (i: int i):<cloref1> void =
    if i < n then let
      val () = map[i] := i in loop1 (i+1)
    end // end of [if]
  // end of [loop1]
  val () = loop1 (0)
//
  fun loop2
    {i:nat | i <= n} (i: int i):<cloref1> void =
    if i >= 2 then let
      val j = randint (i)
      val () = array_exch__intsz (map, i-1, j)
    in
      loop2 (i-1)
    end // end of [if]
  // end of [loop2]
  val () = loop2 (n)
//
in
  map
end // end of [permmap_make_rand]

implement
permmap_make_revmap {n}
  (map, n) = let
  typedef elt = natLt (n)
  val asz = size1_of_int1 (n)
  val map1 = array_make_elt<elt> (asz, 0)
  fun loop
    {i:nat | i <= n} (i: int i):<cloref1> void =
    if i < n then let
      val () = map1[map[i]] := i in loop (i+1)
    end // end of [if]
  // end of [loop]
  val () = loop (0)
in
  map1
end // end of [permmap_make_revmap]

implement
permmap_make_reflect
  {n} (n) = let
  typedef elt = natLt (n)
  val asz = size1_of_int1 (n)
  val (pfgc, pfarr | p) = randperm (n)
  val map = array_make_elt<elt> (asz, 0)
  fun loop
    {i:nat | i <= n} {l:addr} (
    pfarr: !array_v (elt, n-i, l) | p: ptr l, i: int i
  ) :<cloref1> void =
    if n - i >= 2 then let
      val k0 = p->[0] and k1 = p->[1]
      val () = map[k0] := k1 and () = map[k1] := k0
      prval (pfat1, pfarr1) = array_v_uncons {elt} (pfarr)
      prval (pfat2, pfarr2) = array_v_uncons {elt} (pfarr1)
      val () = loop (pfarr2 | p + 2*sizeof<int>, i+2)
      prval pfarr1 = array_v_cons {elt} (pfat2, pfarr2)
      prval () = pfarr := array_v_cons {elt} (pfat1, pfarr1)
    in
      // nothing
    end else () // end of [if]
  // end of [loop]
  val () = loop (pfarr | p, 0)
  val () = array_ptr_free (pfgc, pfarr | p)
in
  map
end // end of [permmap_make_reflect]

end // end of [local]

(* ****** ****** *)

extern fun plugboard_make_rand (): plugboard
extern fun fprint_plugboard (out: FILEref, x: plugboard): void

local
//
// HX:
// for a correct plugboard, encode and decode should be identical;
// however, this constraint is not enforced here.
//
typedef
plugboard_struct = @{
  encode= permmap (N), decode= permmap (N)
} // end of [plugboard_struct]

assume plugboard = ref (plugboard_struct)

extern fun plugboard_get_encmap (x: plugboard): permmap (N)
extern fun plugboard_get_decmap (x: plugboard): permmap (N)

in // in of [local]

implement
plugboard_get_encmap (x) = let
  val (vbox pf | p) = ref_get_view_ptr (x) in p->encode
end // end of [plugboard_get_encmap]
implement
plugboard_get_decmap (x) = let
  val (vbox pf | p) = ref_get_view_ptr (x) in p->decode
end // end of [plugboard_get_decmap]

implement
plugboard_encode (x, n) = let
  val map = plugboard_get_encmap (x)
in
  permmap_get (map, n)
end // end of [plugboard_encode]

implement
plugboard_decode (x, n) = let
  val map = plugboard_get_decmap (x)
in
  permmap_get (map, n)
end // end of [plugboard_decode]

implement
plugboard_make_rand () = let
  val map1 = permmap_make_rand (N)
  val map2 = permmap_make_revmap (map1, N)
  val (pfgc, pfat | p) = ptr_alloc<plugboard_struct> ()
  prval () = free_gc_elim (pfgc)
  val () = p->encode := map1
  val () = p->decode := map2
in
  ref_make_view_ptr (pfat | p)
end // end of [plugboard_make_rand]

implement
fprint_plugboard (out, x) = {
  val () = fprint_string (out, "encode: ")
  val () = fprint_permmap (out, plugboard_get_encmap (x), N)
  val () = fprint_newline (out)
  val () = fprint_string (out, "decode: ")
  val () = fprint_permmap (out, plugboard_get_decmap (x), N)
  val () = fprint_newline (out)
} // end of [fprint_plugboard]

end // end of [local]

(* ****** ****** *)

extern fun rotor_make_rand (): rotor
extern fun fprint_rotor (out: FILEref, x: rotor): void

(* ****** ****** *)

implement
rotor_rotate (x) = rotor_rotate_delta (x, 1)

implement
rotor_rotate_delta
  (x, d) = let
  val shift = addNN (rotor_get_shift (x), d)
in
  rotor_set_shift (x, shift)
end // end of [rotor_rotate_delta]

(* ****** ****** *)

local

typedef
rotor_struct = @{
  shift= abrange, notch= abrange
, encode= permmap (N), decode= permmap (N)
, touched= bool
} // end of [rotor_struct]

assume rotor = ref (rotor_struct)

extern fun rotor_get_encmap (x: rotor): permmap (N)
extern fun rotor_get_decmap (x: rotor): permmap (N)

in // in of [local]

implement
rotor_get_encmap (x) = let
  val (vbox pf | p) = ref_get_view_ptr (x) in p->encode
end // end of [rotor_get_encmap]
implement
rotor_get_decmap (x) = let
  val (vbox pf | p) = ref_get_view_ptr (x) in p->decode
end // end of [rotor_get_decmap]

implement
rotor_get_shift (x) = let
  val (vbox pf | p) = ref_get_view_ptr (x) in p->shift
end // end of [rotor_get_shift]
implement
rotor_set_shift (x, shift) = let
  val (vbox pf | p) = ref_get_view_ptr (x) in p->shift := shift
end // end of [rotor_set_shift]

implement
rotor_get_notch (x) = let
  val (vbox pf | p) = ref_get_view_ptr (x) in subNN (p->notch, p->shift)
end // end of [rotor_get_notch]

implement
rotor_get_touched (x) = let
  val (vbox pf | p) = ref_get_view_ptr (x) in p->touched
end // end of [rotor_set_touched]
implement
rotor_set_touched (x, touched) = let
  val (vbox pf | p) = ref_get_view_ptr (x) in p->touched := touched
end // end of [rotor_set_touched]

implement
rotor_encode (x, n) = let
  val shift = rotor_get_shift (x)
  val n = addNN (n, shift)
  val map = rotor_get_encmap (x)
in
  addNN (permmap_get (map, n), shift)
end // end of [rotor_encode]

implement
rotor_decode (x, n) = let
  val shift = rotor_get_shift (x)
  val n = subNN (n, shift)
  val map = rotor_get_decmap (x)
in
  subNN (permmap_get (map, n), shift)
end // end of [rotor_decode]

implement
rotor_make_rand () = let
  val map1 = permmap_make_rand (N)
  val map2 = permmap_make_revmap (map1, N)
  val (pfgc, pfat | p) = ptr_alloc<rotor_struct> ()
  prval () = free_gc_elim (pfgc)
  val () = p->shift := 0
  val () = p->notch := 0
  val () = p->encode := map1
  val () = p->decode := map2
  val () = p->touched := false
in
  ref_make_view_ptr (pfat | p)
end // end of [rotor_make_rand]

implement
fprint_rotor (out, x) = {
  val () = fprint_string (out, "encode: ")
  val () = fprint_permmap (out, rotor_get_encmap (x), N)
  val () = fprint_newline (out)
  val () = fprint_string (out, "decode: ")
  val () = fprint_permmap (out, rotor_get_decmap (x), N)
  val () = fprint_newline (out)
} // end of [fprint_rotor]

end // end of [local]

(* ****** ****** *)

extern fun rotorseq_rotate_bef (x0: rotor, xs: rotorseq): void
extern fun rotorseq_rotate_aft (x0: rotor, xs: rotorseq): void

implement
rotorseq_rotate (xs) =
  case+ xs of
  | list_cons (x0, xs) => rotorseq_rotate_bef (x0, xs)
  | list_nil () => ()
// end of [rotorseq_rotate]

implement
rotorseq_rotate_bef
  (x0, xs) = let
  val () = rotor_rotate (x0) in rotorseq_rotate_aft (x0, xs)
end // end of [rotorseq_rotate_fst_rest]

implement
rotorseq_rotate_aft
  (x0, xs) = case+ xs of
  | list_cons (x1, xs) => let
      val touched = rotor_get_touched (x1)
    in
      if touched then let
        val () = rotor_set_touched (x1, false) in rotorseq_rotate_bef (x1, xs)
      end else let
        val notch0 = rotor_get_notch (x0)
        val notch1 = rotor_get_notch (x1)
      in
        if notch0 = notch1 then rotor_set_touched (x1, true) else ()
      end (* end of [if] *)
    end // end of [list_cons]
  | list_nil () => ()
// end of [rotorseq_rotate_aft]

implement
rotorseq_encode (xs, n) =
  case+ xs of
  | list_cons (x, xs) => let
      val n = rotor_encode (x, n) in rotorseq_encode (xs, n)
    end // end of [list_cons]
  | list_nil () => n
// end of [rotorseq_encode]

implement
rotorseq_decode (xs, n) =
  case+ xs of
  | list_cons (x, xs) => let
      val n = rotor_decode (x, n) in rotorseq_decode (xs, n)
    end // end of [list_cons]
  | list_nil () => n
// end of [rotorseq_decode]

(* ****** ****** *)

extern fun reflector_make_rand (): reflector
extern fun fprint_reflector (out: FILEref, x: reflector): void

local

typedef
reflector_struct = @{
  encode= permmap (N) // HX: singleton record
} // end of [reflector_struct]

assume reflector = ref (reflector_struct)

extern fun reflector_get_encmap (x: reflector): permmap (N)

in // in of [local]

implement
reflector_get_encmap (x) = let
  val (vbox pf | p) = ref_get_view_ptr (x) in p->encode
end // end of [reflector_get_encmap]

implement
reflector_encode (x, n) = let
  val map = reflector_get_encmap (x) in permmap_get (map, n)
end // end of [reflector_encode]

implement
reflector_make_rand () = let
  val map = permmap_make_reflect (N)
  val (pfgc, pfat | p) = ptr_alloc<reflector_struct> ()
  prval () = free_gc_elim (pfgc)
  val () = p->encode := map
in
  ref_make_view_ptr (pfat | p)
end // end of [reflector_make_rand]

implement
fprint_reflector (out, x) = {
  val () = fprint_string (out, "encode: ")
  val () = fprint_permmap (out, reflector_get_encmap (x), N)
  val () = fprint_newline (out)
} // end of [fprint_reflector]

end // end of [local]

(* ****** ****** *)

local

extern fun enigma_get_plugboard (x: enigma): plugboard
extern fun enigma_get_rotorseq_l2r (x: enigma): rotorseq
extern fun enigma_get_rotorseq_r2l (x: enigma): rotorseq
extern fun enigma_get_reflector (x: enigma): reflector

typedef
enigma_struct = @{
  plugboard= plugboard
, rotorseq_l2r= rotorseq
, rotorseq_r2l= rotorseq
, reflector= reflector
} // end of [reflector_struct]

assume enigma = ref (enigma_struct)

in // in of [local]

implement
enigma_get_plugboard (x) = let
  val (vbox pf | p) = ref_get_view_ptr (x) in p->plugboard
end // end of [enigma_get_plugboard]

implement
enigma_get_rotorseq_l2r (x) = let
  val (vbox pf | p) = ref_get_view_ptr (x) in p->rotorseq_l2r
end // end of [enigma_get_rotorseq_l2r]

implement
enigma_get_rotorseq_r2l (x) = let
  val (vbox pf | p) = ref_get_view_ptr (x) in p->rotorseq_r2l
end // end of [enigma_get_rotorseq_r2l]

implement
enigma_get_reflector (x) = let
  val (vbox pf | p) = ref_get_view_ptr (x) in p->reflector
end // end of [enigma_get_reflector]

implement
enigma_encode (x, n0) = let
//
  val pb = enigma_get_plugboard (x)
  val l2r = enigma_get_rotorseq_l2r (x)
  val r2l = enigma_get_rotorseq_r2l (x)
  val rf = enigma_get_reflector (x)
//
  val () = rotorseq_rotate (r2l)
  val n1 = plugboard_encode (pb, n0)
  val n2 = rotorseq_encode (r2l, n1)
  val n3 = reflector_encode (rf, n2)
  val n4 = rotorseq_decode (l2r, n3)
  val n5 = plugboard_decode (pb, n4)
//
(*
  val () = println! ("enigma: n0 = ", n0)
  val () = println! ("enigma: n1 = ", n1)
  val () = println! ("enigma: n2 = ", n2)
  val () = println! ("enigma: n3 = ", n3)
  val () = println! ("enigma: n4 = ", n4)
  val () = println! ("enigma: n5 = ", n5)
*)
//
in
  n5
end // end of [enigma_encode]

implement
enigma_init_rotorseq
  (x, ns) = let
  fun init (xs: rotorseq, ns: List (abrange)): void =
    case+ xs of
    | list_cons (x, xs) => (case+ ns of
        | list_cons (n, ns) => let
            val () = rotor_set_shift (x, n)
            val () = rotor_set_touched (x, false)
          in
            init (xs, ns)
          end // end of [list_cons]
        | list_nil () => ()
      ) // end of [list_cons]
    | list_nil () => ()
  // end of [init]
  val l2r = enigma_get_rotorseq_l2r (x)
in
  init (l2r, ns)
end // end of [enigma_init]

implement
enigma_make_rand
  (nrotor) = let
  val pb = plugboard_make_rand ()
//
(*
  val () = print ("enigma_make_rand: pb =\n")
  val () = fprint_plugboard (stdout_ref, pb)
*)
//
  val l2r = aux (nrotor) where {
    fun aux {n:nat} (n: int n): list (rotor, n) =
      if n > 0 then let
        val x = rotor_make_rand () in list_cons (x, aux (n-1))
      end else list_nil ()
    // end of [aux]
  } // end of [val]
  val r2l = list_reverse (l2r)
  val r2l = list_of_list_vt (r2l)
//
  val rf = reflector_make_rand ()
(*
  val () = print ("enigma_make_rand: rf =\n")
  val () = fprint_reflector (stdout_ref, rf)
*)
//
  val (pfgc, pfat | p) = ptr_alloc<enigma_struct> ()
  prval () = free_gc_elim (pfgc)
  val () = p->plugboard := pb
  val () = p->rotorseq_l2r := l2r
  val () = p->rotorseq_r2l := r2l
  val () = p->reflector := rf
in
  ref_make_view_ptr (pfat | p)
end // end of [reflector_make_rand]

end // end of [local]

(* ****** ****** *)

(* end of [enigma.dats] *)
