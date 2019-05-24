(*
** VSTTE 2012 Verification Competition
**
** Problem 1
**
//
// All done (VT1, VT2, VT3)
//
// VT1 and VT2 are obviously fulfilled.
// VT3 is also fulfilled according to the definition of [ba_v]
//
*)

(* ****** ****** *)
//
absview ba_v (l:addr, nf: int, nt: int) // array of nf f's and nt t's
//
viewdef fba_v (l:addr, n:int) = ba_v (l, n, 0) // array of n f's
viewdef tba_v (l:addr, n:int) = ba_v (l, 0, n) // array of n t's
//
(* ****** ****** *)

abst@ype
bbool (i:int) = byte // bool values represented by a byte
typedef bbool = [i:two] bbool (i)

(* ****** ****** *)

extern
fun bbool_istrue {i:two} (x: bbool i):<> bool (i==1)
extern
fun bbool_isfalse {i:two} (x: bbool i):<> bool (i==0)

(* ****** ****** *)

fn bbool_ptrget
  {l:addr} {i:two} (
  pf: !bbool i @ l | p: ptr l
) :<> bbool(i) = !p

fn bbool_ptrset
  {l:addr} {i:two} (
  pf: !bbool? @ l >> bbool(i) @ l | p: ptr l, x: bbool(i)
) :<> void = (!p := x)

(* ****** ****** *)

fun swap
  {l1,l2:addr}
  {i1,i2:two} .<>. (
  pf1: !bbool i1 @ l1 >> bbool i2 @ l1
, pf2: !bbool i2 @ l2 >> bbool i1 @ l2
| p1: ptr l1, p2: ptr l2
) :<> void = () where {
  val t = bbool_ptrget (pf1 | p1)
  val () = bbool_ptrset (pf1 | p1, bbool_ptrget (pf2 | p2))
  val () = bbool_ptrset (pf2 | p2, t)
} // end of [swap]

(* ****** ****** *)

extern
praxi ba_v_nil {l:addr} (): ba_v (l, 0, 0)

extern
praxi ba_v_cons
  {l:addr}
  {nf,nt:nat}
  {i:two} (
  pfat: bbool(i) @ l, pf: ba_v (l+1, nf, nt)
) : ba_v (l, nf+1-i, nt+i)

extern
praxi ba_v_snoc
  {l:addr}
  {nf,nt:nat}
  {i:two} (
  pf: ba_v (l, nf, nt), pfat: bbool(i) @ l+nf+nt
) : ba_v (l, nf+1-i, nt+i)

extern
praxi ba_v_unnil {l:addr} (pf: ba_v (l, 0, 0)): void

extern
praxi ba_v_uncons
  {l:addr}
  {nf,nt:nat | nf+nt > 0} (
  pf: ba_v (l, nf, nt)
) : [i:two | i <= nt; 1 <= nf+i] (bbool(i) @ l, ba_v (l+1, nf-1+i, nt-i))

extern
praxi ba_v_unsnoc
  {l:addr}
  {nf,nt:nat | nf+nt > 0} (
  pf: ba_v (l, nf, nt)
) : [i:two | i <= nt; 1 <= nf+i] (bbool(i) @ l+nf+nt-1, ba_v (l, nf-1+i, nt-i))

extern
praxi ba_v_unsplit
  {l:addr} {nf1,nt1:nat} {nf2,nt2:nat} (
  pf1: ba_v (l, nf1, nt1), pf2: ba_v (l+nf1+nt1, nf2, nt2)
) : ba_v (l, nf1+nf2, nt1+nt2)

(* ****** ****** *)

fun tws {l:addr} {n1,nf,nt,n2:nat} .<nf+nt>. (
  pf_l: fba_v (l, n1), pf_m: ba_v (l+n1, nf, nt), pf_r: tba_v (l+n1+nf+nt, n2)
| p: ptr l, i: int n1, j: int (n1+nf+nt)
) :<> (fba_v (l, n1+nf), tba_v (l+n1+nf, nt+n2) | void) =
  if i < j then let
    prval (pfat, pf_m) = ba_v_uncons (pf_m)
    val x_i = !(p+i)
  in
    if bbool_isfalse (x_i) then let
      prval pf_l = ba_v_snoc (pf_l, pfat)
    in
      tws {l} (pf_l, pf_m, pf_r | p, i+1, j)
    end else
      tws_1 (pf_l, pfat, pf_m, pf_r | p, i+1, j)
    // end of [if]
  end else let
    prval () = ba_v_unnil (pf_m)
  in
    (pf_l, pf_r | ())
  end // end of [if]
// end of [tws]

and tws_1 {l:addr} {n1,nf,nt,n2:nat} .<nf+nt>. (
  pf_l: fba_v (l, n1)
, pfat: bbool(1) @ l+n1
, pf_m: ba_v (l+n1+1, nf, nt), pf_r: tba_v (l+n1+1+nf+nt, n2)
| p: ptr l, i: int (n1+1), j: int (n1+1+nf+nt)
) :<> (fba_v (l, n1+nf), tba_v (l+n1+nf, nt+n2+1) | void) =
  if i < j then let
    prval (pfat2, pf_m) = ba_v_unsnoc (pf_m)
    val x_j = bbool_ptrget (pfat2 | p+j-1)
  in
    if bbool_istrue (x_j) then let
      prval pf_r = ba_v_cons (pfat2, pf_r)
    in
      tws_1 (pf_l, pfat, pf_m, pf_r | p, i, j-1)
    end else let
      val () = swap (pfat, pfat2 | p+i-1, p+j-1)
      prval pf_l = ba_v_snoc (pf_l, pfat)
      prval pf_r = ba_v_cons (pfat2, pf_r)
    in
      tws (pf_l, pf_m, pf_r | p, i, j-1)
    end
  end else let
    prval () = ba_v_unnil (pf_m)
    prval pf_r = ba_v_cons (pfat, pf_r)
  in
    (pf_l, pf_r | ())
  end // end of [if]
// end of [tws_1]

(* ****** ****** *)

(*
** The type assigned to [two_way_sort] indicates that
** it turns an array of [nf] f's and [nt] t's into two
** adjacent arrays: the front one contains [nf] f's and
** the rear one [nt] t's.
**
** Would this be enough to cover the VT3 (verification task 3)?
**
*)

fun two_way_sort
  {l:addr} {nf,nt:nat} .<>. (
  pf: ba_v (l, nf, nt) | p: ptr l, n: int(nf+nt)
) :<> (fba_v (l, nf), tba_v (l+nf, nt) | void) =
  tws (ba_v_nil (), pf, ba_v_nil () | p, 0, n)

(* ****** ****** *)
//
// The following code is solely for testing
// the functions implemented above; it is not
// needed if you do not want to test.
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array.dats"
staload _(*anon*) = "prelude/DATS/pointer.dats"

(* ****** ****** *)

local

staload UN = "prelude/SATS/unsafe.sats"
staload _(*anon*) = "prelude/DATS/unsafe.dats"

in

implement
bbool_istrue {i} (x) = let
  val res = $UN.cast2int (x) > 0
  val [b:bool] res = (bool1_of_bool)res
  prval () = __assert () where {
    extern prfun __assert (): [b==(i==1)] void
  } // end of [prval]
in
  res
end // end of [bbool_istrue]

implement
bbool_isfalse {i} (x) = ~bbool_istrue (x)

end // end of [local]

(* ****** ****** *)

staload "libc/SATS/random.sats"

implement
main () = () where {
  #define N 10
  val () = srand48_with_time ()
  val (pfgc, pfarr | p) = array_ptr_alloc<byte> (N)
  val () = loop (pfarr | p, N) where {
    fun loop
      {n:nat} {l:addr} .<n>. (
      pf: !array_v (byte?, n, l) >> array_v (byte, n, l)
    | p: ptr l, n: size_t n
    ) : void =
      if n > 0 then let
        prval (pf1, pf2) = array_v_uncons {byte?} (pf)
        val () = !p := byte_of_int (randint(2))
        val () = loop (pf2 | p+sizeof<byte>, n-1)
      in
        pf := array_v_cons {byte} (pf1, pf2)
      end else let
        prval () = array_v_unnil (pf)
        prval () = pf := array_v_nil ()
      in
        // nothing
      end // end of [if]
  } // end of [val]
  fun pr (
    i: sizeLt (N), x: &byte
  ): void = let
    val () = if i > 0 then print ", "
  in
    if (int_of_byte)x > 0 then print true else print false
  end // end of [pr]
//
  val () = array_ptr_iforeach_fun<byte> (!p, pr, N)
  val () = print_newline ()
//
  prval pfba = __assert (pfarr) where {
    extern
    prfun __assert
      {n:nat} {l:addr} (
      pf: array_v (byte, n, l)
    ) : [nf,nt:nat | nf+nt==n] ba_v (l, nf, nt)
  } // end of [prval]
  val (pfba1, pfba2 | ()) = two_way_sort (pfba | p, N)
  prval pfba = ba_v_unsplit (pfba1, pfba2)
  prval pfarr = __assert (pfba) where {
    extern
    prfun __assert
      {l:addr} {nf,nt:nat}
      (pf: ba_v (l, nf, nt)): array_v (byte, nf+nt, l)
  } // end of [prval]
//
  val () = array_ptr_iforeach_fun<byte> (!p, pr, N)
  val () = print_newline ()
//
  val () = array_ptr_free {byte?} (pfgc, pfarr | p)
} // end of [main]

(* ****** ****** *)

(* end of [problem1.dats] *)
