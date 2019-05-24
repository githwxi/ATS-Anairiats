//
// Author: Matthias Berndt (matthias_berndt AT gmx DOT de)
//   with some minor fixes by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Start Time: September, 2010; Finish Time: October, 2010
//

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"

(* ****** ****** *)
//
// HX-2010-10-19:
// these functions are already in $ATSHOME/DATS/ilistp.dats;
// they are included here to make this solution self-contained.
// 
extern
prfun length_istot {xs:ilist} (): [n:nat] LENGTH (xs, n)
implement
length_istot
  () = istot () where {
  prfun istot {xs:ilist} .<xs>.
    (): [n:nat] LENGTH (xs, n) =
    scase xs of
    | ilist_cons (x, xs) => LENGTHcons (istot {xs} ())
    | ilist_nil () => LENGTHnil ()
  // end of [prfun]
} // end of [length_istot]

extern
prfun length_isfun {xs:ilist} {n1,n2:int}
  (pf1: LENGTH (xs, n1), pf2: LENGTH (xs, n2)): [n1==n2] void
implement
length_isfun (pf1, pf2) = let
  prfun isfun {xs:ilist} {n1,n2:int} .<xs>. (
    pf1: LENGTH (xs, n1), pf2: LENGTH (xs, n2)
  ) : [n1==n2] void =
    scase xs of
    | ilist_cons (x, xs) => let
        prval LENGTHcons (pf1) = pf1 and LENGTHcons (pf2) = pf2
        prval () = isfun {xs} (pf1, pf2)
      in
        // nothing
      end // end of [ilist_cons]
    | ilist_nil () => let
        prval LENGTHnil () = pf1 and LENGTHnil () = pf2 in (*nothing*)
      end // end of [ilist_nil]
  // end of [isfun]
in
  isfun (pf1, pf2)
end // end of [length_isfun]

(* ****** ****** *)

dataprop PATHS(int, int, int) =
  | {y:nat} PATHSbas1(0, y, 1)
  | {x:nat} PATHSbas2(x, 0, 1)
  | {x,y,z1,z2:nat}
    PATHSind(x+1, y+1, z1+z2) of (PATHS(x, y+1, z1), PATHS(x+1, y, z2))
// end of [PATHS]

(* ****** ****** *)

(*
// MB:
// If PATHS_LIST(zs, y) holds, then zs constains numbers z_n, ..., z_2, z_1
// such that PATHS(n, y, z_n), ..., PATHS(2, y, z_2), PATHS(1, y, z_1) hold
*)
dataprop PATHS_LIST(ilist, int (*y*)) = 
  | {y:nat} PATHS_LISTbas(ilist_nil, y)
  | {x,y,z:nat} {zs:ilist}
    PATHS_LISTind(ilist_cons(z, zs), y) of (LENGTH(zs, x), PATHS(x, y, z), PATHS_LIST(zs, y))
// end of [PATHS_LIST]

dataprop SUM (ilist, int) =
  | SUMbas (ilist_nil, 0)
  | {x:int} {xs:ilist} {sum:int} SUMind(ilist_cons(x,xs), x+sum) of SUM(xs, sum)
// end of [SUM]

(* 
// MB:
// PSUMS -- partial sums. 
// let xs = x_n, ..., x_2, x_1. 
// let sums = sum_n, ..., sum_2, sum_1
// If PSUMS(xs, sums) holds, then 
// sum_1 = x_1
// sum_2 = x_1 + x_2
// ...
// sum_n = x_1 + x_2 + ... + x_n
*)
dataprop PSUMS(ilist (*xs*), ilist (*sums*)) = 
  | PSUMSbas(ilist_nil, ilist_nil)
  | {x:int} {xs: ilist} {sum:int} {sums: ilist}
    PSUMSind(ilist_cons(x, xs), ilist_cons(x+sum, sums)) of (PSUMS(xs, sums), SUM (xs, sum))
// end of [PSUMS]

(*
// MB: If PSUMS(xs, sums) holds, then xs and sums have the same length
*)
prfun PSUMS_same_length {xs,sums:ilist} {n:nat} .<xs>.
  (pf1: PSUMS (xs, sums), pf2: LENGTH (xs, n)): LENGTH (sums, n) =
  scase xs of
  | ilist_cons (x, xs1) => let
      prval PSUMSind (pf1, _) = pf1 and LENGTHcons (pf2) = pf2
    in
      LENGTHcons (PSUMS_same_length (pf1, pf2))
    end // end of [ilist_cons]
  | ilist_nil () => let
      prval PSUMSbas () = pf1 and LENGTHnil () = pf2 in LENGTHnil ()
    end // end of [ilist_nil]
// end of [PSUMS_same_length]

(* ****** ****** *)

//
// HX: A representation good enough for 64-bit unsigned integers
//
abst@ype ullint1 (i: int) = ullint
//
symintr ullint1
extern castfn ullint1_int {i:nat} (x: int i):<> ullint1 i
overload ullint1 with ullint1_int
//
extern fun print_ullint1
  {i:nat} (x: ullint1 i): void = "atspre_print_ullint"
extern fun add_ullint1_ullint1
  {z1,z2:nat} (z1: ullint1 z1, z2: ullint1 z2):<> ullint1 (z1+z2)
  = "atspre_add_ullint_ullint"
overload + with add_ullint1_ullint1

(* ****** ****** *)

datatype ilist (ilist) =
  | ilist_nil (ilist_nil) of ()
  | {x:nat} {xs:ilist} ilist_cons (ilist_cons (x, xs)) of (ullint1 x, ilist (xs))
// end of [ilist]

#define nil ilist_nil
#define cons ilist_cons
#define :: ilist_cons

(* ****** ****** *)

(*
// MB: calculate the list of partial sums for any given list.
*)
fun psums {xs:ilist} .<xs>.
  (xs: ilist (xs)):<> [sums: ilist] (PSUMS(xs, sums) | ilist sums) =
  case+ xs of 
  | nil() => (PSUMSbas() | nil())
  | cons (x, nil()) => (PSUMSind(PSUMSbas(), SUMbas()) | x::nil())
  | cons {x} {xs1} (x, xs1 as cons _) => let
      prval pflen_xs1 = length_istot {xs1} ()
      val+ (pf | ys1) = psums (xs1)
      prval LENGTHcons _ = pflen_xs1
      prval pflen_ys1 = PSUMS_same_length (pf, pflen_xs1)
      prval LENGTHcons _ = pflen_ys1
      val+ y1 :: ys2 = ys1
      prval PSUMSind (pf1, pf2) = pf
    in
      (PSUMSind(pf, SUMind(pf2)) | (x+y1)::ys1)
    end
// end of [psums]

(* ****** ****** *)

(*
// MB: the next 100 lines prove PATHS_LIST_PSUMS_lemma1, 
// which allows us to efficiently compute the "paths" function
*)
prfun PATHSisfun{x,y,z1,z2: nat} .<x,y>.
  (pf1: PATHS(x,y,z1), pf2: PATHS(x,y,z2)): [z1 == z2] void = 
  case+ pf1 of 
  | PATHSbas1() => (case+ pf2 of | PATHSbas1() => () | PATHSbas2() => ()) 
  | PATHSbas2() => (case+ pf2 of | PATHSbas1() => () | PATHSbas2() => ())
  | PATHSind(pf11, pf12) => let 
      prval PATHSind(pf21, pf22) = pf2 
      prval () = PATHSisfun(pf11, pf21) 
      prval () = PATHSisfun(pf12, pf22) 
    in
      // nothing
    end // end of [PATHSind]
// end of [PATHSisfun]

prfn lemma_paths_gte_0 {x,y,z: int}
  (pf: PATHS(x,y,z)): [x >= 0 && y >= 0 && z >= 0] void = 
  case+ pf of 
  | PATHSbas1() => ()
  | PATHSbas2() => ()
  | PATHSind(_,_) => ()
// end of [lemma_paths_gte_0]

prfun lemma_sum_paths_list_gte_0
  {ks:ilist}{x,y:int} .<ks>. 
  (pf1: PATHS_LIST(ks, x), pf2: SUM(ks, y)): [y >= 0] void = 
  scase ks of 
  | ilist_nil() => let 
      prval SUMbas() = pf2 
    in
      // nothing
    end
  | ilist_cons(kk, kks) => let 
      prval PATHS_LISTind(_, pf12, pf13) = pf1
      prval SUMind(pff2) = pf2
      prval () = lemma_paths_gte_0(pf12);
      prval () = lemma_sum_paths_list_gte_0(pf13, pff2)
    in
      // nothing
    end // end of [ilist_cons]
// end of [lemma_sum_paths_list_gte_0]

(* this establishes the base case for lemma2, which is proven by induction. *)
prfun lemma3 {ks:ilist} {k,x,z:int} .<ks>. (
  pf1: PATHS_LIST(ilist_cons(k,ks), 0), pf2: LENGTH(ilist_cons(k,ks), x), pf3: SUM(ilist_cons(k, ks), z)
) : PATHS(x-1, 1, z) = let
  prval PATHS_LISTind(pf11,pf12,pf13) = pf1
  prval LENGTHcons(pf2) = pf2
  prval SUMind(pf3) = pf3
in
  scase ks of
  | ilist_nil() => let
      prval LENGTHnil() = pf2
      prval SUMbas() = pf3
      prval () = PATHSisfun(PATHSbas2(), pf12)
    in
      PATHSbas1()
    end // end of [ilist_nil]
  | ilist_cons (kk, kks) => let
      prval LENGTHcons(_) = pf2 (* show that x-2 >= 0 *)
      prval () = lemma_sum_paths_list_gte_0(pf13, pf3) (* the third static argument to lemma3 is >= 0 *)
      prval () = PATHSisfun(PATHSbas2(), pf12) (* prove that k == 1 *)
      prval blub = lemma3(pf13, pf2, pf3)
      prval blubber = PATHSbas2()
    in
      PATHSind(blub, blubber)
    end // end of [ilist_cons]
end // end of [lemma3]

(* this states that paths(x, y) = paths(0, y-1) + paths(1, y-1) + ... + paths(x, y-1) *)
prfun lemma2 {ks:ilist}{k,x,y,z:int}.<ks>. (
  pf1: PATHS_LIST(ilist_cons(k, ks), y), pf2: LENGTH(ilist_cons(k, ks), x), pf3: SUM(ilist_cons(k, ks), z)
) : PATHS(x-1, y+1, z) = 
  sif y == 0 then 
    lemma3(pf1, pf2, pf3)
  else let
    prval PATHS_LISTind(pf11,pf12,pf13) = pf1
    prval LENGTHcons(pf2) = pf2
    prval SUMind(pf3) = pf3
  in
    scase ks of 
    | ilist_nil() => let
        prval SUMbas() = pf3
        prval LENGTHnil() = pf2
        prval LENGTHnil() = pf11
        prval () = PATHSisfun(pf12, PATHSbas1())
      in
        PATHSbas1()
      end
    | ilist_cons(kk, kks) => let
        prval () = length_isfun(pf2, pf11)
        prval () = lemma_paths_gte_0 (lemma2(pf13, pf2, pf3))
      in
        PATHSind(lemma2 (pf13, pf2, pf3),pf12)
      end
    // end of [scase]
  end // end of [sif]

prfun PATHS_LIST_PSUMS_lemma1
  {xs1,xs2: ilist} {y:nat} .<xs1>. (
  pf1: PATHS_LIST(xs1, y), pf2: PSUMS(xs1, xs2)
) : PATHS_LIST(xs2, y+1) = 
  scase xs1 of
  | ilist_nil() => let 
      prval LENGTHnil() = PSUMS_same_length(pf2,LENGTHnil()) 
    in 
      PATHS_LISTbas() 
    end // end of [ilist_nil]
  | ilist_cons(xx1, xxs1) => let
      prval PATHS_LISTind(pf11, pf12, pf13) = pf1
      prval PSUMSind(pf21, pf22) = pf2
      prval foo = lemma2 (pf1, LENGTHcons(pf11), SUMind(pf22))
      prval bar = PATHS_LIST_PSUMS_lemma1(pf13, pf21)
      prval baz = PSUMS_same_length(pf21, pf11)
      prval () = lemma_paths_gte_0(foo)
    in
      PATHS_LISTind(baz, foo, bar)
    end // end of [ilist_cons]
// end of [PATHS_LIST_PSUMS_lemma1]

(* ****** ****** *)

fun paths_list {len,y:nat} .<len+y>.
  (len: int len, y: int y)
  :<> [zs:ilist] ((PATHS_LIST(zs, y), LENGTH(zs, len)) | ilist zs) = 
  case+ y of
  | 0 => (case+ len of
     | 0 => ((PATHS_LISTbas(), LENGTHnil()) | nil())
     | len =>> let
         val+ ((pf1, pf2) | xs) = paths_list (len-1, 0)
       in
         ((PATHS_LISTind(pf2, PATHSbas2(), pf1),LENGTHcons(pf2)) | (ullint1)1::xs)
       end
    ) // end of [0]
  | y =>> let
      val+ ((pf_paths_list, pf_len_xs) | xs) = paths_list(len, y-1)
      val+ (pf_psums | sums) = psums (xs)
      prval pf_len_sums = PSUMS_same_length(pf_psums, pf_len_xs)
      prval pfres = (PATHS_LIST_PSUMS_lemma1(pf_paths_list, pf_psums), PSUMS_same_length(pf_psums, pf_len_xs))
    in
      (pfres | sums)
    end // end of [y > 0]
// end of [paths_list]

fun paths{x,y: nat} .<>.
  (x: int x, y: int y):<> [z: nat] (PATHS(x, y, z) | ullint1 z) =
  case+ y of 
  | 0 => (PATHSbas2() | (ullint1)1)
  | y =>> let
      val+ ((pf_paths_list, pf_len) | zs) = paths_list(x+1, y) 
      prval LENGTHcons pf1_len = pf_len (* needed for exhaustiveness checks *)
      prval PATHS_LISTind(pf1, pf2, pf3) = pf_paths_list
      prval () = length_isfun (pf1_len, pf1)
      val+ z :: _ = zs
    in
      (pf2 | z)
    end // end of [y > 0]
// end of [paths]

implement main () = let 
  val (_ | ans) = paths(20, 20)
//
extern castfn ullint_of_ullint1 {i:nat} (x: ullint1 i):<> ullint
//
  val () = assert_errmsg (ullint_of_ullint1(ans) = 137846528820ULL, #LOCATION)
in
  print ("The answer = "); print_ullint1 ans; print_newline ()
end // end of [main]

(* ****** ****** *)

(* end of [problem15-mberndt.dats] *)
