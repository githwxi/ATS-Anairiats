(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -D_ATS_MULTITHREAD -O3 -o binary-trees2_smp binary-trees2_smp.dats -lpthread -D_ATS_GCATS
*)

(* ****** ****** *)

staload "libc/SATS/pthread.sats"
staload "libc/SATS/pthread_uplock.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

dataviewtype tree (int) =
  Nil(0) | {n1,n2:two} Node(1) of (tree n1, int, tree n2)
// end of [tree]

viewtypedef Tree = [n:two] tree n

fun tree_make (d: int, i: int): Tree =
  if d > 0 then
    let val d1 = d-1 and i2 = i << 1 in      
      Node (tree_make (d1, i2 - 1), i, tree_make (d1, i2))
    end
  else Node (Nil (), i, Nil ())
// end of [tree_make]

fun check_and_free (t: Tree):<!ntm> int =  case+ t of
  | ~Node (tl, i, tr) => i + check_and_free tl - check_and_free tr
  | ~Nil () => 0
// end of [check_and_free]

fun check (t: !Tree):<!ntm> int =  case+ t of
  | Node (!tl, i, !tr) =>
    let val ans = i + check (!tl) - check (!tr) in (fold@ t; ans) end
  | Nil () => (fold@ t; 0)
// end of [check]

fun check_ref (r: ref Tree): int = let
  val (vbox pf | p) = ref_get_view_ptr r in check !p     
end // end of [check_ref]

//

#define MIN_DEPTH 4

//

fn stretch (max_depth: Nat): void = let
   val stretch_depth = max_depth + 1
   val t = tree_make (stretch_depth, 0)
   val c = check_and_free (t)
in
   printf ("stretch tree of depth %i\t check: %i\n", @(stretch_depth, c));
end // end of [stretch]

fn long_lived_tree_make
  (max_depth: Nat): ref Tree = let
  val t = tree_make (max_depth, 0); val t_r = ref<Tree> (t)
in
  t_r
end // end of [long_lived_tree_make]

(* ****** ****** *)

%{^

static inline
ats_ptr_type int_make () {
  return malloc(sizeof(ats_int_type)) ;
}

static inline
ats_void_type int_free (ats_ptr_type p) { free (p); return ; }

%}

extern fun int_make (): [l:addr] (int @ l | ptr l) = "int_make"
extern fun int_free {l:addr} (pf: int @ l | p: ptr l): void = "int_free"

(* ****** ****** *)

viewdef int3_v
  (l_n:addr, l_d:addr, l_c:addr) = @(int @ l_n, int @ l_d, int @ l_c)
viewtypedef lock
  (l_n:addr, l_d:addr, l_c:addr) = uplock (int3_v (l_n, l_d, l_c))
viewtypedef ticket
  (l_n:addr, l_d:addr, l_c:addr) = upticket (int3_v (l_n, l_d, l_c))

dataviewtype locklst =
  | locklst_nil of ()
  | {l_n,l_d,l_c:addr} locklst_cons of (
      ptr l_n, ptr l_d, ptr l_c, lock (l_n, l_d, l_c), locklst
    ) // end of [locklst_cons]
// end of [locklst]

(* ****** ****** *)

fun worker {l_n,l_d,l_c:addr} {d,md:nat | d <= md} (
    pf_n: int @ l_n
  , pf_d: int @ l_d
  , pf_c: int @ l_c
  | tick: ticket (l_n, l_d, l_c)
  , p_n: ptr l_n, p_d: ptr l_d, p_c: ptr l_c
  , d: int d, max_depth: int md
  ) : void = let
  val n = 1 << (max_depth - d + MIN_DEPTH)
  fun loop (i: Nat, c: int):<cloref1> int =
    if i < n then let
      val t = tree_make(d,  i); val c1 = check_and_free t
      val t = tree_make(d, ~i); val c2 = check_and_free t
    in
      loop (i+1, c + c1 + c2)
    end else begin
      c // return value
    end // end of [if]
  val () = !p_n := n
  val () = !p_d := d;
  val () = !p_c := loop (0, 0)
  prval pf = @(pf_n, pf_d, pf_c)
in
  pthread_upticket_upload_and_destroy (pf | tick)
end // end of [worker]

(* ****** ****** *)

fun loop_depths
  (d: Nat, max_depth: Nat, res: &locklst? >> locklst): void =
  if d <= max_depth then let
    val [l_n:addr] (pf_n | p_n) = int_make ()
    val [l_d:addr] (pf_d | p_d) = int_make ()
    val [l_c:addr] (pf_c | p_c) = int_make ()
    viewdef V = @(int @ l_n, int @ l_d, int @ l_c)
    val lock = pthread_uplock_create ()
    val tick = pthread_upticket_create {V} (lock)
    val () =
      pthread_create_detached_cloptr
        (f, tid) where {
      val f = lam ()
        : void =<lin,cloptr1> worker (
        pf_n, pf_d, pf_c | tick, p_n, p_d, p_c, d, max_depth
      ) // end of [val]
      var tid: pthread_t // unintialized
    } // end of [pthread_create_detached_cloptr]
    val () = res := locklst_cons (p_n, p_d, p_c, lock, ?)
    val+ locklst_cons (_, _, _, _, !res1) = res
  in
    loop_depths (d + 2, max_depth, !res1); fold@ res
  end else begin
    res := locklst_nil ()
  end // end of [if]
(* end of [loop_depths] *)

fun finishup (locks: locklst): void = case+ locks of
  | ~locklst_cons (p_n, p_d, p_c, lock, locks) => let
      val (pf | ()) = pthread_uplock_download_and_destroy (lock)
      prval pf_n = pf.0 and pf_d = pf.1 and pf_c = pf.2
      val () = printf (
        "%i\t trees of depth %i\t check: %i\n", @(2 * !p_n, !p_d, !p_c)
      ) // end of printf
      val () = int_free (pf_n | p_n)
      val () = int_free (pf_d | p_d)
      val () = int_free (pf_c | p_c)
    in
      finishup (locks)
    end (* end of [locklst_cons] *)
  | ~locklst_nil () => ()
// end of [finishup]

implement main (argc, argv) = let
  val () = assert_errmsg
    (argc = 2, "Exit: wrong command format!\n")
  val n = int1_of argv.[1]
  val () = assert_errmsg
    (n >= 0, "The input integer needs to be a natural number.\n")
  val () = gc_chunk_count_limit_set (1 << 15)
  val () = gc_chunk_count_limit_max_set (~1) // no max
  val max_depth = max (MIN_DEPTH + 2, n)
  var res: locklst // uninitialized
  val () = loop_depths (MIN_DEPTH, max_depth, res)
  val () = stretch (max_depth)
  val long_lived_tree = long_lived_tree_make (max_depth)
  val () = finishup (res)
in
  printf ("long lived tree of depth %i\t check: %i\n", @(max_depth, check_ref long_lived_tree))
end // end of [main]

(* ****** ****** *)

(* end of [binary-tree2_smp.dats] *)
