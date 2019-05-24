(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -O3 binary-trees.dats -o binary-trees -D_ATS_GCATS
*)

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

dataviewtype tree (int) =
  Nil(0) | {n1,n2:two} Node(1) of (tree n1, int, tree n2)

viewtypedef Tree = [n:two] tree n

fun make (d: int, i: int): Tree =
  if d > 0 then
    let val d1 = d-1 and i2 = i << 1 in      
      Node (make (d1, i2 - 1), i, make (d1, i2))
    end
  else Node (Nil (), i, Nil ())

fun check_and_free (t: Tree):<!ntm> int =  case+ t of
  | ~Node (tl, i, tr) => i + check_and_free tl - check_and_free tr
  | ~Nil () => 0

fun check (t: !Tree):<!ntm> int =  case+ t of
  | Node (!tl, i, !tr) =>
    let val ans = i + check (!tl) - check (!tr) in (fold@ t; ans) end
  | Nil () => (fold@ t; 0)

fun check_ref (r: ref Tree): int = let
  val (pf_box | p) = ref_get_view_ptr r
  prval vbox pf = pf_box
in
  check !p     
end // end of [check_ref]

//

val min_depth: Nat = 4

fn stretch (max_depth: Nat): void = let
   val stretch_depth = max_depth + 1
   val t = make (stretch_depth, 0)
   val c = check_and_free (t)
in
   printf ("stretch tree of depth %i\t check: %i\n", @(stretch_depth, c));
end // end of [stretch]

fn long_lived_tree_make
  (max_depth: Nat): ref Tree = let
  val t = make (max_depth, 0); val t_r = ref<Tree> (t)
in
  t_r
end // end of [long_lived_tree_make]

fun loop_depths (d: Nat, max_depth: Nat): void = begin
  if d <= max_depth then let
    val n = 1 << (max_depth - d + min_depth)
    fun loop (i: Nat, c: int):<cloptr1> int =
      if i < n then let
        val t = make(d, i); val c1 = check_and_free t
        val t = make(d, ~i); val c2 = check_and_free t
      in
        loop (i+1, c + c1 + c2)
      end else c
    val c = loop (0, 0)
  in
    printf ("%i\t trees of depth %i\t check: %i\n", @(2 * n, d, c));
    loop_depths (d + 2, max_depth)
  end
end // end of [loop_depths]

implement
main (argc, argv) = let
//
  val () = assert_errmsg
    (argc = 2, "Exit: wrong command format!\n")
  val n = int1_of argv.[1]
  val () = assert_errmsg
    (n >= 0, "The input integer needs to be a natural number.\n")
//
  val () = gc_chunk_count_limit_set (1 << 15)
  val () = gc_chunk_count_limit_max_set (~1) // infinite
//
  val max_depth = max (min_depth + 2, n)
  val () = stretch (max_depth)
  val long_lived_tree = long_lived_tree_make (max_depth)
//
in
  loop_depths (min_depth, max_depth);
  printf ("long lived tree of depth %i\t check: %i\n", @(max_depth, check_ref long_lived_tree))
end // end of [main]

(* ****** ****** *)

(* end of [binary-tree.dats] *)
