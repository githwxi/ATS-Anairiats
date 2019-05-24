//
// binary-tree.dats
//
// An example testing memory allocation/deallocation
//
// Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

datatype tree (int) =
  Nil(0) | {n1,n2:two} Node(1) of (tree n1, int, tree n2)

viewtypedef Tree = [n:two] tree n

fun make (d: int, i: int):<fun1> Tree =
  if d > 0 then
    let val d1 = d-1 and i2 = i << 1 in
      Node (make (d1, i2 - 1), i, make (d1, i2))
    end
  else Node (Nil (), i, Nil ())

fun check (t: Tree):<fun1> int =  case+ t of
  | Node (tl, i, tr) => i + check tl - check tr
  | Nil () => 0

//

val min_depth: Nat = 4

fn stretch (max_depth: Nat):<fun1> void = let
  val stretch_depth = max_depth + 1
  val t = make (stretch_depth, 0); val c = check (t)
in
  printf ("stretch tree of depth %i\t check: %i\n", @(stretch_depth, c));
end // end of [stretch]

fn long_lived_tree_make (max_depth: Nat):<fun1> Tree =
  make (max_depth, 0)

fun loop_depths (d: Nat, max_depth: Nat):<fun1> void =
  if d <= max_depth then let
    val n = 1 << (max_depth - d + min_depth)
    fun loop (i: Nat, c: int):<cloptr1> int =
      if i < n then let
        val t = make(d,  i); val c1 = check t
        val t = make(d, ~i); val c2 = check t
      in
        loop (i+1, c + c1 + c2)
      end else begin
        c // return value
      end
   val c = loop (0, 0)
 in
   printf ("%i\t trees of depth %i\t check: %i\n", @(2 * n, d, c));
   loop_depths (d + 2, max_depth)
 end // end of [if]

implement main (argc, argv) = let

val () = assert_errmsg_bool1
  (argc = 2, "Exit: wrong command format!\n")
val n = int1_of argv.[1]
val () = assert_errmsg_bool1
  (n >= 0, "The input integer needs to be a natural number.\n")

val () = gc_chunk_count_limit_max_set (~1) // make it infinite!
val max_depth = max (min_depth + 2, n)
val () = stretch (max_depth)
val long_lived_tree = long_lived_tree_make (max_depth)

in

loop_depths (min_depth, max_depth);
printf ("long lived tree of depth %i\t check: %i\n", @(max_depth, check long_lived_tree))

end  

////

(* binarytrees.mlton
 *
 * The Computer Language Shootout
 * http://shootout.alioth.debian.org/
 *
 * Contributed by Troestler Christophe
 * Ported to MLton/SML by sweeks@sweeks.com.
 * Optimized and compressed by Vesa Karvonen.
 * De-optimized by Isaac Gouy
 *)
datatype 'a tree = Nil | Node of 'a tree * 'a * 'a tree
(* fun mk 0 i = Nil | mk d i = Node (mk (d-1) (i*2-1), i, mk (d-1) (i*2)) *)
fun mk 0 i = Node (Nil, i, Nil) | mk d i = Node (mk (d-1) (i*2-1), i, mk (d-1) (i*2))
fun chk Nil = 0 | chk (Node (l, i, r)) = i + chk l - chk r
val n = valOf (Int.fromString (hd (CommandLine.arguments ()))) handle _ => 10
val min' = 4
val max' = Int.max (min' + 2, n)
val stretch' = max' + 1
val i2s = String.translate (fn #"~" => "-" | c => str c) o Int.toString
fun msg h d t = app print [h, Int.toString d, "\t check: ", i2s t, "\n"]
val () = msg "stretch tree of depth " stretch' (chk (mk stretch' 0))
val longLivedTree = mk max' 0
fun loopDepths d =
    if d > max' then ()
    else let val n = Word.toInt (Word.<< (0w1, Word.fromInt (max'-d+min')))
             fun lp (i, c) = if i=n then c
                             else lp (i+1, c + chk (mk d i) + chk (mk d (~i)))
         in msg (Int.toString (2*n)^"\t trees of depth ") d (lp (0, 0))
          ; loopDepths (d + 2) end
val () = loopDepths min'
val () = msg "long lived tree of depth " max' (chk longLivedTree)

////

(* binarytrees.ml
 *
 * The Computer Language Shootout
 * http://shootout.alioth.debian.org/
 *
 * Contributed by Troestler Christophe
 * De-optimized by Isaac Gouy
 *)

type 'a tree = Empty | Node of 'a tree * 'a * 'a tree

let rec make i d =
(* if d = 0 then Empty *)
  if d = 0 then Node(Empty, i, Empty)
  else let i2 = 2 * i and d = d - 1 in Node(make (i2 - 1) d, i, make i2 d)

let rec check = function Empty -> 0 | Node(l, i, r) -> i + check l - check r


let min_depth = 4
let max_depth = (let n = try int_of_string(Array.get Sys.argv 1) with _ -> 10 in
                 max (min_depth + 2) n)
let stretch_depth = max_depth + 1

let () =
  (* Gc.set { (Gc.get()) with Gc.minor_heap_size = 1024 * 1024 }; *)
  let c = check (make 0 stretch_depth) in
  Printf.printf "stretch tree of depth %i\t check: %i\n" stretch_depth c

let long_lived_tree = make 0 max_depth

let rec loop_depths d =
  if d <= max_depth then
    let niter = 1 lsl (max_depth - d + min_depth) and c = ref 0 in
    for i = 1 to niter do c := !c + check(make i d) + check(make (-i) d) done;
    Printf.printf "%i\t trees of depth %i\t check: %i\n" (2 * niter) d !c;
    loop_depths (d + 2)

let () =
  loop_depths min_depth;
  Printf.printf "long lived tree of depth %i\t check: %i\n"
    max_depth (check long_lived_tree)

////

/* The Computer Language Shootout Benchmarks
   http://shootout.alioth.debian.org/

   contributed by Kevin Carson
   compilation:
       gcc -O3 -fomit-frame-pointer -funroll-loops -static binary-trees.c -lm
       icc -O3 -ip -unroll -static binary-trees.c -lm
*/

#include <malloc.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>


typedef struct tn {
    struct tn*    left;
    struct tn*    right;
    long          item;
} treeNode;


treeNode* NewTreeNode(treeNode* left, treeNode* right, long item)
{
    treeNode*    new;

    new = (treeNode*)malloc(sizeof(treeNode));

    new->left = left;
    new->right = right;
    new->item = item;

    return new;
} /* NewTreeNode() */


long ItemCheck(treeNode* tree)
{
    if (tree->left == NULL)
        return tree->item;
    else
        return tree->item + ItemCheck(tree->left) - ItemCheck(tree->right);
} /* ItemCheck() */


treeNode* BottomUpTree(long item, unsigned depth)
{
    if (depth > 0)
        return NewTreeNode
        (
            BottomUpTree(2 * item - 1, depth - 1),
            BottomUpTree(2 * item, depth - 1),
            item
        );
    else
        return NewTreeNode(NULL, NULL, item);
} /* BottomUpTree() */


void DeleteTree(treeNode* tree)
{
    if (tree->left != NULL)
    {
        DeleteTree(tree->left);
        DeleteTree(tree->right);
    }

    free(tree);
} /* DeleteTree() */


int main(int argc, char* argv[])
{
    unsigned   N, depth, minDepth, maxDepth, stretchDepth;
    treeNode   *stretchTree, *longLivedTree, *tempTree;

    N = atol(argv[1]);

    minDepth = 4;

    if ((minDepth + 2) > N)
        maxDepth = minDepth + 2;
    else
        maxDepth = N;

    stretchDepth = maxDepth + 1;

    stretchTree = BottomUpTree(0, stretchDepth);
    printf
    (
        "stretch tree of depth %u\t check: %li\n",
        stretchDepth,
        ItemCheck(stretchTree)
    );

    DeleteTree(stretchTree);

    longLivedTree = BottomUpTree(0, maxDepth);

    for (depth = minDepth; depth <= maxDepth; depth += 2)
    {
        long    i, iterations, check;

        iterations = pow(2, maxDepth - depth + minDepth);

        check = 0;

        for (i = 1; i <= iterations; i++)
        {
            tempTree = BottomUpTree(i, depth);
            check += ItemCheck(tempTree);
            DeleteTree(tempTree);

            tempTree = BottomUpTree(-i, depth);
            check += ItemCheck(tempTree);
            DeleteTree(tempTree);
        } /* for(i = 1...) */

        printf
        (
            "%li\t trees of depth %u\t check: %li\n",
            iterations * 2,
            depth,
            check
        );
    } /* for(depth = minDepth...) */

    printf
    (
        "long lived tree of depth %u\t check: %li\n",
        maxDepth,
        ItemCheck(longLivedTree)
    );

    return 0;
}
