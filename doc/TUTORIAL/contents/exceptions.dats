//
//
// code for illustration in exceptions.dats
//
//

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"

(* ****** ****** *)

exception Fail // Fail: exn
exception Fail_msg of string // Fail_msg: string -> exn

// Fail_msgs : {n:nat} (int n, list (string n)) -> exn
exception {n:nat} Fail_msgs of (int n, list (string, n))

(* ****** ****** *)

datatype bt = E | B of (bt, bt) // datatype for binary trees

fn isBraunTree (bt0: bt): bool = let
  exception NotBraunTree
  fun aux (bt: bt): int = case+ bt of
    | B (bt1, bt2) => let
        val ls = aux bt1 and rs = aux bt2
      in
        if (ls >= rs && rs+1 >= ls) then ls+rs+1 else $raise NotBraunTree()
      end
    | E () => 0
  // end of [aux]
in
  try let val s = aux bt0 in true end with ~NotBraunTree() => false
end // end of [isBraunTree]

(* ****** ****** *)

extern fun{a:t@ype}
  list_iforeach (xs: List a, f: (Nat, a) -<cloref1> void): void
implement{a} list_iforeach (xs, f) = ()

fn nth{a:t@ype} (xs: List a, n: Nat): a = let
  exception Found of a
  fn f (i: Nat, x: a):<cloref1> void = if i = n then $raise (Found x)
in
  try let
    val () = list_iforeach (xs, f) in $raise ListSubscriptException ()
  end with
    ~Found x => x
  // end of [try]
end // end of [nth]

(* ****** ****** *)
////
fn{a:t@ype} nth (xs: List a, n: Nat): a = let
  exception Found of ()
  val ans = ref_make_elt<Option a> (None)
  fn f (i: Nat, x: a): void =
    if i = n then (!ans := Some x; $raise Found ())
  val () = (try let
    val () = list_iforeach (xs, f) in $raise ListSubscriptException ()
  end with
    ~Found () => ()
  ) : void // end of [try]
in
  case !ans of
  | Some x => x | None () => $raise ListSubscriptException ()
end // end of [nth]

(* ****** ****** *)

(* end of [exceptions.dats] *)
