(*
**
** An implementation of functional arrays based on Braun trees.
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2008
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

abstype funarray_t (a:t@ype+ (*element*),  n:int (*size*))
typedef farr (a: t@ype, n: int) = funarray_t (a, n) // an abbreviation

(* ****** ****** *)

// create an empty array
extern fun{} funarray_nil {a:t@ype} ():<(*pure*)> farr (a, 0)

// compute the size of [A]
extern fun{a:t@ype} funarray_length (* O(log^2(n)) *)
  {n:nat} (A: farr (a, n)):<(*pure*)> int n

// obtain the element stored in 'A[i]'
extern fun{a:t@ype} funarray_get_elt_at (* O(log(n)) *)
  {n:nat} (A: farr (a, n), i: natLt n):<(*pure*)> a

// update 'A[i]' with 'x'; note that this creates a new array!
extern fun{a:t@ype} funarray_set_elt_at (* O(log(n)) *)
  {n:nat} (A: farr (a, n), i: natLt n, x: a):<(*pure*)> farr (a, n)

overload [] with funarray_get_elt_at
overload [] with funarray_set_elt_at
  
(* ****** ****** *)

// exchange elements stored in 'A[i]' and 'x'
extern fun{a:t@ype} funarray_xch_elt_at (* O(log(n)) *)
  {n:nat} (A: farr (a, n), i: natLt n, x: &a >> a):<(*pure*)> farr (a, n)

(* ****** ****** *)

// insert an element to the start of the array
extern fun{a:t@ype} funarray_loadd (* O(log(n)) *)
  {n:nat} (A: farr (a, n), x: a):<(*pure*)> farr (a, n+1)

// remove an element from the start of the array
extern fun{a:t@ype} funarray_lorem (* O(log(n)) *)
  {n:pos} (A: farr (a, n)):<(*pure*)> farr (a, n-1)

// remove an element from the start of the array and obtain it
extern fun{a:t@ype} funarray_lorem_get (* O(log(n)) *)
  {n:pos} (A: farr (a, n), x: &a? >> a):<(*pure*)> farr (a, n-1)

(* ****** ****** *)

// insert an element to the end of the array
extern fun{a:t@ype} funarray_hiadd (* O(log(n)) *)
  {n:nat} (A: farr (a, n), n: int n, x: a):<(*pure*)> farr (a, n+1)

// remove an element from the end of the array
extern fun{a:t@ype} funarray_hirem (* O(log(n)) *)
  {n:pos} (A: farr (a, n), n: int n):<(*pure*)> farr (a, n-1)

// remove an element from the end of the array and obtain it
extern fun{a:t@ype} funarray_hirem_get (* O(log(n)) *)
  {n:pos} (A: farr (a, n), n: int n, x: &a? >> a):<(*pure*)> farr (a, n-1)

(* ****** ****** *)

(*
** these higher-order functions are probably not particularly useful as
** they can be readily replaced with for-loops. See the implementation.
*)

extern fun{a:t@ype} funarray_foreach_cloptr {n:nat} {f:eff}
 (A: farr (a, n), n: int n, f: !a -<cloptr,f> void):<f> void

extern fun{a:t@ype} funarray_foreach_cloref {n:nat} {f:eff}
 (A: farr (a, n), n: int n, f:  a -<cloref,f> void):<f> void

extern fun{a:t@ype} funarray_iforeach_cloptr {n:nat} {f:eff}
 (A: farr (a, n), n: int n, f: !(natLt n, a) -<cloptr,f> void):<f> void

extern fun{a:t@ype} funarray_iforeach_cloref {n:nat} {f:eff}
 (A: farr (a, n), n: int n, f:  (natLt n, a) -<cloref,f> void):<f> void

(* ****** ****** *)

datatype brauntree (a:t@ype+, int) =
  | {n1,n2:nat | n2 <= n1; n1 <= n2+1}
    B (a, n1+n2+1) of (a, brauntree (a, n1), brauntree (a, n2))
  | E (a, 0) of ()

stadef bt = brauntree // an abbreviation

(* ****** ****** *)

assume funarray_t (a: t@ype, n:int) = brauntree (a, n)

(* ****** ****** *)

implement{} funarray_nil {a} () = E ()

(* ****** ****** *)

implement{a} funarray_length (A) = size (A) where {
  // this algorithm is taken from a paper by Okasaki
  fun diff {nl,nr:nat | nr <= nl && nl <= nr+1} .<nr>. 
    (nr: int nr, t: bt (a, nl)):<> int (nl-nr) = begin case+ t of
    | B (_, tl, tr) => begin
        if nr > 0 then let
          val nr2 = nr / 2
        in
          if nr > nr2 + nr2 then diff (nr2, tl) else diff (nr2-1, tr)
        end else begin
          1 // return value
        end // end of [if]
      end // end of [B]
     | E () => 0
  end // end of [diff]

  fun size {n:nat} .<n>. (t: bt (a, n)):<> int n = begin
    case+ t of
    | B (_, tl, tr) => begin
        let val nr = size tr in 1 + nr + nr + diff (nr, tl) end
      end // end of [B]
    | E () => 0
  end // end of [size]
} // end of [funarray_length]

(* ****** ****** *)

implement{a} funarray_get_elt_at (A, i) = get_at (A, i) where {
  fun get_at {n,i:nat | i < n} .<n>. (t: bt (a, n), i: int i):<> a =
    if i > 0 then let
      val i2 = i / 2
    in
      if i > i2 + i2 then let
        val+ B (_, tl, _) = t in get_at (tl, i2)
      end else let
        val+ B (_, _, tr) = t in get_at (tr, i2-1)
      end // end of [if]
    end else let
      val+ B (x, _, _) = t in x
    end // end of [if]
} // end of [funarray_get_at]

implement{a} funarray_set_elt_at
  (A, i, x0) = set_at (A, i, x0) where {
  fun set_at {n,i:nat | i < n} .<n>.
    (t: bt (a, n), i: int i, x0: a):<> bt (a, n) =
    if i > 0 then let
      val+ B (x, tl, tr) = t; val i2 = i / 2
    in
      if i > i2 + i2 then begin
        B (x, set_at (tl, i2, x0), tr)
      end else begin
        B (x, tl, set_at (tr, i2-1, x0))
      end // end of [if]
    end else let
      val+ B (_, t1, t2) = t in B (x0, t1, t2)
    end // end of [if]
} // end of [funarray_set_at]

(* ****** ****** *)

implement{a} funarray_xch_elt_at
  (A, i, x0) = xch_at (A, i, x0) where {
  fun xch_at {n,i:nat | i < n} .<n>.
    (t: bt (a, n), i: int i, x0: &a >> a):<> bt (a, n) =
    if i > 0 then let
      val+ B (x, tl, tr) = t; val i2 = i / 2
    in
      if i > i2 + i2 then begin
        B (x, xch_at (tl, i2, x0), tr)
      end else begin
        B (x, tl, xch_at (tr, i2-1, x0))
      end // end of [if]
    end else let
      val x0_val = x0; val+ B (x, t1, t2) = t; val () = x0 := x
    in
      B (x0_val, t1, t2)
    end // end of [if]
} // end of [funarray_xch_at]

(* ****** ****** *)

implement{a} funarray_loadd
  (t, x0) = loadd (t, x0) where {
  fun loadd {n:nat} .<n>.
    (t: bt (a, n), x0: a):<> bt (a, n+1) = begin
    case+ t of
    | B (x, tl, tr) => B (x0, loadd (tr, x), tl)
    | E () => B (x0, E (), E ())
  end // end of [loadd]
} // end of [funarray_loadd]

implement{a} funarray_lorem (t) = lorem (t) where {
  fun lorem {n:int | n > 0} .<n>.
    (t: bt (a, n)):<> bt (a, n-1) = let
    val+ B (_, tl, tr) = t
  in
    case+ tl of
    | B (xl, _, _) => B (xl, tr, lorem tl) | E () => E ()
  end // end of [lorem]
} // end of [brauntree_lorem]

implement{a} funarray_lorem_get (t, x) = let
  val+ B (x0, tl, tr) = t; val () = (x := x0)
in
  case+ tl of
  | B (xl, _, _) => B (xl, tr, funarray_lorem<a> tl) | E () => E ()
end // end of [funarray_lorem_get]

(* ****** ****** *)

implement{a} funarray_hiadd
  (t, n, x0) = hiadd (t, n, x0) where {
  fun hiadd {n:nat} .<n>.
    (t: bt (a, n), n: int n, x0: a):<> bt (a, n+1) =
    if n > 0 then let
      val+ B (x, tl, tr) = t; val n2 = n / 2
    in
      if n > n2 + n2 then begin
        B (x, hiadd (tl, n2, x0), tr)
      end else begin
        B (x, tl, hiadd (tr, n2-1, x0))
      end
    end else begin
      B (x0, E (), E ())
    end // end of [if]
} // end of [funarray_hiadd]

implement{a} funarray_hirem
  (t, n) = hirem (t, n) where {
  fun hirem {n:pos} .<n>.
    (t: bt (a, n), n: int n):<> bt (a, n-1) = let
    val+ B (x, tl, tr) = t; val n2 = n / 2
  in
    case+ tl of
    | B _ => begin
        if n > n2 + n2 then begin
          B (x, tl, hirem (tr, n2))
        end else begin
          B (x, hirem (tl, n2), tr)
        end // end of [if]
      end // end of [B]
    | E () => E ()
  end // end of [hirem]
} // end of [funarray_hirem]

implement{a} funarray_hirem_get
  (t, n, x0) = hirem_get (t, n, x0) where {
  fun hirem_get {n:pos} .<n>.
    (t: bt (a, n), n: int n, x0: &a? >> a):<> bt (a, n-1) = let
    val+ B (x, tl, tr) = t; val n2 = n / 2
  in
    case+ tl of
    | B _ => begin
        if n > n2 + n2 then begin
          B (x, tl, hirem_get (tr, n2, x0))
        end else begin
          B (x, hirem_get (tl, n2, x0), tr)
        end // end of [if]
      end // end of [B]
    | E () => (x0 := x; E ())
  end
  // end of [hirem_get]
} // end of [funarray_hirem_get]

(* ****** ****** *)

implement{a} funarray_foreach_cloptr {n} {f} (A, n, f) = let
  var i: natLte n
in
  for* {i:nat | i <= n} .<n-i>. // termination metric
    (i: int i) => (i := 0; i < n; i := i+1) f (A[i])
end // end of [funarray_foreach]

implement{a} funarray_foreach_cloref {n} {f} (A, n, f) = let
  var i: natLte n
in
  for* {i:nat | i <= n} .<n-i>. // termination metric
    (i: int i) => (i := 0; i < n; i := i+1) f (A[i])
end // end of [funarray_foreach]

(* ****** ****** *)

implement{a} funarray_iforeach_cloptr {n} {f} (A, n, f) = let
  var i: natLte n
in
  for* {i:nat | i <= n} .<n-i>. // termination metric
    (i: int i) => (i := 0; i < n; i := i+1) f (i, A[i])
end // end of [funarray_foreach]

implement{a} funarray_iforeach_cloref {n} {f} (A, n, f) = let
  var i: natLte n
in
  for* {i:nat | i <= n} .<n-i>. // termination metric
    (i: int i) => (i := 0; i < n; i := i+1) f (i, A[i])
end // end of [funarray_foreach]

(* ****** ****** *)

(* end of [funarray.dats] *)
