
//
// This implementation is directly translated from the ocaml
// version attached at the end. It is a lot faster!
//
// Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

(*

machine: dml.bu.edu
command: fannkuch 11

ATS:	6.115u 0.002s 0:06.27 97.4%	0+0k 0+0io 0pf+0w
C:	6.781u 0.009s 0:07.04 96.3%	0+0k 0+0io 0pf+0w
OCAML:  8.926u 0.010s 0:09.09 98.2%	0+0k 0+0io 0pf+0w

*)

%{^

typedef ats_ptr_type iarray ;

ats_ptr_type
iarray_make (ats_int_type n) {
  return malloc(n * sizeof(ats_int_type)) ;
}

static inline
ats_void_type
iarray_free (ats_ptr_type A) { free (A) ; return ; }

static inline
ats_int_type
iarray_get (ats_ptr_type A, ats_int_type i) {
  return ((ats_int_type *)A)[i] ;
}

static inline
ats_void_type
iarray_set (ats_ptr_type A, ats_int_type i, ats_int_type f) {
  ((ats_int_type *)A)[i] = f ; return ;
}

%}

abst@ype iarray = $extype "iarray"

// uninitialized
extern fun iarray_make (sz: int): iarray = "iarray_make"

extern fun iarray_free (A: iarray): void = "iarray_free"

extern fun iarray_get (A: iarray, i: int): int = "iarray_get"

extern fun iarray_set (A: iarray, i: int, x: int): void = "iarray_set"

overload [] with iarray_get
overload [] with iarray_set

//

(* printing integer array *)
fn q (p: iarray, n: int): void =
  let
    var i: int = 0
  in
    while (i < n) (print p[i]; i := i+1) ;
    print_newline ()
  end

(*counting permutations*)
fun a (r: iarray, n: int): int =
  let
    val x = r[n]
  in
    r[n] := x + 1;
    if x = n - 2 then a (r, n+1) else (if x = n - 1 then r[n] := 0; n)
  end

fn w (p: iarray, s: iarray, n: int): int =
  let
    fun loop1 (i: int):<cloptr1> void =
      if i < n then (s[i] := p[i]; loop1 (i+1))

    fun loop2 (x: int, i: int, u: int):<cloptr1> void =
      if i <= u then
        let
           val t = s[i] and o = x - i
        in
           s[i] := s[o]; s[o] := t; loop2 (x, i+1, u)
        end

    fun b (i: int):<cloptr1> bool =
(*
      if i = n then true else (if p[i]<>(i+1) then b(i+1) else false)
*)
      if p[0] = 1 then false else if p[n-1] = n then false else true
      
    fun y (m: int):<cloptr1> int =
      let
        val x = s[0] - 1
      in
        if x = 0 then m else (loop2 (x, 0, (x - 1) >> 1); y (m+1))
      end
  in
    if b 0 then (loop1 (0); y 0) else 0
  end

(*building new permutations*)
fn x (p: iarray, n: int): void =
  let
    fun loop2 (p: iarray, j: int, i: int): void =
      if j < i then (p[j] := p[j+1]; loop2 (p, j+1, i))

    fun loop1 (p: iarray, n: int, i: int): void =
      if i < n then begin
        let val t = p[0] in
          loop2 (p, 0, i); p[i] := t; loop1 (p, n, i+1)
        end
      end
  in
    loop1 (p, n, 1)
  end

fn* f (r: iarray, p: iarray, s: iarray, n: int, i: int, m: int,  z: int): int =
  if z > 0 then
    if i <= n then begin
      q (p, n); x (p, i);
      f (r, p, s, n, a (r, 2), max (m, w (p, s, n)), z-1)
    end else begin
      q (p, n); g (r, p, s, n, i, m)
    end
  else g (r, p, s, n, i, m)

and g (r: iarray, p: iarray, s: iarray, n: int, i: int, m: int): int =
  if i <= n then begin
    x (p, i); g(r, p, s, n, a (r, 2), max (m, w (p, s, n)))
  end else begin
    m // return value of [g]
  end

//

fn usage (cmd: string): void = printf ("usage: %s [integer]\n", @(cmd))

implement main (argc, argv) = let
  val () = if argc <> 2 then (usage argv.[0]; exit {void} (1))
  val () = assert (argc = 2)
  val s = argv.[1]
  val n = int_of_string s
  val r = iarray_make (n+2)
  val () = loop 0 where {
    val n2 = n+2
    fun loop (i: int):<cloptr1> void =
      if i < n2 then (r[i] := i - 1; loop (i+1))
  }
  val p = iarray_make (n)
  val () = loop 0 where {
    fun loop (i: int):<cloptr1> void =
      if i < n then (p[i] := i + 1; loop (i+1))
  }
  val s = iarray_make (n)
  val () = loop 0 where {
    fun loop (i: int):<cloptr1> void =
      if i < n then (s[i] := 0; loop (i+1))
  }
  val ans = f (r, p, s, n, a (r, 2), 0, 30)
in
  printf ("Pfannkuchen(%i) = %i\n", @(n, ans))
end

////

(* The Computer Language Shootout
   http://shootout.alioth.debian.org/

   contributed by Christophe Papazian
   Decembre 2005
*)

(* please compile with -unsafe to optimize speed *)

open Array open Printf

(*global variables*)
let n = try if length Sys.argv>1 then int_of_string Sys.argv.(1)else 7  with _->7
let r = init(n+2)(fun x -> x-1) and p=init n((+)1) and s=create n 0

(*pretty printing function*)
let q() = iter print_int p;print_newline()

(*counting permutations*)
let rec a n = r.(n)<-(r.(n)+1);
  if r.(n)=n-1 then a(n+1)
  else (if r.(n)=n then r.(n)<-0;n)

(*swapping arrays*)
let w m= let rec a i=i=n||(p.(i)<>(i+1)&&a(i+1))in
if a 0 then
  (for i=0 to n-1 do s.(i)<-p.(i)done;
   let rec y m= let x=s.(0)-1 in
   if x=0 then m
   else (for i=0 to((x-1) lsr 1)do
	   let t=s.(i)in let o = x-i in s.(i)<-s.(o);
	   s.(o)<-t done;y(m+1))
   in y m) else 0

(*building new permutations*)
let x n =
  for i=1 to n-1 do let t=p.(0)in
  for j=0 to i-1 do p.(j)<-p.(j+1) done; p.(i)<-t done

(* main *)
let _ = let rec f i m z= (* printing loop *)
  if i <=n && z>0
  then(q();x i;f(a 2)(max m(w 0))(z-1))
  else (if z>0 then q();g i m)
	and g i m= if i <=n (* non printing loop *)
	then(x i; g(a 2)(max m(w 0)))
	else m in
let ans = f (a 2) 0 30 in
printf "Pfannkuchen(%i) = %i\n" n ans

////

/*
 * The Computer Lannguage Shootout
 * http://shootout.alioth.debian.org/
 * Contributed by Heiner Marxen
 *
 * "fannkuch"	for C gcc
 *
 * $Id: fannkuch-gcc.code,v 1.44 2007-05-19 00:42:42 igouy-guest Exp $
 */

#include <stdio.h>
#include <stdlib.h>

#define Int	int
#define Aint	int

    static long
fannkuch( int n )
{
    Aint*	perm;
    Aint*	perm1;
    Aint*	count;
    long	flips;
    long	flipsMax;
    Int		r;
    Int		i;
    Int		k;
    Int		didpr;
    const Int	n1	= n - 1;

    if( n < 1 ) return 0;

    perm  = calloc(n, sizeof(*perm ));
    perm1 = calloc(n, sizeof(*perm1));
    count = calloc(n, sizeof(*count));

    for( i=0 ; i<n ; ++i ) perm1[i] = i;	/* initial (trivial) permu */

    r = n; didpr = 0; flipsMax = 0;
    for(;;) {
	if( didpr < 30 ) {
	    for( i=0 ; i<n ; ++i ) printf("%d", (int)(1+perm1[i]));
	    printf("\n");
	    ++didpr;
	}
	for( ; r!=1 ; --r ) {
	    count[r-1] = r;
	}

#define XCH(x,y)	{ Aint t_mp; t_mp=(x); (x)=(y); (y)=t_mp; }

	if( ! (perm1[0]==0 || perm1[n1]==n1) ) {
	    flips = 0;
	    for( i=1 ; i<n ; ++i ) {	/* perm = perm1 */
		perm[i] = perm1[i];
	    }
	    k = perm1[0];		/* cache perm[0] in k */
	    do {			/* k!=0 ==> k>0 */
		Int	j;
		for( i=1, j=k-1 ; i<j ; ++i, --j ) {
		    XCH(perm[i], perm[j])
		}
		++flips;
		/*
		 * Now exchange k (caching perm[0]) and perm[k]... with care!
		 * XCH(k, perm[k]) does NOT work!
		 */
		j=perm[k]; perm[k]=k ; k=j;
	    }while( k );
	    if( flipsMax < flips ) {
		flipsMax = flips;
	    }
	}

	for(;;) {
	    if( r == n ) {
		return flipsMax;
	    }
	    /* rotate down perm[0..r] by one */
	    {
		Int	perm0 = perm1[0];
		i = 0;
		while( i < r ) {
		    k = i+1;
		    perm1[i] = perm1[k];
		    i = k;
		}
		perm1[r] = perm0;
	    }
	    if( (count[r] -= 1) > 0 ) {
		break;
	    }
	    ++r;
	}
    }
}

    int
main( int argc, char* argv[] )
{
    int		n = (argc>1) ? atoi(argv[1]) : 0;

    printf("Pfannkuchen(%d) = %ld\n", n, fannkuch(n));
    return 0;
}

