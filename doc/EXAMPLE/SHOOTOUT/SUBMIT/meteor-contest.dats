(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -O3 meteor-contest.dats -o meteor-contest -D_ATS_GCATS
*)

(* ****** ****** *)

abst@ype board_t

(* ****** ****** *)

extern fun board_make (): [l:addr] (board_t @ l | ptr l)
  = "board_make"

extern fun board_get (B: &board_t, x: int, y: int): int
  = "board_get"

extern fun board_getset (B: &board_t, x: int, y: int): int
  = "board_getset"

(* ****** ****** *)

%{$

#define NROW 10
#define NCOL 5
#define NCOL2 10

typedef unsigned int uint ;

#define M 2
// #define M (sizeof(uint) / NCOL)

#define BOARDSIZE ((NROW + M - 1) / M)

ats_int_type board_get (
  ats_ptr_type B, ats_int_type x, ats_int_type y
) {
  int i, j, k ;
  uint mask, u ;
  if (x < 0 || x >= NROW) return -1 ;
  if (y < 0 || y >= NCOL2) return -1 ;
  i = x / M ; j = (x % M) * NCOL2 + y ;
  mask = 1 << j ; u = ((uint*)B)[i] ;
  return (mask & u) ;
} /* end of [board_get] */

ats_int_type board_getset (
  ats_ptr_type B, ats_int_type x, ats_int_type y
) {
  int i, j, k ;
  uint u, mask ;
  if (x < 0 || x >= NROW) return -1 ;
  if (y < 0 || y >= NCOL2) return -1 ;
  i = x / M ; j = (x % M) * NCOL2 + y ;
  mask = 1 << j ; u = ((uint*)B)[i] ;
  ((uint*)B)[i] = (mask | u) ;
  return (mask & u) ;
} /* end of [board_getset] */

ats_ptr_type
board_make () {
  int x, y ; ats_ptr_type B ;
  B = calloc((NROW + M - 1) / M, sizeof(uint)) ;
/*
  for (i = 0; i < BOARDSIZE; i += 1) B[i] = 0 ;
*/
  for (x = 0; x < NROW; x += 2) {
    for (y = 1; y < NCOL2; y += 2) board_getset (B, x, y) ;
  }
  for (x = 1; x < NROW; x += 2) {
    for (y = 0; y < NCOL2; y += 2) board_getset (B, x, y) ;
  }
  return ;
} /* end of [board_initialize] */

%}

(* ****** ****** *)

(* end of [meteor-contest.dats] *)
