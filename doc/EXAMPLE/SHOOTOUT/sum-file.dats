//
//
// sum-file.dats -- read lines, parse and tally integers
// The Great Computer Language Shootout
// http://shootout.alioth.debian.org/
//
// This implementation is as efficient as the C code attached
// at the end of this file.
//
// Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//
//

staload "libc/SATS/stdio.sats"
staload "libc/SATS/stdlib.sats"

#define BUFSZ 128

typedef bytes (n:int) = @[byte][n]

#define FGETINT 0

#if FGETINT #then

extern fun fgetint_err {m:file_mode}
  (pf: file_mode_lte (r, m) | file: &FILE m, i: &int? >> int): int
  = "fgetint_err"

fun loop (file: &FILE r, sum: int): int = let
  var i: int // uninitialized
  val err = fgetint_err (file_mode_lte_r_r | file, i)
in
  if err > 0 then loop (file, sum + i) else sum
end // end of [loop]

#else

fun loop {l_buf:addr} (
    pf_buf: !b0ytes(BUFSZ) @ l_buf
  | file: &FILE r
  , p_buf: ptr l_buf
  , sum: int
  ) : int = let
  val (pf_res | res) = fgets_err
    (file_mode_lte_r_r, pf_buf | p_buf, BUFSZ, file)
in
  if res <> null then let
    prval fgets_v_succ pf = pf_res
    val i = atoi (cast_ptr_string p_buf) where {
      extern castfn cast_ptr_string (p: ptr): string
    } // end of [val]
    prval () = pf_buf := bytes_v_of_strbuf_v pf
  in
    loop (pf_buf | file, p_buf, sum + i)
  end else let
    prval fgets_v_fail pf = pf_res
  in
    (pf_buf := pf; sum)
  end
end // end of [loop]

#endif

//

implement main (argc, argv) = let
  val (pf_stdin | p_stdin) = stdin_get ()
#if FGETINT #then
  val sum = loop (!p_stdin, 0)
#else
  val (pf_gc, pf_buf | buf) = malloc_gc (BUFSZ)
  val sum = loop (pf_buf | !p_stdin, buf, 0)
  val () = free_gc (pf_gc, pf_buf | buf)
#endif
  val () = stdin_view_set (pf_stdin | (*none*))
in
  printf ("%i\n", @(sum))
end // end of [main]

//

%{$

// #define FGETC fgetc
#define FGETC fgetc_unlocked

int fgetint_err (ats_ptr_type fp, ats_ptr_type res) {
  int i = 0; char c; int sign;

  sign = 1; c = FGETC((FILE *)fp);

  if (c == '-') {
    sign = -1; c = FGETC((FILE *)fp);
  }

  while (1) {
    if ( '0' <= c && c <= '9') {
      i = i * 10 + (c - '0'); c = FGETC((FILE *)fp);
    } else {
      if (sign > 0) *(int *)res = i; else *(int *)res = -i;
      return c;
    }
  }

  return 0; // deadcode
}

%}

////

/* -*- mode: c -*-
 * $Id: sumcol-gcc.code,v 1.42 2007-05-19 00:42:43 igouy-guest Exp $
 * http://www.bagley.org/~doug/shootout/
 */

#include <stdio.h>
#include <stdlib.h>

#define MAXLINELEN 128

int
main() {
    int sum = 0;
    char line[MAXLINELEN];

    while (fgets_unlocked(line, MAXLINELEN, stdin)) {
	sum += atoi(line);
    }
    printf("%d\n", sum);
    return(0);
}

