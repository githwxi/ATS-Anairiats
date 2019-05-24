(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -O3 -fomit-frame-pointer reverse-complement3.dats -o reverse-complement3
*)

(* ****** ****** *)

// HX: if we forget about safety, ...

(* ****** ****** *)

staload "libc/SATS/stdio.sats"

(* ****** ****** *)

sta l_iubcmpltarr: addr
extern prval
  pfbox_iubcmpltarr: vbox (bytes(BYTE_MAX+1) @ l_iubcmpltarr)
val p_iubcmpltarr = $extval (ptr l_iubcmpltarr, "&iubcmpltarr[0]")

fn iubcmplt_get (b: byte): byte = let
  val i = int1_of_byte (b); prval vbox pf = pfbox_iubcmpltarr in
  p_iubcmpltarr->[i]
end // end of [iubcmplt_get]

(* ****** ****** *)

extern fun ptrget (p: ptr): byte = "mac#theBuffer_ptrget"
extern fun ptrset (p: ptr, b: byte): void = "mac#theBuffer_ptrset"

(* ****** ****** *)

extern fun
search_buf (p: ptr, b: byte): ptr = "search_buf"
implement search_buf (p, b) =
  if ptrget(p) <> b then search_buf (p+1, b) else p
// end of [search_buf]

(* ****** ****** *)

extern fun
reverse_buf (pi: ptr, pj: ptr): void = "reverse_buf"

implement
reverse_buf (pi, pj) = let
  macdef NL = byte_of_char('\n')
in
  if pi < pj then let
    val xi = ptrget (pi)
  in
    if (xi <> NL) then let
      val xj = ptrget (pj)
    in
      if (xj <> NL) then let
        val () = ptrset (pi, iubcmplt_get (xj))
        and () = ptrset (pj, iubcmplt_get (xi))
      in
        reverse_buf (pi+1, pj-1)
      end else reverse_buf (pi, pj-1)
    end else reverse_buf (pi+1, pj)
  end // end of [if]
end // end of [reverse_buf]

(* ****** ****** *)

implement
main () = () where {
  val () = _init () where {
    extern fun _init (): void = "iubcmpltarr_initialize"
  }
  val () = _initset () where {
    extern fun _initset (): void = "mac#theBuffer_initset"
  }
  val () = _reverse () where {
    extern fun _reverse (): void = "mac#theBuffer_reverse"
  }
  val () = _print () where {
    extern fun _print (): void = "mac#theBuffer_print"
  }
} // end of [main]

(* ****** ****** *)

%{^
// HX: reuse some existing C code for initialization

#include <errno.h>

static
unsigned char iubpairs[][2] = {
    {    'A',    'T'    },
    {    'C',    'G'    },
    {    'B',    'V'    },
    {    'D',    'H'    },
    {    'K',    'M'    },
    {    'R',    'Y'    },
    {    '\000',   '\000'   }
} ;

#define BYTE_MAX 255
static
unsigned char iubcmpltarr[1+BYTE_MAX];

static inline
ats_void_type iubcmpltarr_initialize () {
  int i;
  for (i=0; i <= BYTE_MAX; i++) {
    iubcmpltarr[i] = (unsigned char) i;
  }
  for (i=0; iubpairs[i][0] != '\0'; i++) {
    iubcmpltarr[iubpairs[i][0]] = iubpairs[i][1];
    iubcmpltarr[iubpairs[i][1]] = iubpairs[i][0];
    iubcmpltarr[tolower(iubpairs[i][0])] = iubpairs[i][1];
    iubcmpltarr[tolower(iubpairs[i][1])] = iubpairs[i][0];
  }
} /* end of [iubcmpltarr_initialize] */

//
// #define NBYTE 60
//
#define NBYTE 1024*1024
static
char
theBuffer[256*1024*1024] ;
size_t theTotal = 0 ;
void theBuffer_initset () {
  size_t n ;
  char *p = theBuffer ;
  while (1) {
    n = fread (p, 1, NBYTE, stdin) ; if (!n) break ; p += n ;
  } // end of [while]
  theTotal = (p-theBuffer) ;
  return ;
} // end of [theBuffer_initset]

void theBuffer_print () {
  size_t n, tot ;
  char *p ;
  tot = theTotal ; p = theBuffer ;
  while (tot > 0) {
    n = fwrite (p, 1, tot, stdout) ; if (!n) break ; tot -= n ; p += n ;
  } // end of [while]
  return ;
} // end of [theBuffer_print]

static inline
char theBuffer_ptrget
  (char *p) { return *p ; }
static inline
void theBuffer_ptrset
  (char *p, char b) { *p = b; return; }
// end of [theBuffer_set]

void
theBuffer_reverse () {
  extern ats_ptr_type search_buf (ats_ptr_type p, ats_byte_type b) ;
  extern ats_void_type reverse_buf (ats_ptr_type pi, ats_ptr_type pj) ;
  ats_ptr_type p_beg = theBuffer ;
  ats_ptr_type p_end = theBuffer + theTotal-1 ;
  ats_ptr_type p0, p1 ;
//
  p0 = search_buf (p_beg, '>') ; p0 = search_buf (p0, '\n') ;
  p1 = search_buf (p0+1, '>') ;
  reverse_buf (p0+1, p1-1);
//
  p0 = search_buf(p1, '\n') ;
  p1 = search_buf (p0+1, '>') ;
  reverse_buf (p0+1, p1-1);  
//
  p0 = search_buf(p1, '\n') ;
  reverse_buf (p0+1, p_end) ;  
//
  return ;
} // end of [theBuffer_reverse]

%} // end of [%{^]

(* ****** ****** *)

(* end of [reverse-complement3.dats] *)
