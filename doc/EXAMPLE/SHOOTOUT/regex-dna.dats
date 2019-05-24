(*
** The Computer Language Shootout
** http://shootout.alioth.debian.org/
** contributed by Hongwei Xi
**
** regex-dna benchmark using PCRE
**
** compile with:
**   atscc -O3 -fomit-frame-pointer -o regex-dna regex-dna.dats -lpcre
*)

(*
machine: dml.bu.edu
>> time ./regex-dna < fasta50000000.txt
GC initialization is done.
agggtaaa|tttaccct 356
[cgt]gggtaaa|tttaccc[acg] 1250
a[act]ggtaaa|tttacc[agt]t 4252
ag[act]gtaaa|tttac[agt]ct 2894
agg[act]taaa|ttta[agt]cct 5435
aggg[acg]aaa|ttt[cgt]ccct 1537
agggt[cgt]aa|tt[acg]accct 1431
agggta[cgt]a|t[acg]taccct 1608
agggtaa[cgt]|[acg]ttaccct 2178

50833411
50000000
66800214
74.133u 1.504s 1:19.67 94.9%	0+0k 0+0io 0pf+0w
*)

(* ****** ****** *)

%{^

#include <pcre.h>

%}

%{^

static inline
ats_ptr_type malloc_atm (ats_int_type n) {
  ats_ptr_type p = malloc (n) ;
  if (!p) {
    fprintf (stderr, "Exit: [malloc_atm] failed.\n") ; exit (1) ;
  }
  return p ;
}

static inline
ats_void_type free_atm (ats_ptr_type p) { free (p) ; return ; }

%}

viewdef bytes_v (n:int, l:addr) = bytes n @ l

extern fun malloc_atm {n:nat}
  (n: int n): [l:addr] @(bytes_v (n, l) | ptr l) = "malloc_atm"

extern fun free_atm {n:nat} {l:addr}
  (pf: bytes_v (n, l) | p: ptr l): void = "free_atm"


(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/array.dats"

(* ****** ****** *)

viewdef block_v (sz:int, l:addr) = bytes_v (sz, l)
dataviewtype blocklst (int) =
  | {n:nat} {sz:nat} {l:addr} blocklst_cons (n+1) of
      (block_v (sz, l) | int sz, ptr l, blocklst n)
  | blocklst_nil (0)
viewtypedef blocklst = [n:nat] blocklst (n)

(* ****** ****** *)

extern typedef "blocklst_cons_pstruct" =
  blocklst_cons_pstruct (void | int, ptr, blocklst)

(* ****** ****** *)

fun free_blocklst {n:nat}
  (blks: blocklst n): void = begin case+ blks of
  | ~blocklst_cons (pf | sz, p, blks) => begin
      free_atm (pf | p); free_blocklst (blks)
    end
  | ~blocklst_nil () => ()
end // end of [free]

(* ****** ****** *)

extern fun blocklst_length {n:nat}
  (blks: !blocklst n): int n = "blocklst_length"

%{$

ats_int_type blocklst_length (ats_ptr_type blks) {
  int n = 0 ;
  while (blks) {
    n += 1 ; blks = ((blocklst_cons_pstruct)blks)->atslab_2 ;
  }
  return n ;
}

%}

(* ****** ****** *)

extern fun fread_stdin_block {sz:nat} {l:addr}
  (pf: !block_v (sz, l) | sz: int sz, p: ptr l): natLte sz
  = "fread_stdin_block"

%{$

ats_int_type
fread_stdin_block (ats_int_type sz0, ats_ptr_type p0) {
  char *p ; int nread, sz ;
  p = p0; sz = sz0 ;
  while (sz > 0) {
    nread = fread (p, 1, sz, stdin) ;
/*
    fprintf (stderr, "fread_stdin_block: nread = %i\n", nread);
*/
    if (nread > 0) { p += nread ; sz -= nread ; continue ; }
    if (feof (stdin)) break ;
  }
  return (sz0 - sz) ;
} /* end of [fread_stdin_block] */

%}

(* ****** ****** *)

fun fread_stdin_blocklst {sz:nat} (sz: int sz, tot: &int): blocklst = let
  fun loop {tot: addr} (
      pf_tot: !int @ tot | sz: int sz, p_tot: ptr tot, res: &blocklst? >> blocklst
    ) : void = let
    val (pf | p) = malloc_atm (sz)
    val n = fread_stdin_block (pf | sz, p); val () = !p_tot := !p_tot + n
(*
    val () = begin
      print "fread_stdin_blocklst: loop: tot = "; print !p_tot; print_newline ()
    end
*)
    val () = (res := blocklst_cons {0} (pf | sz, p, ?))
    val+ blocklst_cons (_ | _, _, !res1) = res
  in
    if n < sz then begin
      !res1 := blocklst_nil (); fold@ res
    end else begin
      loop (pf_tot | sz, p_tot, !res1); fold@ res
    end // end of [if]
  end // end of [loop]
  var res: blocklst; val () = loop (view@ tot | sz, &tot, res)
in
  res
end // end of [fread_stdin_blocklst]

(* ****** ****** *)

extern fun blocklst_concat_and_free
  {n:nat} (n: int n, blks: blocklst): [l:addr] @(bytes_v (n, l) | ptr l)
  = "blocklst_concat_and_free"

%{$

ats_ptr_type
blocklst_concat_and_free
  (ats_int_type tot, ats_ptr_type blks) {
  char *res0, *res, *p_blk ;
  int lft, sz ; blocklst_cons_pstruct blks_nxt ;

  if (blks) {
    blks_nxt = ((blocklst_cons_pstruct)blks)->atslab_2 ;
    if (!blks_nxt) { /* [blks] is singleton */
      p_blk = ((blocklst_cons_pstruct)blks)->atslab_1 ; ATS_FREE (blks) ;
      return p_blk ;
    }
  } /* end of [if] */

  lft = tot ; res0 = res = malloc_atm (tot) ;

  while (1) {
    if (!blks) break ;
    sz = ((blocklst_cons_pstruct)blks)->atslab_0 ;
    p_blk = ((blocklst_cons_pstruct)blks)->atslab_1 ;
    if (sz < lft) {
      memcpy (res, p_blk, sz) ;
    } else {
      memcpy (res, p_blk, lft) ; lft = 0 ; break ;
    }
    res += sz ; lft -= sz ;
    blks_nxt = ((blocklst_cons_pstruct)blks)->atslab_2 ;
    free_atm (p_blk) ; ATS_FREE (blks) ;
    blks = blks_nxt ;
  }

  if (lft != 0) {
    fprintf (stderr, "string_make_and_free_blocklst: lft = %i", lft);
    exit (1) ;
  }

  return res0 ;
} /* end of [blocklst_concat_and_free] */

%}

(* ****** ****** *)

%{$

ats_int_type count_pattern_match
  (ats_int_type nsrc, ats_ptr_type src, ats_ptr_type pat) {
  int count ;
  pcre *re; pcre_extra *re_ex ; const char *re_e ;
  int err, re_eo, m[3], pos ;

  re = pcre_compile
    ((char*)pat, PCRE_CASELESS, &re_e, &re_eo, NULL) ;
  if (!re) exit (1) ;
  re_ex = pcre_study (re, 0, &re_e);  

  for (count = 0, pos = 0 ; ; ) {
    err = pcre_exec (re, re_ex, (char*)src, nsrc, pos, 0, m, 3) ;
    if (err < 0) break ; count += 1 ; pos = m[1] ;
  } /* end of [for] */

  return count ;
} /* end of [count_pattern_match] */

%} // end of [%{$]

(* ****** ****** *)

extern
fun count_pattern_match
  {n:nat} {l:addr} (
  pf: !bytes_v (n, l) | n: int n, p: ptr l, pat: string
) : int = "count_pattern_match"

(* ****** ****** *)

#define variants_length 9
val variants = array_make_arrpsz{string}($arrpsz(
  "agggtaaa|tttaccct"
, "[cgt]gggtaaa|tttaccc[acg]"
, "a[act]ggtaaa|tttacc[agt]t"
, "ag[act]gtaaa|tttac[agt]ct"
, "agg[act]taaa|ttta[agt]cct"
, "aggg[acg]aaa|ttt[cgt]ccct"
, "agggt[cgt]aa|tt[acg]accct"
, "agggta[cgt]a|t[acg]taccct"
, "agggtaa[cgt]|[acg]ttaccct"
))

fun count_loop {i:nat} {n:nat} {l:addr}
  (pf: !bytes_v (n, l) | n: int n, p: ptr l, i: int i): void =
  if i < variants_length then let
    val pat = variants[i]
    val cnt = count_pattern_match (pf | n, p, pat)
    val () = begin
      print pat ; print ' '; print cnt ; print_newline ()
    end
  in
    count_loop (pf | n, p, i + 1)
  end // end of [if]

(* ****** ****** *)

datatype
seglst (int) =
  | {n:nat}
    seglst_cons (n+1) of (int(*beg*), int(*len*), seglst n)
  | seglst_nil (0)
// end of [seglst]

typedef seglst0 = seglst 0
typedef seglst = [n:nat] seglst (n)

extern
typedef "seglst_cons_pstruct" =
  seglst_cons_pstruct (int, int, seglst)

extern
fun seglst_cons_make (
  beg: int, len: int
) : seglst_cons_pstruct (int, int, seglst0?)
  = "seglst_cons_make"

implement
seglst_cons_make
  (beg, len) = seglst_cons {0} (beg, len, ?)
// end of [seglst_cons_make]

(* ****** ****** *)

extern typedef "int_ptr_type" = @(void | int, ptr)

%{$

ats_void_type subst_copy (
  char *dst
, char *src
, int nsrc
, seglst_cons_pstruct sgs
, char *sub
, int nsub
) {
//
  int ofs, beg, len ;
  seglst_cons_pstruct sgs_nxt ;
//
  ofs = 0 ;
//
  while (sgs) {
/*
    fprintf (stderr, "subst_copy: ofs = %i\n", ofs) ;
    fprintf (stderr, "subst_copy: beg = %i\n", beg) ;
*/
    beg = sgs->atslab_0 ;
    len = beg - ofs ; if (len < 0) {
      fprintf (stderr, "subst_copy: len = %i\n", len) ; exit (1) ;
    } /* end of [if] */
    memcpy (dst, src, len) ; dst += len ; src += len ; ofs = beg ;

    len = sgs->atslab_1 ;
/*
    fprintf (stderr, "subst_copy: len = %i\n", len) ;
*/
    memcpy (dst, sub, nsub) ; dst += nsub ; src += len ; ofs += len ;
    sgs_nxt = sgs->atslab_2 ; ATS_FREE (sgs); sgs = sgs_nxt ;
  }

  len = nsrc - ofs ; if (len < 0) {
    fprintf (stderr, "subst_copy: len = %i\n", len) ; exit (1) ;
  } /* end of [if] */
  memcpy (dst, src, len) ;
/*
  fprintf (stderr, "subst_copy: ofs = %i\n", ofs) ;
*/
  return ;
} /* end of [subst_copy] */

int_ptr_type subst_pattern_string (
  ats_int_type nsrc
, ats_ptr_type src
, ats_ptr_type pat
, ats_ptr_type sub
) {
  char *dst ; int ndst, nsub ; int beg, len, nxt ;
  pcre *re; pcre_extra *re_ex ; const char *re_e ;
  int err, re_eo, m[3], pos ;
  seglst_cons_pstruct sgs0, sgs, *sgs_ptr ;
  int_ptr_type ans ;

  ndst = nsrc ; nsub = strlen ((char*)sub) ;
/*
  fprintf (stderr, "subst_pattern_string: pat = %s\n", pat) ;
*/
  re = pcre_compile
    ((char*)pat, PCRE_CASELESS, &re_e, &re_eo, NULL) ;
  if (!re) exit (1) ;
  re_ex = pcre_study (re, 0, &re_e);  
  for (pos = 0, sgs_ptr = &sgs0 ; ; ) {
/*
    fprintf (stderr, "subst_pattern_string: nsrc = %i\n", nsrc) ;
*/
    err = pcre_exec
      (re, re_ex, (char*)src, nsrc, pos, 0, m, 3) ;
/*
    fprintf (stderr, "subst_pattern_string: err = %i\n", err) ;
*/
    if (err >= 0) {
      beg = m[0] ; pos = m[1] ;
      len = pos - beg ; ndst -= len ; ndst += nsub ;
      sgs = (seglst_cons_pstruct)seglst_cons_make (beg, len) ;
      *sgs_ptr = sgs ; sgs_ptr = (seglst_cons_pstruct*)&(sgs->atslab_2) ;
    } else {
     *sgs_ptr = (seglst_cons_pstruct)0 ; break ;
    }
  } // end of [for]

  dst = malloc_atm (ndst) ;
  ans.atslab_1 = ndst ; ans.atslab_2 = dst ;
  subst_copy (dst, src, nsrc, sgs0, sub, nsub) ;
  return ans ;
} /* end of [subst_pattern_string] */

%}

(* ****** ****** *)

extern
fun subst_pattern_string {n:nat} {l:addr}
  (pf: !bytes_v (n, l) | n: int n, p: ptr l, pat: string, sub: string)
  : [n:nat] [l:addr] @(bytes_v (n, l) | int n, ptr l)
  = "subst_pattern_string"

(* ****** ****** *)

#define subst_length 22
val subst = array_make_arrpsz{string}($arrpsz(
  "B", "(c|g|t)"
, "D", "(a|g|t)"
, "H", "(a|c|t)"
, "K", "(g|t)"
, "M", "(a|c)"
, "N", "(a|c|g|t)"
, "R", "(a|g)"
, "S", "(c|g)"
, "V", "(a|c|g)"
, "W", "(a|t)"
, "Y", "(c|t)"
)) // end of [val]

(* ****** ****** *)

fun subst_loop
  {i:nat} {n:nat} {l:addr} (
  pf: bytes_v (n, l) | n: int n, p: ptr l, i: int i
) : int =
  if i < subst_length - 1 then let
    val pat = subst[i]; val sub = subst[i+1]
    val (pf1 | n1, p1) = subst_pattern_string (pf | n, p, pat, sub)
    val () = free_atm (pf | p)
  in
    subst_loop (pf1 | n1, p1, i + 2)
  end else begin
    let val () = free_atm (pf | p) in n end
  end // end of [if]

(* ****** ****** *)

#define BLOCKSIZE 0x10000 // 0x4000000

implement main () = let
  var n0: int = 0
  val blks = fread_stdin_blocklst (BLOCKSIZE, n0)
(*
  val nblks = blocklst_length (blks)
*)
  val n0 = int1_of_int (n0); val () = assert (n0 >= 0)
  val (pf_bytes | p0) = blocklst_concat_and_free (n0, blks)
  val (pf1_bytes | n1, p1) =
    subst_pattern_string (pf_bytes | n0, p0, ">.*|\n", "")
  val () = free_atm (pf_bytes | p0)
  val () = count_loop (pf1_bytes | n1, p1, 0)
  val n_last = subst_loop (pf1_bytes | n1, p1, 0)

  val () = print_newline ()
  val () = (print n0; print_newline ())
  val () = (print n1; print_newline ())
  val () = (print n_last; print_newline ())
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [regex-dna.dats] *)

////

/*
** The Computer Language Shootout
** http://shootout.alioth.debian.org/
** contributed by Mike Pall
**
** regex-dna benchmark using PCRE
**
** compile with:
**   gcc -O3 -fomit-frame-pointer -o regexdna regexdna.c -lpcre
*/

#define __USE_STRING_INLINES
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <pcre.h>

typedef struct fbuf {
  char *buf;
  size_t size, len;
} fbuf_t;

static void fb_init(fbuf_t *b)
{
  b->buf = NULL;
  b->len = b->size = 0;
}

static char *fb_need(fbuf_t *b, size_t need)
{
  need += b->len;
  if (need > b->size) {
    if (b->size == 0) b->size = need;
    else while (need > b->size) b->size += b->size;
    if (!(b->buf = realloc(b->buf, b->size))) exit(1);
  }
  return b->buf+b->len;
}

#define FB_MINREAD (3<<16)

/* Read all of a stdio stream into dst buffer. */
static size_t fb_readall(fbuf_t *dst, FILE *fp)
{
  char *dp;
  int n;
  for (dp = fb_need(dst, FB_MINREAD);
       (n = fread(dp, 1, dst->size-dst->len, fp)) > 0;
       dp = fb_need(dst, FB_MINREAD)) dst->len += n;
  if (ferror(fp)) exit(1);
  return dst->len;
}

/* Substitute pattern p with replacement r, copying from src to dst buffer. */
static size_t fb_subst(fbuf_t *dst, fbuf_t *src, const char *p, const char *r)
{
  pcre *re;
  pcre_extra *re_ex;
  const char *re_e;
  char *dp;
  int re_eo, m[3], pos, rlen, clen;
  if (!(re = pcre_compile(p, PCRE_CASELESS, &re_e, &re_eo, NULL))) exit(1);
  re_ex = pcre_study(re, 0, &re_e);
  for (dst->len = 0, rlen = strlen(r), pos = 0;
       pcre_exec(re, re_ex, src->buf, src->len, pos, 0, m, 3) >= 0;
       pos = m[1]) {
    clen = m[0]-pos;
    dp = fb_need(dst, clen+rlen);
    dst->len += clen+rlen;
    memcpy(dp, src->buf+pos, clen);
    memcpy(dp+clen, r, rlen);
  }
  clen = src->len-pos;
  dp = fb_need(dst, clen);
  dst->len += clen;
  memcpy(dp, src->buf+pos, clen);
  return dst->len;
}

/* Count all matches with pattern p in src buffer. */
static int fb_countmatches(fbuf_t *src, const char *p)
{
  pcre *re;
  pcre_extra *re_ex;
  const char *re_e;
  int re_eo, m[3], pos, count;
  if (!(re = pcre_compile(p, PCRE_CASELESS, &re_e, &re_eo, NULL))) exit(1);
  re_ex = pcre_study(re, 0, &re_e);
  for (count = 0, pos = 0;
       pcre_exec(re, re_ex, src->buf, src->len, pos, 0, m, 3) >= 0;
       pos = m[1]) count++;
  return count;
}

static const char *variants[] = {
  "agggtaaa|tttaccct",         "[cgt]gggtaaa|tttaccc[acg]",
  "a[act]ggtaaa|tttacc[agt]t", "ag[act]gtaaa|tttac[agt]ct",
  "agg[act]taaa|ttta[agt]cct", "aggg[acg]aaa|ttt[cgt]ccct",
  "agggt[cgt]aa|tt[acg]accct", "agggta[cgt]a|t[acg]taccct",
  "agggtaa[cgt]|[acg]ttaccct", NULL
};

static const char *subst[] = {
  "B", "(c|g|t)", "D", "(a|g|t)",   "H", "(a|c|t)", "K", "(g|t)",
  "M", "(a|c)",   "N", "(a|c|g|t)", "R", "(a|g)",   "S", "(c|g)",
  "V", "(a|c|g)", "W", "(a|t)",     "Y", "(c|t)",   NULL
};

int main(int argc, char **argv)
{
  fbuf_t seq[2];
  const char **pp;
  size_t ilen, clen, slen;
  int flip;
  fb_init(&seq[0]);
  fb_init(&seq[1]);
  ilen = fb_readall(&seq[0], stdin);
  clen = fb_subst(&seq[1], &seq[0], ">.*|\n", "");
  for (pp = variants; *pp; pp++)
    printf("%s %d\n", *pp, fb_countmatches(&seq[1], *pp));
  for (slen = 0, flip = 1, pp = subst; *pp; pp += 2, flip = 1-flip)
    slen = fb_subst(&seq[1-flip], &seq[flip], *pp, pp[1]);
  printf("\n%zu\n%zu\n%zu\n", ilen, clen, slen);
  return 0;
}

////
