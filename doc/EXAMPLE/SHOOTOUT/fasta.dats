(*
** The Computer Language Shootout
** http://shootout.alioth.debian.org/
** 
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -O3 fasta.dats -msse2 -mfpmath=sse -o fasta
*)

(*

machine: dml.bu.edu

command: fasta 25000000 > fasta_output.txt

w/msse
ATS:	20.919u 5.269s 0:31.75 82.4% 0+0k 0+0io 0pf+0w
C  :	21.723u 5.147s 0:29.92 89.7% 0+0k 0+0io 0pf+0w

wo/msse:
ATS: 	22.598u 5.110s 0:32.41 85.4% 0+0k 0+0io 0pf+0w
C  :	25.402u 5.418s 0:33.85 91.0% 0+0k 0+0io 0pf+0w

*)

staload "libc/SATS/stdio.sats"
staload "libc/SATS/stdlib.sats" // for [atoi]

%{^

static inline
ats_void_type fwrite_substring_exn
  (ats_ptr_type s, ats_int_type start, ats_int_type n, ats_ptr_type out)
{
  int res = fwrite(((char*)s)+start, 1, n, (FILE*)out) ;
  if (res < n) ats_exit_errmsg (errno, "Exit: [fwrite] failed.\n") ;
  return ;
}

/* Random number generator (Shootout version) */

#define IM 139968
#define IA 3877
#define IM_recip (1 / (double)IM)
#define IC 29573

#undef IM_recip_is_allowed

static inline
ats_double_type
gen_random (ats_double_type max) {
  static int state = 42 ;

#ifdef IM_recip_is_allowed
  return max * ((state = (state * IA + IC) % IM) * IM_recip) ;
#else
  return max * ((state = (state * IA + IC) % IM) / (double)IM) ;
#endif
}

%}

typedef amino = @{ c= char, p= double }

extern fun gen_random (max: double): double = "gen_random"

fn make_cumulative {n:nat} {l:addr}
  (pf: !(@[amino][n] @ l) | table: ptr l, n: int n): void = let
  fun loop (
      pf: !(@[amino][n] @ l)
    | table: ptr l, n: int n, i: natLte n, prob: double
  ) : void =
    if i < n then let
      val prob = prob + !table.[i].p
    in
      !table.[i].p := prob; loop (pf | table, n, i+1, prob)
    end
in
  loop (pf | table, n, 0, 0.0)
end // end of [make_cumulative]

#define WIDTH 60

extern fun fwrite_substring_exn
  {m,p,n:nat | p + n <= m} {l:addr}
  (s: string m, start: int p, n: int n, file: &FILE w): void
  = "fwrite_substring_exn"

%{^

static inline
ats_void_type fasta_fputc
  (ats_char_type c, ats_ptr_type out) {
  fputc ((char)c, (FILE*)out) ; return ;
}

%}

extern fun fputc {m:file_mode}
  (pf: file_mode_lte (m, w) | c: char, out: &FILE m): void = "fasta_fputc"

fn repeat_fasta {len:nat}
  (file: &FILE w, s: string len, n: Nat): void = let
  val len = string1_length s
  val len = int1_of_size1 (len)
  val () = assert (len >= WIDTH)
  fun loop {n,pos:nat | pos <= len}
    (file: &FILE w, n: int n, pos: int pos):<cloptr1> void =
    if n > WIDTH then let
      val left = len - pos
    in
      if left >= WIDTH then begin
        fwrite_substring_exn (s, pos, WIDTH, file);
        fputc (file_mode_lte_w_w | '\n', file);
        loop (file, n-WIDTH, pos+WIDTH)
      end else begin
        fwrite_substring_exn (s, pos, left, file);
	fwrite_substring_exn (s, 0, WIDTH-left, file);
        fputc (file_mode_lte_w_w | '\n', file);
	loop(file, n-WIDTH, WIDTH-left)
      end
    end else let
      val left = len - pos
    in
      if left >= n then begin
        fwrite_substring_exn (s, pos, n, file);
        fputc (file_mode_lte_w_w | '\n', file);
      end else begin
        fwrite_substring_exn (s, pos, left, file);
	fwrite_substring_exn (s, 0, n-left, file);
        fputc (file_mode_lte_w_w | '\n', file);
      end
    end
in
  loop (file, n, 0)
end // end of [repeat_fasta]

//

fun random_char {i,sz:nat | i <= sz} {l_tbl:addr}
  (pf_tbl: !(@[amino][sz] @ l_tbl) |
  tbl: ptr l_tbl, sz: int sz, prob: double, i: int i): char =
  if i < sz then
    if prob >= !tbl.[i].p then random_char (pf_tbl | tbl, sz, prob, i+1)
    else !tbl.[i].c
  else begin
    exit_errmsg {char} (1, "Exit: [random_char] failed.\n")
  end

fun random_buf
  {sz:nat} {i,len,bsz:nat | i <= len; len <= bsz} {l_tbl,l_buf:addr}
  (pf_tbl: !(@[amino][sz] @ l_tbl), pf_buf: !(@[byte][bsz] @ l_buf) |
   tbl: ptr l_tbl, buf: ptr l_buf, sz: int sz, len: int len, i: int i)
  : void =
  if i < len then let
    val c = random_char (pf_tbl | tbl, sz, gen_random 1.0, 0)
    val () = buf[i] := byte_of_char c
  in
    random_buf (pf_tbl, pf_buf | tbl, buf, sz, len, i+1)
  end

//

fn ignore (x: int): void = ()

//

fn random_fasta {sz:nat} {l_tbl:addr}
  (pf_tbl: !(@[amino][sz] @ l_tbl) |
   file: &FILE w, tbl: ptr l_tbl, sz: int sz, n: Nat): void = let
  fun loop {n:nat} {l_buf:addr} .<n>.
    (pf_tbl: !(@[amino][sz] @ l_tbl), pf_buf: !(@[byte][WIDTH+1] @ l_buf) |
     file: &FILE w, p_buf: ptr l_buf, n: int n):<cloptr1> void =
    if (n > WIDTH) then let
      val () = random_buf (pf_tbl, pf_buf | tbl, p_buf, sz, WIDTH, 0)
      val WIDTH1 = size1_of_int1 (WIDTH+1)
      val _ = fwrite_byte (file_mode_lte_w_w | !p_buf, WIDTH1, file)
    in
      loop (pf_tbl, pf_buf | file, p_buf, n-WIDTH)
    end else let
      val () = random_buf (pf_tbl, pf_buf | tbl, p_buf, sz, n, 0)
      val n = size1_of_int1 n
      val _ = fwrite_byte (file_mode_lte_w_w | !p_buf, n, file)
      val () = fputc (file_mode_lte_w_w | '\n', file)
    in
      // loop exits
    end // end of [if]
  // end of [loop]
  val () = make_cumulative (pf_tbl | tbl, sz)
  val WIDTH1 = size1_of_int1 (WIDTH+1)
  val (pf_gc, pf_buf | buf) = malloc_gc (WIDTH1)
  prval () = pf_buf := bytes_v_of_b0ytes_v (pf_buf)
  val () = buf[WIDTH] := byte_of_char '\n'
in
  loop (pf_tbl, pf_buf | file, buf, n); free_gc (pf_gc, pf_buf | buf)
end // end of [random_fasta]

//

val alu ="\
GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGG\
GAGGCCGAGGCGGGCGGATCACCTGAGGTCAGGAGTTCGAGA\
CCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAAT\
ACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCA\
GCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGG\
AGGCGGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCC\
AGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA"

//

implement main (argc, argv) = let

val () = assert (argc = 2)
val s = argv.[1]
val n = atoi (s)
val n = int1_of_int n
val () = assert (n >= 0)
val (pf_stdout | stdout) = stdout_get ()
val @(pf_gc, pf_iub | iub, iub_sz) = $arrpsz{amino}(
  @{c='a', p=0.27}
, @{c='c', p=0.12}
, @{c='g', p=0.12}
, @{c='t', p=0.27}
, @{c='B', p=0.02}
, @{c='D', p=0.02}
, @{c='H', p=0.02}
, @{c='K', p=0.02}
, @{c='M', p=0.02}
, @{c='N', p=0.02}
, @{c='R', p=0.02}
, @{c='S', p=0.02}
, @{c='V', p=0.02}
, @{c='W', p=0.02}
, @{c='Y', p=0.02}
) // end of [$arrsz]
val @(pf_homo_gc, pf_homo | homo, homo_sz) = $arrpsz{amino}(
  @{c='a', p=0.3029549426680}
, @{c='c', p=0.1979883004921}
, @{c='g', p=0.1975473066391}
, @{c='t', p=0.3015094502008}
) // end of [$arrsz]

val iub_sz = int1_of_size1 (iub_sz)
val homo_sz = int1_of_size1 (homo_sz)

in

fprint (file_mode_lte_w_w | !stdout, ">ONE Homo sapiens alu\n") ;
repeat_fasta (!stdout, alu, n * 2) ;
fprint (file_mode_lte_w_w | !stdout, ">TWO IUB ambiguity codes\n");
random_fasta (pf_iub | !stdout, iub, iub_sz, n * 3) ;
array_ptr_free {amino?} (pf_gc, pf_iub | iub) ;
fprint (file_mode_lte_w_w | !stdout, ">THREE Homo sapiens frequency\n");
random_fasta (pf_homo | !stdout, homo, homo_sz, n * 5) ;
array_ptr_free {amino?} (pf_homo_gc, pf_homo | homo) ;
stdout_view_set (pf_stdout | (*none*))

end

////

(* fasta.ml
 *
 * The Great Computer Language Shootout
 * http://shootout.alioth.debian.org/
 *
 * Contributed by Troestler Christophe
 *)

(* Random number generator (Shootout version) *)
let im = 139968
and ia = 3877
and ic = 29573

let last = ref 42 and inv_im = 1. /. float im
let gen_random  max =
  last := (!last * ia + ic) mod im;
  max *. float !last *. inv_im


let make_cumulative table =
  let prob = ref 0.0 in
  Array.map (fun (c, p) -> prob := !prob +. p; (c, !prob)) table

let rand_char cumul =
  let prob = gen_random 1.0 in
  let i = ref 0 in
  while prob >= snd cumul.(!i) do incr i done;
  fst cumul.(!i)


let width = 60

let make_random_fasta id desc table n =
  Printf.printf ">%s %s\n" id desc;
  let table = make_cumulative table in
  let line = String.make (width+1) '\n' in
  for i = 1 to n / width do
    for j = 0 to width - 1 do line.[j] <- rand_char table done;
    print_string line;
  done;
  let w = n mod width in
  if w > 0 then (
    for j = 1 to w do print_char(rand_char table); done;
    print_char '\n'
  )

(* [write s i0 l w] outputs [w] chars of [s.[0 .. l]], followed by a
   newline, starting with [s.[i0]] and considering the substring [s.[0
   .. l]] as a "circle".
   One assumes [0 <= i0 <= l <= String.length s].
   @return [i0] needed for subsequent writes.  *)
let rec write s i0 l w =
  let len = l - i0 in
  if w <= len then (output stdout s i0 w; print_char '\n'; i0 + w)
  else (output stdout s i0 len; write s 0 l (w - len))

let make_repeat_fasta id desc src n =
  Printf.printf ">%s %s\n" id desc;
  let l = String.length src
  and i0 = ref 0 in
  for i = 1 to n / width do
    i0 := write src !i0 l width;
  done;
  let w = n mod width in
  if w > 0 then ignore(write src !i0 l w)


let alu = "\
GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGG\
GAGGCCGAGGCGGGCGGATCACCTGAGGTCAGGAGTTCGAGA\
CCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAAT\
ACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCA\
GCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGG\
AGGCGGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCC\
AGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA"

let iub = [| ('a', 0.27);  ('c', 0.12);  ('g', 0.12);  ('t', 0.27);
	     ('B', 0.02);  ('D', 0.02);  ('H', 0.02);  ('K', 0.02);
	     ('M', 0.02);  ('N', 0.02);  ('R', 0.02);  ('S', 0.02);
	     ('V', 0.02);  ('W', 0.02);  ('Y', 0.02);  |]

let homosapiens = [| ('a', 0.3029549426680);    ('c', 0.1979883004921);
		     ('g', 0.1975473066391);    ('t', 0.3015094502008);  |]

let () =
  let n = try int_of_string(Array.get Sys.argv 1) with _ -> 1000 in
  make_repeat_fasta "ONE" "Homo sapiens alu" alu (n*2);
  make_random_fasta "TWO" "IUB ambiguity codes" iub (n*3);
  make_random_fasta "THREE" "Homo sapiens frequency" homosapiens (n*5)

////

/* The Computer Language Shootout
 * http://shootout.alioth.debian.org/
 * contributed by Joern Inge Vestgaarden
 * Compile with gcc -O3 -fomit-frame-pointer -march=pentium4 -mfpmath=sse -msse2 -o fasta fasta.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MIN(a,b) ((a) <= (b) ? (a) : (b))
#define LINE_LEN 60

#define IM 139968
#define IA   3877
#define IC  29573
int global_last = 42;
#define gen_random(max) (max*((global_last = (global_last * IA + IC) % IM) / ((float)(IM))))

struct aminoacids {
  float p;
  char c;
};

void make_cumulative (struct aminoacids * genelist, int count) {
    float cp = 0.0;
    int i;
    for (i=0; i < count; i++) {
        cp += genelist[i].p;
        genelist[i].p = cp;
    }
}

void repeat_fasta (const char *s, int n) {
  int len = strlen(s);
  int pos = 0;
  while (n > 0) {
    const int line = MIN(LINE_LEN, n);
    const int left = len-pos;
    n -= line;
    if (left >= line) {     /* Line not broken */
      fwrite(s+pos,1,line,stdout);
      putc('\n', stdout);
      pos += line;
    } else {                /* Line broken */
      fwrite(s+pos,1,left,stdout);
      pos = 0;
      fwrite(s,1,line-left,stdout);
      pos += line - left;
      putc('\n', stdout);
    }
  }
}

void random_fasta (struct aminoacids * genelist, int n) {
  char buf[LINE_LEN+1];
  char *s = NULL;
  struct aminoacids *a = genelist;
  float r;
  while (n > 0) {
    const int line = MIN(LINE_LEN, n);
    const char *end = (char *)buf + line;
    n -= line;
    s = buf;
    while (s < end) {
      r = gen_random(1.0);
      a = genelist;
      while (*((float *)a) < r) ++a; /* Linear search */
      *s++ = a->c;
    }
    *s = '\n';
    fwrite(buf, 1, line+1, stdout);
  }
}


/* Main -- define alphabets, make 3 fragments */

static struct aminoacids iub[] = {
    { 0.27, 'a' },
    { 0.12, 'c' },
    { 0.12, 'g' },
    { 0.27, 't' },
    { 0.02, 'B' },
    { 0.02, 'D' },
    { 0.02, 'H' },
    { 0.02, 'K' },
    { 0.02, 'M' },
    { 0.02, 'N' },
    { 0.02, 'R' },
    { 0.02, 'S' },
    { 0.02, 'V' },
    { 0.02, 'W' },
    { 0.02, 'Y' }
};

#define IUB_LEN (sizeof (iub) / sizeof (struct aminoacids))

static struct aminoacids homosapiens[] = {
    { 0.3029549426680, 'a' },
    { 0.1979883004921, 'c' },
    { 0.1975473066391, 'g' },
    { 0.3015094502008, 't' },
};

#define HOMOSAPIENS_LEN (sizeof (homosapiens) / sizeof (struct aminoacids))

static char * alu =
   "GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGG" \
   "GAGGCCGAGGCGGGCGGATCACCTGAGGTCAGGAGTTCGAGA" \
   "CCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAAT" \
   "ACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCA" \
   "GCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGG" \
   "AGGCGGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCC" \
   "AGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA";

int main (int argc, char * argv[]) {
    int n = 1000;
    if (argc > 1) sscanf (argv[1], "%d", &n);
    make_cumulative (iub, IUB_LEN);
    make_cumulative (homosapiens, HOMOSAPIENS_LEN);

    printf (">ONE Homo sapiens alu\n");
    repeat_fasta ( alu, n*2);
    printf (">TWO IUB ambiguity codes\n");
    random_fasta ( iub,   n*3);
    printf (">THREE Homo sapiens frequency\n");
    random_fasta ( homosapiens,  n*5);

    return 0;
}
