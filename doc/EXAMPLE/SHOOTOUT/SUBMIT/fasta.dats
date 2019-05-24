(*
** The Computer Language Shootout
** http://shootout.alioth.debian.org/
** 
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -O3 fasta.dats -msse2 -mfpmath=sse -o fasta
*)

staload "libc/SATS/stdio.sats"
staload "libc/SATS/stdlib.sats" // for [atoi]

%{^

static inline
ats_void_type fwrite_substring_exn
  (ats_ptr_type s, ats_int_type start, ats_int_type n, ats_ptr_type out)
{
  // locked/unlocked: no observable difference
  int res = fwrite_unlocked(((char*)s)+start, 1, n, (FILE*)out) ;
  if (res < n) ats_exit_errmsg (errno, "Exit: [fwrite] failed.\n") ;
  return ;
}

%}

#define USE_FLOAT_IS_ALLOWED 1 // if not, please change 1 to 0

#if USE_FLOAT_IS_ALLOWED // about 10% gain over using double
typedef float = float
#else
typedef float = double
#endif

extern typedef "float_t" = float

%{$

/* Random number generator (Shootout version) */

#define IM 139968
#define IM_recip (1 / (float)IM)
#define IA 3877
#define IC 29573

#undef IM_recip_is_allowed

// inline
float_t gen_random (float_t max) {
  static int state = 42 ;
#ifdef IM_recip_is_allowed
  return max * ((state = (state * IA + IC) % IM) * IM_recip) ;
#else
  return max * ((state = (state * IA + IC) % IM) / (float)IM) ;
#endif
}

%}

typedef amino = @{ c= char, p= float }

extern fun gen_random (max: float): float = "gen_random"

fn make_cumulative {n:nat} {l:addr}
  (pf: !(@[amino][n] @ l) | table: ptr l, n: size_t n): void = let
  fun loop (
      pf: !(@[amino][n] @ l)
    | table: ptr l, n: size_t n, i: natLte n, prob: float
  ) : void =
    if i < n then let
      val prob = prob + !table.[i].p
    in
      !table.[i].p := prob; loop (pf | table, n, i+1, prob)
    end
in
  loop (pf | table, n, 0, 0.0: float)
end // end of [make_cumulative]

#define WIDTH 60

extern fun fwrite_substring_exn
  {m,p,n:nat | p + n <= m} {l:addr}
  (s: string m, start: int p, n: int n, file: &FILE w): void
  = "fwrite_substring_exn"

%{$

// inline
ats_void_type fasta_fputc (ats_char_type c, ats_ptr_type out) {
  // locked/unlocked: no observable difference
  fputc_unlocked ((char)c, (FILE*)out) ; return ;
}

%}

extern fun fputc {m:file_mode}
  (pf: file_mode_lte (m, w) | c: char, out: &FILE m): void = "fasta_fputc"

fn repeat_fasta {len:nat}
  (file: &FILE w, s: string len, n: Nat): void = let
  val len = string1_length s; val len = int1_of_size1 (len)
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
  tbl: ptr l_tbl, sz: size_t sz, prob: float, i: int i): char =
  if i < sz then
    if prob >= !tbl.[i].p then random_char (pf_tbl | tbl, sz, prob, i+1)
    else !tbl.[i].c
  else begin
    exit_errmsg {char} (1, "Exit: [random_char] failed.\n")
  end

fun random_buf
  {sz:nat} {i,len,bsz:nat | i <= len; len <= bsz} {l_tbl,l_buf:addr}
  (pf_tbl: !(@[amino][sz] @ l_tbl), pf_buf: !(@[byte][bsz] @ l_buf) |
   tbl: ptr l_tbl, buf: ptr l_buf, sz: size_t sz, len: int len, i: int i)
  : void =
  if i < len then let
    val c = random_char (pf_tbl | tbl, sz, gen_random (1.0: float), 0)
    val () = buf[i] := byte_of_char c
  in
    random_buf (pf_tbl, pf_buf | tbl, buf, sz, len, i+1)
  end

//

fn ignore (x: int): void = ()

//

fn random_fasta {sz:nat} {l_tbl:addr}
  (pf_tbl: !(@[amino][sz] @ l_tbl) |
   file: &FILE w, tbl: ptr l_tbl, sz: size_t sz, n: Nat): void = let
  fun loop {n:nat} {l_buf:addr} .<n>.
    (pf_tbl: !(@[amino][sz] @ l_tbl), pf_buf: !(@[byte][WIDTH+1] @ l_buf) |
     file: &FILE w, p_buf: ptr l_buf, n: int n):<cloptr1> void =
    if (n > WIDTH) then let
      val () = random_buf (pf_tbl, pf_buf | tbl, p_buf, sz, WIDTH, 0)
      val W1 = size1_of_int1 (WIDTH+1)
      val _(*int*) = fwrite_byte (file_mode_lte_w_w | !p_buf, W1, file)
    in
      loop (pf_tbl, pf_buf | file, p_buf, n-WIDTH)
    end else let
      val () = random_buf (pf_tbl, pf_buf | tbl, p_buf, sz, n, 0)
      val n = size1_of_int1 n
      val _(*int*) = fwrite_byte (file_mode_lte_w_w | !p_buf, n, file)
      val () = fputc (file_mode_lte_w_w | '\n', file)
    in
      // empty
    end // end of [loop]
  val () = make_cumulative (pf_tbl | tbl, sz)
  val (pf_gc, pf_buf | p_buf) = malloc_gc (WIDTH1) where {
    val WIDTH1 = size1_of_int1 (WIDTH + 1)
  }
  prval pf_buf = bytes_v_of_b0ytes_v (pf_buf)
  val () = p_buf->[WIDTH] := byte_of_char '\n'
  val () = loop (pf_tbl, pf_buf | file, p_buf, n)
  val () = free_gc (pf_gc, pf_buf | p_buf)
in
  // empty
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
val n = atoi (s); val n = int1_of_int n
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
) // end of [val]

val @(pf_homo_gc, pf_homo | homo, homo_sz) = $arrpsz{amino}(
  @{c='a', p=0.3029549426680}
, @{c='c', p=0.1979883004921}
, @{c='g', p=0.1975473066391}
, @{c='t', p=0.3015094502008}
) // end of [val]

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
