(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -O3 -fomit-frame-pointer reverse-complement.dats -o reverse-complement
*)

staload "libc/SATS/stdio.sats"

extern fun iub_comp (b: byte): byte = "iub_comp"
extern fun iub_comp_build (): void = "iub_comp_build"

viewdef bytes_v (n:int,l:addr) = bytes n @ l

(*
** [reverse buf] reverse-complement the string [buf] in place.
*)
fn reverse_buf {pos,bsz:nat | pos <= bsz} {l_buf:addr} 
  (pf: !bytes_v (bsz, l_buf) | buf: ptr l_buf, pos: int pos)
  : void = let
  fun rev {i:nat | i <= pos} .<pos-i>. (
      pf: !bytes_v (bsz, l_buf) | i: int i, j: int (pos-i-1)
    ) :<cloptr1> void = begin
      if i < j then let
        val bufi = buf[i]
      in
        buf[i] := iub_comp buf[j]; buf[j] := iub_comp bufi;
        rev (pf | i+1, j-1)
      end
  end // end of [rev]
in
  rev (pf | 0, pos-1)
end // end of [reverse_buf]

#define BUFSZ 1024
#define WIDTH 60
#define LINE 128

%{^

static inline
ats_void_type fasta_fputc
  (ats_char_type c, ats_ptr_type out) {
  fputc ((char)c, (FILE*)out) ; return ;
}

%}

extern
fun fwrite_buf {pos,len,bsz:nat | pos + len <= bsz} {l_buf:addr}
  (pf_buf: !bytes_v (bsz, l_buf) |
   buf: ptr l_buf, pos: int pos, len: int len, file: &FILE w)
  : void = "fwrite_buf"

extern fun fputc {m:file_mode}
  (pf: file_mode_lte (m, w) | c: char, out: &FILE m)
  : void = "fasta_fputc"

fn print_fasta {n,sz:nat | n <= sz} {l_buf:addr}
  (pf_buf: !bytes_v (sz, l_buf) | buf: ptr l_buf, n: int n): void = let
  fun pr {pos:nat | pos <= n}
    (pf_buf: !bytes_v (sz, l_buf) |
     file: &FILE w, pos: int pos, left: int (n-pos)):<cloptr1> void =
    if left > WIDTH then begin
      fwrite_buf (pf_buf | buf, pos, WIDTH, file);
      fputc (file_mode_lte_w_w | '\n', file);
      pr (pf_buf | file, pos+WIDTH, left-WIDTH)
    end else begin
      fwrite_buf (pf_buf | buf, pos, left, file);
      fputc (file_mode_lte_w_w | '\n', file)
    end
  val (pf_stdout | stdout) = stdout_get ()
in
  pr (pf_buf | !stdout, 0, n); stdout_view_set (pf_stdout | (*none*))
end // end of [print_fasta]

extern fun fread_buf_line
  {pos,len,bsz:nat | pos + len <= bsz} {l_buf:addr}
  (pf_buf: !bytes_v (bsz, l_buf) |
   buf: ptr l_buf, pos: int pos, len: int len, file: &FILE r)
  : [pos_new:int | pos <= pos_new; pos_new < pos+len] int pos_new
  = "fread_buf_line"

#define c2b byte_of_char

implement main (argc, argv) = let

fun loop
  {pos:nat}
  {bsz:int | bsz > 0}
  {l_buf:addr} (
  pf_gc: freebyte_gc_v (bsz, l_buf)
, pf_buf: bytes_v (bsz, l_buf)
| inp: &FILE r, buf: ptr l_buf, bsz: int bsz, pos: int pos
) : void = begin
  if pos + LINE <= bsz then let
    val pos_new = fread_buf_line (pf_buf | buf, pos, LINE, inp)
  in
    if pos_new > pos then
      if buf[pos] = c2b '>' then begin
        if pos > 0 then begin
          reverse_buf (pf_buf | buf, pos); print_fasta (pf_buf | buf, pos)
        end;

        let val (pf_stdout | stdout) = stdout_get () in
          fwrite_buf (pf_buf | buf, pos, pos_new-pos, !stdout);
          fputc (file_mode_lte_w_w | '\n', !stdout);
          stdout_view_set (pf_stdout | (*none*))
        end;

        loop (pf_gc, pf_buf | inp, buf, bsz, 0)
      end else begin
        loop (pf_gc, pf_buf | inp, buf, bsz, pos_new)
      end
    else begin
      if pos > 0 then begin
        reverse_buf (pf_buf | buf, pos);
        print_fasta (pf_buf | buf, pos);
        free_gc (pf_gc, pf_buf | buf)
      end else begin
        free_gc (pf_gc, pf_buf | buf)
      end
    end
  end else let
    val bsz = bsz + bsz
    val (pf_gc, pf_buf | buf) =
      realloc_gc (pf_gc, pf_buf | buf, bsz) where {
      val bsz = size1_of_int1 bsz
    } // end of [val]
    prval pf_buf = bytes_v_of_b0ytes_v pf_buf
  in
    loop (pf_gc, pf_buf | inp, buf, bsz, pos)
  end
end // end of [loop]

val () = iub_comp_build ()
val (pf_stdin | stdin) = stdin_get ()
val (pf_gc, pf_buf | buf) = malloc_gc (BUFSZ)
prval pf_buf = bytes_v_of_b0ytes_v pf_buf
val () = loop (pf_gc, pf_buf | !stdin, buf, BUFSZ, 0)
val () = stdin_view_set (pf_stdin | (*none*))

in
  // empty
end // end of [main]

//

%{^

#include <errno.h>
#include <limits.h>

static unsigned char iubpairs[][2] = {
    {    'A',    'T'    },
    {    'C',    'G'    },
    {    'B',    'V'    },
    {    'D',    'H'    },
    {    'K',    'M'    },
    {    'R',    'Y'    },
    {    '\0',   '\0'   }
};

static unsigned char _iub_comp[1+UCHAR_MAX];

static inline
ats_void_type iub_comp_build () {
  int i;
  for (i=0; i <= UCHAR_MAX; i++) {
    _iub_comp[i] = (unsigned char) i;
  }
  for (i=0; iubpairs[i][0] != '\0'; i++) {
    _iub_comp[iubpairs[i][0]] = iubpairs[i][1];
    _iub_comp[iubpairs[i][1]] = iubpairs[i][0];
    _iub_comp[tolower (iubpairs[i][0])] = iubpairs[i][1];
    _iub_comp[tolower (iubpairs[i][1])] = iubpairs[i][0];
  }
}

static inline
ats_byte_type
iub_comp (ats_byte_type b) { return _iub_comp[b] ; }

ats_int_type fread_buf_line
  (ats_ptr_type buf, ats_int_type pos, ats_int_type len, ats_ptr_type file)
{
  char *src, *res; int n;

  src = (char *)buf+pos ;
  res = fgets (src, (int)len, (FILE *)file) ;
  if (!res) {
    if (feof((FILE *)file)) return pos ;
    else {
      ats_exit_errmsg (errno, "Exit: [fread_buf_line] failed.\n") ;
    }
  }
  n = strlen (src) ;
  if (n>0) {
    return src[n-1] == '\n' ? (pos+n-1) : (pos+n) ;
  }
  return pos ;
}

ats_void_type fwrite_buf 
  (ats_ptr_type buf, ats_int_type pos, ats_int_type len, ats_ptr_type file)
{
  int n;
  char *src ;
  src = (char *)buf + pos ;
  n = fwrite (src, 1, len, file);
  if (n < len) {
    ats_exit_errmsg (errno, "Exit: [fwrite_buf] failed.\n") ;
  }
  return ;
}  

%}

(* ****** ****** *)

(* end of [reverse-complement.dats] *)
