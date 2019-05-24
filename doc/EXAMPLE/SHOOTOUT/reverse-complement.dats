//
// reverse-complement.dats
//
// The Great Computer Language Shootout
// http://shootout.alioth.debian.org/
//
// by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

(*

N = 2,500,000
fasta 2500000 > fasta_output.txt

machine: dml.bu.edu
command: reverse-complement < fasta_output.txt > /dev/null

ATS:	3.443u 1.012s 0:27.15 16.3%	0+0k 0+0io 0pf+0w
C:	4.310u 1.448s 0:32.69 17.5%	0+0k 0+0io 0pf+0w

*)

staload "libc/SATS/stdio.sats"

%{^

ATSinline()
ats_void_type fasta_fputc
  (ats_char_type c, ats_ptr_type out) {
  fputc ((char)c, (FILE*)out) ; return ;
}

%}

extern fun fputc {m:file_mode}
  (pf: file_mode_lte (m, w) | c: char, out: &FILE m): void
  = "fasta_fputc"

extern fun buildIubComplement (): void = "buildIubComplement"
extern fun complement (b: byte): byte = "complement"

(* [reverse buf] reverse-complement the string [buf] in place. *)
fn reverse_buf {pos,bsz:nat | pos <= bsz} 
  (buf: &bytes bsz, pos: int pos): void = let
  fun rev {i:nat | i <= pos} .<pos-i>. (
      buf: &bytes bsz, i: int i, j: int (pos-i-1)
    ) :<cloptr1> void = begin
    if i < j then let
      val bufi = buf.[i]
    in
      buf.[i] := complement buf.[j]; buf.[j] := complement bufi;
      rev (buf, i+1, j-1)
    end // end of [if]
  end // end of [rev]
in
  rev (buf, 0, pos-1)
end // end of [reverse_buf]

#define BUFSZ 1024
#define WIDTH 60
#define LINE 128

extern
fun fwrite_buf {pos,len,bsz:nat | pos + len <= bsz} (
    buf: &bytes bsz, pos: int pos, len: int len, file: &FILE w
  ) : void = "fwrite_buf"

fn print_fasta {n,sz:nat | n <= sz}
  (buf: &bytes sz, n: int n): void = let
    fun pr {pos:nat | pos <= n}
      (file: &FILE w, buf: &bytes sz, pos: int pos, left: int (n-pos))
      :<cloptr1> void =
      if left > WIDTH then begin
        fwrite_buf (buf, pos, WIDTH, file);
        fputc (file_mode_lte_w_w | '\n', file);
        pr (file, buf, pos+WIDTH, left-WIDTH)
      end else begin
        fwrite_buf (buf, pos, left, file);
        fputc (file_mode_lte_w_w | '\n', file)
      end
    val (pf_stdout | stdout) = stdout_get ()
in
  pr (!stdout, buf, 0, n);
  stdout_view_set (pf_stdout | (*none*))
end // end of [print_fasta]

//

extern fun fread_buf_line
  {pos,len,bsz:nat | pos + len <= bsz}
  (buf: &bytes bsz, pos: int pos, len: int len, file: &FILE r)
  : [pos_new:int | pos <= pos_new; pos_new < pos+len] int pos_new
  = "fread_buf_line"

//

#define c2b byte_of_char

implement main (argc, argv) = let
//
fun loop
  {pos:nat}
  {bsz:int | bsz > 0}
  {l_buf:addr} (
  pf_gc: freebyte_gc_v (bsz, l_buf)
, pf_buf: bytes bsz @ l_buf
| inp: &FILE r
, p_buf: ptr l_buf
, bsz: int bsz
, pos: int pos
) : void = begin
  if pos + LINE <= bsz then let
    val pos_new = fread_buf_line (!p_buf, pos, LINE, inp)
  in
    if pos_new > pos then
      if p_buf->[pos] = c2b '>' then begin
        if pos > 0 then begin
          reverse_buf (!p_buf, pos); print_fasta (!p_buf, pos)
        end;

        let val (pf_stdout | stdout) = stdout_get () in
          fwrite_buf (!p_buf, pos, pos_new-pos, !stdout);
          fputc (file_mode_lte_w_w | '\n', !stdout);
          stdout_view_set (pf_stdout | (*none*))
        end;

        loop (pf_gc, pf_buf | inp, p_buf, bsz, 0)
      end else begin
        loop (pf_gc, pf_buf | inp, p_buf, bsz, pos_new)
      end
    else begin
      if pos > 0 then begin
        reverse_buf (!p_buf, pos);
        print_fasta (!p_buf, pos);
        free_gc (pf_gc, pf_buf | p_buf)
      end else begin
        free_gc (pf_gc, pf_buf | p_buf)
      end
    end
  end else let
    val bsz = bsz + bsz
    val (pf_gc, pf_buf | p_buf) =
      realloc_gc (pf_gc, pf_buf | p_buf, bsz) where {
      val bsz = size1_of_int1 bsz
    } // end of [val]
    prval () = pf_buf := bytes_v_of_b0ytes_v (pf_buf)
  in
    loop (pf_gc, pf_buf | inp, p_buf, bsz, pos)
  end // end of [if]
end // end of [loop]
//
val () = buildIubComplement ()
val (pf_stdin | stdin) = stdin_get ()
val (pf_gc, pf_buf | buf) = malloc_gc (BUFSZ)
prval () = pf_buf := bytes_v_of_b0ytes_v (pf_buf)
//
val () = loop (pf_gc, pf_buf | !stdin, buf, BUFSZ, 0)
val () = stdin_view_set (pf_stdin | (*none*))
//
in
  // nothing
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

static unsigned char iubComplement[1+UCHAR_MAX];

// I got a bit lazy; I copied code from the following C program
ATSinline()
ats_void_type
buildIubComplement () {
  int i;
  for (i=0; i <= UCHAR_MAX; i++) iubComplement[i] = (unsigned char) i;
  for (i=0; iubpairs[i][0] != '\0'; i++) {
    iubComplement[iubpairs[i][0]] = iubpairs[i][1];
    iubComplement[iubpairs[i][1]] = iubpairs[i][0];
    iubComplement[tolower (iubpairs[i][0])] = iubpairs[i][1];
    iubComplement[tolower (iubpairs[i][1])] = iubpairs[i][0];
  }
} // end of [buildIubComplement]

ATSinline()
ats_byte_type
complement (ats_byte_type b) { return iubComplement[b] ; }

ats_int_type
fread_buf_line
  (ats_ptr_type buf, ats_int_type pos, ats_int_type len, ats_ptr_type file)
{
  char *src;
  char *res;
  int n;

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
} // end of [fread_buf_line]

ats_void_type
fwrite_buf (
  ats_ptr_type buf, ats_int_type pos, ats_int_type len, ats_ptr_type file
) {
  int n;
  char *src ;
  src = (char *)buf + pos ;
  n = fwrite (src, 1, len, file);
  if (n < len) {
    ats_exit_errmsg (errno, "Exit: [fwrite_buf] failed.\n") ;
  }
  return ;
} // end of [fwrite_buf]

%} // end of [%{^]

////

(* reverse-complement.ml
 *
 * The Great Computer Language Shootout
 * http://shootout.alioth.debian.org/
 *
 * Contributed by Troestler Christophe
 *)


let complement =
  let cplt = Array.init 256 (fun i -> Char.chr i) in
  List.iter (fun (c1, c2) ->
	       cplt.(Char.code c1) <- c2;
	       cplt.(Char.code c2) <- c1;
	       cplt.(Char.code(Char.lowercase c1)) <- c2;
	       cplt.(Char.code(Char.lowercase c2)) <- c1;  )
    [ ('A','T'); ('C','G'); ('B','V'); ('D','H'); ('K','M'); ('R','Y') ];
  cplt

(* [reverse s] reverse-complement the string [s] in place. *)
let reverse s =
  let rec rev i j =
    if i < j then (
      let si = s.[i] in
      s.[i] <- complement.(Char.code s.[j]);
      s.[j] <- complement.(Char.code si);
      rev (i + 1) (j - 1)
    ) in
  rev 0 (String.length s - 1);
  s

let print_fasta =
  let rec print60 pos len dna =
    if len > 60 then (
      output stdout dna pos 60; print_string "\n";
      print60 (pos + 60) (len - 60) dna
    )
    else (output stdout dna pos len; print_string "\n") in
  fun dna -> print60 0 (String.length dna) dna


let () =
  let buf = Buffer.create 4096 in
  try while true do
    let line = input_line stdin in
    if String.length line > 0 && line.[0] = '>' then (
      if Buffer.length buf > 0 then print_fasta(reverse(Buffer.contents buf));
      Buffer.clear buf;
      print_endline line
    )
    else Buffer.add_string buf line
  done with End_of_file -> print_fasta(reverse(Buffer.contents buf))

////

#include <stdio.h>
#include <string.h>
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

static unsigned char iubComplement[1+UCHAR_MAX];

static void buildIubComplement (void) {
    int i;
    for (i=0; i <= UCHAR_MAX; i++) iubComplement[i] = (unsigned char) i;
    for (i=0; iubpairs[i][0] != '\0'; i++) {
    	iubComplement[iubpairs[i][0]] = iubpairs[i][1];
    	iubComplement[iubpairs[i][1]] = iubpairs[i][0];
    	iubComplement[tolower (iubpairs[i][0])] = iubpairs[i][1];
    	iubComplement[tolower (iubpairs[i][1])] = iubpairs[i][0];
    }
}

static void inPlaceReverse (unsigned char * strand, int len) {
    int i;
    for (i=0, len--; i < len; i++,len--) {
    	unsigned char c = strand[i];
    	strand[i] = iubComplement[strand[len]];
    	strand[len] = iubComplement[c];
    }
    if (i == len) strand[i] = iubComplement[strand[i]];
}

static void process (char * strand, int len) {
    char * s, c;

    inPlaceReverse ((unsigned char *) strand, len);
    s = strand;

    while (len > 60) {
    	c = s[60];
    	s[60] = '\0';
    	puts (s);
    	s[60] = c;
    	s += 60;
    	len -= 60;
    }

    s[len] = '\0';
    puts (s);
}

int main (int argc, char * argv[]) {
    static char buffer[1024];
    char * inp = (char *) malloc (129);
    int mlen = 128;
    int slen = 0;

    buildIubComplement ();

    while (NULL != fgets (buffer, 1023, stdin)) {
    	if (buffer[0] == '>') {
    	    if (slen > 0) {
    	    	process (inp, slen);
    	    	slen = 0;
    	    }
    	    printf ("%s", buffer);
    	} else {
    	    int l = strlen (buffer);
    	    while (l > 0 && !isalpha (buffer[l-1])) l--;
    	    while (slen + l > mlen) {
    	    	mlen += mlen;
    	    	inp = (char *) realloc (inp, mlen + 1);
    	    }

    	    memcpy (inp + slen, buffer, l);
    	    slen += l;
    	}
    }
    if (slen > 0) process (inp, slen);
    free (inp);
    return 0;
}
