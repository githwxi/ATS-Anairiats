(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -O3 k-nucleotide.dats -o k-nucleotide -D_ATS_GCATS
*)

(*

N = 1,000,000
fasta 1000000 > fasta_output.txt

machine: dml.bu.edu
command: k-nucleotide < fasta_output.txt

ATS(gc):	8.684u 0.189s 0:09.09 97.4%	0+0k 0+0io 0pf+0w
ATS(ngc):	8.723u 0.529s 0:10.18 90.7%	0+0k 0+0io 8pf+0w

// g++ -O3
C++:		9.951u 0.055s 0:10.24 97.6%	0+0k 0+0io 0pf+0w

// ocamlopt -unsafe -inline 3 -ccopt -O3
OCAML:		13.948u 0.101s 0:14.14 99.2%	0+0k 0+0io 0pf+0w

*)

(* ****** ****** *)

staload "libc/SATS/stdio.sats"

(* ****** ****** *)

// The hashtable implementation is based on linear-probing
#include "symtbl.dats"

(* ****** ****** *)

extern fun dna_count {n,k:nat | k <= n}
  (tbl: symtbl_t, n: int n, k: int k) : symtbl_t = "dna_count"

// a linear datatype
dataviewtype frqlst = FRQLSTnil | FRQLSTcons of (symbol_t, float, frqlst)

// linear append
fun frqlst_append
  (xs0: &frqlst >> frqlst, ys: frqlst): void = begin case xs0 of
  | FRQLSTcons (k, f, !xs) => (frqlst_append (!xs, ys); fold@ xs0)
  | ~FRQLSTnil () => (xs0 := ys)
end // end of [frqlst_append]

// quick sort
fun qsort (xs: frqlst): frqlst = begin case+ xs of
  | FRQLSTcons (!k1_r, !f1_r, !xs1_r) => let
      val k1 = !k1_r and f1 = !f1_r and xs1 = !xs1_r
    in
      partition (
        view@ (!k1_r), view@ (!f1_r), view@ (!xs1_r)
      | xs, xs1_r, k1, f1, xs1, FRQLSTnil (), FRQLSTnil ()
      ) // end of [partition]
    end
  | FRQLSTnil () => (fold@ xs; xs)
end // end of [qsort]

and partition {l00,l01,l1:addr}
  (pf00: symbol_t @ l00, pf01: float @ l01, pf1: frqlst? @ l1 |
   node: FRQLSTcons_unfold (l00, l01, l1), node1: ptr l1,
   k0: symbol_t, f0: float, xs: frqlst, l: frqlst, r: frqlst)
  : frqlst = begin case+ xs of
  | FRQLSTcons (k1, f1, !xs1_r) =>
    let val xs1 = !xs1_r in
      if compare (f1, f0) >= 0 then begin
        !xs1_r := l; fold@ xs;
        partition (pf00, pf01, pf1 | node, node1, k0, f0, xs1, xs, r)
      end else begin
        !xs1_r := r; fold@ xs;
        partition (pf00, pf01, pf1 | node, node1, k0, f0, xs1, l, xs)
      end
    end
  | ~FRQLSTnil () =>
    let var l = qsort l and r = qsort r in
      !node1 := r; fold@ node; frqlst_append (l, node); l
    end
end // end of [partition]

// print and free
fun print_frqlst
  (dna: dna_t, kfs: frqlst): void = begin case+ kfs of
  | ~FRQLSTcons (k, f, kfs) => begin
      print_symbol (dna, k); printf (" %.3f\n", @(double_of f));
      print_frqlst (dna, kfs)
    end
  | ~FRQLSTnil () => ()
end // end of [print_frqlst]

fn write_frequencies {n,k:nat | k <= n}
  (tbl: symtbl_t, n: int n, k: int k): void = let
  val tbl = dna_count (tbl, n, k)
  var total: int = (0: int)
  fn f (k: symbol_t, cnt: int, res: &int):<cloptr> void = (res := res + cnt)
  val () = symtbl_fold {int} (tbl, f, total)
  val ftotal = float_of total
  var frqs: frqlst = FRQLSTnil ()
  fn f (k: symbol_t, cnt: int, res: &frqlst):<cloptr> void =
    let val fval = (float_of 100) * float_of cnt / ftotal in
      res := FRQLSTcons (k, fval, res)
    end
  val () = symtbl_fold {frqlst} (tbl, f, frqs)
in
  print_frqlst (symtbl_dna tbl, qsort frqs)
end // end of [write_frequencies]

(* ****** ****** *)

fn write_count {n,k:nat}
  (tbl: symtbl_t, n: int n, seq: string k): void = let
  val k = string1_length seq; val k = int1_of_size1 k
  val () = assert (k <= n)
  val tbl = dna_count (tbl, n, k)
  val cnt = symtbl_search (tbl, seq)
in
  printf ("%d\t%s\n", @(cnt, seq))
end // end of [write_count]

(* ****** ****** *)

typedef string_int = [n:nat] (string n, int n)

extern fun getline (): string
extern fun getrest (): string_int

dataviewtype charlst (int) =
  | charlst_nil (0)
  | {n:nat} charlst_cons (n+1) of (char, charlst n)

#define nil charlst_nil
#define cons charlst_cons
#define :: charlst_cons

extern fun charlst_is_nil {n:nat} (cs: &charlst n): bool (n == 0) =
  "charlst_is_nil"

implement charlst_is_nil (cs) = case+ cs of
  | nil () => (fold@ cs; true) | cons (c, !cs_r) => (fold@ cs; false)

extern fun
charlst_uncons {n:pos} (cs: &charlst n >> charlst (n-1)): char =
  "charlst_uncons"

implement charlst_uncons (cs) =
  let val ~(c :: cs_r) = cs in cs := cs_r; c end

extern fun
string_make_charlst_int {n:nat} (cs: charlst n, n: int n): string n =
  "string_make_charlst_int"

#define i2c char_of_int

implement getline () = let
  fun loop {n:nat} (cs: charlst n, n: int n): string =
    let val i = getchar () in
      if i >= 0 then let
        val c = i2c i
      in
        if c <> '\n' then loop (charlst_cons (c, cs), n+1)
        else string_make_charlst_int (cs, n)
      end else begin
        string_make_charlst_int (cs, n)
      end
   end // end of [loop]
in
  loop (charlst_nil (), 0)
end // end of [getline]

implement getrest () = let
  fun loop {n:nat} (cs: charlst n, n: int n): string_int =
    let val i = getchar () in
      if i >= 0 then let
        val c = i2c i
      in
        if c <> '\n' then
          loop (charlst_cons (char_toupper c, cs), n+1)
        else loop (cs, n)
      end else begin
        @(string_make_charlst_int (cs, n), n)
      end
    end
in
  loop (charlst_nil (), 0)
end // end of [getrest]

(* ****** ****** *)

extern fun dna_of_string (s: string): dna_t = "dna_of_string"
extern fun is_three (s: string): bool = "is_three"

%{

ats_ptr_type dna_of_string (ats_string_type s) { return s ; }

ats_bool_type is_three (ats_ptr_type s0) {
  char *s = (char*) s0 ;

  if (*s != '>') return ats_false_bool ; ++s ;
  if (*s != 'T') return ats_false_bool ; ++s ;
  if (*s != 'H') return ats_false_bool ; ++s ;
  if (*s != 'R') return ats_false_bool ; ++s ;
  if (*s != 'E') return ats_false_bool ; ++s ;
  if (*s != 'E') return ats_false_bool ;
  return ats_true_bool ;
}

%}

implement main (argc, argv) = let

fun dna_three_get (): string_int = let
  val s = getline ()
in
  if s <> "" then
    if is_three (s) then getrest () else dna_three_get ()
  else begin
    exit_errmsg {string_int} (1, "[dna_three_get] failed.\n")
  end
end // end of [dna_three_get]

val () = gc_chunk_count_limit_max_set (~1) // infinite

val (dna_three, n) = dna_three_get ()
val dna_three = dna_of_string dna_three
val dna_table = symtbl_make (dna_three, 0x1000)
val () = assert (n >= 2)

in

write_frequencies (dna_table, n, 1) ;
print_newline () ;

write_frequencies (dna_table, n, 2) ;
print_newline () ;

write_count (dna_table, n, "GGT") ;
write_count (dna_table, n, "GGTA") ;
write_count (dna_table, n, "GGTATT") ;
write_count (dna_table, n, "GGTATTTTAATT") ;
write_count (dna_table, n, "GGTATTTTAATTTATAGT") ;

end

(* ****** ****** *)

%{$

ats_ptr_type
dna_count (ats_ptr_type tbl, ats_int_type n, ats_int_type k) {
  symbol_t sym ; int i, nk = n - k ;

  symtbl_clear (tbl) ;
  i = 0 ; 
  while (i <= nk) {
    ++i ; sym.beg = i ; sym.len= k ;
    symtbl_insert (tbl, sym, 0) ;
  }
  return tbl ;
}

ats_ptr_type
string_make_charlst_int (ats_ptr_type cs, const ats_int_type n) {
  char *s0, *s;
  s0 = ats_malloc_gc(n+1) ;
  s = s0 + n ; *s = '\0' ; --s ;
  while (!charlst_is_nil(&cs)) { *s = charlst_uncons(&cs) ; --s ; }
  return s0 ;
}

%}

(* ****** ****** *)

(* end of [k-nucleotide.dats] *)

////

(* knucleotide.ml
 *
 * The Great Computer Language Shootout
 * http://shootout.alioth.debian.org/
 *
 * Contributed by Troestler Christophe
 *)

module S = struct
  type t = string

  let size = 0x40000

  let equal (s1:string) s2 = (s1 = s2)

  let hash s =
    let h = ref 0 in
    for i = 0 to String.length s - 1 do h := !h * 5 + Char.code s.[i] done;
    !h
end

module H = Hashtbl.Make(S)

(* [counts k dna] fills and return the hashtable [count] of
   k-nucleotide keys and count values for a particular reading-frame
   of length [k] of the string [dna].  Keys point to mutable values
   for speed (to avoid looking twice the same key to reinsert the
   value). *)
let count = H.create S.size
let counts k dna =
  H.clear count;
  for i = 0 to String.length dna - k do
    let key = String.sub dna i k in
    try incr(H.find count key) with Not_found -> H.add count key (ref 1)
  done;
  count

(* [write_frequencies k dna] writes the frequencies for a
   reading-frame of length [k] sorted by descending frequency and then
   ascending k-nucleotide key. *)
let compare_freq ((k1:string),(f1:float)) (k2, f2) =
  if f1 > f2 then -1 else if f1 < f2 then 1 else compare k1 k2

let write_frequencies k dna =
  let cnt = counts k dna in
  let tot = float(H.fold (fun _ n t -> !n + t) cnt 0) in
  let frq = H.fold (fun k n l -> (k, 100. *. float !n /. tot) :: l) cnt [] in
  let frq = List.sort compare_freq frq in
  List.iter (fun (k,f) -> Printf.printf "%s %.3f\n" k f) frq;
  print_string "\n"

let write_count seq dna =
  let cnt = counts (String.length seq) dna in
  Printf.printf "%d\t%s\n" (try !(H.find cnt seq) with Not_found -> 0) seq

(* Extract DNA sequence "THREE" from stdin *)
let dna_three =
  let is_not_three s = try String.sub s 0 6 <> ">THREE" with _ -> true in
  while is_not_three(input_line stdin) do () done;
  let buf = Buffer.create 1000 in
  (* Skip possible comment *)
  (try while true do
     let line = input_line stdin in
     if line.[0] <> ';' then
       (Buffer.add_string buf (String.uppercase line); raise Exit)
   done with _ -> ());
  (* Read the DNA sequence *)
  (try while true do
       let line = input_line stdin in
       if line.[0] = '>' then raise End_of_file;
       Buffer.add_string buf (String.uppercase line)
   done with End_of_file -> ());
  Buffer.contents buf

let () = Gc.set { (Gc.get()) with Gc.minor_heap_size = 1024 * 2048 }

let () =
  List.iter (fun i -> write_frequencies i dna_three) [1; 2];
  List.iter (fun k -> write_count k dna_three)
    ["GGT"; "GGTA"; "GGTATT"; "GGTATTTTAATT"; "GGTATTTTAATTTATAGT"]

////

/* The Computer Language Shootout
   http://shootout.alioth.debian.org/

   Contributed by Josh Goldfoot
   to compile, use gcc -O3

   This revision uses "simple_hash.h," available from
   http://cvs.alioth.debian.org/cgi-bin/cvsweb.cgi/shootout/bench/Include/?cvsroot=shootout

*/
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <stdlib.h>
#include "../../Include/simple_hash.h"

long
hash_table_size (int fl, long buflen)
{
  long maxsize1, maxsize2;

  maxsize1 = buflen - fl;
  maxsize2 = 4;
  while (--fl > 0 && maxsize2 < maxsize1)
    maxsize2 = maxsize2 * 4;
  if (maxsize1 < maxsize2)
    return maxsize1;
  return maxsize2;
}

struct ht_ht *
generate_frequencies (int fl, char *buffer, long buflen)
{
  struct ht_ht *ht;
  char *reader;
  long i;
  char nulled;

  if (fl > buflen)
    return NULL;

  ht = ht_create (hash_table_size (fl, buflen));
  for (i = 0; i < buflen - fl + 1; i++)
    {
      reader = &(buffer[i]);
      nulled = reader[fl];
      reader[fl] = 0x00;
      ht_find_new (ht, reader)->val++;
      reader[fl] = nulled;
    }
  return ht;
}

typedef struct ssorter
{
  char *string;
  int num;
} sorter;

void
write_frequencies (int fl, char *buffer, long buflen)
{
  struct ht_ht *ht;
  long total, i, j, size;
  struct ht_node *nd;
  sorter *s;
  sorter tmp;

  ht = generate_frequencies (fl, buffer, buflen);
  total = 0;
  size = 0;
  for (nd = ht_first (ht); nd != NULL; nd = ht_next (ht))
    {
      total = total + nd->val;
      size++;
    }
  s = calloc (size, sizeof (sorter));
  i = 0;
  for (nd = ht_first (ht); nd != NULL; nd = ht_next (ht))
    {
      s[i].string = nd->key;
      s[i++].num = nd->val;
    }
  for (i = 0; i < size - 1; i++)
    for (j = i + 1; j < size; j++)
      if (s[i].num < s[j].num)
	{
	  memcpy (&tmp, &(s[i]), sizeof (sorter));
	  memcpy (&(s[i]), &(s[j]), sizeof (sorter));
	  memcpy (&(s[j]), &tmp, sizeof (sorter));
	}
  for (i = 0; i < size; i++)
    printf ("%s %.3f\n", s[i].string, 100 * (float) s[i].num / total);
  printf ("\n");
  ht_destroy (ht);
  free (s);
}

void
write_count (char *searchFor, char *buffer, long buflen)
{
  struct ht_ht *ht;

  ht = generate_frequencies (strlen (searchFor), buffer, buflen);
  printf ("%d\t%s\n", ht_find_new (ht, searchFor)->val, searchFor);
  ht_destroy (ht);
}

int
main ()
{
  char c;
  char *line, *buffer, *tmp, *x;
  int i, linelen, nothree;
  long buflen, seqlen;

  line = malloc (256);
  if (!line)
    return -1;
  seqlen = 0;
  nothree = 1;

  while (nothree && fgets (line, 255, stdin))
    if (line[0] == '>' && line[1] == 'T' && line[2] == 'H')
      nothree = 0;
  free (line);

  buflen = 10240;
  buffer = malloc (buflen + 1);
  if (!buffer)
    return -1;
  x = buffer;

  while (fgets (x, 255, stdin))
    {
      linelen = strlen (x);
      if (linelen)
	{
	  if (x[linelen - 1] == '\n')
	    linelen--;
	  c = x[0];
	  if (c == '>')
	    break;
	  else if (c != ';')
	    {
	      seqlen = seqlen + linelen;
	      if (seqlen + 512 >= buflen)
		{
		  buflen = buflen + 10240;
		  tmp = realloc (buffer, buflen + 1);
		  if (tmp == NULL)
		    return -1;
		  buffer = tmp;
		  x = &(buffer[seqlen]);
		}
	      else
		x = &(x[linelen]);
	      x[0] = 0;
	    }
	}
    }
  for (i = 0; i < seqlen; i++)
    buffer[i] = toupper (buffer[i]);
  write_frequencies (1, buffer, seqlen);
  write_frequencies (2, buffer, seqlen);
  write_count ("GGT", buffer, seqlen);
  write_count ("GGTA", buffer, seqlen);
  write_count ("GGTATT", buffer, seqlen);
  write_count ("GGTATTTTAATT", buffer, seqlen);
  write_count ("GGTATTTTAATTTATAGT", buffer, seqlen);
  free (buffer);
  return 0;
}

////

// The Computer Language Shootout
// http://shootout.alioth.debian.org/
// Contributed by Paul Kitchin

#include <algorithm>
#include <cctype>
#include <cstring>
#include <iomanip>
#include <iostream>
#include <iterator>
#include <set>
#include <vector>
#include <ctime>

template < std::size_t size >
struct hasher
{
   static std::size_t const length = size;
   static char const * string(char const * string)
   {
      static char string_[size + 1] = {0};
      std::strncpy(string_, string, size);
      return string_;
   }
   std::size_t hash(char const * string) const
   {
      std::size_t h = 0;
      for (std::size_t i = 0; i < size; ++i)
      {
         h = (h * 4) + ((string[i] & 0x6) / 2);
      }
      return h;
   }
   bool equal(char const * lhs, char const * rhs) const
   {
      return std::strncmp(lhs, rhs, size) == 0;
   }
};

template < typename key, typename value, typename hash_traits >
class hashtable
   :
   private hash_traits
{

   public:

      struct entry
      {
         entry()
            :
            key_(key()),
            value_(value()),
            next_(0)
         {
         }
         entry(key key_)
            :
            key_(key_),
            value_(value()),
            next_(0)
         {
         }
         bool operator<(entry const & entry) const
         {
            return value_ > entry.value_;
         }
         key key_;
         value value_;
         entry * next_;
      };

      hashtable(std::size_t size)
         :
         size_(power_of_two(size)),
         table_(size_)
      {
      }

      value & operator[](key lookup_key)
      {
         entry * node = &table_[hash(lookup_key) & (size_ - 1)];
         if (node->key_)
         {
            while (!equal(lookup_key, node->key_) && node->next_)
            {
               node = node->next_;
            }
            if (equal(lookup_key, node->key_))
            {
               return node->value_;
            }
            node->next_ = new entry(value());
            node = node->next_;
         }
         node->key_ = lookup_key;
         return node->value_;
      }

      typedef typename std::vector< entry >::const_iterator const_iterator;

      const_iterator begin() const
      {
         return table_.begin();
      }

      const_iterator end() const
      {
         return table_.end();
      }

   private:

      std::size_t power_of_two(std::size_t lower_bound)
      {
         for (std::size_t i = 4; i < 64 * 1024; i *= 2)
         {
            if (i >= lower_bound)
            {
               return i;
            }
         }
         return 1024 * 64;
      }

      std::size_t size_;
      std::vector< entry > table_;

};

template < typename hasher >
void write_frequencies(std::vector< char > const & input)
{
   std::size_t sum = input.size() + 1 - hasher::length;
   typedef hashtable< char const *, std::size_t, hasher > frequency_table;
   frequency_table frequencies(std::min< std::size_t >(1 << (hasher::length * 2), sum));
   for (unsigned int i = 0, i_end = input.size() + 1 - hasher::length; i != i_end; ++i)
   {
      ++frequencies[&input[i]];
   }
   std::set< typename frequency_table::entry > ordered_entries(frequencies.begin(), frequencies.end());
   for (typename std::set< typename frequency_table::entry >::const_iterator i = ordered_entries.begin(), i_end = ordered_entries.end(); i != i_end; ++i)
   {
      std::cout << hasher::string(i->key_) << ' ' << (sum ? double(100 * i->value_) / sum : 0.0) << '\n';
   }
   std::cout << '\n';
}

template < typename hasher >
void write_count(std::vector< char > const & input, char const * string)
{
   std::size_t sum = input.size() + 1 - hasher::length;
   typedef hashtable< char const *, std::size_t, hasher > frequency_table;
   frequency_table frequencies(std::min< std::size_t >(1 << std::min(30u, hasher::length * 2), sum));
   for (unsigned int i = 0, i_end = input.size() + 1 - hasher::length; i != i_end; ++i)
   {
      ++frequencies[&input[i]];
   }
   std::cout << frequencies[string] << '\t' << string << '\n';
}

char to_upper(char c)
{
   return char(std::toupper(c));
}

int main()
{
   std::vector< char > input;
   char buffer[4096];
   while (std::cin.getline(buffer, 4096) && std::strncmp(buffer, ">THREE", 6) != 0)
   {
   }
   while (std::cin.getline(buffer, 4096) && buffer[0] != '>')
   {
      if (buffer[0] != ';')
      {
         input.insert(input.end(), buffer, buffer + std::cin.gcount() - 1);
      }
   }
   std::transform(input.begin(), input.end(), input.begin(), to_upper);
   std::cout << std::setprecision(3) << std::setiosflags(std::ios::fixed);
   write_frequencies< hasher< 1 > >(input);
   write_frequencies< hasher< 2 > >(input);
   write_count< hasher< 3 > >(input, "GGT");
   write_count< hasher< 4 > >(input, "GGTA");
   write_count< hasher< 6 > >(input, "GGTATT");
   write_count< hasher< 12 > >(input, "GGTATTTTAATT");
   write_count< hasher< 18 > >(input, "GGTATTTTAATTTATAGT");
}
