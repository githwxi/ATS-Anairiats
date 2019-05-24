(*
** some scripting code
*)

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list_vt.dats"
staload _(*anon*) = "prelude/DATS/pointer.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "contrib/scripting/SATS/scripting.sats"

staload _(*anon*) = "libats/DATS/hashtable_chain.dats"
staload _(*anon*) = "libats/DATS/linqueue_lst.dats"
staload _(*anon*) = "contrib/scripting/DATS/scripting.dats"

(* ****** ****** *)

typedef intlst = List (int)
typedef intlstref = ref (intlst)

fun readin (
  tbl: STRHASHMAPref (intlstref), inp: FILEref
) : void = let
  val line = input_line (inp)
in
  if stropt_is_some (line) then let
    val line = stropt_unsome (line)
(*
    val () = println! ("line = ", line)
*)
    val xs = string_split_string_list (line, "\s+")
  in
    readin2 (tbl, inp, xs)
  end else () // end of [if]
end // end of [readin]

and readin2 (
  tbl: STRHASHMAPref (intlstref)
, inp: FILEref, xs: List_vt strptr1
) : void =
  case+ xs of
  | ~list_vt_nil () => readin (tbl, inp)
  | _ => let
      val- ~list_vt_cons (name, xs) = xs
      val name = string_of_strptr (name)
      val- ~list_vt_cons (grade, xs) = xs
      val () = strptrlst_free (xs)
      val g = int_of_string ($UN.castvwtp1 {string} (grade))
      val () = strptr_free (grade)
(*
      val () = println! (name, ": ", g)
*)
      val ans = strhashmap_search (tbl, name)
      val () = (case+ ans of
        | ~Some_vt (r) => (!r := list_cons (g, !r))
        | ~None_vt () => begin
            strhashmap_insert (tbl, name, ref (list_cons (g, list_nil)))
          end (* end of [None_vt] *)
      ) : void // end of [val]
    in
      readin (tbl, inp)
    end // end of [_]
// end of [readin2]

(* ****** ****** *)

typedef keyitm = (string, intlstref)

fun avg (r: intlstref): double = let
  fun loop (xs: intlst, n: int, tot: int): double =
    case+ xs of
    | list_cons (x, xs) => loop (xs, n+1, tot + x)
    | list_nil () => (1.0 * tot) / n
  // end of [loop]
  val- list_cons (x, xs) = !r
in
  loop (xs, 1, x)
end // end of [avg]

fun eval (kis: List_vt (keyitm)): void =
  case+ kis of
  | ~list_vt_cons (ki, kis) => let
      val name = ki.0
      val grade = avg (ki.1)
      val () = fprintf (stdout_ref, "%s: %.2f\n", @(name, grade))
    in
      eval (kis)
    end // end of [list_vt_cons]
  | ~list_vt_nil () => ()
// end of [eval]

(* ****** ****** *)

dynload "libats/DATS/regexp.dats"
dynload "contrib/scripting/DATS/scripting.dats"

implement
main () = let
  val inp = open_file_exn ("data/grades.txt", file_mode_r)
  val tbl = strhashmap_make ()
  val () = readin (tbl, inp)
  val kis = strhashmap_listize (tbl)
  typedef keyitm = @(string, intlstref)
  var !p_clo = @lam (x1: &keyitm, x2: &keyitm): Sgn =<clo> compare (x1.0, x2.0)
  val kis = list_vt_mergesort<keyitm> (kis, !p_clo)
  val () = eval (kis)
  val () = close_file_exn (inp)
in
  // nothing
end // end of [main]

(* ****** ****** *)

(* end of [average.dats] *)
