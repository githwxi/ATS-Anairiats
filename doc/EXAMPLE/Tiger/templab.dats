(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload Sym = "symbol.sats"

(* ****** ****** *)

staload "templab.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

local

assume temp_t = int64

#define zro (int64_of_int 0)
#define one (int64_of_int 1)

val the_temp_base = int64_of_int (100)
val the_temp_count = ref_make_elt<int64> (the_temp_base)

in // in of [local]

implement temp_bogus = int64_of_int (~1)

implement temp_is_bogus (tmp) =
  if tmp < zro then true else false
// end of [temp_is_bogus]

implement temp_isnot_bogus (tmp) =
  if tmp >= zro then true else false
// end of [temp_isnot_bogus]

(* ****** ****** *)

implement temp_make_new () = let
  val n = !the_temp_count in !the_temp_count := n + one; n
end // end of [temp_make_new]

implement temp_make_fixed (n) = int64_of_int n

implement eq_temp_temp
  (tmp1, tmp2) = eq_int64_int64 (tmp1, tmp2)
// end of [eq_temp_temp]

implement compare_temp_temp
  (tmp1, tmp2) = compare_int64_int64 (tmp1, tmp2)
// end of [compare_temp_temp]

implement temp_is_fixed (tmp) =
  if tmp < the_temp_base then true else false
// end of [temp_is_special]

implement fprint_temp (out, tmp) = begin
  fprint_string (out, "tmp"); fprint_int64 (out, tmp)
end

end // end of [local]

implement print_temp tmp = fprint_temp (stdout_ref, tmp)
implement prerr_temp tmp = fprint_temp (stderr_ref, tmp)

implement fprint_templst (out, tmps) = let
  fun loop
    (out: FILEref, tmps: templst, i: int): void =
    case+ tmps of
    | list_cons (tmp, tmps) => begin
        if i > 0 then fprint_string (out, ", ");
        fprint_temp (out, tmp); loop (out, tmps, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
in
  loop (out, tmps, 0)
end // end of [fprint_templst]

implement print_templst tmps = fprint_templst (stdout_ref, tmps)
implement prerr_templst tmps = fprint_templst (stderr_ref, tmps)

(* ****** ****** *)

local

datatype label =
  LABint of int | LABname of string
// end of [label]

assume label_t = label

val the_label_count = ref_make_elt<int> (0)
val the_label_fun_count = ref_make_elt<int> (0)
val the_label_str_count = ref_make_elt<int> (0)

in

(* ****** ****** *)

implement label_make_new () = let
  val ind = !the_label_count
  val () = !the_label_count := ind + 1 in
  LABint ind
end // end of [label_make_new]

implement label_make_str_new () = let
  val ind = !the_label_str_count
  val () = !the_label_str_count := ind + 1
  val name = sprintf ("LC%i_TIGERATS", @(ind))
  val name = string_of_strptr (name)
in
  LABname (name)
end // end of [label_make_str_new]

implement label_make_fun_new (fsym) = let
  val ind = !the_label_fun_count
  val () = !the_label_fun_count := ind + 1
  val fnam = $Sym.symbol_name_get fsym
  val name = sprintf ("LF%i_TIGERATS_%s", @(ind, fnam))
  val name = string_of_strptr (name)
in
  LABname (name)
end // end of [label_make_fun_new]

implement label_make_name (name) = LABname (name)

(* ****** ****** *)

implement
label_name_get (lab) = case+ lab of
  | LABint ind => let
      val ptr = sprintf ("L%i_TIGERATS", @(ind)) in string_of_strptr (ptr)
    end // end of [LABint]
  | LABname name => name
// end of [label_name_get]

(* ****** ****** *)

implement eq_label_label (lab1, lab2) =
  case+ (lab1, lab2) of
  | (LABint i1, LABint i2) => eq_int_int (i1, i2)
  | (LABname s1, LABname s2) => eq_string_string (s1, s2)
  | (_, _) => false
// end of [eq_label_label]

implement compare_label_label (lab1, lab2) =
  case+ (lab1, lab2) of
  | (LABint i1, LABint i2) => compare_int_int (i1, i2)
  | (LABname s1, LABname s2) => compare_string_string (s1, s2)
  | (LABint _, LABname _) => ~1
  | (LABname _, LABint _) =>  1
// end of [compare_label_label]

(* ****** ****** *)

implement fprint_label (out, lab) =
  case+ lab of
  | LABint ind =>
      fprintf (out, "L%i_TIGERATS", @(ind))
    // end of [LABint]
  | LABname name => fprint_string (out, name)
// end of [fprint_label]

end // end of [local]

implement print_label lab = fprint_label (stdout_ref, lab)
implement prerr_label lab = fprint_label (stderr_ref, lab)

implement fprint_lablst (out, labs) = let
  fun loop
    (out: FILEref, labs: lablst, i: int): void =
    case+ labs of
    | list_cons (lab, labs) => begin
        if i > 0 then fprint_string (out, ", ");
        fprint_label (out, lab); loop (out, labs, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
in
  loop (out, labs, 0)
end // end of [fprint_lablst]

implement print_lablst labs = fprint_lablst (stdout_ref, labs)
implement prerr_lablst labs = fprint_lablst (stderr_ref, labs)

(* ****** ****** *)

implement tiger_chr = label_make_name ("tiger_chr")
implement tiger_flush = label_make_name ("tiger_flush")
implement tiger_getchar = label_make_name ("tiger_getchar")
implement tiger_ord = label_make_name ("tiger_ord")
implement tiger_print = label_make_name ("tiger_print")
implement tiger_print_int = label_make_name ("tiger_print_int")
implement tiger_size = label_make_name ("tiger_size")
implement tiger_substring = label_make_name ("tiger_substring")
implement tiger_concat = label_make_name ("tiger_concat")
implement tiger_not = label_make_name ("tiger_not")
implement tiger_exit = label_make_name ("tiger_exit")

implement tiger_main = label_make_name ("tiger_main")

implement tiger_array_alloc = label_make_name ("tiger_array_alloc")
implement tiger_array_make_elt = label_make_name ("tiger_array_make_elt")

implement tiger_eq_string_string = label_make_name ("tiger_eq_string_string")
implement tiger_neq_string_string = label_make_name ("tiger_neq_string_string")

(* ****** ****** *)

%{$

ats_uint_type
tigerats_hash_temp (ats_int64_type tmp) {
  uint64_t utmp = tmp ;
  ats_ulint_type hashval = 31415926UL ;
  while (utmp) {
    hashval = (hashval << 5) + hashval ;
    hashval += (utmp & 0xFF) ; utmp >>= 8 ;
  } /* end of [while] */
  return hashval ;
} /* end of [hash_temp] */

%}

(* ****** ****** *)

(* end of [templab.dats] *)
