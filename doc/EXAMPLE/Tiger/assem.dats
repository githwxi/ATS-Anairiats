(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

//
// some extra effort is taken in coding so as to avoid
// generation of garbage as much as possible
//

(* ****** ****** *)

staload TL = "templab.sats"
typedef temp = $TL.temp_t
typedef templst = List (temp)
typedef label = $TL.label_t
typedef lablst = List (label)
typedef lablstopt = Option (lablst)

(* ****** ****** *)

staload "assem.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"
staload _(*anonymous*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

fn fprint_lablstopt
  (out: FILEref, olabs: lablstopt): void =
  case+ olabs of
  | Some labs => $TL.fprint_lablst (out, labs)
  | None () => ()
// end of [fprint_lablstopt]

implement fprint_instr (out, ins) = let
  macdef prstr (str) = fprint_string (out, ,(str))
in
  case+ ins of
  | INSTRoper (asm, src, dst, jump) => begin
      prstr "INSTRoper("; fprint_string (out, asm); prstr "): ";
      prstr "src=["; $TL.fprint_templst (out, src); prstr "]";
      prstr "; ";
      prstr "dst=["; $TL.fprint_templst (out, dst); prstr "]";
      prstr "; ";
      prstr "jump=["; fprint_lablstopt (out, jump); prstr "]"
    end // end of [INSTRoper]
  | INSTRlabel (asm, _) => begin
      prstr "INSTRlabel("; fprint_string (out, asm); prstr ")"
    end // end of [INSTRlabel]
  | INSTRmove (asm, src, dst) => begin
      prstr "INSTRmove("; fprint_string (out, asm); prstr "): ";
      prstr "src=["; $TL.fprint_temp (out, src); prstr "]";
      prstr "; ";
      prstr "dst=["; $TL.fprint_temp (out, dst); prstr "]";
    end // end of [INSTRmove]
end // end of [fprint_instr]

implement print_instr (ins) = fprint_instr (stdout_ref, ins)
implement prerr_instr (ins) = fprint_instr (stderr_ref, ins)

implement fprint_instrlst (out, inss) = let
  fun loop (out: FILEref, inss: instrlst): void =
    case+ inss of
    | list_cons (ins, inss) => begin
        fprint_instr (out, ins); fprint_newline (out); loop (out, inss)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
in
  loop (out, inss)
end // end of [fprint_instrlst]

implement print_instrlst (inss) = fprint_instrlst (stdout_ref, inss)
implement prerr_instrlst (inss) = fprint_instrlst (stderr_ref, inss)

(* ****** ****** *)

viewtypedef charlst_vt = List_vt char

extern fun string_make_list_vt_rev (cs: charlst_vt): string

%{^

static inline
ats_ptr_type string_alloc (ats_int_type n) {
  char *p = ATS_MALLOC (n+1) ; p[n] = '\000'; return p;
} // end of [string_alloc]

%}

implement
  string_make_list_vt_rev (cs) = loop (str, cs, n-1) where {
  fun loop {n,i:nat | i <= n} .<i>.
    (str: string n, cs: list_vt (char, i), i1: int (i-1)): string =
    case+ cs of
    | ~list_vt_cons (c, cs) => let
        val c = char1_of_char c; val () = assert (c <> '\000')
      in
        str[i1] := c; loop {n,i-1} (str, cs, i1-1)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => str
  // end of [loop]
  val n = list_vt_length (cs)
  val str = string_alloc (n) where {
    extern fun string_alloc {n:nat} (n: int n): string n = "string_alloc"
  } // end of [str]
} // end of [string_make_list_vt_rev]

(* ****** ****** *)

extern fun revapp_string_list_vt (str: string, cs: charlst_vt): charlst_vt

implement revapp_string_list_vt (str, cs) = loop (str, cs, 0) where {
  val str = string1_of_string (str)
  fun loop {m,n:nat} {i:nat | i <= m} .<m-i>.
    (str: string m, cs: list_vt (char, n), i: size_t i): list_vt (char, m+n-i) =
    if string_is_atend (str, i) then cs else
      loop (str, list_vt_cons (str[i], cs), i+1)
    // end of [if]
  // end of [loop]
} // end of [revapp_string]

(* ****** ****** *)

implement instr_format (tmpfmt, ins) = let
  #define c2i int_of_char; #define i2c char_of_int
(*
  val () = begin
    prerr "instr_format: ins = "; prerr_instr ins; prerr_newline ()
  end // end of [instr_format]
*)
  fn err (asm: string, res: charlst_vt): string = let
    val () = list_vt_free (res)
  in
    prerr "INTERNAL ERROR";
    prerr ": instr_format: illegal instruction: asm = "; prerr asm;
    prerr_newline ();
    exit {string} (1)
  end // end of [err1]
  
  fn* aux1 {n,i:nat | i <= n} .<n-i>. (
      asm: string n
    , src: templst, dst: templst, jump: lablstopt, i: size_t i
    , res: charlst_vt
    ) :<cloref1> string =
    if string_isnot_atend (asm, i) then let
      val c = asm[i]
    in
      if c <> '`' then let
        val res = list_vt_cons (c, res) in
        aux1 (asm, src, dst, jump, i+1, res)
      end else begin
        aux2 (asm, src, dst, jump, i+1, res)
      end // end of [if]
    end else begin
      string_make_list_vt_rev (res)
    end // end of [if]
  (* end of [aux1] *)

  and aux2 {n,i:nat | i <= n} .<n-i>. (
      asm: string n
    , src: templst, dst: templst, jump: lablstopt, i: size_t i
    , res: charlst_vt
    ) :<cloref1> string =
    if string_isnot_atend (asm, i) then let
      val c = asm[i]
    in
      case+ c of
      | 's' => aux3 (asm, src, dst, jump, c2i c, i+1, res)
      | 'd' => aux3 (asm, src, dst, jump, c2i c, i+1, res)
      | 'j' => aux3 (asm, src, dst, jump, c2i c, i+1, res)
      | '`' => let
          val res = list_vt_cons ('`', res) in aux1 (asm, src, dst, jump, i+1, res)
        end // end of [val]
      | _ => err (asm, res) // illegal instruction
    end else begin
      err (asm, res) // illegal instruction
    end // end of [if]
  (* end of [aux2] *)

  and aux3 {n,i:nat | i <= n} .<n-i>. (
      asm: string n
    , src: templst, dst: templst, jump: lablstopt, c: int, i: size_t i
    , res: charlst_vt  
    ) :<cloref1> string =
    if string_isnot_atend (asm, i) then let
      val c = i2c c; val c1 = asm[i]
    in
      if char_isdigit (c1) then let
        val ind = c1 - '0'
(*
        val () = begin
          prerr "instr_format: aux3: ind ="; prerr ind; prerr_newline ()
        end // end of [val]
*)
        val () = assert (ind >= 0)
      in
        case+ c of
        | 's' => let
            val otmp = list_nth_opt (src, ind)
          in
            case+ otmp of
            | ~Some_vt (tmp) => let
                val name = tmpfmt tmp
                val res = revapp_string_list_vt (name, res)
              in
                aux1 (asm, src, dst, jump, i+1, res)
              end // end of [Some_vt]
            | ~None_vt () => err (asm, res)
          end // end of ['s']
        | 'd' => let
            val otmp = list_nth_opt (dst, ind)
          in
            case+ otmp of
            | ~Some_vt (tmp) => let
                val name = tmpfmt tmp
                val res = revapp_string_list_vt (name, res)
              in
                aux1 (asm, src, dst, jump, i+1, res)
              end // end of [Some_vt]
            | ~None_vt () => err (asm, res)
          end // end of ['d']
        | _ (* 'j' *) => let
            val olab = (case+ jump of
              | Some labs => list_nth_opt (labs, ind)
              | None () => None_vt ()
            ) : Option_vt (label) // end of [val]
          in
            case+ olab of
            | ~Some_vt lab => let
                val name = $TL.label_name_get (lab)
                val res = revapp_string_list_vt (name, res)
              in
                aux1 (asm, src, dst, jump, i+1, res)
              end // end of [Some_vt]
            | ~None_vt () => err (asm, res)
          end // end of [_]
      end else begin
        err (asm, res) // illegal instruction
      end // end of [if]
    end else begin
      err (asm, res) // illegal instruction
    end // end of [if]
  (* end of [aux3] *)
in
  case+ ins of
  | INSTRoper (asm, src, dst, jump) => let
      val asm = string1_of_string asm 
      val res = list_vt_nil () in aux1 (asm, src, dst, jump, 0, res)
    end // end of [INSTRoper]
  | INSTRlabel (asm, _(*lab*)) => asm
  | INSTRmove (asm, src, dst) => let
      val asm = string1_of_string asm
      val src = '[src] and dst = '[dst] and jump = None ()
      val res = list_vt_nil () in aux1 (asm, src, dst, jump, 0, res)
    end // end of [INSTRmove]
end // end of [instr_format]

(* ****** ****** *)

implement instr_ismove (ins) =
  case+ ins of
  | INSTRoper _ => false
  | INSTRlabel _ => false
  | INSTRmove _ => true
// end of [instr_ismove]  

implement instr_uselst_get (ins) =
  case+ ins of
  | INSTRoper (_, src, _, _) => src
  | INSTRlabel _ => '[]
  | INSTRmove (_, src, _) => '[src]
// end of [instr_uselst_get]

implement instr_deflst_get (ins) =
  case+ ins of
  | INSTRoper (_, _, def, _) => def
  | INSTRlabel _ => '[]
  | INSTRmove (_, _, def) => '[def]
// end of [instr_deflst_get]

implement instr_jump_get (ins) = case+ ins of
  | INSTRoper (_, _, _, jump) => jump | _ => None ()
// end of [instr_jump_get]

(* ****** ****** *)

(* end of [assemb.dats] *)
