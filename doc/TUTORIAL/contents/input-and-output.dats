//
// some code for illustrating how I/O is done in ATS
//

//
// How to compile:
//   atscc -o input-and-output -O3 input-and-output.dats

(* ****** ****** *)

staload UNSAFE = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "libc/SATS/stdio.sats"

(* ****** ****** *)

#define i2c char_of_int1

fn filecopy_exn {m1,m2:file_mode} (
    pf1: file_mode_lte (m1, r)
  , pf2: file_mode_lte (m2, w)
  | fil_s: &FILE m1, fil_d: &FILE m2
  ) : void = let
  fun loop
    (fil_s: &FILE m1, fil_d: &FILE m2): void = let
    val c = fgetc_err (pf1 | fil_s)
  in
    if c >= 0 then begin
      fputc_exn (pf2 | i2c c, fil_d); loop (fil_s, fil_d)
    end // end of [if]
  end // end of [loop]
in
  loop (fil_s, fil_d)
end // end of [filecopy_exn]

(* ****** ****** *)

fn filecopy_err {m1,m2:file_mode} (
    pf1: file_mode_lte (m1, r)
  , pf2: file_mode_lte (m2, w)
  | fil_s: &FILE m1, fil_d: &FILE m2
  ) : int = let
  fun loop
    (fil_s: &FILE m1, fil_d: &FILE m2): void = let
    val c = fgetc_err (pf1 | fil_s)
  in
    if c >= 0 then let
      val err = fputc_err (pf2 | i2c c, fil_d)
    in
      loop (fil_s, fil_d)
    end // end of [if]
  end // end of [loop]
  val () = loop (fil_s, fil_d)
in
  if ferror (fil_d) = 0 then ~1 else 0
end // end of [filecopy_err]

(* ****** ****** *)

// concatenation of a list of files
implement main {n} (argc, argv) = let
  val () = case+ argc of
  | 1 => let
      val (pf_stdin | p_stdin) = stdin_get ()
      val (pf_stdout | p_stdout) = stdout_get ()
      val _(*err*) = filecopy_err
        (file_mode_lte_r_r, file_mode_lte_w_w | !p_stdin, !p_stdout)
      val () = stdout_view_set (pf_stdout | (*none*))
      val () = stdin_view_set (pf_stdin | (*none*))
    in
      // empty
    end // end of [1]
  | _ (*argc >= 2*) => loop (argc, argv, 1) where {
      fun loop {i:nat | i <= n}
        (argc: int n, argv: &(@[string][n]), i: int i): void =
        if i < argc then let
          val name = argv.[i]
          val (pfopt | p_ifp) = fopen_err (name, file_mode_r)
          val name = $UNSAFE.castvwtp {string} (name)
        in
          if p_ifp > null then let
            prval Some_v (pf) = pfopt
            val (pf_stdout | p_stdout) = stdout_get ()
            val _(*err*) = filecopy_err
              (file_mode_lte_r_r, file_mode_lte_w_w | !p_ifp, !p_stdout)
            val () = stdout_view_set (pf_stdout | (*none*))
            val () = fclose_exn (pf | p_ifp)
          in
            loop (argc, argv, i+1)
          end else let
            prval None_v () = pfopt
            val () = prerrf ("%s: can't open [%s]\n", @(argv.[0], name))
          in
            exit {void} (1)
          end // end of [if]
        end // end of [if]
    } // end of [_]
  // end of [val]
  val (pf_stdout | p_stdout) = stdout_get ()
  val err = ferror (!p_stdout)
  val () = stdout_view_set (pf_stdout | (*none*))
in
  if (err <> 0) then begin
    prerrf ("%s: error writing stdout\n", @(argv.[0])); exit {void} (2)
  end else begin
    exit {void} (0) // exit normally
  end // end of [if]
end // end of [main]

(* ****** ****** *)

(* end of [input-and-output.dats] *)
