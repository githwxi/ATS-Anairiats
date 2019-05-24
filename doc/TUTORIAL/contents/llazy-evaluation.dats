//
// code used for illustration in llazy-evaluation.html
//

(* ****** ****** *)

staload "libc/SATS/stdio.sats"

(* ****** ****** *)

// making a lazy char stream out of a file handle
extern fun char_stream_make_file (fil: FILEref)
  :<1,~ref> stream (char)

implement char_stream_make_file (fil) = let
  val c = fgetc0_err (fil)
in
  if c <> EOF then let
    val c = char_of_int (c)
  in
    $delay (stream_cons (c, char_stream_make_file fil))
  end else begin
    let val () = fclose0_exn (fil) in $delay (stream_nil ()) end
  end // end of [if]
end // end of [char_stream_make_file]


(* ****** ****** *)

// making a linear lazy char stream out of a file handler
extern fun char_stream_vt_make_file {m:file_mode} {l:addr}
  (pf_mod: file_mode_lte (m, r), pf_fil: FILE m @ l | p_fil: ptr l)
  :<1,~ref> stream_vt (char)

implement char_stream_vt_make_file (pf_mod, pf_fil | p_fil) = let
  val c = fgetc1_err (pf_mod | !p_fil)
in
  if c >= 0 then let // c <> EOF
    val c = char_of_int (c)
  in
    $ldelay (
      stream_vt_cons (c, char_stream_vt_make_file (pf_mod, pf_fil | p_fil))
    , fclose1_exn (pf_fil | p_fil)
    ) // end of [$delay_vt]
  end else let
    val () = fclose1_exn (pf_fil | p_fil) in $ldelay (stream_vt_nil ())
  end // end of [if]
end // end of [char_stream_vt_make_file]

(* ****** ****** *)

(* end of [llazy-evaluation.dats] *)
