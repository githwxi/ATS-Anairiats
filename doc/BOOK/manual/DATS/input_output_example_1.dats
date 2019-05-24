staload "libc/SATS/stdio.sats"

#define i2c char_of_int

fn fcopy_exn
  (src: FILEref, dst: FILEref): void = let
  fun loop (src: FILEref, dst: FILEref): void = let
    val c = fgetc_err (src)
  in
    if c >= 0 then (fputc_exn (i2c c, dst); loop (src, dst))
  end
in
  loop (src, dst)
end // end of [fcopy_exn]

(* ****** ****** *)

// testing [fcopy_exn]

implement main (argc, argv) = let

val cmd = argv.[0]
val () = if (argc < 2) then exit_prerrf {void}
  (1, "Usage: %s [src] or %s [src] [dst]\n", @(cmd, cmd))
val () = assert (argc >= 2)

in

if argc > 2 then let
  val src = fopen_ref_exn (argv.[1], file_mode_r)
  val dst = fopen_ref_exn (argv.[2], file_mode_w)
in
  fcopy_exn (src, dst); fclose_exn (src); fclose_exn (dst)
end else let
  val src = fopen_ref_exn (argv.[1], file_mode_r)
in
  fcopy_exn (src, stdout_ref); fclose_exn src
end // end of [if]

end // end of [main]

(* ****** ****** *)

(* end of [input-and-output.dats] *)
