//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: March, 2011
//
(* ****** ****** *)

staload "libc/SATS/stdio.sats"

#define DEVICE "/dev/scull"
#define c2i int_of_char
#define i2c char_of_int

implement
main () = () where {
//
  val r = $extval (file_mode r, "\"r\"")
  val w = $extval (file_mode w, "\"w\"")
//
  val (pf_fil | p_fil) = fopen_exn (DEVICE, w)
  val () = fprintf (file_mode_lte_w_w | !p_fil, "Hello, world!\n", @())
  val () = fclose_exn (pf_fil | p_fil)
//
  val (pf_fil | p_fil) = fopen_exn (DEVICE, r)
  val (pf_out | p_out) = stdout_get ()
  val () = loop (!p_fil, !p_out) where {
    fun loop
      {l:addr} (
      fil1: &FILE (r), fil2: &FILE (w)
    ) : void = let
      val c = fgetc_err (file_mode_lte_r_r | fil1)
    in
      if (c >= 0) then
        (fputc_exn (file_mode_lte_w_w | (i2c)c, fil2); loop (fil1, fil2))
      else ()
    end // end of [loop]
  } // end of [val]
  val () = stdout_view_set (pf_out | (*none*))
  val () = fclose_exn (pf_fil | p_fil)  
//
} // end of [main]

(* ****** ****** *)

(* end of [test01.dats] *)
