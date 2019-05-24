//
// file copying through the use of file descriptors
//

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: January, 2009

staload "libc/SATS/fcntl.sats"

(* ****** ****** *) 

extern
fun fildescopy
  {fd1,fd2:int} (
  pf1_fd: !fildes_v (fd1), pf2_fd: !fildes_v (fd2)
| fd1: int fd1, fd2: int fd2
) : int(*err*) = "fildescopy"
// end of [fildescopy]

(* ****** ****** *) 

#define BUFSZ 1024

implement fildescopy
  {fd1,fd2:int}
  (pf1_fd, pf2_fd | fd1, fd2) = let
  var !p_buf with pf_buf = @[byte][BUFSZ]()
  stadef l_buf = p_buf
  prval () = pf_buf := bytes_v_of_b0ytes_v (pf_buf)
  var err: int = 0
  fun loop (
      pf_buf: !bytes BUFSZ @ l_buf
    , pf1_fd: !fildes_v (fd1), pf2_fd: !fildes_v (fd2)
    | err: &int
    ) :<cloref1> void = let
    val nread = read_all_err (pf1_fd | fd1, !p_buf, BUFSZ)
(*
    val () = (print "fildescopy: nread = "; print nread; print_newline ())
*)
  in
    if nread >= 0 then
      if nread > 0 then let
        val nread1 = size1_of_ssize1 (nread)
        val nwrite = write_all_err (pf2_fd | fd2, !p_buf, nread1)
(*
        val () = (print "fildescopy: nwrite = "; print nwrite; print_newline ())
*)
      in
        if (nwrite = nread) then loop (pf_buf, pf1_fd, pf2_fd | err) else (err := 1)
      end else () // loop exits
    else (err := 1) // loop exits
  end // end of [loop]
in
  loop (pf_buf, pf1_fd, pf2_fd | err); err
end // end of [fildescopy]
  
(* ****** ****** *)

(* end of [fildescopy.dats] *)
