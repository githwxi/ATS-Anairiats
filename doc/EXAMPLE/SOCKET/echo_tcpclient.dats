(*
**
** An introductory example to UNIX socket programming in ATS
**
** The following code implements a client socket for sending a line to
** a server that echos it back.
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: November, 2008
**
*)

(* ****** ****** *)

staload "libc/SATS/stdio.sats"
staload "libc/sys/SATS/socket.sats"
staload "libc/sys/SATS/sockaddr.sats"
staload "libc/netinet/SATS/in.sats"
staload "libc/sys/SATS/socket_in.sats"
staload "libc/arpa/SATS/inet.sats"

(* ****** ****** *)

#define MAXLINE 128
#define SERVPORT_DEFAULT 9877

fn prerr_usage (cmd: string): void = begin
  prerrf ("usage: %s <IPaddress>", @(cmd)); prerr_newline ()
end // end of [print_usage]

(* ****** ****** *)

extern fun client_loop {fd:int}
  (pfskt: !socket_v (fd, conn) | sockfd: int fd): void

(* ****** ****** *)

implement client_loop {fd:int} (pfskt | sockfd) = let
  #define M MAXLINE
  val b0 = byte_of_int (0)
  var !p_buf_send = @[byte][M](b0) // allocation on stack
  and !p_buf_recv = @[byte][M](b0) // allocation on stack
  fun loop {m:file_mode} {l_buf_send,l_buf_recv:addr} (
      pfskt: !socket_v (fd, conn)
    , pf_buf_send: !b0ytes M @ l_buf_send
    , pf_buf_recv: !bytes M @ l_buf_recv
    , pf_mod: file_mode_lte (m, r)
    | fil: &FILE m, p_buf_send: ptr l_buf_send, p_buf_recv: ptr l_buf_recv
    ) :<cloref1> void = let
    prval pf_buf_send0 = pf_buf_send
    val (pf_fgets | p) = fgets_err (pf_mod, pf_buf_send0 | p_buf_send, M, fil)
  in
    if p <> null then let
      prval fgets_v_succ (pf_buf_send1) = pf_fgets
      val nsend = strbuf_length (!p_buf_send)
      prval () = pf_buf_send := bytes_v_of_strbuf_v (pf_buf_send1)
      val () = socket_write_all_exn (pfskt | sockfd, !p_buf_send, nsend)
      val nread = socket_read_exn (pfskt | sockfd, !p_buf_recv, nsend)
      val (pf_stdout | p_stdout) = stdout_get ()
      val () = fwrite_byte_exn (file_mode_lte_w_w | !p_buf_recv, nread, !p_stdout)
      val () = stdout_view_set (pf_stdout | (*none*))
    in
      loop (pfskt, pf_buf_send, pf_buf_recv, pf_mod | fil, p_buf_send, p_buf_recv)
    end else let
      prval fgets_v_fail (pf_buf_send1) = pf_fgets
      prval () = pf_buf_send := pf_buf_send1
    in
      // loop exists
    end // end of [if]
  end // end of [loop]
  val (pf_stdin | p_stdin) = stdin_get ()
  val () = loop (
    pfskt, view@ !p_buf_send, view@ !p_buf_recv, file_mode_lte_r_r
  | !p_stdin, p_buf_send, p_buf_recv
  )
  val () = stdin_view_set (pf_stdin | (*none*))
in
  // empty
end // end of [client_loop]

(* ****** ****** *)

implement main (argc, argv) = let
  val () = if (argc < 2) then prerr_usage (argv.[0])
  val () = assert (argc >= 2) // redundant at run-time
  val servname = argv.[1]
  val servport = (
    if argc >= 3 then int_of argv.[2] else SERVPORT_DEFAULT
  ) : int
  var inp: in_addr_struct // uninitialized
  val () = inet_aton_exn (servname, inp)
  var servaddr: sockaddr_in_struct // uninitialized
  val () = sockaddr_in_init
    (servaddr, AF_INET, in_addr_struct_get_s_addr inp, in_port_nbo_of_int servport)
  val [fd:int] (pfskt | sockfd) = socket_family_type_exn (AF_INET, SOCK_STREAM)
  val () = connect_in_exn (pfskt | sockfd, servaddr)
  val () = client_loop (pfskt | sockfd)
  val () = socket_close_exn (pfskt | sockfd)
in
  exit (0) // normal exit
end // end of [main]

(* ****** ****** *)

(* end of [echo_tcpclient.dats] *)
