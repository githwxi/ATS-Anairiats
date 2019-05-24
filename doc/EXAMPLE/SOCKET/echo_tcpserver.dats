(*
**
** An introductory example to UNIX socket programming in ATS
**
** The following code implements a server socket for echoing back
** each line it receives from a client.
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: November, 2008
**
*)

(* ****** ****** *)

staload "libc/SATS/signal.sats"
staload "libc/SATS/stdio.sats"
staload "libc/SATS/unistd.sats"
staload "libc/sys/SATS/types.sats"
staload "libc/sys/SATS/socket.sats"
staload "libc/sys/SATS/sockaddr.sats"
staload "libc/netinet/SATS/in.sats"
staload "libc/sys/SATS/socket_in.sats"
staload "libc/arpa/SATS/inet.sats"

(* ****** ****** *)

#define LISTENQ 5
#define MAXLINE 128
#define SERVPORT_DEFAULT 9877

(* ****** ****** *)

extern fun server_action {fd_c:int}
  (pfskt_c: !socket_v (fd_c, conn) | fd_c: int fd_c): void

implement server_action {fd_c} (pfskt_c | fd_c) = let
  #define M MAXLINE
  val b0 = byte_of_int (0)
  var !p_buf = @[byte][M](b0) // allocation on stack
  val () = loop (pfskt_c | !p_buf) where {
    fun loop
      (pfskt_c: !socket_v (fd_c, conn) | buf: &bytes M)
      :<cloref1> void = let
     val nread = socket_read_exn (pfskt_c | fd_c, buf, MAXLINE)
(*
     val nread = socket_read_loop_exn (pfskt_c, pf_buf | fd_c, p_buf, MAXLINE)
*)
   in
     if nread > 0 then let
       val () = socket_write_all_exn (pfskt_c | fd_c, buf, nread)
     in
       loop (pfskt_c | buf)
     end else begin
       // no more bytes // loop exits
     end // end of [if]
   end // end of [loop]
 } // end of [where]
in
  // empty
end // end of [server_action]

(* ****** ****** *)

extern fun server_loop {fd_s:int}
  (pfskt_s: !socket_v (fd_s, listen) | fd_s: int fd_s): void

implement server_loop {fd_s} (pfskt_s | fd_s) = let
  fun loop
    (pfskt_s: !socket_v (fd_s, listen) | fd_s: int fd_s)
    : void = let
    val [fd_c:int] (pfskt_c | fd_c) = accept_null_exn (pfskt_s | fd_s)
    val pid = fork_exn (); val ipid = int_of_pid (pid)
  in
    case+ 0 of
    | _ when ipid > 0 (* parent *) => let
        val () = socket_close_exn (pfskt_c | fd_c)
      in
        loop (pfskt_s | fd_s)
      end // end of [parent]
    | _ (* child: ipid = 0 *) => let
        val () = socket_close_exn (pfskt_s | fd_s)
        val () = server_action (pfskt_c | fd_c)
        val () = socket_close_exn (pfskt_c | fd_c)
        prval pf_io = unit_v ()
        val () = exit_main {void}
          {unit_v} {socket_v (fd_s, listen)} (pf_io | 0)
        prval () = pfskt_s := pf_io
      in
        // empty
      end // end of [child]
  end // end of [loop]
in
  loop (pfskt_s | fd_s)
end // end of [server_loop]

(* ****** ****** *)

%{^

#include <sys/wait.h>

static
ats_void_type
sig_chld (
  signum_t signum
) {
  pid_t pid ; int stat ;

  while (1) {
    pid = waitpid (-1, &stat, WNOHANG) ;
    if (pid > 0) {
      fprintf (stdout, "The child process %i terminated.\n", pid) ;
      continue ;
    } /* end of [if] */
    break ;
  } /* end of [while] */

  return ;
} /* sig_chld */

%} // end of [%{^]

(* ****** ****** *)

extern fun sig_chld (signum: signum_t):<fun> void = "sig_chld"

(* ****** ****** *)

implement main (argc, argv) = let
  val nport = (if argc > 1 then int_of argv.[1] else SERVPORT_DEFAULT): int
  val [fd_s:int] (pfskt_s | fd_s) = socket_family_type_exn (AF_INET, SOCK_STREAM)
  var servaddr: sockaddr_in_struct // uninitialized
  val servport = in_port_nbo_of_int (nport)
  val in4addr_any = in_addr_nbo_of_hbo (INADDR_ANY)
  val () = sockaddr_in_init (servaddr, AF_INET, in4addr_any, servport)
  val () = bind_in_exn (pfskt_s | fd_s, servaddr)
  val () = listen_exn (pfskt_s | fd_s, LISTENQ) 
  val sighandler = sighandler_of_fun (sig_chld)
  val _(*previous sighandler*) = signal (SIGCHLD, sighandler)
  val () = server_loop (pfskt_s | fd_s)
  val () = socket_close_exn (pfskt_s | fd_s)
in
  exit (0)
end // end of [main]

(* ****** ****** *)

(* end of [echo_tcpserver.dats] *)
