//
// An 'echoing' server with preforked processes
//
// Author: Chris Double (chris.double AT double DOT co DOT nz)
//   with minor modification by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: May, 2010
//

(* ****** ****** *)
//
// How to compile:
//   atscc -o echo_preforking echo_preforking.dats
//
// How to test:
//   1: do './echo_preforking &'
//   2: do 'telnet localhost 5000' and input a line from the keyboard
//   3: do (2) as many times as you would like to
//   4: kill the process started by 'echo_preforking' or all of its children
//
(* ****** ****** *)

staload "libc/SATS/signal.sats"
staload "libc/SATS/stdio.sats"
staload "libc/SATS/stdlib.sats" // for EXIT_FAILURE
staload "libc/SATS/unistd.sats"
staload "libc/sys/SATS/wait.sats"
staload "libc/sys/SATS/types.sats"
staload "libc/sys/SATS/socket.sats"
staload "libc/sys/SATS/sockaddr.sats"
staload "libc/netinet/SATS/in.sats"
staload "libc/sys/SATS/socket_in.sats"
staload "libc/arpa/SATS/inet.sats"

(* ****** ****** *)

staload _ = "prelude/DATS/array.dats"

(* ****** ****** *)

macdef int = int_of_pid
fun fork_child {fd:int} (
  pf_sock: !socket_v (fd,listen) |
  fd: int fd
, f: (!socket_v (fd,listen) | int fd, pid_t) -<fun1> void
) : pid_t = let
  val pid = fork_exn()
in
  if (int)pid = 0 then begin
    f (pf_sock | fd, pid); exit(0); // this is the child
  end else pid
end // end of [fork_child]

extern fun fchild {fd:int}
  (pf_sock: !socket_v(fd,listen) | fd: int fd, pid: pid_t):<fun1> void
implement fchild {fd} (pf_sock | fd, pid) = let
  val (pf_client | client) = accept_null_exn (pf_sock | fd)
  val [l:addr] (pfopt | p_fil) = // [pf_client] gets absorbed into [pf_fil]
    socket_fdopen_err (pf_client | client, file_mode_rr)
  prval () = ptr_is_gtez (p_fil)
  val () =
//
if (p_fil = null) then let
  prval socket_fdopen_v_fail (pf) = pfopt
  val () = perror "socket_fdopen"
  val () = socket_close_exn (pf | client)
  val () = exit (EXIT_FAILURE)
in
  // nothing    
end else let // end of [val]
  prval socket_fdopen_v_succ (pf_fil) = pfopt
  val () = fprintf (file_mode_lte_rw_w | !p_fil, "Child %d echo> ", @((int)pid))
  val () = fflush_exn(file_mode_lte_rw_w | !p_fil)
  #define BUFSZ 1024
  var !p_buf with pf_buf = @[byte][BUFSZ]() // stack allocation
  val () = fgets_exn (file_mode_lte_rw_r, pf_buf | p_buf, BUFSZ, !p_fil)
  val () = fprintf (
    file_mode_lte_rw_w | !p_fil, "%s", @(__cast p_buf)
  ) where {
    extern castfn __cast (x: ptr): string // HX: cutting a corner to save time
  } // end of [val]
  // prval () = fpf_fil (pf_fil)
  prval () = pf_buf := bytes_v_of_strbuf_v (pf_buf)
  val () = fclose_exn (pf_fil | p_fil)
  // val () = socket_close_exn (pf_client_c | client) // HX: alreay closed at this point
in
  fchild (pf_sock | fd, pid)
end // end of [val]
//
in
  // nothing
end // end of [fchild]
fun make_server_socket (port: int)
  : [fd:int] (socket_v(fd,listen) | int fd) = let
  val (pf_sock_s | sockfd) = socket_family_type_exn (AF_INET, SOCK_STREAM);
  var servaddr: sockaddr_in_struct
  val servport = in_port_nbo_of_int (port);
  val in4addr = in_addr_nbo_of_hbo (INADDR_ANY);
  val () = sockaddr_in_init (servaddr, AF_INET, in4addr, servport);
  val () = bind_in_exn (pf_sock_s | sockfd, servaddr);
  val () = listen_exn (pf_sock_s | sockfd, 10);
in
  (pf_sock_s | sockfd)
end // end of [make_server_socket]

(* ****** ****** *)

implement main (argc, argv) = let
//
  var port: int = 5000 // default choice
  val () = if argc >= 2 then port := int_of (argv.[1])
  val [fd:int] (pf_sock_s | sockfd) = make_server_socket (port)
//  
  #define NCHILD 2
//
  viewdef V = socket_v(fd,listen)
  var !p_children with pf_children = @[pid_t][NCHILD]() // stack allocation
  var !p_clo = @lam ( // stack-allocated closure
    pf: !V | _: sizeLt NCHILD, x: &pid_t? >> pid_t
  ) : void =<clo> x := $effmask_all (fork_child (pf | sockfd, fchild))
  // end of [var]
  val () = array_ptr_initialize_vclo<pid_t>
    (pf_sock_s | !p_children, NCHILD, !p_clo)
//
  val () = array_ptr_foreach_fun<pid_t> (
    !p_children
  , lam (pid) =<fun> $effmask_all(printf("Forked: %d\n", @((int)pid)))
  , NCHILD
  ) // end of [val]
//
  var status:int = 0
  viewdef V = int @ status
  var !p_clo = @lam // stack-allocated closure
    (pf: !V | pid: &pid_t): void =<clo> let
    val _pid = $effmask_all (waitpid (pid, status, WNONE))
  in
    // nothing
  end // end of [var]
  val () = array_ptr_foreach_vclo<pid_t> {V} (view@ status | !p_children, !p_clo, NCHILD)
//
  val () = socket_close_exn(pf_sock_s | sockfd)
in
  // nothing
end // end of [main]

(* ****** ****** *)

(* end of [echo_preforking.dats] *)
