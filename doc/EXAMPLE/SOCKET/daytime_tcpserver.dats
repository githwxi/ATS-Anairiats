(*
**
** An introductory example to BSD Unix socket programming in ATS
**
** The following code implements a server socket that responds to a request by
** sending out a string representation of the current time. This is a concurrent
** version (in contrast to an iterative version). The use of the function [fork]
** and the type assigned to it should serve as an interesting example for future
** reference.

** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: November, 2008
**
*)

(* ****** ****** *)

staload "libc/SATS/stdio.sats"
staload "libc/SATS/time.sats"
staload "libc/SATS/unistd.sats"
staload "libc/sys/SATS/socket.sats"
staload "libc/sys/SATS/sockaddr.sats"
staload "libc/netinet/SATS/in.sats"
staload "libc/sys/SATS/socket_in.sats"
staload "libc/arpa/SATS/inet.sats"

(* ****** ****** *)

#define LISTENQ 5 // a traditional value
#define TIME_SERVER_PORT 13000 // default value

(*
//
// HX-2008: some ideas:
//
absprop forkdup_p (v: view)
extern praxi forkdup_socket
  {fd:int} {st:status} (): forkdup_p (socket_v (fd, st))
extern praxi forkdup_pair {v1,v2:view}
 (pf1: forkdup_p (v1), pf2: forkdup_p (v2)): forkdup_p @(v1, v2) 
*)

implement main (argc, argv) = let
  val nport = (
    if argc > 1 then int_of argv.[1] else TIME_SERVER_PORT
  ) : int // end of [nport]
  val [fd_s:int] (pfskt_s | fd_s) = socket_family_type_exn (AF_INET, SOCK_STREAM)
  var servaddr: sockaddr_in_struct // uninitialized
  val servport = in_port_nbo_of_int (nport)
  val in4addr_any = in_addr_nbo_of_hbo (INADDR_ANY)
  val () = sockaddr_in_init (servaddr, AF_INET, in4addr_any, servport)
  val () = bind_in_exn (pfskt_s | fd_s, servaddr)
  val () = listen_exn (pfskt_s | fd_s, LISTENQ) 
  val () = loop (pfskt_s | fd_s) where {
    fun loop (
        pfskt_s: !socket_v (fd_s, listen) | fd_s: int fd_s
      ) : void = let
      val [fd_c:int] (pfskt_c | fd_c) = accept_null_exn (pfskt_s | fd_s)
      viewdef V = @(socket_v (fd_s, listen), socket_v (fd_c, conn))
      prval pf = @(pfskt_s, pfskt_c)
      val f_child = lam (pf: V | (*none*)): void =<cloptr1> let
        prval @(pfskt_s, pfskt_c) = pf
        val () = socket_close_exn (pfskt_s | fd_s)
        var ntick = time_get ()
//
        val [l:addr] (fpf_pstr | pstr) = ctime ntick // ctime is non-reentrant
        val () = assert (strptr_isnot_null(pstr))
        val () = () where {
          val str = __cast (pstr) where {
            extern castfn __cast {l>null} (x: !strptr l): string
          } // end of [val]
          val str = string1_of_string (str)
          val strlen = string1_length (str)
//
          extern castfn __cast {n:nat}
            (s: string n): [l:addr] (bytes n @ l, bytes n @ l -<lin,prf> void | ptr l)
          val (pf, fpf | p) = __cast (str)
          val _ = socket_write_all_exn (pfskt_c | fd_c, !p, strlen)
          prval () = fpf (pf)
//
          val () = socket_close_exn (pfskt_c | fd_c)
        } // end of [val]
        prval () = fpf_pstr (pstr)
//
      in
        // empty
      end // f_child
      val () = fork_exec_cloptr_exn {V} (pf | f_child)
      prval () = pfskt_s := pf.0
      prval () = pfskt_c := pf.1
      val () = socket_close_exn (pfskt_c | fd_c)
    in
      loop (pfskt_s | fd_s)
    end // end of [loop]
  } // end of [val]
  val () = socket_close_exn (pfskt_s | fd_s)
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [daytime_tcpserver.dats] *)
