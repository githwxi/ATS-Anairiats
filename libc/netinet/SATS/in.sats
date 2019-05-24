(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Power of Types!
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)  *)

(* ****** ****** *)

%{#
#include "libc/netinet/CATS/in.cats"
%} // end of [%{#]

(* ****** ****** *)

staload SA = "libc/sys/SATS/sockaddr.sats"
typedef sa_family_t = $SA.sa_family_t
stadef socklen_t = $SA.socklen_t // int: length of a sockaddr
stadef sockaddr_struct = $SA.sockaddr_struct

(* ****** ****** *)

abst@ype ipproto_t = int
macdef IPPROTO_IP = $extval (ipproto_t, "IPPROTO_IP")
macdef IPPROTO_HOPOPTS = $extval (ipproto_t, "IPPROTO_HOPOPTS")
macdef IPPROTO_ICMP = $extval (ipproto_t, "IPPROTO_ICMP")
macdef IPPROTO_IGMP = $extval (ipproto_t, "IPPROTO_IGMP")
macdef IPPROTO_IPIP = $extval (ipproto_t, "IPPROTO_IPIP")
macdef IPPROTO_TCP = $extval (ipproto_t, "IPPROTO_TCP")
macdef IPPROTO_EGP = $extval (ipproto_t, "IPPROTO_EGP")
macdef IPPROTO_PUP = $extval (ipproto_t, "IPPROTO_PUP")
macdef IPPROTO_UDP = $extval (ipproto_t, "IPPROTO_UDP")
macdef IPPROTO_IDP = $extval (ipproto_t, "IPPROTO_IDP")
macdef IPPROTO_TP = $extval (ipproto_t, "IPPROTO_TP")
macdef IPPROTO_DCCP = $extval (ipproto_t, "IPPROTO_DCCP")
macdef IPPROTO_IPV6 = $extval (ipproto_t, "IPPROTO_IPV6")
macdef IPPROTO_ROUTING = $extval (ipproto_t, "IPPROTO_ROUTING")
macdef IPPROTO_FRAGMENT = $extval (ipproto_t, "IPPROTO_FRAGMENT")
macdef IPPROTO_RSVP = $extval (ipproto_t, "IPPROTO_RSVP")
macdef IPPROTO_GRE = $extval (ipproto_t, "IPPROTO_GRE")
macdef IPPROTO_ESP = $extval (ipproto_t, "IPPROTO_ESP")
macdef IPPROTO_AH = $extval (ipproto_t, "IPPROTO_AH")
macdef IPPROTO_ICMPV6 = $extval (ipproto_t, "IPPROTO_ICMPV6")
macdef IPPROTO_NONE = $extval (ipproto_t, "IPPROTO_NONE")
macdef IPPROTO_DSTOPTS = $extval (ipproto_t, "IPPROTO_DSTOPTS")
macdef IPPROTO_MTP = $extval (ipproto_t, "IPPROTO_MTP")
macdef IPPROTO_ENCAP = $extval (ipproto_t, "IPPROTO_ENCAP")
macdef IPPROTO_PIM = $extval (ipproto_t, "IPPROTO_PIM")
macdef IPPROTO_COMP = $extval (ipproto_t, "IPPROTO_COMP")
macdef IPPROTO_SCTP = $extval (ipproto_t, "IPPROTO_SCTP")
macdef IPPROTO_UDPLITE = $extval (ipproto_t, "IPPROTO_UDPLITE")
macdef IPPROTO_RAW = $extval (ipproto_t, "IPPROTO_RAW")
macdef IPPROTO_MAX = $extval (ipproto_t, "IPPROTO_MAX")

(* ****** ****** *)

abst@ype in_port_t = $extype"in_port_t"
macdef IPPORT_ECHO = $extval (in_port_t, "IPPORT_ECHO")
macdef IPPORT_DISCARD = $extval (in_port_t, "IPPORT_DISCARD")
macdef IPPORT_SYSTAT = $extval (in_port_t, "IPPORT_SYSTAT")
macdef IPPORT_DAYTIME = $extval (in_port_t, "IPPORT_DAYTIME")
macdef IPPORT_NETSTAT = $extval (in_port_t, "IPPORT_NETSTAT")
macdef IPPORT_FTP = $extval (in_port_t, "IPPORT_FTP")
macdef IPPORT_TELNET = $extval (in_port_t, "IPPORT_TELNET")
macdef IPPORT_SMTP = $extval (in_port_t, "IPPORT_SMTP")
macdef IPPORT_TIMESERVER = $extval (in_port_t, "IPPORT_TIMESERVER")
macdef IPPORT_NAMESERVER = $extval (in_port_t, "IPPORT_NAMESERVER")
macdef IPPORT_WHOIS = $extval (in_port_t, "IPPORT_WHOIS")
macdef IPPORT_MTP = $extval (in_port_t, "IPPORT_MTP")
macdef IPPORT_TFTP = $extval (in_port_t, "IPPORT_TFTP")
macdef IPPORT_RJE = $extval (in_port_t, "IPPORT_RJE")
macdef IPPORT_FINGER = $extval (in_port_t, "IPPORT_FINGER")
macdef IPPORT_TTYLINK = $extval (in_port_t, "IPPORT_TTYLINK")
macdef IPPORT_SUPDUP = $extval (in_port_t, "IPPORT_SUPDUP")
macdef IPPORT_EXECSERVER = $extval (in_port_t, "IPPORT_EXECSERVER")
macdef IPPORT_LOGINSERVER = $extval (in_port_t, "IPPORT_LOGINSERVER")
macdef IPPORT_CMDSERVER = $extval (in_port_t, "IPPORT_CMDSERVER")
macdef IPPORT_EFSSERVER = $extval (in_port_t, "IPPORT_EFSSERVER")
macdef IPPORT_BIFFUDP = $extval (in_port_t, "IPPORT_BIFFUDP")
macdef IPPORT_WHOSERVER = $extval (in_port_t, "IPPORT_WHOSERVER")
macdef IPPORT_ROUTESERVER = $extval (in_port_t, "IPPORT_ROUTESERVER")
macdef IPPORT_RESERVED = $extval (in_port_t, "IPPORT_RESERVED")
macdef IPPORT_USERRESERVED = $extval (in_port_t, "IPPORT_USERRESERVED")

(* ****** ****** *)

(*
macdef INET_ADDRSTRLEN = 16 // for IPv4 dotted-decimal string
macdef INET6_ADDRSTRLEN = 46 // for IPv6 hex string
*)

(* ****** ****** *)

symintr in_port_nbo_of
abst@ype in_port_nbo_t = $extype"in_port_t"
castfn in_port_nbo_of_in_port (n: in_port_t): in_port_nbo_t
overload in_port_nbo_of with in_port_nbo_of_in_port
fun in_port_nbo_of_int
  (n: int): in_port_nbo_t = "atslib_in_port_nbo_of_int"
overload in_port_nbo_of with in_port_nbo_of_int

(* ****** ****** *)

(*
abst@ype in_addr_t = $extype"in_addr_t"
*)
abst@ype in_addr_hbo_t = $extype "in_addr_t"
abst@ype in_addr_nbo_t = $extype "in_addr_t"

(* ****** ****** *)

fun in_addr_nbo_of_hbo
  (n: in_addr_hbo_t): in_addr_nbo_t = "atslib_in_addr_nbo_of_hbo"
// end of [in_addr_nbo_of_hbo]

(* constant addresses in host-byte-order *)

// Address to accept any incoming messages: 0x00000000
macdef INADDR_ANY = $extval (in_addr_hbo_t, "INADDR_ANY")

// Address to send to all hosts: 0xffffffff
macdef INADDR_BROADCAST	= $extval (in_addr_hbo_t, "INADDR_BROADCAST")

// Address indicating an error return: 0xffffffff
macdef INADDR_NONE = $extval (in_addr_hbo_t, "INADDR_NONE")

// Network number for local host loopback
#define	IN_LOOPBACKNET 127

// Address to loopback in software to local host: 127.0.0.1
macdef INADDR_LOOPBACK = $extval (in_addr_hbo_t, "INADDR_LOOPBACK")

(* Defines for Multicast INADDR *)

// 0xe0000000 // 224.0.0.0
macdef INADDR_UNSPEC_GROUP = $extval (in_addr_hbo_t, "INADDR_UNSPEC_GROUP")

// 0xe0000001 // 224.0.0.1
macdef INADDR_ALLHOSTS_GROUP = $extval (in_addr_hbo_t, "INADDR_ALLHOSTS_GROUP")

// 0xe0000002 // 224.0.0.2
macdef INADDR_ALLRTRS_GROUP = $extval (in_addr_hbo_t, "INADDR_ALLRTRS_GROUP")

// 0xe00000ff // 224.0.0.255
macdef INADDR_MAX_LOCAL_GROUP = $extval (in_addr_hbo_t, "INADDR_MAX_LOCAL_GROUP")

(* ****** ****** *)

typedef
in_addr_struct =
$extype_struct "ats_in_addr_type" of {
  s_addr= in_addr_nbo_t // IPv4 address of ulint
} // end of [in_addr_struct]

fun in_addr_struct_get_s_addr
  (inp: in_addr_struct): in_addr_nbo_t = "atslib_in_addr_struct_get_s_addr"
// end of [in_addr_struct_get_s_addr]

(* ****** ****** *)

typedef sockaddr_in_struct =
$extype_struct "ats_sockaddr_in_type" of {
  sin_family= sa_family_t
, sin_port= in_port_nbo_t // uint16
, sin_addr= in_addr_struct
} // end of [sockaddr_in_struct]
typedef sockaddr_in = sockaddr_in_struct
//
sta socklen_in : int // length of [sockaddr_in]
(*
stadef socklen_in = sizeof (sockaddr_in_struct)
*)
macdef socklen_in =
  $extval (socklen_t(socklen_in), "atslib_socklen_in")
//
praxi socklen_lte_in (): [socklen_in <= $SA.socklen_max] void
praxi sockaddr_in_trans {l:addr}
  (pf: !sockaddr_in_struct @ l >> sockaddr_struct(socklen_in) @ l): void
praxi sockaddr_trans_in {l:addr}
  (pf: !sockaddr_struct(socklen_in) @ l >> sockaddr_in_struct @ l): void

(* ****** ****** *)

typedef
in6_addr_struct =
$extype_struct "ats_in6_addr_type" of {
  s6_addr= @[uint8][16] // IPv6 address of 16 bytes
} // end of [in6_addr_struct]

(* ****** ****** *)

typedef sockaddr_in6_struct =
$extype_struct "ats_sockaddr_in6_type" of {
  sin6_family= sa_family_t
, sin6_port= in_port_nbo_t // uint16
, sin6_flowinfo= uint32
, sin6_addr= in6_addr_struct
, sin6_scope_id= uint32
} // end of [sockaddr_in_struct]
typedef sockaddr_in6 = sockaddr_in6_struct

sta socklen_in6 : int // length of [sockaddr_in6]
abst@ype sockaddr_in6_struct = $extype "ats_sockaddr_in6_type"
macdef socklen_in6 = $extval (socklen_t(socklen_in6), "atslib_socklen_in6")
//
praxi socklen_lte_in6 (): [socklen_in6 <= $SA.socklen_max] void
praxi sockaddr_in6_trans {l:addr}
  (pf: !sockaddr_in6_struct @ l >> sockaddr_struct(socklen_in6) @ l): void
praxi sockaddr_trans_in6 {l:addr}
  (pf: !sockaddr_struct(socklen_in6) @ l >> sockaddr_in6_struct @ l): void
//
(* ****** ****** *)

(* end of [in.sats] *)
