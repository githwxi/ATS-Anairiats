(*
**
** A simple cURL example mostly taken from an example by
** chris.double AT double DOT co DOT nz
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: May, 2010
**
*)

(* ****** ****** *)

staload "contrib/cURL/SATS/curl.sats"

(* ****** ****** *)

implement main () = () where {
  val (pf_gerr | gerr) = curl_global_init (CURL_GLOBAL_ALL)
  val () = assertloc (gerr = CURLE_OK)
//
// HX: [curl_easy_init] is advised to be called after [curl_global_init]
//
  val curl  = curl_easy_init ()
  val () = assertloc (curlptr_isnot_null curl)
  val URL = "http://www.ats-lang.org"
  val (pf_err | err) = curl_easy_setopt (curl, CURLOPT_URL, @(URL))
  val () = assertloc (err = CURLE_OK)
  prval () = curlerr_elim_null (pf_err)
  val (pf_err | err) = curl_easy_perform (curl)
  val () = assertloc (err = CURLE_OK)
  prval () = curlerr_elim_null (pf_err)
  val () = curl_easy_cleanup (curl)
  val () = curl_global_cleanup (pf_gerr | (*none*))
} // end of [main]

(* ****** ****** *)

(* end of [cURL-test01.dats] *)
