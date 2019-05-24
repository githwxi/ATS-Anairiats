(*
**
** Author: Hongwei Xi
** Authoremail: gmhwxiATgmailDOTcom
** Start Time: August, 2011
**
*)
//
staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"
//
(* ****** ****** *)
//
#include "utils/atsdoc/HATS/xhtmlatxt.hats"
//
macdef para (x) = xmltagging ("p", ,(x))
macdef emph (x) = xmltagging ("em", ,(x))
//
staload _ = "libatsdoc/DATS/libatsdoc_atext.dats"
//
(* ****** ****** *)

#include "atslangweb_params.hats"

(* ****** ****** *)

#define s2s string_of_strptr

(* ****** ****** *)
//
macdef strcst (x) = atext_strcst ,(x)
macdef strsub (x) = atext_strsub ,(x)
//
fun atext_strsubptr (x: strptr1): atext = atext_strsub ((s2s)x)
//
(* ****** ****** *)

macdef command(x) = xmltagging ("pre", ,(x)) // <pre> ... </pre>

fn filename
  (x: string): atext = let
  val opn = strcst"<span style=\"text-decoration: underline;\">"
  val cls = strcst"</span>"
in
  atext_apptxt3 (opn, strsub(x), cls)
end // end of [filename]

(* ****** ****** *)

fn menu
  (itmlst: string): atext = xmltagging ("ul", itmlst)
// end of [menu]

fn lisub
  (x: string): atext = xmltagging ("li", x)
// end of [lisub]

fn litxt (x: atext): atext =
  atext_apptxt3 (strcst"<li>", x, strcst"</li>")
// end of [litxt]

(* ****** ****** *)

fn BR (): atext = atext_apptxt2 (strcst"<br>", strcst"</br>")

(* ****** ****** *)

fn HR (sz: int): atext = let
  val str = sprintf ("<hr style=\"background-color: #E0E0E0; height: %ipx;\">", @(sz))
in
  atext_strptr (str)
end // end of [HR]

(* ****** ****** *)

fun uid (
  id: string, name: string
) : atext =
  atext_strptr (sprintf ("<a id=\"%s\">%s</a>", @(id, name)))
// end of [uid]

fun ulink (
  link: string, name: string
) : atext =
  atext_strptr (sprintf ("<a href=\"%s\">%s</a>", @(link, name)))
// end of [ulink]

fun ulink1 (
  link: string, name: string
) : atext = let
  val str = sprintf ("<a href=\"%s\">%s</a>", @(link, name))
in
  atext_strsub ((s2s)str)
end // end of [ulink1]

(* ****** ****** *)

#define
ATSLANGSVNROOT
"http://ats-lang.svn.sourceforge.net/svnroot/ats-lang/trunk"
// end of [#define]

fun ATSLANGSVNROOTget (): atext = atext_strcst (ATSLANGSVNROOT)

(* ****** ****** *)

fun ATSLANGWEBROOTget (): atext = atext_strcst (ATSLANGWEBROOT)

val ATSLANGWEBHOME: atext = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/\">Home</a>", @(ATSLANGWEBROOT))
}
val ATSLANGWEBDOWNLOAD: atext = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/DOWNLOAD/\">Download</a>", @(ATSLANGWEBROOT))
}
val ATSLANGWEBDOCUMENT: atext = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/DOCUMENT/\">Documents</a>", @(ATSLANGWEBROOT))
}
val ATSLANGWEBLIBRARY: atext = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/LIBRARY/\">Libraries</a>", @(ATSLANGWEBROOT))
}
val ATSLANGWEBRESOURCE: atext = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/RESOURCE/\">Resources</a>", @(ATSLANGWEBROOT))
}
val ATSLANGWEBCOMMUNITY: atext = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/COMMUNITY/\">Community</a>", @(ATSLANGWEBROOT))
}
val ATSLANGWEBEXAMPLE: atext = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/EXAMPLE/\">Examples</a>", @(ATSLANGWEBROOT))
}
val ATSLANGWEBIMPLEMENT: atext = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/IMPLEMENT/\">Implementations</a>", @(ATSLANGWEBROOT))
}
val ATSLANGWEBPAPER: atext = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/PAPER/\">Papers</a>", @(ATSLANGWEBROOT))
}

(* ****** ****** *)

#ifndef ISTEMP
#define ISTEMP 0
#endif
#if(ISTEMP==0)
val () = theAtextMap_insert_str ("ATSLANGWEBHOME", ATSLANGWEBHOME)
val () = theAtextMap_insert_str ("ATSLANGWEBDOWNLOAD", ATSLANGWEBDOWNLOAD)
val () = theAtextMap_insert_str ("ATSLANGWEBDOCUMENT", ATSLANGWEBDOCUMENT)
val () = theAtextMap_insert_str ("ATSLANGWEBLIBRARY", ATSLANGWEBLIBRARY)
val () = theAtextMap_insert_str ("ATSLANGWEBRESOURCE", ATSLANGWEBRESOURCE)
val () = theAtextMap_insert_str ("ATSLANGWEBCOMMUNITY", ATSLANGWEBCOMMUNITY)
val () = theAtextMap_insert_str ("ATSLANGWEBEXAMPLE", ATSLANGWEBEXAMPLE)
val () = theAtextMap_insert_str ("ATSLANGWEBIMPLEMENT", ATSLANGWEBIMPLEMENT)
val () = theAtextMap_insert_str ("ATSLANGWEBPAPER", ATSLANGWEBPAPER)
#endif // end of [#if(ISTEMP==0)]

(* ****** ****** *)

local

fn make_ahref (
  link: string, name: string
) : string = let
  val res = sprintf ("<a href=\"%s\">%s</a>", @(link, name))
in
  (s2s)res
end // end of [make_ahref]

fn subpage_ahref
  (flag: int, link: string, name: string): string = let
in
  if flag > 0 then let
    val name = sprintf ("<strong>%s</strong>", @(name))
  in
    (s2s)name // name only
  end else 
    make_ahref (link, name)
   // end of [if]
end // end of [subpage_ahref]

val root = ATSLANGWEBROOT

in // in of [local]

fn HOME_ahref
  (flag: int): string = let
  val link = sprintf ("%s/", @(root))
  val link = (s2s)link
in
  subpage_ahref (flag, link, "Home")
end // end of [HOME_ahref]

fn DOWNLOAD_ahref
  (flag: int): string = let
  val link = sprintf ("%s/%s", @(root, "DOWNLOAD"))
  val link = (s2s)link
in
  subpage_ahref (flag, link, "Download")
end // end of [DOWNLOAD_ahref]

fn DOCUMENT_ahref
  (flag: int): string = let
  val link = sprintf ("%s/%s", @(root, "DOCUMENT"))
  val link = (s2s)link
in
  subpage_ahref (flag, link, "Documents")
end // end of [DOCUMENT_ahref]

fn LIBRARY_ahref
  (flag: int): string = let
  val link = sprintf ("%s/%s", @(root, "LIBRARY"))
  val link = (s2s)link
in
  subpage_ahref (flag, link, "Libraries")
end // end of [LIBRARY_ahref]

fn RESOURCE_ahref
  (flag: int): string = let
  val link = sprintf ("%s/%s", @(root, "RESOURCE"))
  val link = (s2s)link
in
  subpage_ahref (flag, link, "Resources")
end // end of [RESOURCE_ahref]

fn COMMUNITY_ahref
  (flag: int): string = let
  val link = sprintf ("%s/%s", @(root, "COMMUNITY"))
  val link = (s2s)link
in
  subpage_ahref (flag, link, "Community")
end // end of [COMMUNITY_ahref]

end // end of [local]

(* ****** ****** *)

fn mysitelinks
  (ent: string): atext = let
//
val flag = (if (ent = "HOME") then 1 else 0): int
val HOME = strcst (HOME_ahref (flag))
//
val flag = (if (ent = "DOWNLOAD") then 1 else 0): int
val DOWNLOAD = strcst (DOWNLOAD_ahref (flag))
//
val flag = (if (ent = "DOCUMENT") then 1 else 0): int
val DOCUMENT = strcst (DOCUMENT_ahref (flag))
//
val flag = (if (ent = "LIBRARY") then 1 else 0): int
val LIBRARY = strcst (LIBRARY_ahref (flag))
//
val flag = (if (ent = "RESOURCE") then 1 else 0): int
val RESOURCE = strcst (RESOURCE_ahref (flag))
//
val flag = (if (ent = "COMMUNITY") then 1 else 0): int
val COMMUNITY = strcst (COMMUNITY_ahref (flag))
//
val xs = $lst {atext} (
  HOME, DOWNLOAD, DOCUMENT, LIBRARY, RESOURCE, COMMUNITY
) // end of [val]
//
val sep = strcst ("<span class=\"separator\"> | </span>")
//
in
  atext_concatxtsep (xs, sep)
end // end of [mysitelinks]

(* ****** ****** *)

local

(* ****** ****** *)

fun get_name
  (ent: string): string = let
in
//
case+ ent of
| "HOME" => "Home"
| "DOWNLOAD" => "Download"
| "DOCUMENT" => "Documents"
| "LIBRARY" => "Libraries"
| "RESOURCE" => "Resources"
| "COMMUNITY" => "Community"
| _ => "__ERROR__"
//
end // end of [get_name]

(* ****** ****** *)

fun get_path
  (ent: string): string = let
in
  case+ ent of
  | "HOME" => ATSLANGWEBROOT
  | _ => let
      val res = sprintf ("%s/%s", @(ATSLANGWEBROOT, ent)) in s2s(res)
    end // end of [_]
end // end of [get_path]

(* ****** ****** *)

typedef stringlst = List (string)

val _HOME = $lst{string}(
  "what_is_ats", "What is ATS?"
, "what_is_ats_good_for", "What is ATS good for?"
, "acknowledgments", "Acknowledgments"
) // end of [val]
val _DOWNLOAD = $lst{string}(
  "ATS_packages", "ATS packages for download"
, "installation_require", "Requirements for installation"
, "installation_debian", "Installation of official Debian package"
, "installation_redhat", "Installation of unofficial Redhat package"
, "installation_srccomp", "Installation through source compilation"
, "installation_atscntrb", "Installation of ATS2-contrib"
) // end of [val]
val _DOCUMENT = $lst{string}(
  "ATSINTRObook", "Introduction to Programming in ATS"
, "ATSTUTORbook", "A Tutorial on Programming Features in ATS"
, "ATSAPUE3book", "ATS for Programming in the UNIX environment"
, "ATSGTKbook", "ATS/GTK Tutorial"
, "ATSCAIRObook", "ATS/Cairo Tutorial"
) // end of [val]
val _LIBRARY = $lst{string}(
  "ATSLIB_prelude", "ATSLIB/prelude"
, "ATSLIB_libc", "ATSLIB/libc"
, "ATSLIB_libats", "ATSLIB/libats"
, "ATSLIB_libats_ML", "ATSLIB/libats/ML"
, "ATSLIB_libatslex", "ATSLIB/libatslex"
, "ATSLIB_contrib", "ATSLIB/contrib"
) // end of [val]
val _RESOURCE = $lst{string}(
  "ATS_edit", "Editing ATS source code"
, "ATS_eval", "Evaluating ATS source code on-line"
, "ATS_utility", "ATS-related utility commands"
, "ATS_compile", "Compiling projects based on ATS"
, "ATS_courses", "Courses about ATS and based on ATS"
) // end of [val]
val _COMMUNITY = $lst{string}(
  "ATS_wikipage", "Wiki for ATS users"
, "ATS_QandA_forum", "Q&amp;A forum for ATS users"
, "ATS_devel_forum", "Discussion forum for ATS developers"
, "ATS_mailing_list", "Mailing-list for ATS users"
, "ATS_irc_channel", "IRC channel for ATS users: ##ats"
, "ATS_reddit_news", "ATS news at reddit"
) // end of [val]

fun get_xylst
  (ent: string): stringlst = let
in
  case+ ent of
  | "HOME" => _HOME
  | "DOWNLOAD" => _DOWNLOAD
  | "DOCUMENT" => _DOCUMENT
  | "LIBRARY" => _LIBRARY
  | "RESOURCE" => _RESOURCE
  | "COMMUNITY" => _COMMUNITY
  | _ => list_nil ()
end // end of [get_xylst]

(* ****** ****** *)

fun menugen (
  path: string, xys: List(string)
) : atextlst = let
in
  case+ xys of
  | list_cons (x, xys) => let
      val link =
        sprintf ("%s#%s", @(path, x))
      val link = s2s(link)
      val- list_cons (y, xys) = xys
      val itm = litxt (ulink (link, y))
    in
      list_cons (itm, menugen (path, xys))
    end // end of [list_cons]
  | list_nil () => list_nil ()
end // end of [menugen]

fun sitelink_li
  (knd: int, myent: string, ent: string): atext = let
//
val ismy = (myent = ent): bool
//
fun sitelink_li_ul
  (ent: string): atext = let
  val path = get_path (ent)
  val xylst = get_xylst (ent)
  val itmlst = menugen (path, xylst)
  val sep = atext_newline()
  val _beg = atext_strcst ("<ul>\n")
  val _itmlst = atext_concatxtsep (itmlst, sep)
  val _end = atext_strcst ("\n</ul>\n")
in
  atext_apptxt3 (_beg, _itmlst, _end)
end // end of [sitelink_li_ul]
//
val path = get_path (ent)
val name = get_name (ent)
val name = (
  if ismy then let
    val name = sprintf ("<strong>%s</strong>", @(name))
  in
    s2s(name)
  end else let
    val name = sprintf ("<span style=\"text-decoration: underline\">%s</span>", @(name))
  in
    s2s(name)
  end // end of [if]
) : string // end of [val]
val _lnk = (
  if ismy then ulink ("#", name) else ulink (path, name)
) : atext // end of [val]
val _itm = (
  if ismy then _lnk
  else if knd = 2 then let
    val _menu = sitelink_li_ul (ent) in atext_apptxt2 (_lnk, _menu)
  end else _lnk // end of [if]
) : atext // end of [val]
//
val _beg = atext_strcst "<li>"
val _end = atext_strcst "</li>\n"
//
in
  atext_apptxt3 (_beg, _itm, _end)
end // end of [sitelink_li]

in // in of [local]

fun mysitelinks23
  (knd: int, ent: string): atext = let
//
  val res = list_nil {atext} ()
  val li = sitelink_li (knd, ent, "HOME")
  val res = list_cons (li, res)
  val li = sitelink_li (knd, ent, "DOWNLOAD")
  val res = list_cons (li, res)
  val li = sitelink_li (knd, ent, "DOCUMENT")
  val res = list_cons (li, res)
  val li = sitelink_li (knd, ent, "LIBRARY")
  val res = list_cons (li, res)
  val li = sitelink_li (knd, ent, "RESOURCE")
  val res = list_cons (li, res)
  val li = sitelink_li (knd, ent, "COMMUNITY")
  val res = list_cons (li, res)
//
  val res = list_reverse (res)
  val res = list_of_list_vt (res)
//
  val sep = atext_newline ()
//
  val _beg =
  (
    case+ knd of
    | 2 => atext_strcst ("<ul id=\"jsddm\">\n")
    | 3 => atext_strcst ("<ul id=\"jsddm\">\n")
    | _ => atext_strcst ("<ul id=\"jsddm-none\">\n")
  ) : atext // end of [val]
  val _lis = atext_concatxtsep (res, sep)
  val _end = atext_strcst ("\n</ul>\n")
//
in
  atext_apptxt3 (_beg, _lis, _end)
end // end of [mysitelinks23]

fun mysitelinks2
  (ent: string): atext = mysitelinks23 (2, ent)
fun mysitelinks3
  (ent: string): atext = mysitelinks23 (3, ent)

end // end of [local]

(* ****** ****** *)

fun staexp (x: string) = let
  val opn = "<span class=atsyntax_staexp>"
  val cls = "</span>"
in
  atext_appstr3 (opn, x, cls)
end // end of [staexp]

fun dynexp (x: string) = let
  val opn = "<span class=atsyntax_dynexp>"
  val cls = "</span>"
in
  atext_appstr3 (opn, x, cls)
end // end of [dynexp]

(* ****** ****** *)
//
local
//
staload "utils/atsyntax/SATS/ats2xhtml.sats"
dynload "utils/atsyntax/DATS/ats2xhtml.dats"
//
in
//
fun ats2xhtmls
  (x: string): atext = let
  val [l:addr]
    str = ats2xhtml_strcode (0(*stadyn*), x)
  prval () = addr_is_gtez {l} ()
in
  if strptr_is_null (str) then let
    prval () = strptr_free_null (str) in atext_nil ()
  end else atext_strptr (str) // end of [if]
end // end of [atx2xhtmls]

fun ats2xhtmld
  (x: string): atext = let
  val [l:addr]
    str = ats2xhtml_strcode (1(*stadyn*), x)
  prval () = addr_is_gtez {l} ()
in
  if strptr_is_null (str) then let
    prval () = strptr_free_null (str) in atext_nil ()
  end else atext_strptr (str) // end of [if]
end // end of [atx2xhtmld]
//
end // end of [local]
//
(* ****** ****** *)

(* end of [atslangwebatxt.dats] *)
