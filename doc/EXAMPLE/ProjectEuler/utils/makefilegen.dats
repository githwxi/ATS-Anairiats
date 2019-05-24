(*
**
** For generating Makefiles for PE problems
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2010
**
*)

(* ****** ****** *)

staload "libc/SATS/time.sats"
staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "makefilegen.sats"

(* ****** ****** *)

#define ATSUSRDEFAULT "/usr"

(* ****** ****** *)

implement
emit_ATSUSRQ (out) = let
  val () = fprintf (out, "\
ATSUSRQ=\"$(ATSHOME)\"\n\
ifeq ($(ATSUSRQ),\"\")\n\
ATSUSRQ=\"%s\"
endif\n\
"
,
@(ATSUSRDEFAULT)
) // end of [val]
in
  // nothing
end // end of [emit_ATSUSRQ]

(* ****** ****** *)

implement
emit_ATSCC (out) = {
  val () = fprint (out, "ATSCC=$(ATSUSRQ)/bin/atscc\n")
} // end of [emit_ATSCC]

(* ****** ****** *)

implement
emit_ATSOPT (out) = {
  val () = fprint (out, "ATSOPT=$(ATSUSRQ)/bin/atsopt\n")
} // end of [emit_ATSOPT]

(* ****** ****** *)

fun emit_header
  (out: FILEref): void = {
  var time: time_t // uninitialized
  val () = assertloc (time_get_and_set (time))
  prval () = opt_unsome (time)
  val () = fprint_string (out, "#\n")
  val (fpf_str | p_str) = ctime (time)
  val () = fprintf (out, "# Time of Generation: %s", @($UN.castvwtp1 {string} (p_str)))
  prval () = fpf_str (p_str)
  val () = fprint_string (out, "#\n")
} // end of [emit_header]

(* ****** ****** *)

fun emit_sep (out: FILEref): void = {
  val () = fprint_string (out, "\n######\n\n")
} // end of [emit_sep]

(* ****** ****** *)

fun emit_all (out: FILEref): void = {
  val () = fprint_string (out, ".PHONY: all\n")
  val () = fprint_string (out, "all:: checkall\n")
  val () = fprint_string (out, "all:: cleanall\n")
} // end of [emit_all]

(* ****** ****** *)

fun emit_checkall_itemname
  (out: FILEref, itemname: string): void = {
  val () = fprintf (out, "checkall:: %s\n", @(itemname))
} // end of [emit_checkall_itemname]

(* ****** ****** *)

fun emit01_item_comp_and_exec
  (out: FILEref, itemname: string): void = {
  val () = fprintf (out, "%s: %s.dats\n", @(itemname, itemname))
  val () = fprintf (out, "\t$(ATSCC) -O2 -o $@ $< && ./%s\n", @(itemname))
} // end of [emit01_item_comp_and_exec]

fun emit01pfck_item_comp_and_exec
  (out: FILEref, itemname: string): void = {
  val () = fprintf (out, "%s: %s.dats\n", @(itemname, itemname))
  val () = fprintf (out, "\t$(ATSCC) -D_ATS_PROOFCHECK -O2 -o $@ $< && ./%s\n", @(itemname))
} // end of [emit01pfck_item_comp_and_exec]

fun emit02_item_comp_and_exec
  (out: FILEref, itemname: string): void = {
  val () = fprintf (out, "%s: %s.dats\n", @(itemname, itemname))
  val () = fprintf (out, "\t$(ATSCC) -O2 -o $@ $< -lm && ./%s\n", @(itemname))
} // end of [emit02_item_comp_and_exec]

fun emit02gc_item_comp_and_exec
  (out: FILEref, itemname: string): void = {
  val () = fprintf (out, "%s: %s.dats\n", @(itemname, itemname))
  val () = fprintf (out, "\t$(ATSCC) -DATS_GCATS -O2 -o $@ $< -lm && ./%s\n", @(itemname))
} // end of [emit02gc_item_comp_and_exec]

fun emit03_item_comp_and_exec
  (out: FILEref, itemname: string): void = {
  val () = fprintf (out, "%s: %s.dats\n", @(itemname, itemname))
  val () = fprintf (out, "\t$(ATSCC) -O2 -o $@ $< -lats -lgmp && ./%s\n", @(itemname))
} // end of [emit03_item_comp_and_exec]

fun emit04_item_comp_and_exec
  (out: FILEref, itemname: string): void = {
  val () = fprintf (out, "%s: %s.dats\n", @(itemname, itemname))
  val () = fprintf (out, "\t$(ATSCC) -O2 -o $@ $< -lats -lgmp -lm && ./%s\n", @(itemname))
} // end of [emit04_item_comp_and_exec]

(* ****** ****** *)

fun emit_RMF (out: FILEref): void = {
  val () = fprint_string (out, "RMF = rm -f\n")
} // end of [emit_RMF]

(* ****** ****** *)

fun emit_clean (out: FILEref): void = {
  val () = fprint_string (out, "clean:\n")
  val () = fprint_string (out, "\t$(RMF) *~\n")
  val () = fprint_string (out, "\t$(RMF) *_?ats.c *_?ats.o\n")
} // end of [emit_clean]

(* ****** ****** *)

fun emit_cleanall_clean (out: FILEref): void = {
  val () = fprint_string (out, "cleanall:: clean\n")
} // end of [emit_cleanall_clean]

fun emit_cleanall_rmf_namepat
  (out: FILEref, filename: string): void = {
  val () = fprintf (out, "cleanall:: ; $(RMF) %s\n", @(filename))
} // end of [emit_cleanall_rmf_namepat]

(* ****** ****** *)

fun emit01_Makefile (
  out: FILEref, itemname: string
) : void = {
  val () = emit_header (out)
  val () = emit_sep (out)
  val () = emit_ATSUSRQ (out)
  val () = emit_ATSCC (out)
  val () = emit_ATSOPT (out)
  val () = emit_sep (out)
  val () = emit_all (out)
  val () = emit_checkall_itemname (out, itemname)
  val () = emit_sep (out)
  val () = emit01_item_comp_and_exec (out, itemname)
  val () = emit_sep (out)
  val () = emit_RMF (out)
  val () = emit_sep (out)
  val () = emit_clean (out)
  val () = emit_cleanall_clean (out)
  val () = emit_cleanall_rmf_namepat (out, itemname)
} // end of [emit01_Makefile]

(* ****** ****** *)

fun emit02_Makefile (
  out: FILEref, itemname: string
) : void = {
  val () = emit_header (out)
  val () = emit_sep (out)
  val () = emit_ATSUSRQ (out)
  val () = emit_ATSCC (out)
  val () = emit_ATSOPT (out)
  val () = emit_sep (out)
  val () = emit_all (out)
  val () = emit_checkall_itemname (out, itemname)
  val () = emit_sep (out)
  val () = emit02_item_comp_and_exec (out, itemname)
  val () = emit_sep (out)
  val () = emit_RMF (out)
  val () = emit_sep (out)
  val () = emit_clean (out)
  val () = emit_cleanall_clean (out)
  val () = emit_cleanall_rmf_namepat (out, itemname)
} // end of [emit02_Makefile]

(* ****** ****** *)

fun emit03_Makefile (
  out: FILEref, itemname: string
) : void = {
  val () = emit_header (out)
  val () = emit_sep (out)
  val () = emit_ATSUSRQ (out)
  val () = emit_ATSCC (out)
  val () = emit_ATSOPT (out)
  val () = emit_sep (out)
  val () = emit_all (out)
  val () = emit_checkall_itemname (out, itemname)
  val () = emit_sep (out)
  val () = emit03_item_comp_and_exec (out, itemname) // -lgmp
  val () = emit_sep (out)
  val () = emit_RMF (out)
  val () = emit_sep (out)
  val () = emit_clean (out)
  val () = emit_cleanall_clean (out)
  val () = emit_cleanall_rmf_namepat (out, itemname)
} // end of [emit03_Makefile]

(* ****** ****** *)

fun emit04_Makefile (
  out: FILEref, itemname: string
) : void = {
  val () = emit_header (out)
  val () = emit_sep (out)
  val () = emit_ATSUSRQ (out)
  val () = emit_ATSCC (out)
  val () = emit_ATSOPT (out)
  val () = emit_sep (out)
  val () = emit_all (out)
  val () = emit_checkall_itemname (out, itemname)
  val () = emit_sep (out)
  val () = emit04_item_comp_and_exec (out, itemname) // -lgmp -lm
  val () = emit_sep (out)
  val () = emit_RMF (out)
  val () = emit_sep (out)
  val () = emit_clean (out)
  val () = emit_cleanall_clean (out)
  val () = emit_cleanall_rmf_namepat (out, itemname)
} // end of [emit04_Makefile]

(* ****** ****** *)

fun emit_Makefile_problem1
  (out: FILEref): void = {
  val itemname = "problem1-hwxi"
  val itemname2 = "problem1-hwxi2"
  val () = emit_header (out)
  val () = emit_sep (out)
  val () = emit_ATSUSRQ (out)
  val () = emit_ATSCC (out)
  val () = emit_ATSOPT (out)
  val () = emit_sep (out)
  val () = emit_all (out)
  val () = emit_checkall_itemname (out, itemname)
  val () = emit_checkall_itemname (out, itemname2)
  val () = emit_sep (out)
  val () = emit01_item_comp_and_exec (out, itemname)
  val () = emit01pfck_item_comp_and_exec (out, itemname2)
  val () = emit_sep (out)
  val () = emit_RMF (out)
  val () = emit_sep (out)
  val () = emit_clean (out)
  val () = emit_cleanall_clean (out)
  val () = emit_cleanall_rmf_namepat (out, itemname)
  val () = emit_cleanall_rmf_namepat (out, itemname2)
} // end of [emit_Makefile_problem1]

(* ****** ****** *)

fun emit_Makefile_problem2
  (out: FILEref): void = {
  val itemname = "problem2-hwxi"
  val itemname2 = "problem2-hwxi2"
  val () = emit_header (out)
  val () = emit_sep (out)
  val () = emit_ATSUSRQ (out)
  val () = emit_ATSCC (out)
  val () = emit_ATSOPT (out)
  val () = emit_sep (out)
  val () = emit_all (out)
  val () = emit_checkall_itemname (out, itemname)
  val () = emit_checkall_itemname (out, itemname2)
  val () = emit_sep (out)
  val () = emit03_item_comp_and_exec (out, itemname) // -lgmp
  val () = emit01pfck_item_comp_and_exec (out, itemname2)
  val () = emit_sep (out)
  val () = emit_RMF (out)
  val () = emit_sep (out)
  val () = emit_clean (out)
  val () = emit_cleanall_clean (out)
  val () = emit_cleanall_rmf_namepat (out, itemname)
  val () = emit_cleanall_rmf_namepat (out, itemname2)
} // end of [emit_Makefile_problem2]

(* ****** ****** *)

fun emit_Makefile_problem3
  (out: FILEref): void = emit03_Makefile (out, "problem3-hwxi")
// end of [emit_Makefile_problem3]

fun emit_Makefile_problem4
  (out: FILEref): void = emit01_Makefile (out, "problem4-hwxi")
// end of [emit_Makefile_problem4]

fun emit_Makefile_problem5
  (out: FILEref): void = emit03_Makefile (out, "problem5-hwxi")
// end of [emit_Makefile_problem5]

(* ****** ****** *)

fun emit_Makefile_problem6
  (out: FILEref): void = {
  val itemname = "problem6-hwxi"
  val itemname2 = "problem6-hwxi2"
  val () = emit_header (out)
  val () = emit_sep (out)
  val () = emit_ATSUSRQ (out)
  val () = emit_ATSCC (out)
  val () = emit_ATSOPT (out)
  val () = emit_sep (out)
  val () = emit_all (out)
  val () = emit_checkall_itemname (out, itemname)
  val () = emit_checkall_itemname (out, itemname2)
  val () = emit_sep (out)
  val () = emit01_item_comp_and_exec (out, itemname)
  val () = emit01_item_comp_and_exec (out, itemname2)
  val () = emit_sep (out)
  val () = emit_RMF (out)
  val () = emit_sep (out)
  val () = emit_clean (out)
  val () = emit_cleanall_clean (out)
  val () = emit_cleanall_rmf_namepat (out, itemname)
  val () = emit_cleanall_rmf_namepat (out, itemname2)
} // end of [emit_Makefile_problem6]

(* ****** ****** *)

fun emit_Makefile_problem7
  (out: FILEref): void = {
  val itemname = "problem7-hwxi"
  val itemname2 = "problem7-hwxi2"
  val () = emit_header (out)
  val () = emit_sep (out)
  val () = emit_ATSUSRQ (out)
  val () = emit_ATSCC (out)
  val () = emit_ATSOPT (out)
  val () = emit_sep (out)
  val () = emit_all (out)
  val () = emit_checkall_itemname (out, itemname)
  val () = emit_checkall_itemname (out, itemname2)
  val () = emit_sep (out)
  val () = emit01_item_comp_and_exec (out, itemname)
  val () = emit02_item_comp_and_exec (out, itemname2) // -lm
  val () = emit_sep (out)
  val () = emit_RMF (out)
  val () = emit_sep (out)
  val () = emit_clean (out)
  val () = emit_cleanall_clean (out)
  val () = emit_cleanall_rmf_namepat (out, itemname)
  val () = emit_cleanall_rmf_namepat (out, itemname2)
} // end of [emit_Makefile_problem7]

(* ****** ****** *)

fun emit_Makefile_problem8
  (out: FILEref): void = emit01_Makefile (out, "problem8-hwxi")
// end of [emit_Makefile_problem8]

fun emit_Makefile_problem9
  (out: FILEref): void = emit01_Makefile (out, "problem9-hwxi")
// end of [emit_Makefile_problem9]

fun emit_Makefile_problem10
  (out: FILEref): void = emit01_Makefile (out, "problem10-hwxi")
// end of [emit_Makefile_problem10]

(* ****** ****** *)

fun emit_Makefile_problem11
  (out: FILEref): void = emit01_Makefile (out, "problem11-hwxi")
// end of [emit_Makefile_problem11]

fun emit_Makefile_problem12
  (out: FILEref): void = emit01_Makefile (out, "problem12-hwxi")
// end of [emit_Makefile_problem12]

fun emit_Makefile_problem13
  (out: FILEref): void = emit03_Makefile (out, "problem13-hwxi")
// end of [emit_Makefile_problem13]

fun emit_Makefile_problem14
  (out: FILEref): void = emit03_Makefile (out, "problem14-hwxi")
// end of [emit_Makefile_problem14]

(* ****** ****** *)

fun emit_Makefile_problem15
  (out: FILEref): void = {
  val itemname = "problem15-hwxi"
  val itemname2 = "problem15-hwxi2"
  val itemname3 = "problem15-mberndt"
  val () = emit_header (out)
  val () = emit_sep (out)
  val () = emit_ATSUSRQ (out)
  val () = emit_ATSCC (out)
  val () = emit_ATSOPT (out)
  val () = emit_sep (out)
  val () = emit_all (out)
  val () = emit_checkall_itemname (out, itemname)
  val () = emit_checkall_itemname (out, itemname2)
  val () = emit_checkall_itemname (out, itemname3)
  val () = emit_sep (out)
  val () = emit03_item_comp_and_exec (out, itemname) // -lgmp
  val () = emit01_item_comp_and_exec (out, itemname2)
  val () = emit01_item_comp_and_exec (out, itemname3)
  val () = emit_sep (out)
  val () = emit_RMF (out)
  val () = emit_sep (out)
  val () = emit_clean (out)
  val () = emit_cleanall_clean (out)
  val () = emit_cleanall_rmf_namepat (out, itemname)
  val () = emit_cleanall_rmf_namepat (out, itemname2)
  val () = emit_cleanall_rmf_namepat (out, itemname3)
} // end of [emit_Makefile_problem15]

(* ****** ****** *)

fun emit_Makefile_problem16
  (out: FILEref): void = {
  val itemname = "problem16-hwxi"
  val itemname2 = "problem16-hwxi2"
  val () = emit_header (out)
  val () = emit_sep (out)
  val () = emit_ATSUSRQ (out)
  val () = emit_ATSCC (out)
  val () = emit_ATSOPT (out)
  val () = emit_sep (out)
  val () = emit_all (out)
  val () = emit_checkall_itemname (out, itemname)
  val () = emit_checkall_itemname (out, itemname2)
  val () = emit_sep (out)
  val () = emit03_item_comp_and_exec (out, itemname) // -lgmp
  val () = emit01_item_comp_and_exec (out, itemname2)
  val () = emit_sep (out)
  val () = emit_RMF (out)
  val () = emit_sep (out)
  val () = emit_clean (out)
  val () = emit_cleanall_clean (out)
  val () = emit_cleanall_rmf_namepat (out, itemname)
  val () = emit_cleanall_rmf_namepat (out, itemname2)
} // end of [emit_Makefile_problem16]

(* ****** ****** *)

fun emit_Makefile_problem17
  (out: FILEref): void = emit01_Makefile (out, "problem17-hwxi")
// end of [emit_Makefile_problem17]

fun emit_Makefile_problem18
  (out: FILEref): void = emit01_Makefile (out, "problem18-hwxi")
// end of [emit_Makefile_problem18]

fun emit_Makefile_problem19
  (out: FILEref): void = emit01_Makefile (out, "problem19-hwxi")
// end of [emit_Makefile_problem19]

(* ****** ****** *)

fun emit_Makefile_problem20
  (out: FILEref): void = {
  val itemname = "problem20-hwxi"
  val itemname2 = "problem20-hwxi2"
  val () = emit_header (out)
  val () = emit_sep (out)
  val () = emit_ATSUSRQ (out)
  val () = emit_ATSCC (out)
  val () = emit_ATSOPT (out)
  val () = emit_sep (out)
  val () = emit_all (out)
  val () = emit_checkall_itemname (out, itemname)
  val () = emit_checkall_itemname (out, itemname2)
  val () = emit_sep (out)
  val () = emit03_item_comp_and_exec (out, itemname) // -lgmp
  val () = emit01_item_comp_and_exec (out, itemname2)
  val () = emit_sep (out)
  val () = emit_RMF (out)
  val () = emit_sep (out)
  val () = emit_clean (out)
  val () = emit_cleanall_clean (out)
  val () = emit_cleanall_rmf_namepat (out, itemname)
  val () = emit_cleanall_rmf_namepat (out, itemname2)
} // end of [emit_Makefile_problem20]

(* ****** ****** *)

fun emit_Makefile_problem21
  (out: FILEref): void = emit01_Makefile (out, "problem21-hwxi")
// end of [emit_Makefile_problem21]

fun emit_Makefile_problem22
  (out: FILEref): void = emit01_Makefile (out, "problem22-hwxi")
// end of [emit_Makefile_problem22]

fun emit_Makefile_problem23
  (out: FILEref): void = emit01_Makefile (out, "problem23-hwxi")
// end of [emit_Makefile_problem23]

fun emit_Makefile_problem24
  (out: FILEref): void = emit01_Makefile (out, "problem24-hwxi")
// end of [emit_Makefile_problem24]

(* ****** ****** *)

fun emit_Makefile_problem25
  (out: FILEref): void = {
  val itemname = "problem25-hwxi"
  val itemname2 = "problem25-hwxi2"
  val () = emit_header (out)
  val () = emit_sep (out)
  val () = emit_ATSUSRQ (out)
  val () = emit_ATSCC (out)
  val () = emit_ATSOPT (out)
  val () = emit_sep (out)
  val () = emit_all (out)
  val () = emit_checkall_itemname (out, itemname)
  val () = emit_checkall_itemname (out, itemname2)
  val () = emit_sep (out)
  val () = emit03_item_comp_and_exec (out, itemname) // -lgmp
  val () = emit01_item_comp_and_exec (out, itemname2)
  val () = emit_sep (out)
  val () = emit_RMF (out)
  val () = emit_sep (out)
  val () = emit_clean (out)
  val () = emit_cleanall_clean (out)
  val () = emit_cleanall_rmf_namepat (out, itemname)
  val () = emit_cleanall_rmf_namepat (out, itemname2)
} // end of [emit_Makefile_problem25]

(* ****** ****** *)

fun emit_Makefile_problem26
  (out: FILEref): void = emit01_Makefile (out, "problem26-hwxi")
// end of [emit_Makefile_problem26]

fun emit_Makefile_problem27
  (out: FILEref): void = emit01_Makefile (out, "problem27-hwxi")
// end of [emit_Makefile_problem27]

fun emit_Makefile_problem28
  (out: FILEref): void = emit01_Makefile (out, "problem28-hwxi")
// end of [emit_Makefile_problem28]

fun emit_Makefile_problem29
  (out: FILEref): void = emit03_Makefile (out, "problem29-hwxi") // -lgmp
// end of [emit_Makefile_problem29]

(* ****** ****** *)

fun emit_Makefile_problem30
  (out: FILEref): void = emit01_Makefile (out, "problem30-hwxi")
// end of [emit_Makefile_problem30]

fun emit_Makefile_problem31
  (out: FILEref): void = emit01_Makefile (out, "problem31-hwxi")
// end of [emit_Makefile_problem31]

fun emit_Makefile_problem32
  (out: FILEref): void = emit01_Makefile (out, "problem32-hwxi")
// end of [emit_Makefile_problem32]

fun emit_Makefile_problem33
  (out: FILEref): void = emit01_Makefile (out, "problem33-hwxi")
// end of [emit_Makefile_problem33]

fun emit_Makefile_problem34
  (out: FILEref): void = emit01_Makefile (out, "problem34-hwxi")
// end of [emit_Makefile_problem34]

fun emit_Makefile_problem35
  (out: FILEref): void = emit01_Makefile (out, "problem35-hwxi")
// end of [emit_Makefile_problem35]

fun emit_Makefile_problem36
  (out: FILEref): void = emit01_Makefile (out, "problem36-hwxi")
// end of [emit_Makefile_problem36]

fun emit_Makefile_problem37
  (out: FILEref): void = emit01_Makefile (out, "problem37-hwxi")
// end of [emit_Makefile_problem37]

fun emit_Makefile_problem38
  (out: FILEref): void = emit01_Makefile (out, "problem38-hwxi")
// end of [emit_Makefile_problem38]

fun emit_Makefile_problem39
  (out: FILEref): void = emit02_Makefile (out, "problem39-hwxi") // -lm
// end of [emit_Makefile_problem39]

(* ****** ****** *)

fun emit_Makefile_problem40
  (out: FILEref): void = emit01_Makefile (out, "problem40-hwxi")
// end of [emit_Makefile_problem40]

fun emit_Makefile_problem41
  (out: FILEref): void = emit01_Makefile (out, "problem41-hwxi")
// end of [emit_Makefile_problem41]

fun emit_Makefile_problem42
  (out: FILEref): void = emit02_Makefile (out, "problem42-hwxi") // -lm
// end of [emit_Makefile_problem42]

fun emit_Makefile_problem43
  (out: FILEref): void = emit01_Makefile (out, "problem43-hwxi")
// end of [emit_Makefile_problem43]

fun emit_Makefile_problem44
  (out: FILEref): void = emit02_Makefile (out, "problem44-hwxi") // -lm
// end of [emit_Makefile_problem44]

fun emit_Makefile_problem45
  (out: FILEref): void = emit02_Makefile (out, "problem45-hwxi") // -lm
// end of [emit_Makefile_problem45]

fun emit_Makefile_problem46
  (out: FILEref): void = emit01_Makefile (out, "problem46-hwxi")
// end of [emit_Makefile_problem46]

fun emit_Makefile_problem47
  (out: FILEref): void = emit01_Makefile (out, "problem47-hwxi")
// end of [emit_Makefile_problem47]

fun emit_Makefile_problem48
  (out: FILEref): void = emit03_Makefile (out, "problem48-hwxi") // -lgmp
// end of [emit_Makefile_problem48]

fun emit_Makefile_problem49
  (out: FILEref): void = emit01_Makefile (out, "problem49-hwxi")
// end of [emit_Makefile_problem49]

fun emit_Makefile_problem50
  (out: FILEref): void = emit01_Makefile (out, "problem50-hwxi")
// end of [emit_Makefile_problem50]

(* ****** ****** *)

fun emit_Makefile_problem51
  (out: FILEref): void = emit02_Makefile (out, "problem51-hwxi") // -lm
// end of [emit_Makefile_problem51]

fun emit_Makefile_problem52
  (out: FILEref): void = emit01_Makefile (out, "problem52-hwxi")
// end of [emit_Makefile_problem52]

fun emit_Makefile_problem53
  (out: FILEref): void = emit01_Makefile (out, "problem53-hwxi")
// end of [emit_Makefile_problem53]

fun emit_Makefile_problem55
  (out: FILEref): void = emit03_Makefile (out, "problem55-hwxi") // -lgmp
// end of [emit_Makefile_problem55]

fun emit_Makefile_problem56
  (out: FILEref): void = emit03_Makefile (out, "problem56-hwxi") // -lgmp
// end of [emit_Makefile_problem56]

fun emit_Makefile_problem57
  (out: FILEref): void = emit03_Makefile (out, "problem57-hwxi") // -lgmp
// end of [emit_Makefile_problem57]

fun emit_Makefile_problem58
  (out: FILEref): void = emit02_Makefile (out, "problem58-hwxi") // -lm
// end of [emit_Makefile_problem58]

fun emit_Makefile_problem60
  (out: FILEref): void = {
  val itemname = "problem60-hwxi"
  val () = emit_header (out)
  val () = emit_sep (out)
  val () = emit_ATSUSRQ (out)
  val () = emit_ATSCC (out)
  val () = emit_ATSOPT (out)
  val () = emit_sep (out)
  val () = emit_all (out)
  val () = emit_checkall_itemname (out, itemname)
  val () = emit_sep (out)
  val () = emit02gc_item_comp_and_exec (out, itemname) // -lm
  val () = emit_sep (out)
  val () = emit_RMF (out)
  val () = emit_sep (out)
  val () = emit_clean (out)
  val () = emit_cleanall_clean (out)
  val () = emit_cleanall_rmf_namepat (out, itemname)
} // end of [emit_Makefile_problem60]

(* ****** ****** *)

fun emit_Makefile_problem63
  (out: FILEref): void = emit02_Makefile (out, "problem63-hwxi") // -lm
// end of [emit_Makefile_problem63]

fun emit_Makefile_problem65
  (out: FILEref): void = emit03_Makefile (out, "problem65-hwxi") // -lgmp
// end of [emit_Makefile_problem65]

fun emit_Makefile_problem66
  (out: FILEref): void = emit04_Makefile (out, "problem66-hwxi") // -lgmp -lm
// end of [emit_Makefile_problem66]

fun emit_Makefile_problem69
  (out: FILEref): void = emit01_Makefile (out, "problem69-hwxi")
// end of [emit_Makefile_problem69]

(* ****** ****** *)

fun emit_Makefile_problem71
  (out: FILEref): void = emit01_Makefile (out, "problem71-hwxi")
// end of [emit_Makefile_problem71]

fun emit_Makefile_problem73
  (out: FILEref): void = emit01_Makefile (out, "problem73-hwxi")
// end of [emit_Makefile_problem73]

fun emit_Makefile_problem75
  (out: FILEref): void = emit02_Makefile (out, "problem75-hwxi") // -lm
// end of [emit_Makefile_problem75]

fun emit_Makefile_problem76
  (out: FILEref): void = emit01_Makefile (out, "problem76-hwxi")
// end of [emit_Makefile_problem76]

fun emit_Makefile_problem77
  (out: FILEref): void = emit02_Makefile (out, "problem77-hwxi") // -lm
// end of [emit_Makefile_problem77]

fun emit_Makefile_problem78
  (out: FILEref): void = emit01_Makefile (out, "problem78-hwxi")
// end of [emit_Makefile_problem78]

fun emit_Makefile_problem80
  (out: FILEref): void = emit04_Makefile (out, "problem80-hwxi") // -lgmp -lm
// end of [emit_Makefile_problem80]

(* ****** ****** *)

fun emit_Makefile_problem92
  (out: FILEref): void = emit01_Makefile (out, "problem92-hwxi")
// end of [emit_Makefile_problem92]

fun emit_Makefile_problem94
  (out: FILEref): void = emit02_Makefile (out, "problem94-hwxi") // -lm
// end of [emit_Makefile_problem94]

fun emit_Makefile_problem97
  (out: FILEref): void = emit03_Makefile (out, "problem97-hwxi") // -lgmp
// end of [emit_Makefile_problem97]

(* ****** ****** *)

fun emit_Makefile_problem100
  (out: FILEref): void = emit02_Makefile (out, "problem100-hwxi") // -lm
// end of [emit_Makefile_problem100]

fun emit_Makefile_problem104
  (out: FILEref): void = emit03_Makefile (out, "problem104-hwxi") // -lgmp
// end of [emit_Makefile_problem104]

fun emit_Makefile_problem108
  (out: FILEref): void = emit01_Makefile (out, "problem108-hwxi")
// end of [emit_Makefile_problem108]

fun emit_Makefile_problem110
  (out: FILEref): void = emit02_Makefile (out, "problem110-hwxi") // -lm
// end of [emit_Makefile_problem110]

fun emit_Makefile_problem120
  (out: FILEref): void = emit01_Makefile (out, "problem120-hwxi")
// end of [emit_Makefile_problem120]

fun emit_Makefile_problem122
  (out: FILEref): void = emit02_Makefile (out, "problem122-hwxi") // -lm
// end of [emit_Makefile_problem122]

fun emit_Makefile_problem123
  (out: FILEref): void = emit02_Makefile (out, "problem123-hwxi") // -lm
// end of [emit_Makefile_problem123]

fun emit_Makefile_problem125
  (out: FILEref): void = emit02_Makefile (out, "problem125-hwxi") // -lm
// end of [emit_Makefile_problem125]

fun emit_Makefile_problem145
  (out: FILEref): void = emit01_Makefile (out, "problem145-hwxi")
// end of [emit_Makefile_problem145]

fun emit_Makefile_problem157
  (out: FILEref): void = emit01_Makefile (out, "problem157-hwxi")
// end of [emit_Makefile_problem157]

fun emit_Makefile_problem162
  (out: FILEref): void = emit03_Makefile (out, "problem162-hwxi") // -lgmp
// end of [emit_Makefile_problem162]

fun emit_Makefile_problem164
  (out: FILEref): void = emit01_Makefile (out, "problem164-hwxi")
// end of [emit_Makefile_problem164]

fun emit_Makefile_problem169
  (out: FILEref): void = emit01_Makefile (out, "problem169-hwxi")
// end of [emit_Makefile_problem169]

fun emit_Makefile_problem301
  (out: FILEref): void = emit01_Makefile (out, "problem301-hwxi")
// end of [emit_Makefile_problem301]

(* ****** ****** *)

implement
main (argc, argv) = () where {
  val () = assertloc (argc >= 2)
  val arg1 = argv.[1]
  val () = case+ arg1 of
//
    | "problem1" => emit_Makefile_problem1 (stdout_ref)
    | "problem2" => emit_Makefile_problem2 (stdout_ref)
    | "problem3" => emit_Makefile_problem3 (stdout_ref)
    | "problem4" => emit_Makefile_problem4 (stdout_ref)
    | "problem5" => emit_Makefile_problem5 (stdout_ref)
    | "problem6" => emit_Makefile_problem6 (stdout_ref)
    | "problem7" => emit_Makefile_problem7 (stdout_ref)
    | "problem8" => emit_Makefile_problem8 (stdout_ref)
    | "problem9" => emit_Makefile_problem9 (stdout_ref)
    | "problem10" => emit_Makefile_problem10 (stdout_ref)
//
    | "problem11" => emit_Makefile_problem11 (stdout_ref)
    | "problem12" => emit_Makefile_problem12 (stdout_ref)
    | "problem13" => emit_Makefile_problem13 (stdout_ref)
    | "problem14" => emit_Makefile_problem14 (stdout_ref)
    | "problem15" => emit_Makefile_problem15 (stdout_ref)
    | "problem16" => emit_Makefile_problem16 (stdout_ref)
    | "problem17" => emit_Makefile_problem17 (stdout_ref)
    | "problem18" => emit_Makefile_problem18 (stdout_ref)
    | "problem19" => emit_Makefile_problem19 (stdout_ref)
    | "problem20" => emit_Makefile_problem20 (stdout_ref)
//
    | "problem21" => emit_Makefile_problem21 (stdout_ref)
    | "problem22" => emit_Makefile_problem22 (stdout_ref)
    | "problem23" => emit_Makefile_problem23 (stdout_ref)
    | "problem24" => emit_Makefile_problem24 (stdout_ref)
    | "problem25" => emit_Makefile_problem25 (stdout_ref)
    | "problem26" => emit_Makefile_problem26 (stdout_ref)
    | "problem27" => emit_Makefile_problem27 (stdout_ref)
    | "problem28" => emit_Makefile_problem28 (stdout_ref)
    | "problem29" => emit_Makefile_problem29 (stdout_ref)
    | "problem30" => emit_Makefile_problem30 (stdout_ref)
//
    | "problem31" => emit_Makefile_problem31 (stdout_ref)
    | "problem32" => emit_Makefile_problem32 (stdout_ref)
    | "problem33" => emit_Makefile_problem33 (stdout_ref)
    | "problem34" => emit_Makefile_problem34 (stdout_ref)
    | "problem35" => emit_Makefile_problem35 (stdout_ref)
    | "problem36" => emit_Makefile_problem36 (stdout_ref)
    | "problem37" => emit_Makefile_problem37 (stdout_ref)
    | "problem38" => emit_Makefile_problem38 (stdout_ref)
    | "problem39" => emit_Makefile_problem39 (stdout_ref)
    | "problem40" => emit_Makefile_problem40 (stdout_ref)
//
    | "problem41" => emit_Makefile_problem41 (stdout_ref)
    | "problem42" => emit_Makefile_problem42 (stdout_ref)
    | "problem43" => emit_Makefile_problem43 (stdout_ref)
    | "problem44" => emit_Makefile_problem44 (stdout_ref)
    | "problem45" => emit_Makefile_problem45 (stdout_ref)
    | "problem46" => emit_Makefile_problem46 (stdout_ref)
    | "problem47" => emit_Makefile_problem47 (stdout_ref)
    | "problem48" => emit_Makefile_problem48 (stdout_ref)
    | "problem49" => emit_Makefile_problem49 (stdout_ref)
    | "problem50" => emit_Makefile_problem50 (stdout_ref)
//
    | "problem51" => emit_Makefile_problem51 (stdout_ref)
    | "problem52" => emit_Makefile_problem52 (stdout_ref)
    | "problem53" => emit_Makefile_problem53 (stdout_ref)
    | "problem55" => emit_Makefile_problem55 (stdout_ref)
    | "problem56" => emit_Makefile_problem56 (stdout_ref)
    | "problem57" => emit_Makefile_problem57 (stdout_ref)
    | "problem58" => emit_Makefile_problem58 (stdout_ref)
    | "problem60" => emit_Makefile_problem60 (stdout_ref)
//
    | "problem63" => emit_Makefile_problem63 (stdout_ref)
    | "problem65" => emit_Makefile_problem65 (stdout_ref)
    | "problem66" => emit_Makefile_problem66 (stdout_ref)
    | "problem69" => emit_Makefile_problem69 (stdout_ref)
//
    | "problem71" => emit_Makefile_problem71 (stdout_ref)
    | "problem73" => emit_Makefile_problem73 (stdout_ref)
    | "problem75" => emit_Makefile_problem75 (stdout_ref)
    | "problem76" => emit_Makefile_problem76 (stdout_ref)
    | "problem77" => emit_Makefile_problem77 (stdout_ref)
    | "problem78" => emit_Makefile_problem78 (stdout_ref)
    | "problem80" => emit_Makefile_problem80 (stdout_ref)
//
    | "problem92" => emit_Makefile_problem92 (stdout_ref)
    | "problem94" => emit_Makefile_problem94 (stdout_ref)
    | "problem97" => emit_Makefile_problem97 (stdout_ref)
//
    | "problem100" => emit_Makefile_problem100 (stdout_ref)
    | "problem104" => emit_Makefile_problem104 (stdout_ref)
    | "problem108" => emit_Makefile_problem108 (stdout_ref)
    | "problem110" => emit_Makefile_problem110 (stdout_ref)
    | "problem120" => emit_Makefile_problem120 (stdout_ref)
    | "problem122" => emit_Makefile_problem122 (stdout_ref)
    | "problem123" => emit_Makefile_problem123 (stdout_ref)
    | "problem125" => emit_Makefile_problem125 (stdout_ref)
    | "problem145" => emit_Makefile_problem145 (stdout_ref)
    | "problem157" => emit_Makefile_problem157 (stdout_ref)
    | "problem162" => emit_Makefile_problem162 (stdout_ref)
    | "problem164" => emit_Makefile_problem164 (stdout_ref)
    | "problem169" => emit_Makefile_problem169 (stdout_ref)
    | "problem301" => emit_Makefile_problem301 (stdout_ref)
//
    | _ => ()
  // end of [val]
} // end of [main]

(* ****** ****** *)

(* end of [makefilegen.dats] *)
