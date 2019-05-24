(*
**
** A simple example for testing some Xlib functions
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: January, 2010
**
*)

(* ****** ****** *)

staload "contrib/X11/SATS/X.sats"
staload "contrib/X11/SATS/Xlib.sats"

(* ****** ****** *)

implement main () = () where {
  val dpy = XOpenDisplay (stropt_none)
  val () = assertloc (Display_ptr_isnot_null dpy)
  val bpxl = XBlackPixel (dpy, 0)
  val () = (print "bpxl = "; print bpxl; print_newline ())
  val wpxl = XWhitePixel (dpy, 0)
  val () = (print "wpxl = "; print wpxl; print_newline ())
  val nconn = XConnectionNumber (dpy)
  val () = (print "nconn = "; print nconn; print_newline ())
  val colormap = XDefaultColormap (dpy, 0)
  val () = let
    val xid = __cast (colormap) where {
      extern castfn __cast (x: Colormap):<> ulint
    }
  in
    print "colormap = "; print xid; print_newline ()
  end // end of [val]
  val depth = XDefaultDepth (dpy, 0)
  val () = (print "depth = "; print depth; print_newline ())
//
  var asz: int
  val xarr = XListDepths (dpy, 0, asz)
  val p_arr = ptr_of (xarr)
  val () = assertloc (p_arr > null)
  prval () = opt_unsome (asz)
  val () = (print "asz = "; print_int asz; print_newline ())
  val () = (print "p_arr = "; print p_arr; print_newline ())
  val () = XFree (xarr)
//
  val gc = XDefaultGC (dpy, 0)
//
  val window = XDefaultRootWindow (dpy)
  val () = let
    val xid = __cast (window) where {
      extern castfn __cast (x: Window):<> ulint
    }
  in
    print "window = "; print xid; print_newline ()
  end // end of [val]
//
  val nscr = XDefaultScreen (dpy)
  val () = (print "nscr = "; print nscr; print_newline ())
//
  val ncell = XDisplayCells (dpy, 0)
  val () = (print "ncell = "; print ncell; print_newline ())
//
  val nplane = XDisplayPlanes (dpy, 0)
  val () = (print "nplane = "; print nplane; print_newline ())
//
  val name = XDisplayString (dpy)
  val () = (print "name = "; print name; print_newline ())
//
  val maxsz = XMaxRequestSize (dpy)
  val () = (print "maxsz = "; print maxsz; print_newline ())
//
  val version = XProtocolVersion (dpy)
  val () = (print "version = "; print version; print_newline ())
  val revision = XProtocolRevision (dpy)
  val () = (print "revision = "; print revision; print_newline ())
  val vendor = XServerVendor (dpy)
  val () = (print "vendor = "; print vendor; print_newline ())
  val release = XVendorRelease (dpy)
  val () = (print "release = "; print release; print_newline ())
//
  val last = XLastKnownRequestProcessed (dpy)
  val () = (print "last = "; print last; print_newline ())
  val next = XNextRequest (dpy)
  val () = (print "next = "; print next; print_newline ())
//
  val nque = XQLength (dpy)
  val () = (print "nque = "; print nque; print_newline ())
//
  val rtwin = XRootWindow (dpy, 0)
  val () = let
    val xid = __cast (rtwin) where {
      extern castfn __cast (x: Window):<> ulint
    }
  in
    print "rtwin = "; print xid; print_newline ()
  end // end of [val]
//
  val scrcnt = XScreenCount (dpy)
  val () = (print "scrcnt = "; print scrcnt; print_newline ())
//
  val ht = XDisplayHeight (dpy, 0)
  val () = (print "ht = "; print ht; print_newline ())
  val ht_mm = XDisplayHeightMM (dpy, 0)
  val () = (print "ht_mm = "; print ht_mm; print_newline ())
  val wd = XDisplayWidth (dpy, 0)
  val () = (print "wd = "; print wd; print_newline ())
  val wd_mm = XDisplayWidthMM (dpy, 0)
  val () = (print "wd_mm = "; print wd_mm; print_newline ())
//
  val win = XCreateSimpleWindow (dpy, rtwin, 0, 0, 100U, 100U, 0U, 0UL, 0UL)
  val () = XMapWindow (dpy, win)
  val () = XRaiseWindow (dpy, win)
  val () = XFlush (dpy)
  // val () = XDestroyWindow (dpy, win)
  val _ = sleep (5u) where {
    staload "libc/SATS/unistd.sats"
  }
//
  val () = XCloseDisplay (dpy)
} // end of [main]

(* ****** ****** *)

(* end of [Xlib-test01.dats] *)
