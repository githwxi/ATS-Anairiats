(*
**
** A basic example taken from the O'Reily book
** on Xlib programming (programmer's manual)
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: February, 2010
**
*)

(* ****** ****** *)

staload "contrib/X11/SATS/X.sats"
staload "contrib/X11/SATS/Xlib.sats"

(* ****** ****** *)

%{^
#include "bitmaps/icon_bitmap"
%} // end of [%{^]

(* ****** ****** *)

#define BITMAPDEPTH 1
#define TOO_SMALL 0
#define BIG_ENOUGH 1

(* ****** ****** *)

symintr uint
overload uint with uint_of_int // no-op casting

(* ****** ****** *)

fun load_font {l_dpy:agz}
  (display: !Display_ptr l_dpy)
  : [l:addr] (XFreeFont_v l, XFontStruct @ l | ptr l)
  = let
  val fontname = "9x15"
  val (pf_free, pfopt | p) = XLoadQueryFont (display, fontname)
  val () = assert_errmsg (p <> null, #LOCATION)
  prval Some_v pf = pfopt
in
  (pf_free, pf | p)
end // end of [load_font]

(* ****** ****** *)

fun getGC {l:agz} (
    display: !Display_ptr l
  , screen_num: int
  , win: Window, gc: &ptr? >> GCptr1, font_info: &XFontStruct
  ) : void = () where {
  val valuemask = 0UL // Ignore XGCvalues and use defaults
  var values: XGCValues
  val () = gc := XCreateGC (display, (Drawable)win, valuemask, values)
  val () = XSetFont(display, gc, font_info.fid)
(*
** Specify black foreground since default window background is white
** and default foreground is undefined
*)
  val () =
    XSetForeground (display, gc, b_pix) where {
    val b_pix = XBlackPixel (display, screen_num)
  } // end of [val]
  val () = XSetLineAttributes (
    display, gc, line_width, line_style, cap_style, join_style
  ) where {
    val line_width = 6U
    val line_style = LineOnOffDash
    val cap_style = CapRound
    val join_style = JoinRound
  } // end of [val]
  val () = XSetDashes (
    display, gc, dash_offset, !p_dash_list, list_length
  ) where {
    val dash_offset = 0
    #define i2c char_of_int
    var !p_dash_list = @[char]((i2c)12, (i2c)24)
    val list_length = 2
  } // end of [val]
} // end of [getGC]

(* ****** ****** *)

staload PRINTF = "libc/SATS/printf.sats"

(* ****** ****** *)

symintr int
overload int with int1_of_size1 // no-op casting

fun place_text {l1,l2:agz} (
    display: !Display_ptr l1
  , screen_num: int
  , win: Window
  , gc: !GCptr l2
  , ftinfo: &XFontStruct
  , win_width: int, win_height: int
  ) : void = let
//
  val string1 = "Hi! I'm a window, who are you?"
  val string2 = "To terminate program; Press any key"
  val string3 = "or button while in this window."
//
  val len1 = string_length (string1)
  val len1 = (int)len1
  val len2 = string_length (string2)
  val len2 = (int)len2
  val len3 = string_length (string3)
  val len3 = (int)len3
  val width1 = XTextWidth(ftinfo, string1, len1)
  val width2 = XTextWidth(ftinfo, string2, len2)
  val width3 = XTextWidth(ftinfo, string3, len3)
//
  val font_height = ftinfo.ascent + ftinfo.descent
//
  val () = XDrawString (
    display, (Drawable)win, gc, (win_width - width1)/2, font_height, string1, len1
  ) // end of [val]
  val () = XDrawString (
    display, (Drawable)win, gc, (win_width - width2)/2, win_height-2*font_height, string2, len2
  ) // end of [val]
  val () = XDrawString (
    display, (Drawable)win, gc, (win_width - width3)/2, win_height-font_height, string3, len3
  ) // end of [val]
//
  val string4 = "Screen Dimensions:"
  val len4 = string_length (string4)
  val len4 = (int)len4
//
  #define NBUF 64
  var !p_cd_height with pf_cd_height = @[byte][NBUF]()
  var !p_cd_width with pf_cd_width = @[byte][NBUF]()
  var !p_cd_depth with pf_cd_depth = @[byte][NBUF]()
//
  var x_offset: int = win_width/4;
  var y_offset: int = win_height/2 - font_height - ftinfo.descent
//
  val _n = $PRINTF.snprintf (
    pf_cd_height | p_cd_height, NBUF, " Height - %d pixels", @(height)
  ) where {
    val height = XDisplayHeight (display, screen_num)
  } // end of [val]
  val len1 = strbuf_length (!p_cd_height)
  val len1 = (int)len1
//
  val _n = $PRINTF.snprintf (
    pf_cd_width | p_cd_width, NBUF, " Width - %d pixels", @(width)
  ) where {
    val width = XDisplayWidth (display, screen_num)
  } // end of [val]
  val len2 = strbuf_length (!p_cd_width)
  val len2 = (int)len2
//
  val _n = $PRINTF.snprintf (
    pf_cd_depth | p_cd_depth, NBUF, " Depth - %d pixels", @(depth)
  ) where {
    val depth = XDefaultDepth (display, screen_num)
  } // end of [val]
  val len3 = strbuf_length (!p_cd_depth)
  val len3 = (int)len3
//
  val () = XDrawString
    (display, (Drawable)win, gc, x_offset, y_offset, string4, len4)
  val () = y_offset := y_offset + font_height
//
  extern castfn __cast {m,n:nat} (p: &strbuf (m, n)): string n
  val () = XDrawString (
    display, (Drawable)win, gc, x_offset, y_offset, string, len1
  ) where {
    val string = __cast (!p_cd_height)
  } // end of [val]
  val () = y_offset := y_offset + font_height
//
  val () = XDrawString (
    display, (Drawable)win, gc, x_offset, y_offset, string, len2
  ) where {
    val string = __cast (!p_cd_width)
  } // end of [val]
  val () = y_offset := y_offset + font_height
//
  val () = XDrawString (
    display, (Drawable)win, gc, x_offset, y_offset, string, len3
  ) where {
    val string = __cast (!p_cd_depth)
  } // end of [val]
  val () = y_offset := y_offset + font_height
//  
  prval () = pf_cd_height := bytes_v_of_strbuf_v (pf_cd_height)
  prval () = pf_cd_width := bytes_v_of_strbuf_v (pf_cd_width)
  prval () = pf_cd_depth := bytes_v_of_strbuf_v (pf_cd_depth)
//
in
  // nothing
end // end of [place_text]

(* ****** ****** *)

fun place_graphics {l1,l2:agz} (
    display: !Display_ptr l1
  , win: Window
  , gc: !GCptr l2
  , window_width: int
  , window_height: int
  ) : void = let
  val width =
    3 * window_width / 4
  val height = window_height / 2
  val x = window_width / 2 - width / 2
  val y = window_height / 2 - height / 2
in
  XDrawRectangle (display, (Drawable)win, gc, x, y, (uint)width, (uint)height)
end // end of [place_graphics]

(* ****** ****** *)

fun TooSmall {l1,l2:agz} (
    display: !Display_ptr l1
  , win: Window
  , gc: !GCptr l2
  , ftinfo: &XFontStruct
  ) : void = let
  val string1 = "Too Small"
  val len1 = string_length (string1)
  val len1 = (int)len1
  val x_offset = 2
  val y_offset = ftinfo.ascent + 2
in
   XDrawString (
     display, (Drawable)win, gc, x_offset, y_offset, string1, len1
   ) // end of [XDrawString]
end // end of [TooSmall]

(* ****** ****** *)

implement main (argc, argv) = () where {
  val progname = argv.[0]
//
  var window_size: int = TOO_SMALL
//
  val xpszhnt = XAllocSizeHints ()
  val pszhnt = ptr_of (xpszhnt)
  val () = assert_errmsg (pszhnt > null, #LOCATION)
  prval (pfszhnt_at, fpfszhnt) = XPtr_viewget (xpszhnt)
//
  val xpwmhnt = XAllocWMHints ()
  val pwmhnt = ptr_of (xpwmhnt)
  val () = assert_errmsg (pwmhnt > null, #LOCATION)
  prval (pfwmhnt_at, fpfwmhnt) = XPtr_viewget (xpwmhnt)
//
  val xpcshnt = XAllocClassHint ()
  val pcshnt = ptr_of (xpcshnt)
  val () = assert_errmsg (pcshnt > null, #LOCATION)
  prval (pfcshnt_at, fpfcshnt) = XPtr_viewget (xpcshnt)
//
  val display_name = (case+ 0 of
    | _ when argc >= 2 => stropt_some (string1_of_string argv.[1])
    | _ => stropt_none // using the default
  ) : Stropt
  val [l_dpy:addr] display = XOpenDisplay (display_name)
  val () = assert_errmsg (Display_ptr_isnot_null display, #LOCATION)
  val screen_num = XDefaultScreen (display)
  val display_width = XDisplayWidth (display, screen_num)
(*
  val () = begin
    print "display_width = "; print display_width; print_newline ()
  end // end of [val]
*)
  val display_height = XDisplayHeight (display, screen_num)
(*
  val () = begin
    print "display_height = "; print display_height; print_newline ()
  end // end of [val]
*)
//
  var x: int = 0 and y: int = 0
  var width: int = display_width/3
  and height: int = display_height/4
//
  val border_width = 4
  val win = XCreateSimpleWindow (
    display, parent, x, y
  , (uint)width, (uint)height, (uint)border_width, b_pix, w_pix
  ) where {
    val parent = XRootWindow (display, screen_num)
    val b_pix = XBlackPixel (display, screen_num)
    val w_pix = XWhitePixel (display, screen_num)
  }  // end of [val]
//
  val icon_pixmap = XCreateBitmapFromData (
    display, (Drawable)win, icon_bitmap_bits, icon_bitmap_width, icon_bitmap_height
  ) where {
    val icon_bitmap_width = $extval (uint, "icon_bitmap_width")
    val icon_bitmap_height = $extval (uint, "icon_bitmap_height")
    val icon_bitmap_bits = $extval (ptr, "icon_bitmap_bits")
  } // end of [icon_pixmap]
//
   val () = pszhnt->flags := (PPosition lor PSize lor PMinSize)
   val () = pszhnt->min_width := 300
   val () = pszhnt->min_height := 200
   prval pfszhnt_at = __cast (pfszhnt_at) where {
     extern prfun __cast {l:addr} (pf: XSizeHints? @ l): XSizeHints @ l
   }
//
   var windowName: XTextProperty and iconName: XTextProperty
//
   val window_name = "Basic Window Program"
   val (pf1_free | status) = XStringToTextProperty(window_name, windowName)
   val () = assert_errmsg ((int_of)status <> 0, #LOCATION)
   stavar _:addr
   prval () = opt_unsome {XTextProperty _} (windowName)
//
   val icon_name = "basicwin"
   val (pf2_free | status) = XStringToTextProperty(icon_name, iconName)
   val () = assert_errmsg ((int_of)status <> 0, #LOCATION)
   stavar _:addr
   prval () = opt_unsome {XTextProperty _} (iconName)
//
   val () = pwmhnt->initial_state := NormalState
   val () = pwmhnt->input := true
   val () = pwmhnt->icon_pixmap := icon_pixmap
   val () = pwmhnt->flags := (StateHint lor IconPixmapHint lor InputHint)
   prval pfwmhnt_at = __cast (pfwmhnt_at) where {
     extern prfun __cast {l:addr} (pf: XWMHints? @ l): XWMHints @ l
   }
//
   val () = pcshnt->res_name := progname
   val () = pcshnt->res_class := "Basicwin"
   val () = XSetWMProperties
     (display, win, windowName, iconName, argv, argc, !pszhnt, !pwmhnt, !pcshnt)
   // end of [XSetWMProperties]
//
   val () = XFree (pf1_free | windowName.value)
   val () = XFree (pf2_free | iconName.value)
//
  val () = XSelectInput (display, win, flag) where {
    val flag = ExposureMask lor KeyPressMask lor ButtonPressMask lor StructureNotifyMask
  } // end of [val]
//
  var gc: GCptr1 // unintialized
  val [l_ftinfo:addr]
    (pf_free, pf_ftinfo | p_ftinfo) = load_font (display)
  val () = getGC (display, screen_num, win, gc, !p_ftinfo)
  val () = XMapWindow(display, win)
//
  var report: XEvent? // uninitialized
  val () = while (true) let
    val () = XNextEvent (display, report)
    val type = report.type
  in
    case+ 0 of
    | _ when (type = Expose) => begin
        case+ 0 of
        | _ when window_size = TOO_SMALL =>
            TooSmall (display, win, gc, !p_ftinfo)
          // end of [TOO_SMALL]
        | _ => () where { // BIG_ENOUGH
            val () = place_text
              (display, screen_num, win, gc, !p_ftinfo, width, height)
            val () = place_graphics (display, win, gc, width, height)
          } // end of [BIG_ENOUGH]
      end // end of [Expose]
    | _ when (type = ConfigureNotify) => let
        prval (pf, fpf) = XEvent_xconfigure_castdn (view@ report)
        val width = (&report)->width
        val height = (&report)->height
        prval () = view@ report := fpf (pf)
      in
        if (width < pszhnt->min_width) then
          window_size := TOO_SMALL
        else if (height < pszhnt->min_height) then
          window_size := TOO_SMALL
        else window_size := BIG_ENOUGH
      end // end of [ConfigureNotify]
    | _ when (type = ButtonPress orelse type = KeyPress) => (break)
    | _ => () // ignored
  end // end of [val]
//
  val () = XFreeFont
    (pf_free, pf_ftinfo | display, p_ftinfo)
  prval () = minus_addback (fpfszhnt, pfszhnt_at | xpszhnt)
  val () = XFree (xpszhnt)
  prval () = minus_addback (fpfwmhnt, pfwmhnt_at | xpwmhnt)
  val () = XFree (xpwmhnt)
  prval () = minus_addback (fpfcshnt, pfcshnt_at | xpcshnt)
  val () = XFree (xpcshnt)
//
  val () = XFreeGC (display, gc)
  val () = XCloseDisplay (display)
} // end of [main]

(* ****** ****** *)

////

(* ****** ****** *)

//
// HX-2010-02-17:
// For a quick reference, I attach as follows
// the original code taken from the O'Reily book on
// Xlib Programming.
//

(* ****** ****** *)

#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/Xos.h>
#include <X11/Xatom.h>
#include <stdio.h>
#include "bitmaps/icon_bitmap"
#define BITMAPDEPTH 1
#define TOO_SMALL 0
#define BIG_ENOUGH 1
/* These are used as arguments to nearly every Xlib routine, so it
 * saves routine arguments to declare them global; if there were
 * additional source files, they would be declared extern there */
Display *display;
int screen_num;
/* progname is the string by which this program was invoked; this
 * is global because it is needed in most application functions */
static char *progname;
void main(argc, argv)
int argc;
char **argv;
{
   Window win;
   unsigned int width, height;     /* Window size */
   int x, y;                       /* Window position */
   unsigned int border_width = 4;  /* Four pixels */
   unsigned int display_width, display_height;
   unsigned int icon_width, icon_height;
   char *window_name = "Basic Window Program";
   char *icon_name = "basicwin";
   Pixmap icon_pixmap;
   XSizeHints *size_hints;
   XIconSize *size_list;
   XWMHints *wm_hints;
   XClassHint *class_hints;
   XTextProperty windowName, iconName;
   int count;
   XEvent report;
   GC gc;
   XFontStruct *font_info;
   char *display_name = NULL;
   int window_size = 0;         /* BIG_ENOUGH or TOO_SMALL to
                         * display contents */
   progname = argv[0];
   if (!(size_hints = XAllocSizeHints())) {
      fprintf(stderr, "%s: failure allocating memory, progname);
        exit(0);
   }
   if (!(wm_hints = XAllocWMHints())) {
      fprintf(stderr, "%s: failure allocating memory, progname);
        exit(0);
   }
   if (!(class_hints = XAllocClassHint())) {
      fprintf(stderr, "%s: failure allocating memory, progname);
        exit(0);
   }
   /* Connect to X server */
   if ( (display=XOpenDisplay(display_name)) == NULL )
   {
      (void) fprintf( stderr, "%s: cannot connect to X server %s\n",
            progname, XDisplayName(display_name));
      exit( -1 );
   }
   /* Get screen size from display structure macro */
   screen_num = DefaultScreen(display);
   display_width = DisplayWidth(display, screen_num);
   display_height = DisplayHeight(display, screen_num);
   /* Note that in a real application, x and y would default
    * to 0 but would be settable from the command line or
    * resource database */
   x = y = 0;
   /* Size window with enough room for text */
   width = display_width/3, height = display_height/4;
   /* Create opaque window */
   win = XCreateSimpleWindow(display, RootWindow(display,screen_num),
         x, y, width, height, border_width, BlackPixel(display,
         screen_num), WhitePixel(display,screen_num));
   /* Get available icon sizes from window manager */
   if (XGetIconSizes(display, RootWindow(display,screen_num),
         &size_list, &count) == 0)
      (void) fprintf( stderr, "%s: Window manager didn't set \
            icon sizes - using default.\n", progname);
   else {
      ;
      /* A real application would search through size_list
       * here to find an acceptable icon size and then
       * create a pixmap of that size; this requires that
       * the application have data for several sizes of icons */
   }
   /* Create pixmap of depth 1 (bitmap) for icon */
   icon_pixmap = XCreateBitmapFromData(display, win,
         icon_bitmap_bits, icon_bitmap_width,
         icon_bitmap_height);
   /* Set size hints for window manager; the window manager
    * may override these settings */
   /* Note that in a real application, if size or position
    * were set by the user, the flags would be USPosition
    * and USSize and these would override the window manager's
    * preferences for this window */
   /* x, y, width, and height hints are now taken from
    * the actual settings of the window when mapped; note
    * that PPosition and PSize must be specified anyway */
   size_hints->flags = PPosition | PSize | PMinSize;
   size_hints->min_width = 300;
   size_hints->min_height = 200;
   /* These calls store window_name and icon_name into
    * XTextProperty structures and set their other fields
    * properly */
   if (XStringListToTextProperty(&window_name, 1, &windowName) == 0) {
      (void) fprintf( stderr, "%s: structure allocation for \
            windowName failed.\n", progname);
      exit(-1);
   }

   if (XStringListToTextProperty(&icon_name, 1, &iconName) == 0) {
      (void) fprintf( stderr, "%s: structure allocation for \
            iconName failed.\n", progname);
      exit(-1);
   }
   wm_hints->initial_state = NormalState;
   wm_hints->input = True;
   wm_hints->icon_pixmap = icon_pixmap;
   wm_hints->flags = StateHint | IconPixmapHint | InputHint;
   class_hints->res_name = progname;
   class_hints->res_class = "Basicwin";
   XSetWMProperties(display, win, &windowName, &iconName,
         argv, argc, size_hints, wm_hints,
         class_hints);
   }
   /* Select event types wanted */
   XSelectInput(display, win, ExposureMask | KeyPressMask |
         ButtonPressMask | StructureNotifyMask);
   load_font(&font_info);
   /* Create GC for text and drawing */
   getGC(win, &gc, font_info);
   /* Display window */
   XMapWindow(display, win);
   /* Get events, use first to display text and graphics */
   while (1)  {
      XNextEvent(display, &report);
      switch  (report.type) {
      case Expose:
         /* Unless this is the last contiguous expose,
          * don't draw the window */
         if (report.xexpose.count != 0)
            break;
         /* If window too small to use */
         if (window_size == TOO_SMALL)
            TooSmall(win, gc, font_info);
         else {
            /* Place text in window */
            place_text(win, gc, font_info, width, height);
            /* Place graphics in window */
            place_graphics(win, gc, width, height);
         }
         break;
      case ConfigureNotify:
         /* Window has been resized; change width
          * and height to send to place_text and
          * place_graphics in next Expose */
         width = report.xconfigure.width;
         height = report.xconfigure.height;
         if ((width < size_hints->min_width) ||
               (height < size_hints->min_height))
            window_size = TOO_SMALL;
         else
            window_size = BIG_ENOUGH;
         break;
      case ButtonPress:
         /* Trickle down into KeyPress (no break) */
      case KeyPress:
         XUnloadFont(display, font_info->fid);
         XFreeGC(display, gc);
         XCloseDisplay(display);
         exit(1);
      default:
         /* All events selected by StructureNotifyMask
          * except ConfigureNotify are thrown away here,
          * since nothing is done with them */
         break;
      } /* End switch */
   } /* End while */
}

getGC(win, gc, font_info)
Window win;
GC *gc;
XFontStruct *font_info;
{
   unsigned long valuemask = 0; /* Ignore XGCvalues and
                         * use defaults */
   XGCValues values;
   unsigned int line_width = 6;
   int line_style = LineOnOffDash;
   int cap_style = CapRound;
   int join_style = JoinRound;
   int dash_offset = 0;
   static char dash_list[] = {12, 24};
   int list_length = 2;
   /* Create default Graphics Context */
   *gc = XCreateGC(display, win, valuemask, &values);
   /* Specify font */
   XSetFont(display, *gc, font_info->fid);
   /* Specify black foreground since default window background
    * is white and default foreground is undefined */
   XSetForeground(display, *gc, BlackPixel(display,screen_num));
   /* Set line attributes */
   XSetLineAttributes(display, *gc, line_width, line_style,
         cap_style, join_style);
   /* Set dashes */
   XSetDashes(display, *gc, dash_offset, dash_list, list_length);
}
load_font(font_info)
XFontStruct **font_info;
{
   char *fontname = "9x15";
   /* Load font and get font information structure */
   if ((*font_info = XLoadQueryFont(display,fontname)) == NULL)
   {
      (void) fprintf( stderr, "%s: Cannot open 9x15 font\n",
            progname);
      exit( -1 );
   }
}

place_text(win, gc, font_info, win_width, win_height)
Window win;
GC gc;
XFontStruct *font_info;
unsigned int win_width, win_height;
{
   char *string1 = "Hi! I'm a window, who are you?";
   char *string2 = "To terminate program; Press any key";
   char *string3 = "or button while in this window.";
   char *string4 = "Screen Dimensions:";
   int len1, len2, len3, len4;
   int width1, width2, width3;
   char cd_height[50], cd_width[50], cd_depth[50];
   int font_height;
   int initial_y_offset, x_offset;
   /* Need length for both XTextWidth and XDrawString */
   len1 = strlen(string1);
   len2 = strlen(string2);
   len3 = strlen(string3);
   /* Get string widths for centering */
   width1 = XTextWidth(font_info, string1, len1);
   width2 = XTextWidth(font_info, string2, len2);
   width3 = XTextWidth(font_info, string3, len3);
   font_height = font_info->ascent + font_info->descent;
   /* Output text, centered on each line */
   XDrawString(display, win, gc, (win_width - width1)/2,
         font_height,
         string1, len1);
   XDrawString(display, win, gc, (win_width - width2)/2,
         (int)(win_height - (2 * font_height)),
         string2, len2);
   XDrawString(display, win, gc, (win_width - width3)/2,
         (int)(win_height - font_height),
         string3, len3);
   /* Copy numbers into string variables */
   (void) sprintf(cd_height, " Height - %d pixels",
         DisplayHeight(display,screen_num));
   (void) sprintf(cd_width, " Width  - %d pixels",
         DisplayWidth(display,screen_num));
   (void) sprintf(cd_depth, " Depth  - %d plane(s)",
         DefaultDepth(display, screen_num));
   /* Reuse these for same purpose */
   len4 = strlen(string4);
   len1 = strlen(cd_height);
   len2 = strlen(cd_width);
   len3 = strlen(cd_depth);
   /* To center strings vertically, we place the first string
    * so that the top of it is two font_heights above the center
    * of the window; since the baseline of the string is what
    * we need to locate for XDrawString and the baseline is
    * one font_info -> ascent below the top of the character,
    * the final offset of the origin up from the center of
    * the window is one font_height + one descent */
   initial_y_offset = win_height/2 - font_height -
         font_info->descent;
   x_offset = (int) win_width/4;
   XDrawString(display, win, gc, x_offset, (int) initial_y_offset,
         string4,len4);
   XDrawString(display, win, gc, x_offset, (int) initial_y_offset +
         font_height,cd_height,len1);
   XDrawString(display, win, gc, x_offset, (int) initial_y_offset +
         2 * font_height,cd_width,len2);
   XDrawString(display, win, gc, x_offset, (int) initial_y_offset +
         3 * font_height,cd_depth,len3);
}

place_graphics(win, gc, window_width, window_height)
Window win;
GC gc;
unsigned int window_width, window_height;
{
   int x, y;
   int width, height;
   height = window_height/2;
   width = 3 * window_width/4;
   x = window_width/2 - width/2;  /* Center */
   y = window_height/2 - height/2;
   XDrawRectangle(display, win, gc, x, y, width, height);
}

TooSmall(win, gc, font_info)
Window win;
GC gc;
XFontStruct *font_info;
{
   char *string1 = "Too Small";
   int y_offset, x_offset;
   y_offset = font_info->ascent + 2;
   x_offset = 2;
   /* Output text, centered on each line */
   XDrawString(display, win, gc, x_offset, y_offset, string1,
         strlen(string1));
}
