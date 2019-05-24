staload "glib.sats"

sta GtkObject : gcls
  sta GtkWidget : gcls
    sta GtkContainer : gcls
      sta GtkBin : gcls
        sta GtkWindow : gcls
          sta GtkDialog : gcls
        sta GtkAlignment : gcls
        sta GtkFrame : gcls
        sta GtkButton : gcls
        sta GtkItem : gcls
          sta GtkMenuItem : gcls
            sta GtkCheckMenuItem : gcls
              sta GtkRadioMenuItem : gcls
            sta GtkImageMenuItem : gcls
            sta GtkSeparatorMenuItem : gcls
            sta GtkTearoffMenuItem : gcls
          sta GtkListItem : gcls
          sta GtkTreeItem : gcls
      // end of [GtkBin]
      sta GtkBox : gcls
        sta GtkButtonBox : gcls
        sta GtkHBox : gcls
        sta GtkVBox : gcls
      sta GtkMenuShell : gcls
        sta GtkMenuBar : gcls
        sta GtkMenu : gcls
      // end of [GtkMenuShell]
      sta GtkTable : gcls
    // end of [GtkContainer]
    sta GtkMisc : gcls
      sta GtkLabel : gcls
      sta GtkArrow : gcls
      sta GtkImage : gcls
      sta GtkPixmap : gcls
    sta GtkSeparator : gcls
      sta GtkHSeparator : gcls
      sta GtkVSeparator : gcls
  // end of [GtkWidget]


// end of [GtkObject]

(* ****** ****** *)

absprop gcls_lte (gcls, gcls)
stadef <= = gcls_lte

(* ****** ****** *)

prval GtkWindowIsGtkWindow : gcls_lte (GtkWindow, GtkWindow)
prval GtkWindowIsGtkBin : gcls_lte (GtkWindow, GtkBin)
prval GtkWindowIsGtkContainer : gcls_lte (GtkWindow, GtkContainer)
prval GtkWindowIsGtkWidget : gcls_lte (GtkWindow, GtkWidget)
prval GtkWindowIsGtkObject : gcls_lte (GtkWindow, GtkObject)

prval GtkButtonIsGtkWidget : gcls_lte (GtkButton, GtkWidget)
prval GtkButtonIsGtkButton : gcls_lte (GtkButton, GtkButton)

//

prval GtkMenuItemIsGtkMenuItem : gcls_lte (GtkMenuItem, GtkMenuItem)
prval GtkMenuItemIsGtkWidget : gcls_lte (GtkMenuItem, GtkWidget)

prval GtkMenuIsGtkWidget : gcls_lte (GtkMenu, GtkWidget)
prval GtkMenuIsGtkMenuShell : gcls_lte (GtkMenu, GtkMenuShell)
prval GtkMenuIsGtkMenu : gcls_lte (GtkMenu, GtkMenu)

//

prval GtkHBoxIsGtkWidget : gcls_lte (GtkHBox, GtkWidget)
prval GtkHBoxIsGtkContainer : gcls_lte (GtkHBox, GtkContainer)
prval GtkHBoxIsGtkBox : gcls_lte (GtkHBox, GtkBox)
prval GtkHBoxIsGtkHBox : gcls_lte (GtkHBox, GtkHBox)

prval GtkVBoxIsGtkWidget : gcls_lte (GtkVBox, GtkWidget)
prval GtkVBoxIsGtkContainer : gcls_lte (GtkVBox, GtkContainer)
prval GtkVBoxIsGtkBox : gcls_lte (GtkVBox, GtkBox)
prval GtkVBoxIsGtkVBox : gcls_lte (GtkVBox, GtkVBox)

prval GtkTableIsGtkWidget : gcls_lte (GtkTable, GtkWidget)
prval GtkTableIsGtkContainer : gcls_lte (GtkTable, GtkContainer)
prval GtkTableIsGtkTable : gcls_lte (GtkTable, GtkTable)

//

prval GtkMiscIsGtkWidget : gcls_lte (GtkMisc, GtkWidget)
prval GtkMiscIsGtkMisc : gcls_lte (GtkMisc, GtkMisc)

prval GtkLabelIsGtkWidget : gcls_lte (GtkLabel, GtkWidget)
prval GtkLabelIsGtkMisc : gcls_lte (GtkLabel, GtkMisc)
prval GtkLabelIsGtkLabel : gcls_lte (GtkLabel, GtkLabel)

prval GtkArrowIsGtkWidget : gcls_lte (GtkArrow, GtkWidget)
prval GtkArrowIsGtkMisc : gcls_lte (GtkArrow, GtkMisc)
prval GtkArrowIsGtkArrow : gcls_lte (GtkArrow, GtkArrow)

prval GtkImageIsGtkWidget : gcls_lte (GtkImage, GtkWidget)
prval GtkImageIsGtkMisc : gcls_lte (GtkImage, GtkMisc)
prval GtkImageIsGtkImage : gcls_lte (GtkImage, GtkImage)

prval GtkPixmapIsGtkWidget : gcls_lte (GtkPixmap, GtkWidget)
prval GtkPixmapIsGtkMisc : gcls_lte (GtkPixmap, GtkMisc)
prval GtkPixmapIsGtkPixmap : gcls_lte (GtkPixmap, GtkPixmap)

//

prval GtkSeparatorIsGtkWidget : gcls_lte (GtkSeparator, GtkWidget)
prval GtkHSeparatorIsGtkWidget : gcls_lte (GtkHSeparator, GtkWidget)
prval GtkVSeparatorIsGtkWidget : gcls_lte (GtkVSeparator, GtkWidget)

//

(* ****** ****** *)

abst@ype GtkWindowType = $extype "GtkWindowType"
macdef GTK_WINDOW_TOPLEVEL = $extval (GtkWindowType, "GTK_WINDOW_TOPLEVEL")
macdef GTK_WINDOW_POPUP = $extval (GtkWindowType, "GTK_WINDOW_POPUP")

abst@ype GtkSortType = $extype "GtkSortType"
macdef GTK_SORT_ASCENDING = $extval (GtkSortType, "GTK_SORT_ASCENDING")
macdef GTK_SORT_DESCENDING = $extval (GtkSortType, "GTK_SORT_DESCENDING")

(* ****** ****** *)

fun gtk_main (): void = "ats_gtk_main"
fun gtk_main_quit (): void = "ats_gtk_main_quit"

(* ****** ****** *)

fun gtk_widget_destroy {c:gcls} {l:addr}
  (pf1: c <= GtkWidget, pf2: gobj c @ l | p: ptr l): void
  = "ats_gtk_widget_destroy"

fun gtk_widget_show {c:gcls} {l:addr}
  (pf: c <= GtkWidget | _: &gobj c): void
  = "ats_gtk_widget_show"

fun gtk_widget_hide {c:gcls} {l:addr}
  (pf: c <= GtkWidget | _: &gobj c): void
  = "ats_gtk_widget_hide"

(* ****** ****** *)

fun gtk_window_new
  (_: GtkWindowType): [l:addr] (gobj (GtkWindow) @ l | ptr l)
  = "ats_gtk_window_new"

fun gtk_dialog_new (): [l:addr] (gobj (GtkDialog) @ l | ptr l)

fun gtk_button_new_with_label
  (_: string): [l:addr] (gobj (GtkButton) @ l | ptr l)
  = "ats_gtk_button_new_with_label"

fun gtk_button_new_with_mnemonic
  (_: string): [l:addr] (gobj (GtkButton) @ l | ptr l)
  = "ats_gtk_button_new_with_mnemonic"

fun gtk_button_set_label {c:gcls}
  (pf: c <= GtkButton | _: &gobj c, _: string): void
  = "ats_gtk_button_set_label"

fun gtk_menu_new (): [l:addr] (gobj (GtkMenu) @ l | ptr l)
  = "ats_gtk_menu_new"

fun gtk_menu_item_new_with_label
  (_: string): [l:addr] (gobj (GtkMenuItem) @ l | ptr l)
  = "ats_gtk_menu_item_new_with_label"

//

fun gtk_hbox_new (homogeneous: gboolean, spacing: int)
  : [l:addr] (gobj GtkHBox @ l | ptr l)
  = "ats_gtk_hbox_new"

fun gtk_vbox_new (homogeneous: gboolean, spacing: int)
  : [l:addr] (gobj GtkVBox @ l | ptr l)
  = "ats_gtk_vbox_new"

fun gtk_table_new (nrow: Nat, ncol: Nat, homogeneous: gboolean)
  : [l:addr] (gobj GtkTable @ l | ptr l)
  = "ats_gtk_table_new"

//

fun gtk_label_new (text: string)
  : [l:addr] (gobj GtkLabel @ l | ptr l)
  = "ats_gtk_label_new"

//

fun gtk_hseparator_new ()
  : [l:addr] (gobj GtkHSeparator @ l | ptr l)
  = "ats_gtk_hseparator_new"

fun gtk_vseparator_new ()
  : [l:addr] (gobj GtkVSeparator @ l | ptr l)
  = "ats_gtk_vseparator_new"

(* ****** ****** *)

fun gtk_toplevel_add {c:gcls} {l:addr}
  (pf1: c <= GtkWidget, pf2: gobj c @ l | p: ptr l): void
  = "ats_gtk_toplevel_add"

fun gtk_container_add {c1,c2:gcls} {l:addr}
  (pf1: c1 <= GtkContainer, pf2: c2 <= GtkWidget, pf3: gobj c2 @ l |
   _: &gobj c1, p: ptr l)
  : void
  = "ats_gtk_container_add"

fun gtk_container_add_ref {c1,c2:gcls}
  (pf1: c1 <= GtkContainer, pf2: c2 <= GtkWidget |
   _: &gobj c1, _: &gobj c2)
  : void
  = "ats_gtk_container_add_ref"

//

fun gtk_menu_shell_append {c1,c2:gcls} {l:addr}
  (pf1: c1 <= GtkMenuShell, pf2: c2 <= GtkMenuItem, pf3: gobj c2 @ l |
   _: &gobj c1, p: ptr l)
  : void
  = "ats_gtk_menu_shell_append"

fun gtk_menu_shell_prepend {c1,c2:gcls} {l:addr}
  (pf1: c1 <= GtkMenuShell, pf2: c2 <= GtkMenuItem, pf3: gobj c2 @ l |
   _: &gobj c1, p: ptr l)
  : void
  = "ats_gtk_menu_shell_prepend"

//

fun gtk_box_pack_start
  {c1,c2:gcls} {l:addr}
  (pf1: c1 <= GtkBox,
   pf2: c2 <= GtkWidget,
   pf3: gobj c2 @ l |
   box: &gobj c1,
   widget: ptr l,
   expand: gboolean,
   fill: gboolean,
   padding: Nat)
  : void
  = "ats_gtk_box_pack_start"

fun gtk_box_pack_end
  {c1,c2:gcls} {l:addr}
  (pf1: c1 <= GtkBox,
   pf2: c2 <= GtkWidget,
   pf3: gobj c2 @ l |
   box: &gobj c1,
   widget: ptr l,
   expand: gboolean,
   fill: gboolean,
   padding: Nat)
  : void
  = "ats_gtk_box_pack_end"

fun gtk_table_attach_defaults
  {c1,c2:gcls} {l:addr}
  (pf1: c1 <= GtkTable,
   pf2: c2 <= GtkWidget,
   pf3: gobj c2 @ l |
   table: &gobj c1,
   widget: ptr l,
   left_attach: Nat,
   right_attach: Nat,
   top_attach: Nat,
   bottom_attach: Nat)
  : void
  = "ats_gtk_table_attach_defaults"

(* ****** ****** *)

fun gtk_container_set_border_width {c:gcls}
  (pf: c <= GtkContainer | _: &gobj c, _: Nat): void
  = "ats_gtk_container_set_border_width"

fun gtk_widget_set_size_request {c:gcls}
  (pf: c <= GtkWidget | _: &gobj c, _: int, _: int): void
  = "ats_gtk_widget_set_size_request"

fun gtk_table_set_row_spacing {c:gcls}
  (pf: c <= GtkTable | _: &gobj c, _: Nat, _: Nat): void
  = "ats_gtk_table_set_row_spacing"

fun gtk_table_set_col_spacing {c:gcls}
  (pf: c <= GtkTable | _: &gobj c, _: Nat, _: Nat): void
  = "ats_gtk_table_set_col_spacing"

(* ****** ****** *)

(* end of [gtk.sats] *)
