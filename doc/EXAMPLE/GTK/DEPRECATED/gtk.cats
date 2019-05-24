#include <gtk/gtk.h>
#include <glib-object.h>

static inline
ats_void_type
ats_gtk_main () { gtk_main () ;  return ; }

static inline
ats_void_type
ats_gtk_main_quit () { gtk_main_quit () ;  return ; }

/* ****** ****** */

static inline
ats_void_type
ats_gtk_widget_destroy (ats_ptr_type wid) {
  return gtk_widget_destroy ((GtkWidget *)wid) ;
}

static inline
ats_void_type
ats_gtk_widget_show (ats_ptr_type wid) {
  gtk_widget_show ((GtkWidget *)wid) ; return ;
}

/* ****** ****** */

static inline
ats_ptr_type
ats_gtk_window_new (GtkWindowType type) {
  return gtk_window_new (type) ;
}

static inline
ats_ptr_type
ats_gtk_dialog_new () { return gtk_dialog_new () ; }

/* ****** ****** */

static inline
ats_ptr_type
ats_gtk_button_new_with_label (ats_ptr_type label) {
  GtkWidget* button ;
  button = gtk_button_new_with_label ((gchar*)label) ;
  g_object_ref (button) ;
  gtk_object_sink ((GtkObject*)button) ;
  return button ;
}

static inline
ats_ptr_type
ats_gtk_button_new_with_mnemonic (ats_ptr_type label) {
  GtkWidget* button ;
  button = gtk_button_new_with_mnemonic ((gchar*)label) ;
  g_object_ref (button) ;
  gtk_object_sink ((GtkObject*)button) ;
  return button ;
}

static inline
ats_void_type
ats_gtk_button_set_label (ats_ptr_type button, ats_ptr_type label) {
  gtk_button_set_label ((GtkButton*)button, (gchar*)label) ;
  return ;
}

static inline
ats_ptr_type ats_gtk_menu_new () {
  GtkWidget* menu ;
  menu = gtk_menu_new () ;
  g_object_ref (menu) ;
  gtk_object_sink ((GtkObject*)menu) ;
  return menu ;
}

static inline
ats_ptr_type
ats_gtk_menu_item_new_with_label (ats_ptr_type label) {
  GtkWidget* menu_item ;
  menu_item = gtk_menu_item_new_with_label ((gchar*)label) ;
  g_object_ref (menu_item) ;
  gtk_object_sink ((GtkObject*)menu_item) ;
  return menu_item ;
}

//

static inline
ats_ptr_type
ats_gtk_hbox_new (gboolean homo, ats_int_type spacing) {
  GtkWidget* hbox ;
  hbox = gtk_hbox_new (homo, (gint)spacing) ;
  g_object_ref (hbox) ;
  gtk_object_sink ((GtkObject*)hbox) ;
  return hbox ;
}

static inline
ats_ptr_type
ats_gtk_vbox_new (gboolean homo, ats_int_type spacing) {
  GtkWidget* vbox ;
  vbox = gtk_vbox_new (homo, (gint)spacing) ;
  g_object_ref (vbox) ;
  gtk_object_sink ((GtkObject*)vbox) ;
  return vbox ;
}

static inline
ats_ptr_type ats_gtk_table_new
  (ats_int_type nrow, ats_int_type ncol, gboolean homo) {
  GtkWidget* table ;
  table = gtk_table_new ((guint)nrow, (guint)ncol, homo) ;
  g_object_ref (table) ;
  gtk_object_sink ((GtkObject*)table) ;
  return table ;
}

//

static inline
ats_ptr_type ats_gtk_label_new (ats_ptr_type text) {
  GtkWidget* lab ;
  lab = gtk_label_new ((gchar*)text) ;
  g_object_ref (lab) ;
  gtk_object_sink ((GtkObject*)lab) ;
  return lab ;
}

//

static inline
ats_ptr_type ats_gtk_hseparator_new () {
  GtkWidget* hsep ;
  hsep = gtk_hseparator_new () ;
  g_object_ref (hsep) ;
  gtk_object_sink ((GtkObject*)hsep) ;
  return hsep ;
}

static inline
ats_ptr_type ats_gtk_vseparator_new () {
  GtkWidget* vsep ;
  vsep = gtk_vseparator_new () ;
  g_object_ref (vsep) ;
  gtk_object_sink ((GtkObject*)vsep) ;
  return vsep ;
}

/* ****** ****** */

static inline
ats_void_type
ats_gtk_toplevel_add (ats_ptr_type gobj) { return ; }

static inline
ats_void_type
ats_gtk_container_add (ats_ptr_type container, ats_ptr_type widget)
{
  gtk_container_add ((GtkContainer*)container, (GtkWidget*)widget) ;
  g_object_unref (widget) ;
  return ;
}

static inline
ats_void_type
ats_gtk_container_add_ref (ats_ptr_type container, ats_ptr_type widget)
{
  gtk_container_add ((GtkContainer*)container, (GtkWidget*)widget) ;
  return ;
}

static inline
ats_void_type
ats_gtk_menu_shell_append (ats_ptr_type shell, ats_ptr_type widget)
{
  gtk_menu_shell_append ((GtkMenuShell*)shell, (GtkWidget*)widget) ;
  g_object_unref (widget) ;
  return ;
}

//

static inline
ats_void_type ats_gtk_box_pack_start
  (ats_ptr_type box, ats_ptr_type widget,
   gboolean expand, gboolean fill, ats_int_type padding)
{

  gtk_box_pack_start (
    (GtkBox*)box, (GtkWidget*)widget, expand, fill, (guint)padding
  ) ;
  g_object_unref (widget) ;
  return ;
}

static inline
ats_void_type ats_gtk_box_pack_end
  (ats_ptr_type box, ats_ptr_type widget,
   gboolean expand, gboolean fill, ats_int_type padding)
{

  gtk_box_pack_start (
    (GtkBox*)box, (GtkWidget*)widget, expand, fill, (guint)padding
  ) ;
  g_object_unref (widget) ;
  return ;
}

static inline
ats_void_type ats_gtk_table_attach_defaults
  (ats_ptr_type table, ats_ptr_type widget,
   ats_int_type left, ats_int_type right, ats_int_type top, ats_int_type bottom)
{
  gtk_table_attach_defaults (
    (GtkTable*)table, (GtkWidget*)widget,
     (guint)left, (guint)right, (guint)top, (guint)bottom
  ) ;
  g_object_unref (widget) ;
  return ;
}

/* ****** ****** */

static inline
ats_void_type
ats_gtk_container_set_border_width
  (ats_ptr_type gobj, ats_int_type width) {
  gtk_container_set_border_width ((GtkContainer*)gobj, (guint)width) ;
  return ;
}

static inline
ats_void_type
ats_gtk_widget_set_size_request
  (ats_ptr_type widget, ats_int_type width, ats_int_type height) {
  gtk_widget_set_size_request ((GtkWidget*)widget, (gint)width, (gint)height) ;
  return ;
}

static inline
ats_void_type
ats_gtk_table_set_row_spacing
  (ats_ptr_type table, ats_int_type row, ats_int_type spacing)
{
  gtk_table_set_row_spacing ((GtkTable*)table, (guint)row, (guint)spacing) ;
  return ;
}

static inline
ats_void_type
ats_gtk_table_set_col_spacing
  (ats_ptr_type table, ats_int_type col, ats_int_type spacing)
{
  gtk_table_set_col_spacing ((GtkTable*)table, (guint)col, (guint)spacing) ;
  return ;
}

/* ****** ****** */

/* end of [gtk.cats] */
