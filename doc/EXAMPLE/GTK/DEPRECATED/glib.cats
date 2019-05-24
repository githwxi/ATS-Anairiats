#include <glib-object.h>

/* ****** ****** */

typedef gchar *gchar_ptr ;

/* ****** ****** */

static inline
ats_ptr_type
ats_g_object_ref (ats_ptr_type gobj) {
  g_object_ref ((gpointer)gobj) ; return gobj ;
}

static inline
ats_void_type
ats_g_object_unref (ats_ptr_type gobj) {
  g_object_unref ((gpointer)gobj) ; return ;
}

/* ****** ****** */

static inline
ats_ptr_type
ats_g_objref_make_some (ats_ptr_type gobj) {
  ats_ptr_type *p ;
  p = ats_malloc_ngc (sizeof(ats_ptr_type)) ;
  *p = gobj ; return p ;
}

static inline
ats_ptr_type
ats_g_objref_make_none () { 
  ats_ptr_type *p ;
  p = ats_malloc_ngc (sizeof(ats_ptr_type)) ;
  *p = (ats_ptr_type)0 ;
  return p ;
}

static inline
ats_ptr_type
ats_g_objref_get (ats_ptr_type gobjref) {
  ats_ptr_type p ;
  p = *(ats_ptr_type*)gobjref ;
  *(ats_ptr_type*)gobjref = (ats_ptr_type)0 ;
/*
  if (!p) {
    ats_exit_errmsg (1, "Exit: [g_objref_get] failed.\n") ;
  }
*/
  return p ;
}

static inline
ats_void_type
ats_g_objref_set (ats_ptr_type gobjref, ats_ptr_type gobj) {
/*
  if (*(ats_ptr_type*)gobjref) {
    ats_exit_errmsg (1, "Exit: [g_objref_set] failed.\n") ;
  }
*/
  *(ats_ptr_type*)gobjref = gobj ;
  return ;
}

/* ****** ****** */

static inline
ats_void_type
ats_g_signal_connect
  (ats_ref_type gobj, ats_ptr_type signal, ats_ptr_type callback, ats_ref_type data)
{
  g_signal_connect
    ((gpointer)gobj, (gchar_ptr)signal, (GCallback)callback, (gpointer)data) ;
  return ;
}

static inline
ats_void_type
ats_g_signal_connect_event
  (ats_ref_type gobj, ats_ptr_type signal, ats_ptr_type callback, ats_ref_type data)
{
  g_signal_connect
    ((gpointer)gobj, (gchar_ptr)signal, (GCallback)callback, (gpointer)data) ;
  return ;
}

static inline
ats_void_type
ats_g_signal_connect_swapped
  (ats_ref_type gobj, gchar_ptr signal, ats_ptr_type callback, ats_ref_type data)
{
  g_signal_connect_swapped
   ((gpointer)gobj, signal, (GCallback)callback, (gpointer)data) ;
  return ;
}

/* ****** ****** */

/* end of [glib.cats] */
