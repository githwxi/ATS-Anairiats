/*******************************************************************/
/*                                                                 */
/*                        Applied Type System                      */
/*                                                                 */
/*                          (c) Hongwei Xi                         */
/*                                                                 */
/*                            2002 - 2007                          */
/*                                                                 */
/*                         Boston University                       */
/*                                                                 */
/*                   Distributed by permission only.               */
/*                                                                 */
/*******************************************************************/

/* Author: Hongwei Xi ( hwxi AT cs DOT bu DOT edu ) */

globals_head the_globals_head = {
  0 // int position
, 0 // global_root *roots
, 0 // globals_entry *rest
#ifdef __ATS_MULTITHREAD
, PTHREAD_MUTEX_INITIALIZER
#endif
} ; 

static inline
ats_void_type
the_globals_head_get() {
#ifdef __ATS_MULTITHREAD
  pthread_mutex_lock (&the_globals_head.lock) ;
#endif
  return ;
}

static inline
ats_void_type
the_globals_head_set() {
#ifdef __ATS_MULTITHREAD
  pthread_mutex_lock (&the_globals_head.lock) ;
#endif
  return ;
}

globals_entry*
globals_entry_make (global_root *roots, globals_entry *next) {
  globals_entry* entry ;
  entry = malloc (sizeof(globals_entry)) ;
  if (!entry) { 
    ats_exit_errmsg(1, "Exit: [globals_entry_make: malloc] failed.\n") ;
  }
  entry->roots = roots ; entry->next = next ;
  return entry ;
}

ats_void_type gcats_markroot_bsz (freeitm *x, size_t bsz) {
  global_root *roots ; int position ;
  globals_entry *entry ;
  
  roots = the_globals_head.roots ;
  position = the_globals_head.position ;

  if (position > 0) {
    --position ;
    roots[position].data = x ;
    roots[position].size = bsz ;
    the_globals_head.position = position ; 
    return ;
  }

  if (roots) { // already initialized
    the_globals_head.rest = globals_entry_make (roots, the_globals_head.rest) ;
  }

  roots = malloc (GLOBALS_ENTRY_PAGESIZE * sizeof(global_root)) ;
  if (!roots) {
    ats_exit_errmsg(1, "Exit: [gcats_markroot: malloc] failed.\n") ;
  }

  the_globals_head.roots = roots ;
  the_globals_head.position = GLOBALS_ENTRY_PAGESIZE - 1 ;
  roots[GLOBALS_ENTRY_PAGESIZE - 1].data =  x ;
  roots[GLOBALS_ENTRY_PAGESIZE - 1].size =  bsz ;
  return ;
}

/* ****** ****** */

/* end of [globals.cats] */

