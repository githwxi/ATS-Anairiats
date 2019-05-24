//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
/* ****** ****** */

#ifndef ATS_SCULLC_CATS
#define ATS_SCULLC_CATS

/* ****** ****** */

#include "contrib/linux/CATS/array.cats"
#include "contrib/linux/CATS/integer.cats"
#include "contrib/linux/CATS/pointer.cats"
#include "contrib/linux/CATS/sizetype.cats"

/* ****** ****** */

#include <linux/slab.h>
#include <linux/cdev.h>
#include <linux/semaphore.h>

#include "../scullc.h"

typedef struct scullc_dev scullc_dev_struct ;
typedef struct scullc_qset scullc_qset_struct ;

/* ****** ****** */

typedef unsigned long int ulint ;
#define add_loff_int(x, y) (((ulint)x) + ((ulint)y))

/* ****** ****** */

#define scullc_ptr_make_null() (NULL)
#define scullc_ptr_free_null(p) (NULL)

/* ****** ****** */

extern struct kmem_cache *scullc_cache;

/* ****** ****** */

ATSinline()
ats_ptr_type
scullc_qtmptr_make
  (int n) {
  ats_ptr_type p ;
  p = kmem_cache_alloc(scullc_cache, GFP_KERNEL) ;
  if (p != NULL) memset(p, 0, n) ;
  return p ;
} // end of [scullc_qtmptr_make]

ATSinline()
ats_void_type
scullc_qtmptr_free
  (ats_ptr_type p) {
  if (p) {
    kmem_cache_free(scullc_cache, p) ;
  } ; return ;
} // end of [scullc_qtmptr_free]

/* ****** ****** */

ATSinline()
ats_ptr_type
scullc_qdatptr_make
  (int m) {
  size_t bsz = m*sizeof(ats_ptr_type) ;
  ats_ptr_type *p = (ats_ptr_type)ATS_MALLOC(bsz) ;
  if (p != NULL) memset(p, 0, bsz) ;
  return p ;
} // end of [scullc_qdatptr_make]

/* ****** ****** */

ATSinline()
ats_ptr_type
scullc_qset_alloc () {
  return ATS_MALLOC(sizeof(scullc_qset_struct)) ;
} // end of [scullc_qset_alloc]

ATSinline()
ats_void_type
scullc_qset_free (ats_ptr_type p) { return ATS_FREE(p) ; }

/* ****** ****** */

ATSinline()
ats_ptr_type
scullc_qset_get_next
  (ats_ptr_type p) {
  return ((scullc_qset_struct*)p)->next ;
} // end of [scullc_qset_get_next]

ATSinline()
ats_void_type
scullc_qset_set_next (
  ats_ptr_type p, ats_ptr_type n
) {
  ((scullc_qset_struct*)p)->next = n ; return ;
} // end of [scullc_qset_set_next]

/* ****** ****** */

#endif // end of [ATS_SCULLC_CATS]

/* ****** ****** */

/* end of [scullc.cats] */
