//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
/* ****** ****** */

#ifndef ATS_SCULL_CATS
#define ATS_SCULL_CATS

/* ****** ****** */

#include "contrib/linux/CATS/array.cats"
#include "contrib/linux/CATS/integer.cats"
#include "contrib/linux/CATS/pointer.cats"
#include "contrib/linux/CATS/sizetype.cats"

/* ****** ****** */

#include <linux/slab.h>
#include <linux/cdev.h>
#include <linux/semaphore.h>

#include "../scull.h"

typedef struct scull_dev scull_dev_struct ;
typedef struct scull_qset scull_qset_struct ;

/* ****** ****** */

ATSinline()
ats_int_type
scull_dev_acquire
  (scull_dev_struct *dev) {
  return down_interruptible(&dev->sem) ;
} // end of [scull_dev_acquire]

ATSinline()
ats_void_type
scull_dev_release
  (scull_dev_struct *dev) {
  up(&dev->sem) ; return ;
} // end of [scull_dev_release]

/* ****** ****** */

typedef unsigned long int ulint ;
#define add_loff_int(x, y) (((ulint)x) + ((ulint)y))

/* ****** ****** */

#define scull_ptr_make_null() (NULL)
#define scull_ptr_free_null(p) (NULL)

/* ****** ****** */

ATSinline()
ats_ptr_type
scull_qtmptr_make
  (int n) {
  ats_ptr_type p = (ats_ptr_type)ATS_MALLOC(n) ;
  if (p != NULL) memset(p, 0, n) ;
  return p ;
} // end of [scull_qtmptr_make]

ATSinline()
ats_void_type
scull_qtmptr_free
  (ats_ptr_type p) {
  if (p) ATS_FREE(p) ; return ;
} // end of [scull_qtmptr_free]

/* ****** ****** */

ATSinline()
ats_ptr_type
scull_qdatptr_make
  (int m) {
  size_t bsz = m*sizeof(ats_ptr_type) ;
  ats_ptr_type *p = (ats_ptr_type)ATS_MALLOC(bsz) ;
  if (p != NULL) memset(p, 0, bsz) ;
  return p ;
} // end of [scull_qdatptr_make]

/* ****** ****** */

ATSinline()
ats_ptr_type
scull_qset_alloc () {
  return ATS_MALLOC(sizeof(scull_qset_struct)) ;
} // end of [scull_qset_alloc]

ATSinline()
ats_void_type
scull_qset_free (ats_ptr_type p) { return ATS_FREE(p) ; }

/* ****** ****** */

ATSinline()
ats_ptr_type
scull_qset_get_next
  (ats_ptr_type p) {
  return ((scull_qset_struct*)p)->next ;
} // end of [scull_qset_get_next]

ATSinline()
ats_void_type
scull_qset_set_next (
  ats_ptr_type p, ats_ptr_type n
) {
  ((scull_qset_struct*)p)->next = n ; return ;
} // end of [scull_qset_set_next]

/* ****** ****** */

#endif // end of [ATS_SCULL_CATS]

/* ****** ****** */

/* end of [scull.cats] */
