/*
**
** An interesting example found at:
**
** http://rigaux.org/language-study/various/is-a-cow-an-animal/
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: November, 2010
**
*/

/* ****** ****** */

typedef
struct {
  char *name ; // != NULL
  int energy ;
  int refcnt ;
} THINGstruct ;

/* ****** ****** */

#define thing_get_name_mac(X) (((THINGstruct*)X)->name)
#define thing_get_energy_mac(X) (((THINGstruct*)X)->energy)
#define thing_get_refcnt_mac(X) (((THINGstruct*)X)->refcnt)

/* ****** ****** */

ATSinline()
ats_ptr_type
thing_get_name
  (ats_ptr_type X) { return thing_get_name_mac(X) ; }
// end of [thing_get_name]

ATSinline()
ats_int_type
thing_get_energy
  (ats_ptr_type X) { return thing_get_energy_mac(X) ; }
// end of [thing_get_energy]

/* ****** ****** */

ATSinline()
ats_void_type
eat_animal_food (
  ats_ptr_type A, ats_ptr_type F
) {
  thing_get_energy_mac(A) += thing_get_energy_mac(F) ; return ;
} // end of [eat_animal_food]

/* ****** ****** */

ATSinline()
ats_ptr_type
thing_ref (
  ats_ptr_type X
) {
  thing_get_refcnt_mac(X) += 1 ; return X ;
} // end of [thing_ref]

ATSinline()
ats_void_type
thing_unref (
  ats_ptr_type X
) {
  thing_get_refcnt_mac(X) -= 1 ;
  if (thing_get_refcnt_mac(X) == 0) ATS_FREE(X) ;
  return ;
} // end of [thing_unref]

/* ****** ****** */

ATSinline()
ats_ptr_type
new_grass (int energy) {
  THINGstruct *X ;
  X = ATS_MALLOC (sizeof(THINGstruct)) ;
  thing_get_name_mac(X) = "grass" ;
  thing_get_energy_mac(X) = energy ;
  thing_get_refcnt_mac(X) = 1 ;
  return X ;
} // end of [new_grass]

ATSinline()
ats_ptr_type
new_carrot (int energy) {
  THINGstruct *X ;
  X = ATS_MALLOC (sizeof(THINGstruct)) ;
  thing_get_name_mac(X) = "carrot" ;
  thing_get_energy_mac(X) = energy ;
  thing_get_refcnt_mac(X) = 1 ;
  return X ;
} // end of [new_carrot]

/* ****** ****** */

ATSinline()
ats_ptr_type
new_rabbit (int energy) {
  THINGstruct *X ;
  X = ATS_MALLOC (sizeof(THINGstruct)) ;
  thing_get_name_mac(X) = "rabbit" ;
  thing_get_energy_mac(X) = energy ;
  thing_get_refcnt_mac(X) = 1 ;
  return X ;
} // end of [new_rabbit]

ATSinline()
ats_ptr_type
new_cow (int energy) {
  THINGstruct *X ;
  X = ATS_MALLOC (sizeof(THINGstruct)) ;
  thing_get_name_mac(X) = "cow" ;
  thing_get_energy_mac(X) = energy ;
  thing_get_refcnt_mac(X) = 1 ;
  return X ;
} // end of [new_cow]

ATSinline()
ats_ptr_type
new_human (int energy) {
  THINGstruct *X ;
  X = ATS_MALLOC (sizeof(THINGstruct)) ;
  thing_get_name_mac(X) = "human" ;
  thing_get_energy_mac(X) = energy ;
  thing_get_refcnt_mac(X) = 1 ;
  return X ;
} // end of [new_human]

/* ****** ****** */

/* end of [isacowananimal.cats] */
