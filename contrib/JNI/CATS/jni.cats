/*
**
** An interface for ATS to interact with JNI
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** Start Time: September, 2011
**
*/

/* ****** ****** */

#ifndef ATS_CONTRIB_JNI_CATS
#define ATS_CONTRIB_JNI_CATS

/* ****** ****** */

#include <jni.h>

/* ****** ****** */

ATSinline()
ats_ptr_type
JNIEnv_GetStringUTFChars
(
  ats_ptr_type env, ats_ptr_type src
) {
  return (*((JNIEnv*)env))->GetStringUTFChars((JNIEnv*)env, (jstring)src, (jboolean*)0) ;
} // end of [JNIEnv_GetStringUTFChars]

ATSinline()
ats_void_type
JNIEnv_ReleaseStringUTFChars
(
  ats_ptr_type env, ats_ptr_type src, ats_ptr_type dst
) {
  (*((JNIEnv*)env))->ReleaseStringUTFChars((JNIEnv*)env, (jstring)src, (char*)dst) ; return ;
} // end of [JNIEnv_ReleaseStringUTFChars]

/* ****** ****** */

ATSinline()
ats_ptr_type
JNIEnv_NewStringUTF
(
  ats_ptr_type env, ats_ptr_type str
) {
  return (*((JNIEnv*)env))->NewStringUTF((JNIEnv*)env, (char*)str) ;
} // end of [JNIEnv_GetStringUTFChars]

/* ****** ****** */

#endif /* [ATS_CONTRIB_JNI_CATS] */

/* end of [jni.cats] */
