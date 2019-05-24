(*
**
** An interface for ATS to interact with JNI
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** Start Time: September, 2011
**
*)

(* ****** ****** *)

%{#
#include "contrib/JNI/CATS/jni.cats"
%} // end of [%{#]

(* ****** ****** *)
//
abst@ype jint = $extype "jint"
abst@ype jshort = $extype "jshort"
abst@ype jlong = $extype "jlong"
abst@ype jsize = $extype "jsize"
//
abst@ype jboolean = $extype "jboolean"
//
abst@ype jchar = $extype "jchar"
abst@ype jbyte = $extype "jbyte"
//
abst@ype jfloat = $extype "jfloat"
abst@ype jdouble = $extype "jdouble"
//
typedef Void = void
//
(* ****** ****** *)

abstype jstring = $extype "jstring"

(* ****** ****** *)

absviewtype JNIEnvptr

abstype jclass 
abstype jobject (l:addr)
abstype jstring (l:addr)
typedef jstring0 = [l:agez] jstring (l)

absview JNIEnv_GetStringUTFChars_v (src:addr, dst:addr)

(* ****** ****** *)

fun JNIEnv_GetStringUTFChars
  {l1:agz} (
  env: !JNIEnvptr, x: jstring l1
) : [l2:addr] (JNIEnv_GetStringUTFChars_v (l1, l2) | strptr l2)
  = "mac#JNIEnv_GetStringUTFChars"
// end of [JNIEnv_GetStringUTFChars]

fun JNIEnv_ReleaseStringUTFChars
  {l1:agz} {l2:addr} (
  pf: JNIEnv_GetStringUTFChars_v (l1, l2) | env: !JNIEnvptr, src: jstring l1, dst: strptr l2
) : void = "mac#JNIEnv_ReleaseStringUTFChars"
// end of [JNIEnv_ReleaseStringUTFChars]

(* ****** ****** *)

fun JNIEnv_NewStringUTF
  (env: !JNIEnvptr, str: string): jstring0 = "mac#JNIEnv_NewStringUTF"
// end of [JNIEnv_NewStringUTF]

(* ****** ****** *)

(* end of [jni.sats] *)
