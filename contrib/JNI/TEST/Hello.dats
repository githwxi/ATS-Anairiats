(*
** A simple example of JNI
*)

(* ****** ****** *)

staload "contrib/JNI/SATS/jni.sats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)

extern
fun printHello {l:agz}
  (env: !JNIEnvptr, obj: !jobject l): void = "ext#Java_Hello_printHello"
// end of [printHello]

extern
fun printHelloFrom {l1,l2:agz} (
  env: !JNIEnvptr, obj: !jobject l1, whom: jstring l2
) : void = "ext#Java_Hello_printHelloFrom" // end of [printHelloFrom]

(* ****** ****** *)

implement
printHello (env, obj) = let
//
val () = printf ("Hello, world!\n", @())
//
val () = loop (msg, 0) where {
  fun loop {n,i:nat | i <= n} .<n-i>.
    (msg: string n, i: size_t i): void =
    if string_isnot_atend (msg, i) then let
      val () = fprint_char (stdout_ref, msg[i]) in loop (msg, i+1)
    end else ()
  // end of [loop]
  val msg = "Hello, world!\n"
} // end of [val]
//
in
// nothing
end // end of [printHello]

(* ****** ****** *)

implement
printHelloFrom (env, obj, whom) = let
  val () = printf ("Hello from ", @())
  val (pf | strp) = JNIEnv_GetStringUTFChars (env, whom)
  val () = fprint_strptr (stdout_ref, strp); val () = print ("!\n")
  val () = JNIEnv_ReleaseStringUTFChars (pf | env, whom, strp)
in
  // nothing
end // end of [printHelloFrom]

(* ****** ****** *)

extern
fun hello
  (env: !JNIEnvptr, cls: jclass): jstring0 = "ext#Java_Hello_hello"
// end of [hello]

implement
hello (env, cls) = JNIEnv_NewStringUTF (env, "Hello!\n")

(* ****** ****** *)

(* end of [Hello.dats] *)
