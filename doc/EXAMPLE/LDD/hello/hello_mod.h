#ifndef HELLO_MOD_H
#define HELLO_MOD_H
//
// from ${ATSHOME}/ccomp/runtime/ats_types.h
//
typedef int ats_int_type ;
typedef void ats_void_type ;
typedef void *ats_ptr_type ;
//
// from ${ATSHOME}/ccomp/runtime/ats_basic.h
//
#define ATSunused __attribute__ ((unused))
#define ATSstatic_fun(ty, name) static ty name
#define ATSlocal(ty, var) ty ATSunused var
#define ATSlocal_void(var) // void var
//
// for handling a call like: printk (KERN_INFO "...")
//
#ifdef ATSstrcst
#undef ATSstrcst
#endif
#define ATSstrcst(x) x
//
#endif

/* end of [hello_mod.h] */
