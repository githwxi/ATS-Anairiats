/*
**
** TIGERATS: a compiler for Tiger written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*/

/* ****** ****** */

#define WORDSIZE_TARGET 32 (* bits *)

/* ****** ****** */

/*
// please uncomment this one if you need to generate a compiler //
// for Tiger that spills out MIPS code (or more precisely, SPIM code)
// #define MARCH "SPIM" // the emitted code is intended to be run
// by the SPIM simulator
*/

/* ****** ****** */

/*
// this one, if uncommented, allows you to generate a compiler
// for Tiger that spills out x86 assembly for 32-bit machines
// #define MARCH "x86_32" // the emitted code is to be run on an x86
// 32-bit machine
*/

/* ****** ****** */

/* end of [params.hats] */

