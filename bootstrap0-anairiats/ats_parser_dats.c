/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2013-8-29: 22h:22m
**
*/

/* include some .h files */
#ifndef _ATS_HEADER_NONE
#include "ats_config.h"
#include "ats_basics.h"
#include "ats_types.h"
#include "ats_exception.h"
#include "ats_memory.h"
#endif /* _ATS_HEADER_NONE */

/* include some .cats files */
#ifndef _ATS_PRELUDE_NONE
#include "prelude/CATS/basics.cats"
#include "prelude/CATS/bool.cats"
#include "prelude/CATS/byte.cats"
#include "prelude/CATS/char.cats"
#include "prelude/CATS/float.cats"
#include "prelude/CATS/integer.cats"
#include "prelude/CATS/integer_fixed.cats"
#include "prelude/CATS/integer_ptr.cats"
#include "prelude/CATS/lazy.cats"
#include "prelude/CATS/lazy_vt.cats"
#include "prelude/CATS/pointer.cats"
#include "prelude/CATS/printf.cats"
#include "prelude/CATS/reference.cats"
#include "prelude/CATS/sizetype.cats"
#include "prelude/CATS/string.cats"
#include "prelude/CATS/array.cats"
#include "prelude/CATS/list.cats"
#include "prelude/CATS/matrix.cats"
#include "prelude/CATS/option.cats"
#endif /* _ATS_PRELUDE_NONE */
/* prologues from statically loaded files */
/* external codes at top */

#include "libc/CATS/stdio.cats" // for [atslib_fopen_exn]

/* type definitions */
typedef struct {
int tag ;
ats_ptr_type atslab_0 ;
} anairiats_sum_0 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYBEGnone) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYBEGi0de) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYBEGs0rtid) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYBEGsi0de) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYBEGdi0de) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYBEGs0exp) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYBEGd0exp) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYBEGd0ecseq_sta) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYBEGd0ecseq_dyn) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYRESi0de) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYRESs0exp) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYRESd0exp) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYRESd0eclst) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_bool_type, atspre_gt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_ptr_type, atslib_fopen_exn) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, atsopt_filename_full) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, ATS_2d0_2e2_2e10_2src_2libats_lex_lexing_2esats__infile_make_file) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, ATS_2d0_2e2_2e10_2src_2libats_lex_lexing_2esats__infile_make_stdin) () ;
ATSextern_fun(ats_ptr_type, lexbuf_make_infile) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, lexing_lexbuf_set) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, lexing_lexbuf_free) () ;
ATSextern_val(ats_int_type, ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_none) ;
ATSextern_val(ats_int_type, ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_i0de) ;
ATSextern_val(ats_int_type, ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_s0rtid) ;
ATSextern_val(ats_int_type, ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_si0de) ;
ATSextern_val(ats_int_type, ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_di0de) ;
ATSextern_val(ats_int_type, ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_s0exp) ;
ATSextern_val(ats_int_type, ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_d0exp) ;
ATSextern_val(ats_int_type, ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_d0ecseq_sta) ;
ATSextern_val(ats_int_type, ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_d0ecseq_dyn) ;
ATSextern_fun(ats_int_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__token_of_yybeg) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_stdin_yyres) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_filename_yyres) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, yyparse_main) (ats_int_type) ;
ATSextern_fun(ats_ptr_type, atsopt_yyres_i0de) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, atsopt_yyres_s0exp) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, atsopt_yyres_d0exp) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, atsopt_yyres_d0eclst) (ats_ptr_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
extern
ats_void_type ATS_2d0_2e2_2e10_2prelude_2basics_dyn_2esats__file_mode_lte_r_r_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_bool_type flag_is_sta_0 (ats_int_type arg0) ;
static
ats_bool_type flag_is_dyn_1 (ats_int_type arg0) ;

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/research/Anairiats/src/ats_parser.dats: 2174(line=71, offs=4) -- 2216(line=71, offs=46)
*/
ATSstaticdec()
ats_bool_type
flag_is_sta_0 (ats_int_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp0) ;

__ats_lab_flag_is_sta_0:
tmp0 = atspre_eq_int_int (arg0, 0) ;
return (tmp0) ;
} /* end of [flag_is_sta_0] */

/*
// /home/hwxi/research/Anairiats/src/ats_parser.dats: 2220(line=72, offs=4) -- 2262(line=72, offs=46)
*/
ATSstaticdec()
ats_bool_type
flag_is_dyn_1 (ats_int_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp1) ;

__ats_lab_flag_is_dyn_1:
tmp1 = atspre_gt_int_int (arg0, 0) ;
return (tmp1) ;
} /* end of [flag_is_dyn_1] */

/*
// /home/hwxi/research/Anairiats/src/ats_parser.dats: 2439(line=83, offs=22) -- 2459(line=83, offs=42)
*/
ATSglobaldec()
ats_ptr_type
atsopt_yyres_i0de (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp2) ;

__ats_lab_atsopt_yyres_i0de:
tmp2 = ATS_MALLOC(sizeof(anairiats_sum_0)) ;
((ats_sum_ptr_type)tmp2)->tag = 0 ;
ats_selptrset_mac(anairiats_sum_0, tmp2, atslab_0, arg0) ;
return (tmp2) ;
} /* end of [atsopt_yyres_i0de] */

/*
// /home/hwxi/research/Anairiats/src/ats_parser.dats: 2552(line=88, offs=23) -- 2575(line=88, offs=46)
*/
ATSglobaldec()
ats_ptr_type
atsopt_yyres_s0exp (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp3) ;

__ats_lab_atsopt_yyres_s0exp:
tmp3 = ATS_MALLOC(sizeof(anairiats_sum_0)) ;
((ats_sum_ptr_type)tmp3)->tag = 1 ;
ats_selptrset_mac(anairiats_sum_0, tmp3, atslab_0, arg0) ;
return (tmp3) ;
} /* end of [atsopt_yyres_s0exp] */

/*
// /home/hwxi/research/Anairiats/src/ats_parser.dats: 2668(line=93, offs=23) -- 2691(line=93, offs=46)
*/
ATSglobaldec()
ats_ptr_type
atsopt_yyres_d0exp (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp4) ;

__ats_lab_atsopt_yyres_d0exp:
tmp4 = ATS_MALLOC(sizeof(anairiats_sum_0)) ;
((ats_sum_ptr_type)tmp4)->tag = 2 ;
ats_selptrset_mac(anairiats_sum_0, tmp4, atslab_0, arg0) ;
return (tmp4) ;
} /* end of [atsopt_yyres_d0exp] */

/*
// /home/hwxi/research/Anairiats/src/ats_parser.dats: 2793(line=98, offs=25) -- 2820(line=98, offs=52)
*/
ATSglobaldec()
ats_ptr_type
atsopt_yyres_d0eclst (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp5) ;

__ats_lab_atsopt_yyres_d0eclst:
tmp5 = ATS_MALLOC(sizeof(anairiats_sum_0)) ;
((ats_sum_ptr_type)tmp5)->tag = 3 ;
ats_selptrset_mac(anairiats_sum_0, tmp5, atslab_0, arg0) ;
return (tmp5) ;
} /* end of [atsopt_yyres_d0eclst] */

/*
// /home/hwxi/research/Anairiats/src/ats_parser.dats: 2933(line=109, offs=16) -- 3325(line=121, offs=50)
*/
ATSglobaldec()
ats_int_type
ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__token_of_yybeg (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_int_type, tmp6) ;

__ats_lab_ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__token_of_yybeg:
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
if (((ats_sum_ptr_type)arg0)->tag != 0) { goto __ats_lab_1_0 ; }
__ats_lab_0_1:
tmp6 = ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_none ;
break ;

/* branch: __ats_lab_1 */
__ats_lab_1_0:
if (((ats_sum_ptr_type)arg0)->tag != 1) { goto __ats_lab_2_0 ; }
__ats_lab_1_1:
tmp6 = ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_i0de ;
break ;

/* branch: __ats_lab_2 */
__ats_lab_2_0:
if (((ats_sum_ptr_type)arg0)->tag != 2) { goto __ats_lab_3_0 ; }
__ats_lab_2_1:
tmp6 = ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_s0rtid ;
break ;

/* branch: __ats_lab_3 */
__ats_lab_3_0:
if (((ats_sum_ptr_type)arg0)->tag != 3) { goto __ats_lab_4_0 ; }
__ats_lab_3_1:
tmp6 = ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_si0de ;
break ;

/* branch: __ats_lab_4 */
__ats_lab_4_0:
if (((ats_sum_ptr_type)arg0)->tag != 4) { goto __ats_lab_5_0 ; }
__ats_lab_4_1:
tmp6 = ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_di0de ;
break ;

/* branch: __ats_lab_5 */
__ats_lab_5_0:
if (((ats_sum_ptr_type)arg0)->tag != 5) { goto __ats_lab_6_0 ; }
__ats_lab_5_1:
tmp6 = ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_s0exp ;
break ;

/* branch: __ats_lab_6 */
__ats_lab_6_0:
if (((ats_sum_ptr_type)arg0)->tag != 6) { goto __ats_lab_7_0 ; }
__ats_lab_6_1:
tmp6 = ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_d0exp ;
break ;

/* branch: __ats_lab_7 */
__ats_lab_7_0:
if (((ats_sum_ptr_type)arg0)->tag != 7) { goto __ats_lab_8_0 ; }
__ats_lab_7_1:
tmp6 = ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_d0ecseq_sta ;
break ;

/* branch: __ats_lab_8 */
__ats_lab_8_0:
// if (((ats_sum_ptr_type)arg0)->tag != 8) { ats_deadcode_failure_handle () ; }
__ats_lab_8_1:
tmp6 = ATS_2d0_2e2_2e10_2src_2ats_lexer_2esats__YYBEG_d0ecseq_dyn ;
break ;
} while (0) ;
return (tmp6) ;
} /* end of [ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__token_of_yybeg] */

/*
// /home/hwxi/research/Anairiats/src/ats_parser.dats: 3410(line=128, offs=3) -- 3765(line=141, offs=2)
*/
ATSglobaldec()
ats_ptr_type
ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_stdin_yyres (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp7) ;
ATSlocal (ats_int_type, tmp8) ;
ATSlocal (ats_ptr_type, tmp9) ;
ATSlocal (ats_ptr_type, tmp10) ;
ATSlocal (ats_ptr_type, tmp11) ;
ATSlocal (ats_ptr_type, tmp12) ;
// ATSlocal_void (tmp13) ;
ATSlocal (ats_ptr_type, tmp14) ;
// ATSlocal_void (tmp15) ;

__ats_lab_ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_stdin_yyres:
tmp8 = ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__token_of_yybeg (arg0) ;
tmp9 = ATS_2d0_2e2_2e10_2src_2libats_lex_lexing_2esats__infile_make_stdin () ;
tmp10 = ats_selsin_mac(tmp9, atslab_1) ;
tmp11 = lexbuf_make_infile (tmp10) ;
tmp12 = ats_selsin_mac(tmp11, atslab_1) ;
/* tmp13 = */ lexing_lexbuf_set (tmp12) ;
tmp14 = yyparse_main (tmp8) ;
/* tmp15 = */ lexing_lexbuf_free () ;
tmp7 = tmp14 ;
return (tmp7) ;
} /* end of [ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_stdin_yyres] */

/*
// /home/hwxi/research/Anairiats/src/ats_parser.dats: 3839(line=145, offs=3) -- 4114(line=155, offs=2)
*/
ATSglobaldec()
ats_ptr_type
ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_stdin_d0eclst (ats_int_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp16) ;
ATSlocal (ats_ptr_type, tmp17) ;
ATSlocal (ats_bool_type, tmp19) ;
ATSlocal (ats_ptr_type, tmp20) ;
ATSlocal (ats_bool_type, tmp22) ;
ATSlocal (ats_ptr_type, tmp23) ;
ATSlocal (ats_ptr_type, tmp24) ;
ATSlocal (ats_ptr_type, tmp25) ;

__ats_lab_ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_stdin_d0eclst:
/* ats_ptr_type tmp17 ; */
tmp17 = (ats_sum_ptr_type)(&ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYBEGnone) ;
tmp19 = flag_is_sta_0 (arg0) ;
if (tmp19) {
tmp20 = (ats_sum_ptr_type)(&ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYBEGd0ecseq_sta) ;
tmp17 = tmp20 ;
} else {
/* empty */
} /* end of [if] */
tmp22 = flag_is_dyn_1 (arg0) ;
if (tmp22) {
tmp23 = (ats_sum_ptr_type)(&ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYBEGd0ecseq_dyn) ;
tmp17 = tmp23 ;
} else {
/* empty */
} /* end of [if] */
tmp24 = ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_stdin_yyres (tmp17) ;
if (((ats_sum_ptr_type)tmp24)->tag != 3) { ats_caseof_failure_handle ("/home/hwxi/research/Anairiats/src/ats_parser.dats: 4082(line=153, offs=8) -- 4109(line=153, offs=35)") ; }
tmp25 = ats_caselptrlab_mac(anairiats_sum_0, tmp24, atslab_0) ;
tmp16 = tmp25 ;
return (tmp16) ;
} /* end of [ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_stdin_d0eclst] */

/*
// /home/hwxi/research/Anairiats/src/ats_parser.dats: 4212(line=161, offs=3) -- 4906(line=183, offs=2)
*/
ATSglobaldec()
ats_ptr_type
ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_filename_yyres (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp26) ;
ATSlocal (ats_int_type, tmp27) ;
ATSlocal (ats_ptr_type, tmp28) ;
ATSlocal (ats_ptr_type, tmp29) ;
ATSlocal (ats_ptr_type, tmp30) ;
ATSlocal (ats_ptr_type, tmp31) ;
ATSlocal (ats_ptr_type, tmp32) ;
ATSlocal (ats_ptr_type, tmp33) ;
ATSlocal (ats_ptr_type, tmp34) ;
// ATSlocal_void (tmp35) ;
ATSlocal (ats_ptr_type, tmp36) ;
// ATSlocal_void (tmp37) ;

__ats_lab_ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_filename_yyres:
tmp27 = ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__token_of_yybeg (arg0) ;
tmp28 = atsopt_filename_full (arg1) ;
tmp29 = atslib_fopen_exn (tmp28, "r") ;
tmp30 = ats_selsin_mac(tmp29, atslab_1) ;
tmp31 = ATS_2d0_2e2_2e10_2src_2libats_lex_lexing_2esats__infile_make_file (tmp30) ;
tmp32 = ats_selsin_mac(tmp31, atslab_1) ;
tmp33 = lexbuf_make_infile (tmp32) ;
tmp34 = ats_selsin_mac(tmp33, atslab_1) ;
/* tmp35 = */ lexing_lexbuf_set (tmp34) ;
tmp36 = yyparse_main (tmp27) ;
/* tmp37 = */ lexing_lexbuf_free () ;
tmp26 = tmp36 ;
return (tmp26) ;
} /* end of [ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_filename_yyres] */

/*
// /home/hwxi/research/Anairiats/src/ats_parser.dats: 4986(line=187, offs=3) -- 5287(line=198, offs=2)
*/
ATSglobaldec()
ats_ptr_type
ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_filename_d0eclst (ats_int_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp38) ;
ATSlocal (ats_ptr_type, tmp39) ;
ATSlocal (ats_bool_type, tmp41) ;
ATSlocal (ats_ptr_type, tmp42) ;
ATSlocal (ats_bool_type, tmp44) ;
ATSlocal (ats_ptr_type, tmp45) ;
ATSlocal (ats_ptr_type, tmp46) ;
ATSlocal (ats_ptr_type, tmp47) ;

__ats_lab_ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_filename_d0eclst:
/* ats_ptr_type tmp39 ; */
tmp39 = (ats_sum_ptr_type)(&ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYBEGnone) ;
tmp41 = flag_is_sta_0 (arg0) ;
if (tmp41) {
tmp42 = (ats_sum_ptr_type)(&ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYBEGd0ecseq_sta) ;
tmp39 = tmp42 ;
} else {
/* empty */
} /* end of [if] */
tmp44 = flag_is_dyn_1 (arg0) ;
if (tmp44) {
tmp45 = (ats_sum_ptr_type)(&ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__YYBEGd0ecseq_dyn) ;
tmp39 = tmp45 ;
} else {
/* empty */
} /* end of [if] */
tmp46 = ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_filename_yyres (tmp39, arg1) ;
if (((ats_sum_ptr_type)tmp46)->tag != 3) { ats_caseof_failure_handle ("/home/hwxi/research/Anairiats/src/ats_parser.dats: 5255(line=196, offs=8) -- 5282(line=196, offs=35)") ; }
tmp47 = ats_caselptrlab_mac(anairiats_sum_0, tmp46, atslab_0) ;
tmp38 = tmp47 ;
return (tmp38) ;
} /* end of [ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__parse_from_filename_d0eclst] */

/* static load function */

extern ats_void_type ATS_2d0_2e2_2e10_2src_2ats_syntax_2esats__staload (void) ;
extern ats_void_type ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__staload (void) ;
extern ats_void_type ATS_2d0_2e2_2e10_2src_2libats_lex_lexing_2esats__staload (void) ;

ats_void_type
ATS_2d0_2e2_2e10_2src_2ats_parser_2edats__staload () {
static int ATS_2d0_2e2_2e10_2src_2ats_parser_2edats__staload_flag = 0 ;
if (ATS_2d0_2e2_2e10_2src_2ats_parser_2edats__staload_flag) return ;
ATS_2d0_2e2_2e10_2src_2ats_parser_2edats__staload_flag = 1 ;

ATS_2d0_2e2_2e10_2src_2ats_syntax_2esats__staload () ;
ATS_2d0_2e2_2e10_2src_2ats_parser_2esats__staload () ;
ATS_2d0_2e2_2e10_2src_2libats_lex_lexing_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type ATS_2d0_2e2_2e10_2src_2ats_parser_2edats__dynload_flag ;

ats_void_type
ATS_2d0_2e2_2e10_2src_2ats_parser_2edats__dynload () {
ATS_2d0_2e2_2e10_2src_2ats_parser_2edats__dynload_flag = 1 ;
ATS_2d0_2e2_2e10_2src_2ats_parser_2edats__staload () ;

#ifdef _ATS_PROOFCHECK
ATS_2d0_2e2_2e10_2prelude_2basics_dyn_2esats__file_mode_lte_r_r_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* marking static variables for GC */

/* marking external values for GC */

/* code for dynamic loading */
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [/home/hwxi/research/Anairiats/bootstrap1/ats_parser_dats.c] */
