/* A Bison parser, made by GNU Bison 2.5.  */

/* Bison implementation for Yacc-like parsers in C
   
      Copyright (C) 1984, 1989-1990, 2000-2011 Free Software Foundation, Inc.
   
   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.
   
   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "2.5"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1

/* Using locations.  */
#define YYLSP_NEEDED 0



/* Copy the first part of user declarations.  */

/* Line 268 of yacc.c  */
#line 17 "ats_grammar.yats"

//
#include <stdio.h> // for [fprintf]
#include "ats_memory.h" // HX: loading [ats_types.h] as well
/*
// HX: this is okay
#define malloc ats_malloc_gc
#define realloc ats_realloc_gc
#define free ats_free_gc
*/
//
// HX-2011-09-06:
//
#define malloc ats_malloc_ngc
#define realloc ats_realloc_ngc
#define free ats_free_ngc

extern void yyerror (char *s) ;

/* ****** ****** */

typedef ats_ptr_type c0har_t ;
typedef ats_ptr_type e0xtcode_t ;
typedef ats_ptr_type f0loat_t ;
typedef ats_ptr_type f0loatsp_t ;
typedef ats_ptr_type i0nt_t ;
typedef ats_ptr_type i0ntsp_t ;
typedef ats_ptr_type s0tring_t ;
typedef ats_ptr_type t0kn_t ;

typedef ats_ptr_type abskind_t ;
typedef ats_ptr_type dcstkind_t ;
typedef ats_ptr_type datakind_t ;
typedef ats_ptr_type stadefkind_t ;
typedef ats_ptr_type valkind_t ;
typedef ats_ptr_type funkind_t ;
typedef ats_ptr_type lamkind_t ;
typedef lamkind_t fixkind_t ;
typedef ats_ptr_type srpifkindtok_t ;

typedef ats_ptr_type i0de_t ;
typedef ats_ptr_type i0delst_t ;
typedef ats_ptr_type i0delstlst_t ;
typedef ats_ptr_type i0dext_t ;
typedef ats_ptr_type l0ab_t ;

typedef ats_ptr_type p0rec_t ;

typedef ats_ptr_type e0xp_t ;
typedef ats_ptr_type e0xplst_t ;
typedef ats_ptr_type e0xpopt_t ;

typedef ats_ptr_type e0fftag_t ;
typedef ats_ptr_type e0fftaglst_t ;
typedef ats_ptr_type e0fftaglstopt_t ;

typedef ats_ptr_type s0rtq_t ;
typedef ats_ptr_type s0rt_t ;
typedef ats_ptr_type s0rtlst_t ;
typedef ats_ptr_type s0rtopt_t ;
typedef ats_ptr_type s0rtpol_t ;

typedef ats_ptr_type d0atsrtcon_t ;
typedef ats_ptr_type d0atsrtconlst_t ;
typedef ats_ptr_type d0atsrtdec_t ;
typedef ats_ptr_type d0atsrtdeclst_t ;

typedef ats_ptr_type s0taq_t ;
typedef ats_ptr_type d0ynq_t ;
typedef ats_ptr_type sqi0de_t ;
typedef ats_ptr_type dqi0de_t ;
typedef ats_ptr_type arrqi0de_t ;
typedef ats_ptr_type tmpqi0de_t ;
typedef ats_ptr_type s0arg_t ;
typedef ats_ptr_type s0arglst_t ;
typedef ats_ptr_type s0arglstlst_t ;
typedef ats_ptr_type s0exp_t ;
typedef ats_ptr_type s0expext_t ; // for external types
typedef ats_ptr_type s0explst_t ;
typedef ats_ptr_type s0expopt_t ;
typedef ats_ptr_type s0explstlst_t ;
typedef ats_ptr_type s0explstopt_t ;
typedef ats_ptr_type labs0explst_t ;
typedef ats_ptr_type s0arrind_t ;
typedef ats_ptr_type t1mps0explstlst_t ; // with location information
typedef ats_ptr_type s0rtext_t ;
typedef ats_ptr_type s0qua_t ;
typedef ats_ptr_type s0qualst_t ;
typedef ats_ptr_type s0qualstlst_t ;
typedef ats_ptr_type s0qualstopt_t ;
typedef ats_ptr_type impqi0de_t ;

typedef ats_ptr_type sp0at_t ;

typedef ats_ptr_type d0atarg_t ;
typedef ats_ptr_type d0atarglst_t ;
typedef ats_ptr_type s0rtdef_t ;
typedef ats_ptr_type s0rtdeflst_t ;
typedef ats_ptr_type s0tacon_t ;
typedef ats_ptr_type s0taconlst_t ;
typedef ats_ptr_type s0tacst_t ;
typedef ats_ptr_type s0tacstlst_t ;
typedef ats_ptr_type s0tavar_t ;
typedef ats_ptr_type s0tavarlst_t ;
typedef ats_ptr_type s0expdef_t ;
typedef ats_ptr_type s0expdeflst_t ;
typedef ats_ptr_type s0aspdec_t ;
typedef ats_ptr_type d0atcon_t ;
typedef ats_ptr_type d0atconlst_t ;
typedef ats_ptr_type d0atdec_t ;
typedef ats_ptr_type d0atdeclst_t ;
typedef ats_ptr_type e0xndec_t ;
typedef ats_ptr_type e0xndeclst_t ;

typedef ats_ptr_type p0arg_t ;
typedef ats_ptr_type p0arglst_t ;
typedef ats_ptr_type d0arg_t ;
typedef ats_ptr_type d0arglst_t ;
typedef ats_ptr_type m0acarg_t ;
typedef ats_ptr_type m0acarglst_t ;
typedef ats_ptr_type extnamopt_t ;
typedef ats_ptr_type d0cstdec_t ;
typedef ats_ptr_type d0cstdeclst_t ;
typedef ats_ptr_type p0at_t ;
typedef ats_ptr_type p0atlst_t ;
typedef ats_ptr_type labp0atlst_t ;
typedef ats_ptr_type s0vararg_t ;
typedef ats_ptr_type s0exparg_t ;
typedef ats_ptr_type f0arg_t ;
typedef ats_ptr_type f0arglst_t ;
typedef ats_ptr_type s0elop_t ;
typedef ats_ptr_type witht0ype_t ;
typedef ats_ptr_type d0exp_t ;
typedef ats_ptr_type d0explst_t ;
typedef ats_ptr_type d0expopt_t ;
typedef ats_ptr_type labd0explst_t ;
typedef ats_ptr_type d0arrind_t ;
typedef ats_ptr_type ifhead_t ;
typedef ats_ptr_type casehead_t ;
typedef ats_ptr_type loophead_t ;
typedef ats_ptr_type tryhead_t ;
typedef ats_ptr_type m0atch_t ;
typedef ats_ptr_type m0atchlst_t ;
typedef ats_ptr_type guap0at_t ;
typedef ats_ptr_type c0lau_t ;
typedef ats_ptr_type c0laulst_t ;
typedef ats_ptr_type sc0lau_t ;
typedef ats_ptr_type sc0laulst_t ;
typedef ats_ptr_type i0nvarg_t ;
typedef ats_ptr_type i0nvarglst_t ;
typedef ats_ptr_type i0nvresstate_t ;
typedef ats_ptr_type loopi0nv_t ;
typedef ats_ptr_type initestpost_t ;
typedef ats_ptr_type v0aldec_t ;
typedef ats_ptr_type v0aldeclst_t ;
typedef ats_ptr_type f0undec_t ;
typedef ats_ptr_type f0undeclst_t ;
typedef ats_ptr_type v0arwth_t ;
typedef ats_ptr_type v0ardec_t ;
typedef ats_ptr_type v0ardeclst_t ;
typedef ats_ptr_type m0acdef_t ;
typedef ats_ptr_type m0acdeflst_t ;
typedef ats_ptr_type i0mpdec_t ;
typedef ats_ptr_type d0ec_t ;
typedef ats_ptr_type d0eclst_t ;
typedef ats_ptr_type d0ecllst_t ;
typedef ats_ptr_type guad0ec_t ;

/* ****** ****** */

typedef ats_ptr_type yyres_t ;

/* ****** ****** */

yyres_t theYYVALyyres ; /* the result of parsing */

/* ****** ****** */

extern abskind_t abskind_prop (void) ;
extern abskind_t abskind_type (void) ;
extern abskind_t abskind_t0ype (void) ;
extern abskind_t abskind_view (void) ;
extern abskind_t abskind_viewtype (void) ;
extern abskind_t abskind_viewt0ype (void) ;

extern dcstkind_t dcstkind_fun (void) ;
extern dcstkind_t dcstkind_val (void) ;
extern dcstkind_t dcstkind_castfn (void) ;
extern dcstkind_t dcstkind_praxi (void) ;
extern dcstkind_t dcstkind_prfun (void) ;
extern dcstkind_t dcstkind_prval (void) ;

extern datakind_t datakind_prop (void) ;
extern datakind_t datakind_type (void) ;
extern datakind_t datakind_view (void) ;
extern datakind_t datakind_viewtype (void) ;

extern stadefkind_t stadefkind_generic (void) ;
extern stadefkind_t stadefkind_prop (t0kn_t) ;
extern stadefkind_t stadefkind_type (t0kn_t) ;
extern stadefkind_t stadefkind_view (t0kn_t) ;
extern stadefkind_t stadefkind_viewtype (t0kn_t) ;

extern valkind_t valkind_val (void) ;
extern valkind_t valkind_valminus (void) ;
extern valkind_t valkind_valplus (void) ;
extern valkind_t valkind_prval (void) ;

extern funkind_t funkind_fn (void) ;
extern funkind_t funkind_fnstar (void) ;
extern funkind_t funkind_fun (void) ;
extern funkind_t funkind_castfn (void) ;
extern funkind_t funkind_prfn (void) ;
extern funkind_t funkind_prfun (void) ;

extern lamkind_t lamkind_lam (t0kn_t) ;
extern lamkind_t lamkind_atlam (t0kn_t) ;
extern lamkind_t lamkind_llam (t0kn_t) ;
extern lamkind_t lamkind_atllam (t0kn_t) ;
extern fixkind_t fixkind_fix (t0kn_t) ;
extern fixkind_t fixkind_atfix (t0kn_t) ;

extern srpifkindtok_t srpifkindtok_if (t0kn_t) ;
extern srpifkindtok_t srpifkindtok_ifdef (t0kn_t) ;
extern srpifkindtok_t srpifkindtok_ifndef (t0kn_t) ;

/* ****** ****** */

extern i0de_t i0de_make_ampersand (t0kn_t) ;
extern i0de_t i0de_make_backslash (t0kn_t) ;
extern i0de_t i0de_make_bang (t0kn_t) ;
extern i0de_t i0de_make_eq (t0kn_t) ;
extern i0de_t i0de_make_gt (t0kn_t) ;
extern i0de_t i0de_make_gtlt (t0kn_t) ;
extern i0de_t i0de_make_lt (t0kn_t) ;
extern i0de_t i0de_make_minusgt (t0kn_t) ;
extern i0de_t i0de_make_minuslt (t0kn_t) ;
extern i0de_t i0de_make_minusltgt (t0kn_t) ;
extern i0de_t i0de_make_module (t0kn_t) ;
extern i0de_t i0de_make_r0ead (t0kn_t) ;
extern i0de_t i0de_make_tilde (t0kn_t) ;
extern i0de_t i0de_make_t0ype (t0kn_t) ;
extern i0de_t i0de_make_viewt0ype (t0kn_t) ;

extern i0de_t i0de_make_DO (t0kn_t) ;
extern i0de_t i0de_make_IN (t0kn_t) ;
extern i0de_t i0de_make_WHILE (t0kn_t) ;

extern i0delst_t i0delst_nil (void) ;
extern i0delst_t i0delst_sing (i0de_t) ;
extern i0delst_t i0delst_cons (i0de_t, i0delst_t) ;

extern i0delstlst_t i0delstlst_nil (void) ;
extern i0delstlst_t i0delstlst_cons (i0delst_t, i0delstlst_t) ;

extern l0ab_t l0ab_ide (i0de_t) ;
extern l0ab_t l0ab_int (i0nt_t) ;

extern i0de_t stai0de_make (i0de_t) ;

/* ****** ****** */

extern p0rec_t p0rec_emp (void) ;
extern p0rec_t p0rec_ide (i0de_t) ;
extern p0rec_t p0rec_int (i0nt_t) ;
extern p0rec_t p0rec_opr (i0de_t, i0de_t/*opr*/, i0nt_t) ;

/* ****** ****** */

extern e0xp_t e0xp_app (e0xp_t, e0xp_t) ;
extern e0xp_t e0xp_char (c0har_t) ;
extern e0xp_t e0xp_eval (t0kn_t, e0xp_t, t0kn_t) ;
extern e0xp_t e0xp_float (f0loat_t) ;
extern e0xp_t e0xp_ide (i0de_t) ;
extern e0xp_t e0xp_int (i0nt_t) ;
extern e0xp_t e0xp_list (t0kn_t, e0xplst_t, t0kn_t) ;
extern e0xp_t e0xp_string (s0tring_t) ;

extern e0xp_t e0xp_FILENAME (t0kn_t) ; // a special string constant
extern e0xp_t e0xp_LOCATION (t0kn_t) ; // a special string constant

extern e0xplst_t e0xplst_nil (void) ;
extern e0xplst_t e0xplst_cons (e0xp_t, e0xplst_t) ;
extern e0xpopt_t e0xpopt_none (void) ;
extern e0xpopt_t e0xpopt_some (e0xp_t) ;

/* ****** ****** */

extern e0fftag_t e0fftag_cst (int, i0de_t) ;
extern e0fftag_t e0fftag_var (i0de_t) ;
extern e0fftag_t e0fftag_var_fun (t0kn_t) ;
extern e0fftag_t e0fftag_int (i0nt_t) ;
extern e0fftaglst_t e0fftaglst_nil (void) ;
extern e0fftaglst_t e0fftaglst_cons (e0fftag_t, e0fftaglst_t) ;
extern e0fftaglstopt_t e0fftaglstopt_none (void) ;
extern e0fftaglstopt_t e0fftaglstopt_some (e0fftaglst_t) ;

/* ****** ****** */

extern s0rtq_t s0rtq_str (s0tring_t) ;
extern s0rtq_t s0rtq_sym (i0de_t) ;

extern s0rt_t s0rt_prop (t0kn_t) ;
extern s0rt_t s0rt_type (t0kn_t) ;
extern s0rt_t s0rt_t0ype (t0kn_t) ;
extern s0rt_t s0rt_view (t0kn_t) ;
extern s0rt_t s0rt_viewtype (t0kn_t) ;
extern s0rt_t s0rt_viewt0ype (t0kn_t) ;

extern s0rt_t s0rt_app (s0rt_t, s0rt_t) ;
extern s0rt_t s0rt_ide (i0de_t) ;
extern s0rt_t s0rt_qid (s0rtq_t, i0de_t) ;
extern s0rt_t s0rt_list (t0kn_t, s0rtlst_t, t0kn_t) ;
extern s0rt_t s0rt_tup (t0kn_t, s0rtlst_t, t0kn_t) ;

extern s0rtlst_t s0rtlst_nil (void) ;
extern s0rtlst_t s0rtlst_cons (s0rt_t, s0rtlst_t) ;

extern s0rtopt_t s0rtopt_none (void) ;
extern s0rtopt_t s0rtopt_some (s0rt_t) ;

extern s0rtpol_t s0rtpol_make (s0rt_t, int) ;

/* ****** ****** */

/*
** datasort declaration
*/
extern d0atsrtcon_t d0atsrtcon_make_none (i0de_t) ;
extern d0atsrtcon_t d0atsrtcon_make_some (i0de_t, s0rt_t) ;
extern d0atsrtconlst_t d0atsrtconlst_nil (void) ;
extern d0atsrtconlst_t d0atsrtconlst_cons (d0atsrtcon_t, d0atsrtconlst_t) ;
extern d0atsrtdec_t d0atsrtdec_make (i0de_t, d0atsrtconlst_t) ;
extern d0atsrtdeclst_t d0atsrtdeclst_nil (void) ;
extern d0atsrtdeclst_t d0atsrtdeclst_cons (d0atsrtdec_t, d0atsrtdeclst_t) ;

/* ****** ****** */

/*
** static qualifiers
*/
extern s0taq_t s0taq_symdot (i0de_t) ;
extern s0taq_t s0taq_symcolon (i0de_t) ;
extern s0taq_t s0taq_fildot (s0tring_t) ;

/*
** dynamic qualifiers
*/
extern d0ynq_t d0ynq_symcolon(i0de_t) ;
extern d0ynq_t d0ynq_symdot(i0de_t) ;
extern d0ynq_t d0ynq_symdot_symcolon(i0de_t, i0de_t) ;
extern d0ynq_t d0ynq_fildot(s0tring_t) ;
extern d0ynq_t d0ynq_fildot_symcolon(s0tring_t, i0de_t) ;

/* ****** ****** */

/*
** (qualified) static identifiers
*/
extern sqi0de_t sqi0de_make_none (i0de_t) ;
extern sqi0de_t sqi0de_make_some (s0taq_t, i0de_t) ;

/*
** (qualified) dynamic identifiers
*/
extern dqi0de_t dqi0de_make_none (i0de_t) ;
extern dqi0de_t dqi0de_make_some (d0ynq_t, i0de_t) ;

/*
** (qualified) array identifiers
*/
extern arrqi0de_t arrqi0de_make_none (i0de_t) ;
extern arrqi0de_t arrqi0de_make_some (d0ynq_t, i0de_t) ;

/*
** (qualified) template identifiers
*/
extern tmpqi0de_t tmpqi0de_make_none (i0de_t) ;
extern tmpqi0de_t tmpqi0de_make_some (d0ynq_t, i0de_t) ;

/* ****** ****** */

/*
** static arguments
*/
extern s0arg_t s0arg_make (i0de_t, s0rtopt_t) ;
extern s0arg_t s0arg_make_none (i0de_t) ;
extern s0arglst_t s0arglst_nil (void) ;
extern s0arglst_t s0arglst_cons (s0arg_t, s0arglst_t) ;
extern s0arglstlst_t s0arglstlst_nil (void) ;
extern s0arglstlst_t s0arglstlst_cons (s0arglst_t, s0arglstlst_t) ;
extern s0arglstlst_t s0arglstlst_cons_ide (i0de_t, s0arglstlst_t) ;

/* ****** ****** */

extern impqi0de_t impqi0de_make_none (dqi0de_t) ;
extern impqi0de_t impqi0de_make_some
  (tmpqi0de_t, s0explst_t, t1mps0explstlst_t, t0kn_t) ;

/* ****** ****** */

extern sp0at_t sp0at_con (sqi0de_t, s0arglst_t, t0kn_t) ;

/* ****** ****** */

/*
** static expressions
*/
extern s0exp_t s0exp_ann (s0exp_t, s0rt_t) ;
extern s0exp_t s0exp_app (s0exp_t, s0exp_t) ;
extern s0exp_t s0exp_char (c0har_t) ;
extern s0exp_t s0exp_exi (t0kn_t, int/*funres*/, s0qualst_t, t0kn_t) ;
extern s0expext_t s0expext_nam (t0kn_t, s0tring_t/*name*/) ;
extern s0expext_t s0expext_app (s0expext_t/*fun*/, s0exp_t/*arg*/) ;
extern s0exp_t s0exp_extern (s0expext_t) ;
extern s0exp_t s0exp_ide (i0de_t) ;
extern s0exp_t s0exp_imp (t0kn_t, e0fftaglst_t, t0kn_t) ;
extern s0exp_t s0exp_imp_emp (t0kn_t) ;
extern s0exp_t s0exp_int (i0nt_t) ;
extern s0exp_t s0exp_intsp_err (i0nt_t) ; /* error handling */
extern s0exp_t s0exp_lams (t0kn_t, s0arglstlst_t, s0rtopt_t, s0exp_t) ;
extern s0exp_t s0exp_list (t0kn_t, s0explst_t, t0kn_t) ;
extern s0exp_t s0exp_list2 (t0kn_t, s0explst_t, s0explst_t, t0kn_t) ;
/*
// HX-2010-12-04: inadequate design
extern s0exp_t s0exp_named (i0de_t, s0exp_t) ;
*/
extern s0exp_t s0exp_opide (t0kn_t, i0de_t) ;
extern s0exp_t s0exp_qid (s0taq_t, i0de_t) ;
extern s0exp_t s0exp_struct (t0kn_t, labs0explst_t, t0kn_t) ;
extern s0exp_t s0exp_tyarr (t0kn_t, s0exp_t, s0arrind_t) ;
extern s0exp_t s0exp_tyrec (int, t0kn_t, labs0explst_t, t0kn_t) ;
extern s0exp_t s0exp_tyrec_ext (t0kn_t, s0tring_t, labs0explst_t, t0kn_t) ;
extern s0exp_t s0exp_tytup (int, t0kn_t, s0explst_t, t0kn_t) ;
extern s0exp_t s0exp_tytup2 (int, t0kn_t, s0explst_t, s0explst_t, t0kn_t) ;
extern s0exp_t s0exp_uni (t0kn_t, s0qualst_t, t0kn_t) ;
extern s0exp_t s0exp_union (t0kn_t, s0exp_t, labs0explst_t, t0kn_t) ;

extern s0explst_t s0explst_nil (void) ;
extern s0explst_t s0explst_cons (s0exp_t, s0explst_t) ;

extern s0expopt_t s0expopt_none (void) ;
extern s0expopt_t s0expopt_some (s0exp_t) ;

extern s0explstlst_t s0explstlst_nil (void) ;
extern s0explstlst_t s0explstlst_cons (s0explst_t, s0explstlst_t) ;

extern s0explstopt_t s0explstopt_none (void) ;
extern s0explstopt_t s0explstopt_some (s0explst_t) ;

extern labs0explst_t labs0explst_nil (void) ;
extern labs0explst_t labs0explst_cons (l0ab_t, s0exp_t, labs0explst_t) ;

extern s0arrind_t s0arrind_make_sing (s0explst_t, t0kn_t) ;
extern s0arrind_t s0arrind_make_cons (s0explst_t, s0arrind_t) ;

extern t1mps0explstlst_t gtlt_t1mps0expseqseq_nil (void) ;
extern t1mps0explstlst_t
gtlt_t1mps0expseqseq_cons_tok (t0kn_t, s0explst_t, t1mps0explstlst_t) ;
// end of [extern]

/* ****** ****** */

extern s0rtext_t s0rtext_srt (s0rt_t) ;
extern s0rtext_t s0rtext_sub
  (t0kn_t, i0de_t, s0rtext_t, s0exp_t, s0explst_t, t0kn_t) ;

extern s0qua_t s0qua_prop(s0exp_t) ;
extern s0qua_t s0qua_vars(i0de_t, i0delst_t, s0rtext_t) ;
extern s0qualst_t s0qualst_nil (void) ;
extern s0qualst_t s0qualst_cons (s0qua_t, s0qualst_t) ;
extern s0qualstlst_t s0qualstlst_nil (void) ;
extern s0qualstlst_t s0qualstlst_cons (s0qualst_t, s0qualstlst_t) ;
extern s0qualstopt_t s0qualstopt_none (void) ;
extern s0qualstopt_t s0qualstopt_some (s0qualst_t) ;

/* ****** ****** */

extern d0atarg_t d0atarg_srt (s0rtpol_t) ;
extern d0atarg_t d0atarg_id_srt (i0de_t, s0rtpol_t) ;
extern d0atarglst_t d0atarglst_nil (void) ;
extern d0atarglst_t d0atarglst_cons (d0atarg_t, d0atarglst_t) ;

/* ****** ****** */

extern s0rtdef_t s0rtdef_make (i0de_t, s0rtext_t) ;
extern s0rtdeflst_t s0rtdeflst_nil (void) ;
extern s0rtdeflst_t s0rtdeflst_cons (s0rtdef_t, s0rtdeflst_t) ;

/* ****** ****** */

extern s0tacon_t s0tacon_make_none_none (i0de_t) ;
extern s0tacon_t s0tacon_make_some_none (i0de_t, d0atarglst_t, t0kn_t) ;
extern s0tacon_t s0tacon_make_none_some (i0de_t, s0exp_t) ;
extern s0tacon_t s0tacon_make_some_some (i0de_t, d0atarglst_t, s0exp_t) ;
extern s0taconlst_t s0taconlst_nil (void) ;
extern s0taconlst_t s0taconlst_cons (s0tacon_t, s0taconlst_t) ;

extern s0tacst_t s0tacst_make_none (i0de_t, s0rt_t) ;
extern s0tacst_t s0tacst_make_some (i0de_t, d0atarglst_t, s0rt_t) ;
extern s0tacstlst_t s0tacstlst_nil (void) ;
extern s0tacstlst_t s0tacstlst_cons (s0tacst_t, s0tacstlst_t) ;

extern s0tavar_t s0tavar_make (i0de_t, s0rt_t) ;
extern s0tavarlst_t s0tavarlst_nil (void) ;
extern s0tavarlst_t s0tavarlst_cons (s0tavar_t, s0tavarlst_t) ;

/* ****** ****** */

extern s0expdef_t s0expdef_make (i0de_t, s0arglstlst_t, s0rtopt_t, s0exp_t) ;
extern s0expdeflst_t s0expdeflst_nil (void) ;
extern s0expdeflst_t s0expdeflst_cons (s0expdef_t, s0expdeflst_t) ;
//
extern s0aspdec_t s0aspdec_make (i0de_t, s0arglstlst_t, s0rtopt_t, s0exp_t) ;
//
extern d0atcon_t
d0atcon_make (s0qualstlst_t, i0de_t, s0explstopt_t, s0expopt_t) ;
extern d0atconlst_t d0atconlst_nil (void) ;
extern d0atconlst_t d0atconlst_cons (d0atcon_t, d0atconlst_t) ;
//
extern d0atdec_t d0atdec_make_none (i0de_t, d0atconlst_t) ;
extern d0atdec_t
d0atdec_make_some (i0de_t, d0atarglst_t, t0kn_t, d0atconlst_t) ;
extern d0atdeclst_t d0atdeclst_nil (void) ;
extern d0atdeclst_t d0atdeclst_cons (d0atdec_t, d0atdeclst_t) ;
//
extern e0xndec_t e0xndec_make (s0qualstlst_t, i0de_t, s0expopt_t) ;
extern e0xndeclst_t e0xndeclst_nil (void) ;
extern e0xndeclst_t e0xndeclst_cons (e0xndec_t, e0xndeclst_t) ;

/* ****** ****** */

extern p0arg_t p0arg_make_none (i0de_t) ;
extern p0arg_t p0arg_make_some (i0de_t, s0exp_t) ;
extern p0arglst_t p0arglst_nil (void) ;
extern p0arglst_t p0arglst_cons (p0arg_t, p0arglst_t) ;
//
extern d0arg_t d0arg_var (i0de_t) ;
extern d0arg_t d0arg_dyn (t0kn_t, p0arglst_t, t0kn_t) ;
extern d0arg_t d0arg_dyn2 (t0kn_t, p0arglst_t, p0arglst_t, t0kn_t) ;
extern d0arg_t d0arg_sta (t0kn_t, s0qualst_t, t0kn_t) ;
extern d0arglst_t d0arglst_nil (void) ;
extern d0arglst_t d0arglst_cons (d0arg_t, d0arglst_t) ;
//
extern m0acarg_t m0acarg_one (i0de_t) ;
extern m0acarg_t m0acarg_lst (t0kn_t, i0delst_t, t0kn_t) ;
extern m0acarglst_t m0acarglst_nil () ;
extern m0acarglst_t m0acarglst_cons (m0acarg_t, m0acarglst_t) ;

/* ****** ****** */

extern extnamopt_t extnamopt_none (void) ;
extern extnamopt_t extnamopt_some (s0tring_t) ;

extern d0cstdec_t
d0cstdec_make (i0de_t, d0arglst_t, e0fftaglstopt_t, s0exp_t, extnamopt_t) ;
extern d0cstdeclst_t d0cstdeclst_nil (void) ;
extern d0cstdeclst_t d0cstdeclst_cons (d0cstdec_t, d0cstdeclst_t) ;

/* ****** ****** */

extern p0at_t p0at_ann (p0at_t, s0exp_t) ;
extern p0at_t p0at_apps (p0at_t, p0atlst_t) ;
extern p0at_t p0at_as (i0de_t, p0at_t) ;
extern p0at_t p0at_char (c0har_t) ;
extern p0at_t p0at_exist (t0kn_t, s0arglst_t, t0kn_t) ;
extern p0at_t p0at_float (f0loat_t); 
extern p0at_t p0at_free (t0kn_t, p0at_t); 
extern p0at_t p0at_ide (i0de_t) ;
extern p0at_t p0at_int (i0nt_t) ;
extern p0at_t p0at_list (t0kn_t, p0atlst_t, t0kn_t) ;
extern p0at_t p0at_list2 (t0kn_t, p0atlst_t, p0atlst_t, t0kn_t) ;
extern p0at_t p0at_lst (t0kn_t, p0atlst_t, t0kn_t) ;
extern p0at_t p0at_qid (d0ynq_t, i0de_t) ;
extern p0at_t p0at_opide (t0kn_t, i0de_t) ;
extern p0at_t p0at_rec (int, t0kn_t, labp0atlst_t, t0kn_t) ;
extern p0at_t p0at_ref (t0kn_t, i0de_t); 
extern p0at_t p0at_refas (t0kn_t, i0de_t, p0at_t); 
extern p0at_t p0at_svararg (t0kn_t, s0vararg_t, t0kn_t) ;
extern p0at_t p0at_string (s0tring_t) ;
extern p0at_t p0at_tup (int, t0kn_t, p0atlst_t, t0kn_t) ;
extern p0at_t p0at_tup2 (int, t0kn_t, p0atlst_t, p0atlst_t, t0kn_t) ;
//
extern p0atlst_t p0atlst_nil (void) ;
extern p0atlst_t p0atlst_cons (p0at_t, p0atlst_t) ;
//
extern labp0atlst_t labp0atlst_nil (void) ;
extern labp0atlst_t labp0atlst_dot (void) ;
extern labp0atlst_t labp0atlst_cons (l0ab_t, p0at_t, labp0atlst_t) ;
//
extern s0vararg_t s0vararg_one (void) ;
extern s0vararg_t s0vararg_all (void) ;
extern s0vararg_t s0vararg_seq (s0arglst_t) ;

/* ****** ****** */

extern s0exparg_t s0exparg_one (void) ;
extern s0exparg_t s0exparg_all (void) ;
extern s0exparg_t s0exparg_seq (s0explst_t) ;

extern f0arg_t f0arg_sta1 (t0kn_t, s0qualst_t, t0kn_t) ;
extern f0arg_t f0arg_sta2 (t0kn_t, s0arglst_t, t0kn_t) ;
extern f0arg_t f0arg_dyn (p0at_t) ;
extern f0arg_t f0arg_met_none (t0kn_t) ;
extern f0arg_t f0arg_met_some (t0kn_t, s0explst_t, t0kn_t) ;
extern f0arglst_t f0arglst_nil (void) ;
extern f0arglst_t f0arglst_cons (f0arg_t, f0arglst_t) ;

extern s0elop_t s0elop_make (int, t0kn_t) ;

extern witht0ype_t witht0ype_none (void) ;
extern witht0ype_t witht0ype_prop (s0exp_t) ;
extern witht0ype_t witht0ype_type (s0exp_t) ;
extern witht0ype_t witht0ype_view (s0exp_t) ;
extern witht0ype_t witht0ype_viewtype (s0exp_t) ;

/* ****** ****** */

/*
** dynamic expressions
*/
extern d0exp_t d0exp_ann (d0exp_t, s0exp_t) ;
//
extern d0exp_t d0exp_apps (d0exp_t, d0explst_t) ;
//
extern d0exp_t d0exp_arrinit_none
  (t0kn_t, s0exp_t, d0explst_t /*elt*/, t0kn_t) ;
extern d0exp_t d0exp_arrinit_some
  (t0kn_t, s0exp_t, d0exp_t /*asz*/, d0explst_t /*elt*/, t0kn_t) ;
//
extern d0exp_t d0exp_arrpsz
  (t0kn_t, s0exp_t, t0kn_t/*lparen*/, d0explst_t, t0kn_t/*rparen*/) ;
//
extern d0exp_t d0exp_arrsub (arrqi0de_t, d0arrind_t) ;
//
extern d0exp_t d0exp_char (t0kn_t) ;
//
extern d0exp_t d0exp_caseof (casehead_t, d0exp_t, t0kn_t, c0laulst_t) ;
//
extern d0exp_t d0exp_crypt (int, t0kn_t) ;
//
extern d0exp_t d0exp_decseq (t0kn_t, d0eclst_t, t0kn_t) ;
//
extern d0exp_t d0exp_delay (int/*lin*/, t0kn_t) ;
//
extern d0exp_t d0exp_dynload (t0kn_t) ;
//
// HX: [d0exp_effmask_*] are implemented in [ats_effect.dats]
//
extern d0exp_t d0exp_effmask_all (t0kn_t) ;
extern d0exp_t d0exp_effmask_exn (t0kn_t) ;
extern d0exp_t d0exp_effmask_ntm (t0kn_t) ;
extern d0exp_t d0exp_effmask_ref (t0kn_t) ;
//
extern d0exp_t d0exp_exist (t0kn_t, s0exparg_t, t0kn_t, d0exp_t, t0kn_t) ;
//
extern d0exp_t d0exp_extval (t0kn_t, s0exp_t, s0tring_t, t0kn_t) ;
//
extern d0exp_t d0exp_fix
  (fixkind_t, i0de_t, f0arglst_t, s0expopt_t, e0fftaglstopt_t, d0exp_t) ;
//
extern d0exp_t d0exp_float (f0loat_t) ;
extern d0exp_t d0exp_floatsp (f0loatsp_t) ;
//
extern d0exp_t d0exp_foldat (t0kn_t, d0explst_t) ;
//
extern d0exp_t d0exp_for_itp (loophead_t, initestpost_t, d0exp_t) ;
//
extern d0exp_t d0exp_freeat (t0kn_t, d0explst_t) ;
//
extern d0exp_t d0exp_ide (i0de_t) ;
extern d0exp_t d0exp_idext (i0de_t) ;
//
extern d0exp_t d0exp_if_none (ifhead_t, d0exp_t, d0exp_t) ;
extern d0exp_t d0exp_if_some (ifhead_t, d0exp_t, d0exp_t, d0exp_t) ;
//
extern d0exp_t d0exp_int (i0nt_t) ;
extern d0exp_t d0exp_intsp (i0ntsp_t) ;
//
extern
d0exp_t d0exp_lam
  (lamkind_t, f0arglst_t, s0expopt_t, e0fftaglstopt_t, d0exp_t) ;
//
extern
d0exp_t d0exp_let_seq (t0kn_t, d0eclst_t, t0kn_t, d0explst_t, t0kn_t) ;
//
extern
d0exp_t d0exp_list (t0kn_t, d0explst_t, t0kn_t) ;
extern
d0exp_t d0exp_list2 (t0kn_t, d0explst_t, d0explst_t, t0kn_t) ;
//
extern
d0exp_t d0exp_lst (
  int, t0kn_t, s0expopt_t, t0kn_t/*lparen*/, d0explst_t, t0kn_t/*rparen*/
) ; // end of [d0exp_lst]
extern d0exp_t d0exp_lst_quote (t0kn_t, d0explst_t, t0kn_t) ;
//
extern d0exp_t d0exp_loopexn (int, t0kn_t) ;
//
extern d0exp_t d0exp_macsyn_cross (t0kn_t, d0explst_t, t0kn_t) ;
extern d0exp_t d0exp_macsyn_decode (t0kn_t, d0explst_t, t0kn_t) ;
extern d0exp_t d0exp_macsyn_encode_seq (t0kn_t, d0explst_t, t0kn_t) ;
//
extern d0exp_t d0exp_opide (t0kn_t, i0de_t) ;
extern d0exp_t d0exp_ptrof (t0kn_t) ;
extern d0exp_t d0exp_qid (d0ynq_t, i0de_t) ;
extern d0exp_t d0exp_raise (t0kn_t, d0exp_t) ;
extern d0exp_t d0exp_rec (int, t0kn_t, labd0explst_t, t0kn_t) ;
extern d0exp_t d0exp_scaseof (casehead_t, s0exp_t, t0kn_t, sc0laulst_t) ;
extern d0exp_t d0exp_sel_lab (t0kn_t, l0ab_t) ;
extern d0exp_t d0exp_sel_ind (t0kn_t, d0arrind_t) ;
extern d0exp_t d0exp_seq (t0kn_t, d0explst_t, t0kn_t) ;
extern d0exp_t d0exp_sexparg (t0kn_t, s0exparg_t, t0kn_t) ;
extern d0exp_t d0exp_showtype (t0kn_t, d0exp_t) ;
extern d0exp_t d0exp_sif (ifhead_t, s0exp_t, d0exp_t, d0exp_t) ;
extern d0exp_t d0exp_string (s0tring_t) ;
extern d0exp_t d0exp_tmpid (tmpqi0de_t, s0explst_t, t1mps0explstlst_t, t0kn_t) ;
extern d0exp_t d0exp_trywith_seq (tryhead_t, d0explst_t, t0kn_t, c0laulst_t) ;
extern d0exp_t d0exp_tup (int, t0kn_t, d0explst_t, t0kn_t) ;
extern d0exp_t d0exp_tup2 (int, t0kn_t, d0explst_t, d0explst_t, t0kn_t) ;
extern d0exp_t d0exp_viewat (t0kn_t) ;
extern d0exp_t d0exp_where (d0exp_t, d0eclst_t, t0kn_t) ;
extern d0exp_t d0exp_while (loophead_t, d0exp_t, d0exp_t) ;
//
extern d0exp_t d0exp_FILENAME (t0kn_t) ; // a special string constant
extern d0exp_t d0exp_LOCATION (t0kn_t) ; // a special string constant
//
extern d0explst_t d0explst_nil (void) ;
extern d0explst_t d0explst_cons (d0exp_t, d0explst_t) ;
extern d0explst_t d0explst_sing (d0exp_t) ;
//
extern d0expopt_t d0expopt_none (void) ;
extern d0expopt_t d0expopt_some (d0exp_t) ;
//
extern labd0explst_t labd0explst_nil (void) ;
extern labd0explst_t labd0explst_cons (l0ab_t, d0exp_t, labd0explst_t) ;
//
extern d0arrind_t d0arrind_make_sing (d0explst_t, t0kn_t) ;
extern d0arrind_t d0arrind_make_cons (d0explst_t, d0arrind_t) ;

/* ****** ****** */

extern ifhead_t ifhead_make (t0kn_t, i0nvresstate_t) ;
extern casehead_t casehead_make (int, t0kn_t, i0nvresstate_t) ;
extern loophead_t loophead_make_none (t0kn_t) ;
extern loophead_t loophead_make_some (t0kn_t, loopi0nv_t, t0kn_t) ;
extern tryhead_t tryhead_make (t0kn_t) ;

/* ****** ****** */

/*
** pattern matching
*/
extern m0atch_t m0atch_make_none (d0exp_t) ;
extern m0atch_t m0atch_make_some (d0exp_t, p0at_t) ;
extern m0atchlst_t m0atchlst_nil (void) ;
extern m0atchlst_t m0atchlst_cons (m0atch_t, m0atchlst_t) ;

extern guap0at_t guap0at_make_none (p0at_t) ;
extern guap0at_t guap0at_make_some (p0at_t, d0exp_t) ;

extern c0lau_t c0lau_make (guap0at_t, int, int, d0exp_t) ;
extern c0laulst_t c0laulst_nil (void) ;
extern c0laulst_t c0laulst_cons (c0lau_t, c0laulst_t) ;

extern sc0lau_t sc0lau_make (sp0at_t, d0exp_t) ;
extern sc0laulst_t sc0laulst_nil (void) ;
extern sc0laulst_t sc0laulst_cons (sc0lau_t, sc0laulst_t) ;

/* ****** ****** */

extern i0nvarg_t i0nvarg_make_none (i0de_t) ;
extern i0nvarg_t i0nvarg_make_some (i0de_t, s0exp_t) ;

extern i0nvarglst_t i0nvarglst_nil (void) ;
extern i0nvarglst_t i0nvarglst_cons (i0nvarg_t, i0nvarglst_t) ;

extern i0nvresstate_t i0nvresstate_none (void) ;
extern i0nvresstate_t i0nvresstate_some (s0qualstopt_t, i0nvarglst_t) ;

extern loopi0nv_t loopi0nv_make
  (s0qualstopt_t, s0explstopt_t, i0nvarglst_t, i0nvresstate_t) ;

extern initestpost_t initestpost_make
  (t0kn_t, d0explst_t, t0kn_t, d0explst_t, t0kn_t, d0explst_t, t0kn_t) ;
// end of [extern]

/* ****** ****** */

extern v0aldec_t v0aldec_make (p0at_t, d0exp_t, witht0ype_t) ;
extern v0aldeclst_t v0aldeclst_nil (void) ;
extern v0aldeclst_t v0aldeclst_cons (v0aldec_t, v0aldeclst_t) ;

extern f0undec_t f0undec_make_none
  (i0de_t, f0arglst_t, d0exp_t, witht0ype_t) ;
extern f0undec_t f0undec_make_some
  (i0de_t, f0arglst_t, e0fftaglstopt_t, s0exp_t, d0exp_t, witht0ype_t) ;
extern f0undeclst_t f0undeclst_nil (void) ;
extern f0undeclst_t f0undeclst_cons (f0undec_t, f0undeclst_t) ;

extern v0arwth_t v0arwth_none () ;
extern v0arwth_t v0arwth_some (i0de_t) ;

extern v0ardec_t v0ardec_make_some_none
  (int /*stadyn*/, i0de_t, v0arwth_t, s0exp_t) ;
extern v0ardec_t v0ardec_make_none_some
  (int /*stadyn*/, i0de_t, v0arwth_t, d0exp_t) ;
extern v0ardec_t v0ardec_make_some_some
  (int /*stadyn*/, i0de_t, s0exp_t, v0arwth_t, d0exp_t) ;
extern v0ardeclst_t v0ardeclst_nil (void) ;
extern v0ardeclst_t v0ardeclst_cons (v0ardec_t, v0ardeclst_t) ;

/* ****** ****** */

extern m0acdef_t m0acdef_make (i0de_t, m0acarglst_t, d0exp_t) ;
extern m0acdeflst_t m0acdeflst_nil (void) ;
extern m0acdeflst_t m0acdeflst_cons (m0acdef_t, m0acdeflst_t) ;

/* ****** ****** */

extern
i0mpdec_t i0mpdec_make (impqi0de_t, f0arglst_t, s0expopt_t, d0exp_t) ;
// end of [i0mpdec_make]
 
/* ****** ****** */

/*
** static and dynamic declarations
*/
extern d0ec_t d0ec_infix (t0kn_t, p0rec_t, int, i0delst_t) ;
extern d0ec_t d0ec_prefix (t0kn_t, p0rec_t, i0delst_t) ;
extern d0ec_t d0ec_postfix (t0kn_t, p0rec_t, i0delst_t) ;
extern d0ec_t d0ec_nonfix (t0kn_t, i0delst_t) ;
extern d0ec_t d0ec_symintr (t0kn_t, i0delst_t) ;
extern d0ec_t d0ec_include (int/*0:sta/1:dyn*/, s0tring_t) ;
extern d0ec_t d0ec_e0xpundef (i0de_t) ;
extern d0ec_t d0ec_e0xpdef (i0de_t, e0xpopt_t) ;
extern d0ec_t d0ec_e0xpact_assert (e0xp_t) ;
extern d0ec_t d0ec_e0xpact_error (e0xp_t) ;
extern d0ec_t d0ec_e0xpact_print (e0xp_t) ;
extern d0ec_t d0ec_srtdefs (s0rtdef_t, s0rtdeflst_t) ;
extern d0ec_t d0ec_datsrts (int/*para*/, d0atsrtdec_t, d0atsrtdeclst_t) ;
extern d0ec_t d0ec_stacons (abskind_t, s0tacon_t, s0taconlst_t) ;
extern d0ec_t d0ec_stacsts (s0tacst_t, s0tacstlst_t) ;
extern d0ec_t d0ec_stavars (s0tavar_t, s0tavarlst_t) ;
extern d0ec_t d0ec_sexpdefs (stadefkind_t, s0expdef_t, s0expdeflst_t) ;
extern d0ec_t d0ec_propdefs (t0kn_t, s0expdef_t, s0expdeflst_t) ;
extern d0ec_t d0ec_typedefs (t0kn_t, s0expdef_t, s0expdeflst_t) ;
extern d0ec_t d0ec_viewdefs (t0kn_t, s0expdef_t, s0expdeflst_t) ;
extern d0ec_t d0ec_viewtypedefs (t0kn_t, s0expdef_t, s0expdeflst_t) ;
extern d0ec_t d0ec_saspdec (s0aspdec_t) ;
extern d0ec_t d0ec_dcstdecs
  (dcstkind_t, s0qualstlst_t, d0cstdec_t, d0cstdeclst_t) ;
extern d0ec_t d0ec_datdecs
  (datakind_t, d0atdec_t, d0atdeclst_t, s0explstopt_t) ;
extern d0ec_t d0ec_exndecs (t0kn_t, e0xndec_t, e0xndeclst_t) ;
//
extern d0ec_t d0ec_classdec_none (t0kn_t, i0de_t) ;
extern d0ec_t d0ec_classdec_some (t0kn_t, i0de_t, s0exp_t) ;
//
extern d0ec_t d0ec_overload (t0kn_t, i0de_t, dqi0de_t) ;
extern d0ec_t d0ec_overload_lrbrackets (t0kn_t, t0kn_t, t0kn_t, dqi0de_t) ;
//
extern d0ec_t d0ec_dynload (s0tring_t) ;
extern d0ec_t d0ec_staload_none (s0tring_t) ;
extern d0ec_t d0ec_staload_some (i0de_t, s0tring_t) ;

extern d0ec_t d0ec_extype (s0tring_t, s0exp_t) ;
extern d0ec_t d0ec_extval (s0tring_t, d0exp_t) ;
extern d0ec_t d0ec_extcode_dyn (e0xtcode_t) ;
extern d0ec_t d0ec_extcode_sta (e0xtcode_t) ;
extern d0ec_t d0ec_valdecs (valkind_t, v0aldec_t, v0aldeclst_t) ;
extern d0ec_t d0ec_valdecs_par (v0aldec_t, v0aldeclst_t) ;
extern d0ec_t d0ec_valdecs_rec (v0aldec_t, v0aldeclst_t) ;
extern d0ec_t d0ec_fundecs (funkind_t, s0qualstlst_t, f0undec_t, f0undeclst_t) ;
extern d0ec_t d0ec_vardecs (v0ardec_t, v0ardeclst_t) ;
extern d0ec_t d0ec_macdefs (int, m0acdef_t, m0acdeflst_t) ;
extern d0ec_t d0ec_impdec (t0kn_t, s0arglstlst_t, i0mpdec_t) ;

extern d0ec_t d0ec_local (t0kn_t, d0eclst_t, d0eclst_t, t0kn_t) ;
extern d0ec_t d0ec_guadec (srpifkindtok_t, guad0ec_t) ;

extern guad0ec_t guad0ec_one (e0xp_t, d0eclst_t, t0kn_t) ;
extern guad0ec_t guad0ec_two (e0xp_t, d0eclst_t, d0eclst_t, t0kn_t) ;
extern guad0ec_t guad0ec_cons (e0xp_t, d0eclst_t, srpifkindtok_t, guad0ec_t) ;

extern d0eclst_t d0eclst_nil (void) ;
extern d0eclst_t d0eclst_cons (d0ec_t, d0eclst_t) ;
extern d0ecllst_t d0ecllst_nil (void) ;
extern d0ecllst_t d0ecllst_cons (d0ecllst_t, d0ec_t) ;
extern d0eclst_t d0ecllst_reverse (d0ecllst_t) ;

/* ****** ****** */

/*
** HX: implemented in [ats_parser.dats]
*/
extern yyres_t atsopt_yyres_i0de (i0de_t) ;
extern yyres_t atsopt_yyres_s0exp (s0exp_t) ;
extern yyres_t atsopt_yyres_d0exp (d0exp_t) ;
extern yyres_t atsopt_yyres_d0eclst (d0eclst_t) ;

/* ****** ****** */

typedef union {
t0kn_t t0kn ;
c0har_t c0har ;
e0xtcode_t e0xtcode ;
f0loat_t f0loat ;
f0loatsp_t f0loatsp ;
i0nt_t i0nt ;
i0ntsp_t i0ntsp ;
s0tring_t s0tring ;
i0de_t i0de ;
i0delst_t i0delst ;
l0ab_t l0ab ;
p0rec_t p0rec ;
abskind_t abskind ;
dcstkind_t dcstkind ;
datakind_t datakind ;
stadefkind_t stadefkind ;
valkind_t valkind ;
funkind_t funkind ;
lamkind_t lamkind ;
fixkind_t fixkind ;
srpifkindtok_t srpifkindtok ;
e0xp_t e0xp ;
e0xplst_t e0xplst ;
e0xpopt_t e0xpopt ;
e0fftag_t e0fftag ;
e0fftaglst_t e0fftaglst ;
e0fftaglstopt_t e0fftaglstopt ;
s0rt_t s0rt ;
s0rtq_t s0rtq ;
s0rtlst_t s0rtlst ;
s0rtopt_t s0rtopt ;
s0rtpol_t s0rtpol ;
d0atsrtcon_t d0atsrtcon ;
d0atsrtconlst_t d0atsrtconlst ;
d0atsrtdec_t d0atsrtdec ;
d0atsrtdeclst_t d0atsrtdeclst ;
s0taq_t s0taq ;
d0ynq_t d0ynq ;
sqi0de_t sqi0de ;
dqi0de_t dqi0de ;
arrqi0de_t arrqi0de ;
tmpqi0de_t tmpqi0de ;
s0arg_t s0arg ;
s0arglst_t s0arglst ;
s0arglstlst_t s0arglstlst ;
sp0at_t sp0at ;
s0exp_t s0exp ;
s0expext_t s0expext ;
s0explst_t s0explst ;
s0expopt_t s0expopt ;
s0explstlst_t s0explstlst ;
s0explstopt_t s0explstopt ;
labs0explst_t labs0explst ;
s0arrind_t s0arrind ;
t1mps0explstlst_t t1mps0explstlst ;
s0qua_t s0qua ;
s0qualst_t s0qualst ;
s0qualstlst_t s0qualstlst ;
s0qualstopt_t s0qualstopt ;
s0rtext_t s0rtext ;
impqi0de_t impqi0de ;
s0rtdef_t s0rtdef ;
s0rtdeflst_t s0rtdeflst ;
d0atarg_t d0atarg ;
d0atarglst_t d0atarglst ;
s0tacon_t s0tacon ;
s0taconlst_t s0taconlst ;
s0tacst_t s0tacst ;
s0tacstlst_t s0tacstlst ;
s0tavar_t s0tavar ;
s0tavarlst_t s0tavarlst ;
s0expdef_t s0expdef ;
s0expdeflst_t s0expdeflst ;
s0aspdec_t s0aspdec ;
d0atcon_t d0atcon ;
d0atconlst_t d0atconlst ;
d0atdec_t d0atdec ;
d0atdeclst_t d0atdeclst ;
e0xndec_t e0xndec ;
e0xndeclst_t e0xndeclst ;
p0arg_t p0arg ;
p0arglst_t p0arglst ;
d0arg_t d0arg ;
d0arglst_t d0arglst ;
extnamopt_t extnamopt ;
d0cstdec_t d0cstdec ;
d0cstdeclst_t d0cstdeclst ;
s0vararg_t s0vararg ;
s0exparg_t s0exparg ;
s0elop_t s0elop ;
witht0ype_t witht0ype ;
p0at_t p0at ;
p0atlst_t p0atlst ;
labp0atlst_t labp0atlst ;
f0arg_t f0arg ;
f0arglst_t f0arglst ;
d0exp_t d0exp ;
d0explst_t d0explst ;
d0expopt_t d0expopt ;
labd0explst_t labd0explst ;
d0arrind_t d0arrind ;
ifhead_t ifhead ;
casehead_t casehead ;
loophead_t loophead ;
tryhead_t tryhead ;
m0atch_t m0atch ;
m0atchlst_t m0atchlst ;
guap0at_t guap0at ;
c0lau_t c0lau ;
c0laulst_t c0laulst ;
sc0lau_t sc0lau ;
sc0laulst_t sc0laulst ;
i0nvarg_t i0nvarg ;
i0nvarglst_t i0nvarglst ;
i0nvresstate_t i0nvresstate ;
loopi0nv_t loopi0nv ;
initestpost_t initestpost ;
m0acarg_t m0acarg ;
m0acarglst_t m0acarglst ;
m0acdef_t m0acdef ;
m0acdeflst_t m0acdeflst ;
v0aldec_t v0aldec ;
v0aldeclst_t v0aldeclst ;
f0undec_t f0undec ;
f0undeclst_t f0undeclst ;
v0arwth_t v0arwth ;
v0ardec_t v0ardec ;
v0ardeclst_t v0ardeclst ;
i0mpdec_t i0mpdec ;
d0ec_t d0ec ;
d0eclst_t d0eclst ;
} YYSTYPE_union ;
#define YYSTYPE YYSTYPE_union



/* Line 268 of yacc.c  */
#line 1113 "ats_grammar_yats.c"

/* Enabling traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* Enabling the token table.  */
#ifndef YYTOKEN_TABLE
# define YYTOKEN_TABLE 0
#endif


/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     YYBEG_i0de = 258,
     YYBEG_s0rtid = 259,
     YYBEG_si0de = 260,
     YYBEG_di0de = 261,
     YYBEG_s0exp = 262,
     YYBEG_d0exp = 263,
     YYBEG_d0ecseq_sta = 264,
     YYBEG_d0ecseq_dyn = 265,
     TOKEN_eof = 266,
     LITERAL_char = 267,
     LITERAL_extcode = 268,
     LITERAL_float = 269,
     LITERAL_floatsp = 270,
     LITERAL_int = 271,
     LITERAL_intsp = 272,
     LITERAL_string = 273,
     IDENTIFIER_alp = 274,
     IDENTIFIER_sym = 275,
     IDENTIFIER_arr = 276,
     IDENTIFIER_tmp = 277,
     IDENTIFIER_ext = 278,
     IDENTIFIER_dlr = 279,
     IDENTIFIER_srp = 280,
     ABSPROP = 281,
     ABSTYPE = 282,
     ABST0YPE = 283,
     ABSVIEW = 284,
     ABSVIEWTYPE = 285,
     ABSVIEWT0YPE = 286,
     AND = 287,
     AS = 288,
     ASSUME = 289,
     ATLAM = 290,
     ATLLAM = 291,
     ATFIX = 292,
     BEGIN = 293,
     BREAK = 294,
     CASE = 295,
     CASEMINUS = 296,
     CASEPLUS = 297,
     CASTFN = 298,
     CLASSDEC = 299,
     CONTINUE = 300,
     DATASORT = 301,
     DATAPARASORT = 302,
     DATAPROP = 303,
     DATATYPE = 304,
     DATAVIEW = 305,
     DATAVIEWTYPE = 306,
     DO = 307,
     DYN = 308,
     DYNLOAD = 309,
     ELSE = 310,
     END = 311,
     EXCEPTION = 312,
     EXTERN = 313,
     FIX = 314,
     FN = 315,
     FNSTAR = 316,
     FOR = 317,
     FORSTAR = 318,
     FUN = 319,
     IF = 320,
     IMPLEMENT = 321,
     IN = 322,
     INFIX = 323,
     INFIXL = 324,
     INFIXR = 325,
     LAM = 326,
     LET = 327,
     LLAM = 328,
     LOCAL = 329,
     MACDEF = 330,
     MACRODEF = 331,
     NONFIX = 332,
     OF = 333,
     OP = 334,
     OVERLOAD = 335,
     PAR = 336,
     POSTFIX = 337,
     PRAXI = 338,
     PREFIX = 339,
     PRFN = 340,
     PRFUN = 341,
     PROPDEF = 342,
     PROPMINUS = 343,
     PROPPLUS = 344,
     PRVAL = 345,
     REC = 346,
     R0EAD = 347,
     SCASE = 348,
     SIF = 349,
     SORTDEF = 350,
     STACST = 351,
     STADEF = 352,
     STAIF = 353,
     STALOAD = 354,
     STAVAR = 355,
     SYMELIM = 356,
     SYMINTR = 357,
     THEN = 358,
     TRY = 359,
     TYPEDEF = 360,
     TYPEMINUS = 361,
     TYPEPLUS = 362,
     T0YPE = 363,
     T0YPEMINUS = 364,
     T0YPEPLUS = 365,
     VAL = 366,
     VALMINUS = 367,
     VALPLUS = 368,
     VAR = 369,
     VIEWDEF = 370,
     VIEWMINUS = 371,
     VIEWPLUS = 372,
     VIEWTYPEDEF = 373,
     VIEWTYPEMINUS = 374,
     VIEWTYPEPLUS = 375,
     VIEWT0YPE = 376,
     VIEWT0YPEMINUS = 377,
     VIEWT0YPEPLUS = 378,
     WHEN = 379,
     WHERE = 380,
     WHILE = 381,
     WHILESTAR = 382,
     WITH = 383,
     WITHPROP = 384,
     WITHTYPE = 385,
     WITHVIEW = 386,
     WITHVIEWTYPE = 387,
     AMPERSAND = 388,
     BACKQUOTE = 389,
     BACKSLASH = 390,
     BANG = 391,
     BAR = 392,
     COMMA = 393,
     COLON = 394,
     SEMICOLON = 395,
     DOT = 396,
     EQ = 397,
     LT = 398,
     GT = 399,
     DOLLAR = 400,
     HASH = 401,
     TILDE = 402,
     DOTDOT = 403,
     DOTDOTDOT = 404,
     EQLT = 405,
     EQGT = 406,
     EQLTGT = 407,
     EQGTGT = 408,
     EQSLASHEQGT = 409,
     EQSLASHEQGTGT = 410,
     GTLT = 411,
     DOTLT = 412,
     GTDOT = 413,
     DOTLTGTDOT = 414,
     MINUSLT = 415,
     MINUSGT = 416,
     MINUSLTGT = 417,
     COLONLT = 418,
     COLONLTGT = 419,
     BACKQUOTELPAREN = 420,
     COMMALPAREN = 421,
     PERCENTLPAREN = 422,
     DLRARRPSZ = 423,
     DLRLST_T = 424,
     DLRLST_VT = 425,
     DLRREC_T = 426,
     DLRREC_VT = 427,
     DLRTUP_T = 428,
     DLRTUP_VT = 429,
     DLRDELAY = 430,
     DLRLDELAY = 431,
     DLRDYNLOAD = 432,
     DLREFFMASK_ALL = 433,
     DLREFFMASK_EXN = 434,
     DLREFFMASK_NTM = 435,
     DLREFFMASK_REF = 436,
     DLRDECRYPT = 437,
     DLRENCRYPT = 438,
     DLREXTERN = 439,
     DLREXTVAL = 440,
     DLREXTYPE = 441,
     DLREXTYPE_STRUCT = 442,
     DLRFOLD = 443,
     DLRUNFOLD = 444,
     DLRRAISE = 445,
     DLRSHOWTYPE = 446,
     SRPFILENAME = 447,
     SRPLOCATION = 448,
     SRPCHARCOUNT = 449,
     SRPLINECOUNT = 450,
     SRPASSERT = 451,
     SRPDEFINE = 452,
     SRPELSE = 453,
     SRPELIF = 454,
     SRPELIFDEF = 455,
     SRPELIFNDEF = 456,
     SRPENDIF = 457,
     SRPERROR = 458,
     SRPIF = 459,
     SRPIFDEF = 460,
     SRPIFNDEF = 461,
     SRPINCLUDE = 462,
     SRPPRINT = 463,
     SRPTHEN = 464,
     SRPUNDEF = 465,
     FOLDAT = 466,
     FREEAT = 467,
     VIEWAT = 468,
     LPAREN = 469,
     RPAREN = 470,
     LBRACKET = 471,
     RBRACKET = 472,
     LBRACE = 473,
     RBRACE = 474,
     ATLPAREN = 475,
     ATLBRACKET = 476,
     ATLBRACE = 477,
     QUOTELPAREN = 478,
     QUOTELBRACKET = 479,
     QUOTELBRACE = 480,
     HASHLPAREN = 481,
     HASHLBRACKET = 482,
     HASHLBRACE = 483,
     PATAS = 484,
     PATFREE = 485,
     SEXPLAM = 486,
     DEXPLAM = 487,
     DEXPFIX = 488,
     CLAUS = 489,
     DEXPCASE = 490,
     DEXPIF = 491,
     DEXPRAISE = 492,
     DEXPSHOWTYPE = 493,
     DEXPTRY = 494,
     DEXPFOR = 495,
     DEXPWHILE = 496,
     BARCLAUSSEQNONE = 497,
     TMPSEXP = 498,
     TMPSARG = 499,
     SARRIND = 500,
     SEXPDARGSEQEMPTY = 501
   };
#endif



#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED

# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
#endif


/* Copy the second part of user declarations.  */


/* Line 343 of yacc.c  */
#line 1400 "ats_grammar_yats.c"

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#elif (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
typedef signed char yytype_int8;
#else
typedef short int yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(e) ((void) (e))
#else
# define YYUSE(e) /* empty */
#endif

/* Identity function, used to suppress warnings about constant conditions.  */
#ifndef lint
# define YYID(n) (n)
#else
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static int
YYID (int yyi)
#else
static int
YYID (yyi)
    int yyi;
#endif
{
  return yyi;
}
#endif

#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (YYID (0))
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
	     && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
	 || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)				\
    do									\
      {									\
	YYSIZE_T yynewbytes;						\
	YYCOPY (&yyptr->Stack_alloc, Stack, yysize);			\
	Stack = &yyptr->Stack_alloc;					\
	yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
	yyptr += yynewbytes / sizeof (*yyptr);				\
      }									\
    while (YYID (0))

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from FROM to TO.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(To, From, Count) \
      __builtin_memcpy (To, From, (Count) * sizeof (*(From)))
#  else
#   define YYCOPY(To, From, Count)		\
      do					\
	{					\
	  YYSIZE_T yyi;				\
	  for (yyi = 0; yyi < (Count); yyi++)	\
	    (To)[yyi] = (From)[yyi];		\
	}					\
      while (YYID (0))
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  179
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   3051

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  247
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  205
/* YYNRULES -- Number of rules.  */
#define YYNRULES  652
/* YYNRULES -- Number of states.  */
#define YYNSTATES  1254

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   501

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    87,    88,    89,    90,    91,    92,    93,    94,
      95,    96,    97,    98,    99,   100,   101,   102,   103,   104,
     105,   106,   107,   108,   109,   110,   111,   112,   113,   114,
     115,   116,   117,   118,   119,   120,   121,   122,   123,   124,
     125,   126,   127,   128,   129,   130,   131,   132,   133,   134,
     135,   136,   137,   138,   139,   140,   141,   142,   143,   144,
     145,   146,   147,   148,   149,   150,   151,   152,   153,   154,
     155,   156,   157,   158,   159,   160,   161,   162,   163,   164,
     165,   166,   167,   168,   169,   170,   171,   172,   173,   174,
     175,   176,   177,   178,   179,   180,   181,   182,   183,   184,
     185,   186,   187,   188,   189,   190,   191,   192,   193,   194,
     195,   196,   197,   198,   199,   200,   201,   202,   203,   204,
     205,   206,   207,   208,   209,   210,   211,   212,   213,   214,
     215,   216,   217,   218,   219,   220,   221,   222,   223,   224,
     225,   226,   227,   228,   229,   230,   231,   232,   233,   234,
     235,   236,   237,   238,   239,   240,   241,   242,   243,   244,
     245,   246
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     7,    11,    15,    19,    23,    27,    31,
      35,    37,    39,    41,    43,    45,    47,    49,    51,    53,
      55,    57,    59,    61,    63,    65,    67,    69,    71,    73,
      75,    77,    79,    81,    83,    85,    87,    89,    91,    93,
      95,    97,    99,   101,   103,   105,   107,   109,   111,   113,
     115,   117,   119,   121,   122,   124,   126,   128,   130,   132,
     134,   136,   138,   140,   142,   144,   146,   148,   150,   151,
     154,   156,   158,   160,   162,   164,   168,   170,   171,   173,
     177,   183,   186,   188,   190,   192,   194,   196,   198,   200,
     202,   206,   210,   211,   214,   215,   219,   220,   222,   224,
     227,   230,   232,   234,   236,   237,   240,   241,   245,   247,
     249,   253,   256,   258,   261,   265,   267,   269,   271,   273,
     275,   277,   279,   281,   284,   288,   292,   293,   296,   297,
     301,   303,   305,   307,   309,   311,   313,   315,   317,   319,
     321,   323,   325,   327,   329,   333,   335,   338,   339,   343,
     347,   348,   352,   355,   358,   362,   365,   368,   372,   376,
     381,   383,   385,   387,   389,   391,   393,   395,   397,   399,
     401,   403,   406,   407,   411,   413,   415,   417,   419,   421,
     423,   425,   427,   429,   431,   434,   436,   438,   440,   443,
     445,   447,   450,   452,   454,   457,   458,   461,   464,   465,
     468,   469,   473,   474,   477,   482,   483,   486,   487,   491,
     492,   497,   502,   504,   506,   510,   516,   518,   520,   522,
     524,   527,   530,   534,   540,   544,   548,   553,   558,   564,
     570,   577,   584,   588,   592,   597,   602,   609,   615,   619,
     621,   625,   629,   633,   636,   638,   641,   644,   645,   649,
     653,   656,   661,   663,   668,   669,   672,   673,   677,   681,
     683,   692,   693,   695,   696,   700,   704,   705,   709,   712,
     713,   718,   719,   725,   727,   730,   732,   733,   736,   737,
     741,   742,   746,   748,   753,   757,   758,   762,   764,   768,
     769,   772,   773,   777,   779,   784,   788,   795,   796,   800,
     804,   811,   812,   816,   820,   821,   825,   831,   832,   836,
     842,   843,   848,   849,   853,   854,   857,   862,   864,   867,
     868,   872,   876,   883,   884,   888,   889,   893,   897,   898,
     902,   904,   908,   909,   912,   913,   917,   919,   923,   929,
     933,   934,   937,   938,   941,   947,   948,   952,   954,   956,
     958,   960,   962,   964,   966,   968,   969,   972,   975,   978,
     981,   984,   988,   992,   997,  1000,  1002,  1004,  1006,  1008,
    1010,  1013,  1016,  1019,  1023,  1029,  1033,  1037,  1041,  1047,
    1053,  1057,  1061,  1065,  1067,  1071,  1072,  1075,  1076,  1079,
    1080,  1084,  1086,  1091,  1092,  1095,  1101,  1105,  1107,  1111,
    1113,  1114,  1117,  1121,  1123,  1124,  1127,  1130,  1134,  1139,
    1146,  1153,  1158,  1163,  1169,  1176,  1180,  1184,  1187,  1190,
    1195,  1201,  1203,  1205,  1207,  1209,  1211,  1213,  1215,  1217,
    1219,  1222,  1225,  1227,  1229,  1231,  1233,  1236,  1239,  1241,
    1243,  1245,  1247,  1249,  1251,  1253,  1255,  1257,  1259,  1266,
    1276,  1282,  1285,  1288,  1292,  1297,  1303,  1307,  1313,  1319,
    1325,  1329,  1333,  1337,  1341,  1345,  1350,  1355,  1361,  1367,
    1371,  1375,  1380,  1385,  1392,  1396,  1400,  1404,  1410,  1414,
    1418,  1419,  1422,  1424,  1426,  1427,  1430,  1433,  1438,  1439,
    1442,  1444,  1446,  1450,  1451,  1454,  1457,  1460,  1463,  1466,
    1469,  1472,  1474,  1478,  1482,  1484,  1485,  1488,  1489,  1493,
    1494,  1496,  1500,  1504,  1505,  1510,  1511,  1517,  1519,  1523,
    1526,  1527,  1531,  1533,  1537,  1541,  1545,  1549,  1553,  1555,
    1558,  1559,  1563,  1567,  1569,  1572,  1573,  1577,  1578,  1582,
    1583,  1587,  1589,  1592,  1596,  1597,  1600,  1601,  1605,  1609,
    1610,  1614,  1615,  1621,  1626,  1634,  1636,  1637,  1640,  1641,
    1645,  1647,  1651,  1652,  1655,  1660,  1661,  1665,  1670,  1671,
    1675,  1681,  1689,  1690,  1694,  1695,  1698,  1703,  1709,  1714,
    1721,  1722,  1726,  1732,  1736,  1740,  1744,  1748,  1752,  1755,
    1758,  1761,  1765,  1768,  1771,  1774,  1778,  1782,  1786,  1790,
    1794,  1798,  1802,  1805,  1810,  1814,  1817,  1822,  1827,  1833,
    1837,  1842,  1846,  1851,  1854,  1859,  1863,  1864,  1867,  1868,
    1871,  1873,  1878,  1880,  1883,  1886,  1892,  1897,  1904,  1910,
    1912,  1913,  1917,  1919,  1925,  1931,  1937,  1941,  1946,  1951,
    1956,  1960,  1964,  1970,  1972,  1975,  1978,  1981,  1986,  1993,
    1999,  2001,  2002
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int16 yyrhs[] =
{
     248,     0,    -1,     9,   446,    11,    -1,    10,   450,    11,
      -1,     3,   260,    11,    -1,     4,   279,    11,    -1,     5,
     291,    11,    -1,     6,   294,    11,    -1,     7,   311,    11,
      -1,     8,   382,    11,    -1,    26,    -1,    27,    -1,    28,
      -1,    29,    -1,    30,    -1,    31,    -1,    64,    -1,   111,
      -1,    43,    -1,    83,    -1,    86,    -1,    90,    -1,    48,
      -1,    49,    -1,    50,    -1,    51,    -1,    97,    -1,    87,
      -1,   105,    -1,   115,    -1,   118,    -1,   111,    -1,   112,
      -1,   113,    -1,    90,    -1,    60,    -1,    61,    -1,    64,
      -1,    43,    -1,    85,    -1,    86,    -1,    71,    -1,    35,
      -1,    73,    -1,    36,    -1,    59,    -1,    37,    -1,   204,
      -1,   205,    -1,   206,    -1,   199,    -1,   200,    -1,   201,
      -1,    -1,   209,    -1,    19,    -1,    20,    -1,   133,    -1,
     135,    -1,   136,    -1,   142,    -1,   144,    -1,   156,    -1,
     143,    -1,   161,    -1,   162,    -1,   147,    -1,    24,    -1,
      -1,   260,   262,    -1,    23,    -1,    52,    -1,   126,    -1,
     260,    -1,    16,    -1,   214,   264,   215,    -1,    19,    -1,
      -1,    16,    -1,   214,   260,   215,    -1,   214,   260,    20,
      16,   215,    -1,   267,   268,    -1,   268,    -1,    12,    -1,
      14,    -1,    16,    -1,    18,    -1,   192,    -1,   193,    -1,
     260,    -1,   214,   269,   215,    -1,   167,   267,   215,    -1,
      -1,   267,   270,    -1,    -1,   138,   267,   270,    -1,    -1,
     267,    -1,    19,    -1,   136,   272,    -1,   147,   272,    -1,
     272,    -1,    64,    -1,    16,    -1,    -1,   273,   275,    -1,
      -1,   138,   273,   275,    -1,   139,    -1,   164,    -1,   163,
     274,   144,    -1,   277,   280,    -1,   280,    -1,   261,   141,
      -1,   145,    18,   141,    -1,    19,    -1,    20,    -1,   108,
      -1,   121,    -1,   135,    -1,   161,    -1,   162,    -1,   279,
      -1,   278,   279,    -1,   214,   281,   215,    -1,   220,   281,
     215,    -1,    -1,   277,   282,    -1,    -1,   138,   277,   282,
      -1,   277,    -1,    88,    -1,    89,    -1,   106,    -1,   107,
      -1,   109,    -1,   110,    -1,   116,    -1,   117,    -1,   119,
      -1,   120,    -1,   122,    -1,   123,    -1,   260,    -1,   260,
      78,   277,    -1,   286,    -1,   284,   286,    -1,    -1,   137,
     284,   286,    -1,   260,   142,   285,    -1,    -1,    32,   287,
     288,    -1,   261,   141,    -1,   261,   139,    -1,   145,    18,
     141,    -1,   261,   141,    -1,   261,   139,    -1,   261,   261,
     139,    -1,   145,    18,   141,    -1,   145,    18,   261,   139,
      -1,    19,    -1,    20,    -1,    92,    -1,   133,    -1,   135,
      -1,   136,    -1,   144,    -1,   143,    -1,   161,    -1,   147,
      -1,   291,    -1,   289,   291,    -1,    -1,   138,   291,   293,
      -1,    19,    -1,    20,    -1,   135,    -1,   136,    -1,   142,
      -1,   144,    -1,   156,    -1,   143,    -1,   147,    -1,   294,
      -1,   290,   294,    -1,    19,    -1,    20,    -1,   294,    -1,
      79,   294,    -1,    21,    -1,   298,    -1,   290,   298,    -1,
      22,    -1,   300,    -1,   290,   300,    -1,    -1,   139,   277,
      -1,   291,   302,    -1,    -1,   303,   305,    -1,    -1,   138,
     303,   305,    -1,    -1,   291,   306,    -1,   214,   304,   215,
     306,    -1,    -1,   303,   308,    -1,    -1,   138,   303,   308,
      -1,    -1,   218,   307,   219,   309,    -1,   292,   214,   304,
     215,    -1,   313,    -1,   314,    -1,   311,   139,   277,    -1,
      71,   306,   302,   151,   311,    -1,    12,    -1,    16,    -1,
      17,    -1,   291,    -1,    79,   291,    -1,   289,   291,    -1,
     214,   321,   215,    -1,   214,   321,   137,   321,   215,    -1,
     220,   321,   215,    -1,   223,   321,   215,    -1,   173,   214,
     321,   215,    -1,   174,   214,   321,   215,    -1,   220,   321,
     137,   321,   215,    -1,   223,   321,   137,   321,   215,    -1,
     173,   214,   321,   137,   321,   215,    -1,   174,   214,   321,
     137,   321,   215,    -1,   222,   325,   219,    -1,   225,   325,
     219,    -1,   171,   218,   325,   219,    -1,   172,   218,   325,
     219,    -1,   187,    18,    78,   218,   325,   219,    -1,   221,
     311,   217,   216,   316,    -1,   160,   274,   144,    -1,   162,
      -1,   218,   318,   219,    -1,   216,   318,   217,    -1,   227,
     318,   217,    -1,   313,   312,    -1,   312,    -1,   186,    18,
      -1,   314,   312,    -1,    -1,   218,   311,   219,    -1,   216,
     311,   217,    -1,   321,   217,    -1,   321,   217,   216,   316,
      -1,   313,    -1,   291,   293,   139,   320,    -1,    -1,   317,
     319,    -1,    -1,   137,   317,   319,    -1,   140,   317,   319,
      -1,   277,    -1,   218,   291,   139,   320,   137,   311,   322,
     219,    -1,    -1,   324,    -1,    -1,   137,   311,   322,    -1,
     140,   311,   322,    -1,    -1,   138,   311,   323,    -1,   311,
     323,    -1,    -1,   264,   142,   311,   326,    -1,    -1,   138,
     264,   142,   311,   326,    -1,   312,    -1,   327,   312,    -1,
     327,    -1,    -1,   328,   330,    -1,    -1,   138,   328,   330,
      -1,    -1,   156,   329,   331,    -1,   295,    -1,   301,   329,
     331,   144,    -1,   279,   142,   320,    -1,    -1,    32,   333,
     334,    -1,   283,    -1,   260,   139,   283,    -1,    -1,   335,
     337,    -1,    -1,   138,   335,   337,    -1,   291,    -1,   291,
     214,   336,   215,    -1,   291,   142,   311,    -1,   291,   214,
     336,   215,   142,   311,    -1,    -1,    32,   338,   339,    -1,
     291,   139,   277,    -1,   291,   214,   336,   215,   139,   277,
      -1,    -1,    32,   340,   341,    -1,   291,   139,   277,    -1,
      -1,    32,   342,   343,    -1,   291,   306,   302,   142,   311,
      -1,    -1,    32,   344,   345,    -1,   292,   306,   302,   142,
     311,    -1,    -1,   218,   318,   219,   347,    -1,    -1,   214,
     321,   215,    -1,    -1,    78,   311,    -1,   347,   294,   348,
     349,    -1,   352,    -1,   350,   352,    -1,    -1,   137,   350,
     352,    -1,   291,   142,   351,    -1,   291,   214,   336,   215,
     142,   351,    -1,    -1,    32,   353,   354,    -1,    -1,   125,
     344,   345,    -1,   347,   294,   349,    -1,    -1,    32,   356,
     357,    -1,   296,    -1,   296,   139,   311,    -1,    -1,   358,
     360,    -1,    -1,   138,   358,   360,    -1,   296,    -1,   214,
     359,   215,    -1,   214,   359,   137,   359,   215,    -1,   218,
     318,   219,    -1,    -1,   361,   362,    -1,    -1,   142,    18,
      -1,   294,   362,   276,   311,   363,    -1,    -1,    32,   364,
     365,    -1,   148,    -1,   149,    -1,   304,    -1,   148,    -1,
     149,    -1,   324,    -1,   141,    -1,   161,    -1,    -1,   129,
     311,    -1,   130,   311,    -1,   131,   311,    -1,   132,   311,
      -1,   371,   373,    -1,   370,   139,   311,    -1,   296,    33,
     370,    -1,   136,   296,    33,   370,    -1,   147,   370,    -1,
      12,    -1,    16,    -1,    14,    -1,    18,    -1,   296,    -1,
     136,   296,    -1,    79,   296,    -1,   290,   296,    -1,   214,
     374,   215,    -1,   214,   374,   137,   374,   215,    -1,   224,
     374,   217,    -1,   220,   374,   215,    -1,   223,   374,   215,
      -1,   220,   374,   137,   374,   215,    -1,   223,   374,   137,
     374,   215,    -1,   222,   376,   219,    -1,   225,   376,   219,
      -1,   216,   304,   217,    -1,   371,    -1,   218,   366,   219,
      -1,    -1,   372,   373,    -1,    -1,   370,   375,    -1,    -1,
     138,   370,   375,    -1,   149,    -1,   264,   142,   370,   377,
      -1,    -1,   138,   149,    -1,   138,   264,   142,   370,   377,
      -1,   218,   318,   219,    -1,   371,    -1,   157,   321,   158,
      -1,   159,    -1,    -1,   378,   379,    -1,   218,   304,   219,
      -1,   371,    -1,    -1,   380,   381,    -1,   383,   387,    -1,
     382,   139,   311,    -1,   392,   382,   103,   382,    -1,   392,
     382,   103,   382,    55,   382,    -1,   393,   311,   103,   382,
      55,   382,    -1,   394,   382,    78,   410,    -1,   395,   311,
      78,   413,    -1,   255,   379,   389,   390,   382,    -1,   256,
     294,   379,   389,   390,   382,    -1,   396,   424,   382,    -1,
     397,   383,   382,    -1,   190,   382,    -1,   191,   382,    -1,
     398,   401,   128,   410,    -1,   382,   125,   218,   450,   219,
      -1,    12,    -1,    14,    -1,    15,    -1,    16,    -1,    17,
      -1,    18,    -1,   192,    -1,   193,    -1,   294,    -1,    79,
     294,    -1,   290,   260,    -1,   263,    -1,   133,    -1,    39,
      -1,    45,    -1,   211,   385,    -1,   212,   385,    -1,   213,
      -1,   182,    -1,   183,    -1,   175,    -1,   176,    -1,   177,
      -1,   178,    -1,   179,    -1,   180,    -1,   181,    -1,   221,
     311,   217,   214,   399,   215,    -1,   221,   311,   217,   216,
     382,   217,   214,   399,   215,    -1,   168,   315,   214,   399,
     215,    -1,   299,   388,    -1,   368,   264,    -1,   368,   216,
     388,    -1,   301,   329,   331,   144,    -1,   227,   367,   137,
     382,   217,    -1,   214,   399,   215,    -1,   214,   399,   137,
     399,   215,    -1,   169,   315,   214,   399,   215,    -1,   170,
     315,   214,   399,   215,    -1,   224,   399,   217,    -1,    38,
     401,    56,    -1,   214,   402,   215,    -1,   220,   399,   215,
      -1,   223,   399,   215,    -1,   173,   214,   399,   215,    -1,
     174,   214,   399,   215,    -1,   220,   399,   137,   399,   215,
      -1,   223,   399,   137,   399,   215,    -1,   222,   403,   219,
      -1,   225,   403,   219,    -1,   171,   218,   403,   219,    -1,
     172,   218,   403,   219,    -1,   185,   214,   311,   138,    18,
     215,    -1,   167,   382,   215,    -1,   166,   382,   215,    -1,
     165,   401,   215,    -1,    72,   450,    67,   401,    56,    -1,
     218,   450,   219,    -1,   218,   367,   219,    -1,    -1,   384,
     385,    -1,   383,    -1,   384,    -1,    -1,   386,   387,    -1,
     399,   217,    -1,   399,   217,   216,   388,    -1,    -1,   139,
     311,    -1,   151,    -1,   152,    -1,   150,   274,   144,    -1,
      -1,   422,   151,    -1,    65,   391,    -1,    94,   391,    -1,
      40,   391,    -1,    41,   391,    -1,    42,   391,    -1,    93,
     391,    -1,    62,    -1,    63,   423,   151,    -1,   127,   423,
     151,    -1,   104,    -1,    -1,   382,   400,    -1,    -1,   138,
     382,   400,    -1,    -1,   382,    -1,   382,   140,   401,    -1,
     382,   140,   401,    -1,    -1,   264,   142,   382,   404,    -1,
      -1,   138,   264,   142,   382,   404,    -1,   382,    -1,   382,
      33,   370,    -1,   405,   407,    -1,    -1,    32,   405,   407,
      -1,   370,    -1,   370,   124,   406,    -1,   408,   151,   382,
      -1,   408,   153,   382,    -1,   408,   154,   382,    -1,   408,
     155,   382,    -1,   411,    -1,   409,   411,    -1,    -1,   137,
     409,   411,    -1,   310,   151,   382,    -1,   414,    -1,   412,
     414,    -1,    -1,   137,   412,   414,    -1,    -1,   218,   318,
     219,    -1,    -1,   157,   321,   158,    -1,   159,    -1,   294,
     139,    -1,   294,   139,   311,    -1,    -1,   417,   419,    -1,
      -1,   138,   417,   419,    -1,   214,   418,   215,    -1,    -1,
     216,   318,   217,    -1,    -1,   139,   421,   214,   418,   215,
      -1,   415,   416,   420,   422,    -1,   214,   399,   140,   399,
     140,   399,   215,    -1,   296,    -1,    -1,   425,   427,    -1,
      -1,   138,   425,   427,    -1,   425,    -1,   214,   426,   215,
      -1,    -1,   428,   429,    -1,   294,   429,   142,   382,    -1,
      -1,    32,   430,   431,    -1,   370,   142,   382,   369,    -1,
      -1,    32,   432,   433,    -1,   297,   379,   142,   382,   369,
      -1,   297,   379,   276,   311,   142,   382,   369,    -1,    -1,
      32,   434,   435,    -1,    -1,   128,   296,    -1,   296,   436,
     142,   382,    -1,   136,   296,   436,   142,   382,    -1,   296,
     139,   311,   436,    -1,   296,   139,   311,   436,   142,   382,
      -1,    -1,    32,   437,   438,    -1,   332,   381,   389,   142,
     382,    -1,    68,   266,   262,    -1,    69,   266,   262,    -1,
      70,   266,   262,    -1,    84,   266,   262,    -1,    82,   266,
     262,    -1,    77,   262,    -1,   102,   262,    -1,   210,   260,
      -1,   197,   260,   271,    -1,   196,   267,    -1,   203,   267,
      -1,   208,   267,    -1,    95,   333,   334,    -1,    46,   287,
     288,    -1,    47,   287,   288,    -1,   249,   338,   339,    -1,
      96,   340,   341,    -1,   100,   342,   343,    -1,   252,   344,
     345,    -1,    34,   346,    -1,   251,   353,   354,   355,    -1,
      57,   356,   357,    -1,    44,   291,    -1,    44,   291,   139,
     311,    -1,    80,   294,   128,   295,    -1,    80,   216,   217,
     128,   295,    -1,    75,   430,   431,    -1,    75,    91,   430,
     431,    -1,    76,   430,   431,    -1,    76,    91,   430,   431,
      -1,    99,    18,    -1,    99,   265,   142,    18,    -1,   218,
     318,   219,    -1,    -1,   441,   442,    -1,    -1,   443,   140,
      -1,   440,    -1,   250,   442,   364,   365,    -1,    13,    -1,
     257,   445,    -1,   207,    18,    -1,    74,   446,    67,   446,
      56,    -1,   267,   259,   446,   202,    -1,   267,   259,   446,
     198,   446,   202,    -1,   267,   259,   446,   258,   445,    -1,
     447,    -1,    -1,   447,   444,   443,    -1,   440,    -1,    58,
     250,   442,   364,   365,    -1,    58,   105,    18,   142,   311,
      -1,    58,   111,    18,   142,   382,    -1,   253,   432,   433,
      -1,   111,    81,   432,   433,    -1,   111,    91,   432,   433,
      -1,   254,   442,   434,   435,    -1,   114,   437,   438,    -1,
      66,   309,   439,    -1,    74,   450,    67,   450,    56,    -1,
      13,    -1,   257,   449,    -1,   207,    18,    -1,    54,    18,
      -1,   267,   259,   450,   202,    -1,   267,   259,   450,   198,
     450,   202,    -1,   267,   259,   450,   258,   449,    -1,   451,
      -1,    -1,   451,   448,   443,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,  1560,  1560,  1561,  1562,  1563,  1564,  1565,  1566,  1567,
    1571,  1572,  1573,  1574,  1575,  1576,  1580,  1581,  1582,  1583,
    1584,  1585,  1589,  1590,  1591,  1592,  1596,  1597,  1598,  1599,
    1600,  1604,  1605,  1606,  1607,  1611,  1612,  1613,  1614,  1615,
    1616,  1620,  1621,  1622,  1623,  1627,  1628,  1632,  1633,  1634,
    1638,  1639,  1640,  1644,  1645,  1649,  1650,  1651,  1652,  1653,
    1654,  1655,  1656,  1657,  1658,  1659,  1660,  1664,  1668,  1669,
    1673,  1674,  1675,  1679,  1680,  1681,  1685,  1689,  1690,  1691,
    1692,  1696,  1697,  1701,  1702,  1703,  1704,  1705,  1706,  1707,
    1708,  1709,  1713,  1714,  1718,  1719,  1723,  1724,  1728,  1732,
    1733,  1734,  1735,  1736,  1740,  1741,  1745,  1746,  1750,  1751,
    1752,  1756,  1757,  1761,  1762,  1766,  1767,  1768,  1769,  1770,
    1771,  1772,  1776,  1777,  1778,  1779,  1783,  1784,  1788,  1789,
    1793,  1794,  1795,  1796,  1797,  1798,  1799,  1800,  1801,  1802,
    1803,  1804,  1805,  1809,  1810,  1814,  1815,  1819,  1820,  1824,
    1828,  1829,  1833,  1834,  1835,  1839,  1840,  1841,  1842,  1843,
    1847,  1848,  1849,  1850,  1851,  1852,  1853,  1854,  1855,  1856,
    1860,  1861,  1865,  1866,  1870,  1871,  1872,  1873,  1874,  1875,
    1876,  1877,  1878,  1882,  1883,  1887,  1888,  1892,  1893,  1897,
    1901,  1902,  1906,  1910,  1911,  1915,  1916,  1920,  1924,  1925,
    1929,  1930,  1934,  1935,  1936,  1940,  1941,  1945,  1946,  1950,
    1951,  1955,  1959,  1960,  1961,  1962,  1966,  1967,  1968,  1969,
    1970,  1971,  1972,  1973,  1974,  1975,  1976,  1977,  1978,  1979,
    1980,  1981,  1982,  1983,  1984,  1985,  1986,  1987,  1988,  1989,
    1990,  1991,  1992,  1996,  1997,  2001,  2002,  2006,  2007,  2008,
    2012,  2013,  2017,  2018,  2022,  2023,  2027,  2028,  2029,  2033,
    2034,  2038,  2039,  2043,  2044,  2045,  2049,  2050,  2054,  2058,
    2059,  2063,  2064,  2068,  2069,  2073,  2077,  2078,  2082,  2083,
    2087,  2088,  2092,  2093,  2097,  2101,  2102,  2106,  2107,  2111,
    2112,  2116,  2117,  2121,  2122,  2123,  2124,  2128,  2129,  2133,
    2134,  2138,  2139,  2143,  2147,  2148,  2152,  2156,  2157,  2161,
    2165,  2166,  2170,  2171,  2175,  2176,  2180,  2184,  2185,  2189,
    2190,  2194,  2195,  2199,  2200,  2204,  2205,  2209,  2213,  2214,
    2218,  2219,  2223,  2224,  2228,  2229,  2233,  2234,  2235,  2236,
    2240,  2241,  2245,  2246,  2250,  2254,  2255,  2259,  2260,  2261,
    2265,  2266,  2267,  2271,  2272,  2276,  2277,  2278,  2279,  2280,
    2284,  2285,  2286,  2287,  2288,  2292,  2293,  2294,  2295,  2296,
    2297,  2298,  2299,  2300,  2301,  2302,  2303,  2304,  2305,  2306,
    2307,  2308,  2309,  2313,  2314,  2318,  2319,  2323,  2324,  2328,
    2329,  2333,  2334,  2338,  2339,  2340,  2344,  2345,  2346,  2347,
    2351,  2352,  2356,  2357,  2361,  2362,  2366,  2367,  2368,  2369,
    2370,  2371,  2372,  2373,  2374,  2375,  2376,  2377,  2378,  2379,
    2380,  2384,  2385,  2386,  2387,  2388,  2389,  2390,  2391,  2392,
    2393,  2394,  2395,  2396,  2397,  2398,  2399,  2400,  2401,  2402,
    2403,  2404,  2405,  2406,  2407,  2408,  2409,  2410,  2411,  2412,
    2413,  2414,  2415,  2416,  2417,  2418,  2419,  2420,  2421,  2422,
    2423,  2424,  2425,  2426,  2427,  2428,  2429,  2430,  2431,  2432,
    2433,  2434,  2435,  2436,  2437,  2438,  2439,  2440,  2441,  2445,
    2449,  2450,  2454,  2455,  2459,  2460,  2464,  2465,  2469,  2470,
    2474,  2475,  2476,  2480,  2481,  2485,  2489,  2493,  2494,  2495,
    2499,  2503,  2504,  2508,  2512,  2516,  2517,  2521,  2522,  2526,
    2527,  2528,  2532,  2536,  2537,  2541,  2542,  2546,  2547,  2551,
    2555,  2556,  2560,  2561,  2565,  2566,  2567,  2568,  2572,  2573,
    2577,  2578,  2582,  2586,  2587,  2591,  2592,  2596,  2597,  2601,
    2602,  2603,  2607,  2608,  2612,  2613,  2617,  2618,  2622,  2626,
    2627,  2631,  2632,  2636,  2640,  2644,  2648,  2649,  2653,  2654,
    2658,  2659,  2663,  2664,  2668,  2672,  2673,  2677,  2681,  2682,
    2686,  2687,  2691,  2692,  2696,  2697,  2701,  2702,  2703,  2704,
    2708,  2709,  2713,  2717,  2718,  2719,  2720,  2721,  2722,  2723,
    2724,  2725,  2726,  2727,  2728,  2729,  2730,  2731,  2732,  2733,
    2734,  2735,  2736,  2737,  2738,  2739,  2740,  2741,  2742,  2743,
    2744,  2745,  2746,  2747,  2748,  2752,  2756,  2757,  2761,  2762,
    2766,  2767,  2768,  2769,  2770,  2771,  2775,  2776,  2777,  2781,
    2785,  2786,  2790,  2791,  2792,  2793,  2794,  2795,  2796,  2797,
    2798,  2799,  2800,  2801,  2802,  2803,  2804,  2808,  2809,  2810,
    2814,  2818,  2819
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "YYBEG_i0de", "YYBEG_s0rtid",
  "YYBEG_si0de", "YYBEG_di0de", "YYBEG_s0exp", "YYBEG_d0exp",
  "YYBEG_d0ecseq_sta", "YYBEG_d0ecseq_dyn", "TOKEN_eof", "LITERAL_char",
  "LITERAL_extcode", "LITERAL_float", "LITERAL_floatsp", "LITERAL_int",
  "LITERAL_intsp", "LITERAL_string", "IDENTIFIER_alp", "IDENTIFIER_sym",
  "IDENTIFIER_arr", "IDENTIFIER_tmp", "IDENTIFIER_ext", "IDENTIFIER_dlr",
  "IDENTIFIER_srp", "ABSPROP", "ABSTYPE", "ABST0YPE", "ABSVIEW",
  "ABSVIEWTYPE", "ABSVIEWT0YPE", "AND", "AS", "ASSUME", "ATLAM", "ATLLAM",
  "ATFIX", "BEGIN", "BREAK", "CASE", "CASEMINUS", "CASEPLUS", "CASTFN",
  "CLASSDEC", "CONTINUE", "DATASORT", "DATAPARASORT", "DATAPROP",
  "DATATYPE", "DATAVIEW", "DATAVIEWTYPE", "DO", "DYN", "DYNLOAD", "ELSE",
  "END", "EXCEPTION", "EXTERN", "FIX", "FN", "FNSTAR", "FOR", "FORSTAR",
  "FUN", "IF", "IMPLEMENT", "IN", "INFIX", "INFIXL", "INFIXR", "LAM",
  "LET", "LLAM", "LOCAL", "MACDEF", "MACRODEF", "NONFIX", "OF", "OP",
  "OVERLOAD", "PAR", "POSTFIX", "PRAXI", "PREFIX", "PRFN", "PRFUN",
  "PROPDEF", "PROPMINUS", "PROPPLUS", "PRVAL", "REC", "R0EAD", "SCASE",
  "SIF", "SORTDEF", "STACST", "STADEF", "STAIF", "STALOAD", "STAVAR",
  "SYMELIM", "SYMINTR", "THEN", "TRY", "TYPEDEF", "TYPEMINUS", "TYPEPLUS",
  "T0YPE", "T0YPEMINUS", "T0YPEPLUS", "VAL", "VALMINUS", "VALPLUS", "VAR",
  "VIEWDEF", "VIEWMINUS", "VIEWPLUS", "VIEWTYPEDEF", "VIEWTYPEMINUS",
  "VIEWTYPEPLUS", "VIEWT0YPE", "VIEWT0YPEMINUS", "VIEWT0YPEPLUS", "WHEN",
  "WHERE", "WHILE", "WHILESTAR", "WITH", "WITHPROP", "WITHTYPE",
  "WITHVIEW", "WITHVIEWTYPE", "AMPERSAND", "BACKQUOTE", "BACKSLASH",
  "BANG", "BAR", "COMMA", "COLON", "SEMICOLON", "DOT", "EQ", "LT", "GT",
  "DOLLAR", "HASH", "TILDE", "DOTDOT", "DOTDOTDOT", "EQLT", "EQGT",
  "EQLTGT", "EQGTGT", "EQSLASHEQGT", "EQSLASHEQGTGT", "GTLT", "DOTLT",
  "GTDOT", "DOTLTGTDOT", "MINUSLT", "MINUSGT", "MINUSLTGT", "COLONLT",
  "COLONLTGT", "BACKQUOTELPAREN", "COMMALPAREN", "PERCENTLPAREN",
  "DLRARRPSZ", "DLRLST_T", "DLRLST_VT", "DLRREC_T", "DLRREC_VT",
  "DLRTUP_T", "DLRTUP_VT", "DLRDELAY", "DLRLDELAY", "DLRDYNLOAD",
  "DLREFFMASK_ALL", "DLREFFMASK_EXN", "DLREFFMASK_NTM", "DLREFFMASK_REF",
  "DLRDECRYPT", "DLRENCRYPT", "DLREXTERN", "DLREXTVAL", "DLREXTYPE",
  "DLREXTYPE_STRUCT", "DLRFOLD", "DLRUNFOLD", "DLRRAISE", "DLRSHOWTYPE",
  "SRPFILENAME", "SRPLOCATION", "SRPCHARCOUNT", "SRPLINECOUNT",
  "SRPASSERT", "SRPDEFINE", "SRPELSE", "SRPELIF", "SRPELIFDEF",
  "SRPELIFNDEF", "SRPENDIF", "SRPERROR", "SRPIF", "SRPIFDEF", "SRPIFNDEF",
  "SRPINCLUDE", "SRPPRINT", "SRPTHEN", "SRPUNDEF", "FOLDAT", "FREEAT",
  "VIEWAT", "LPAREN", "RPAREN", "LBRACKET", "RBRACKET", "LBRACE", "RBRACE",
  "ATLPAREN", "ATLBRACKET", "ATLBRACE", "QUOTELPAREN", "QUOTELBRACKET",
  "QUOTELBRACE", "HASHLPAREN", "HASHLBRACKET", "HASHLBRACE", "PATAS",
  "PATFREE", "SEXPLAM", "DEXPLAM", "DEXPFIX", "CLAUS", "DEXPCASE",
  "DEXPIF", "DEXPRAISE", "DEXPSHOWTYPE", "DEXPTRY", "DEXPFOR", "DEXPWHILE",
  "BARCLAUSSEQNONE", "TMPSEXP", "TMPSARG", "SARRIND", "SEXPDARGSEQEMPTY",
  "$accept", "theStartEntry", "abskind", "dcstkind", "datakind",
  "stadefkind", "valkind", "funkind", "lamkind", "fixkind", "srpifkind",
  "srpelifkind", "srpthenopt", "i0de", "i0de_dlr", "i0deseq", "i0dext",
  "l0ab", "stai0de", "p0rec", "e0xp", "atme0xp", "e0xpseq", "commae0xpseq",
  "e0xpopt", "e0ffid", "e0fftag", "e0fftagseq", "commae0fftagseq",
  "colonwith", "s0rt", "s0rtq", "s0rtid", "atms0rt", "s0rtseq",
  "commas0rtseq", "s0rtpol", "d0atsrtcon", "d0atsrtconseq",
  "bard0atsrtconseq", "d0atsrtdec", "andd0atsrtdecseq", "s0taq", "d0ynq",
  "si0de", "sqi0de", "commasi0deseq", "di0de", "dqi0de", "pi0de", "fi0de",
  "arri0de", "arrqi0de", "tmpi0de", "tmpqi0de", "colons0rtopt", "s0arg",
  "s0argseq", "commas0argseq", "s0argseqseq", "decs0argseq",
  "commadecs0argseq", "decs0argseqseq", "sp0at", "s0exp", "atms0exp",
  "apps0exp", "exts0exp", "s0expelt", "s0arrind", "s0qua", "s0quaseq",
  "barsemis0quaseq", "s0rtext", "s0expseq", "barsemis0expseq",
  "commas0expseq", "s0expseq1", "labs0expseq", "commalabs0expseq",
  "t0mps0exp", "t1mps0exp", "t1mps0expseq", "commat1mps0expseq",
  "gtlt_t1mps0expseqseq", "impqi0de", "s0rtdef", "ands0rtdefseq",
  "d0atarg", "d0atargseq", "commad0atargseq", "s0tacon", "ands0taconseq",
  "s0tacst", "ands0tacstseq", "s0tavar", "ands0tavarseq", "s0expdef",
  "ands0expdefseq", "s0aspdec", "conq0uaseq", "coni0ndopt", "cona0rgopt",
  "d0atcon", "d0atconseq", "bard0atconseq", "d0atdec", "andd0atdecseq",
  "s0expdefseqopt", "e0xndec", "ande0xndecseq", "p0arg", "p0argseq",
  "commap0argseq", "d0arg", "d0argseq", "extnamopt", "d0cstdec",
  "andd0cstdecseq", "s0vararg", "s0exparg", "s0elop", "witht0ype", "p0at",
  "atmp0at", "argp0at", "argp0atseq", "p0atseq", "commap0atseq",
  "labp0atseq", "commalabp0atseq", "f0arg1", "f0arg1seq", "f0arg2",
  "f0arg2seq", "d0exp", "atmd0exp", "s0expdarg", "s0expdargseq",
  "argd0exp", "argd0expseq", "d0arrind", "colons0expopt", "funarrow",
  "caseinv", "ifhead", "sifhead", "casehead", "scasehead", "forhead",
  "whilehead", "tryhead", "d0expcommaseq", "commad0expseq",
  "d0expsemiseq0", "d0expsemiseq1", "labd0expseq", "commalabd0expseq",
  "m0atch", "m0atchseq", "andm0atchseq", "guap0at", "c0lau", "c0lauseq",
  "barc0lauseq", "sc0lau", "sc0lauseq", "barsc0lauseq", "i0nvqua",
  "i0nvmet", "i0nvarg", "i0nvargseq", "commai0nvargseq", "i0nvargstate",
  "i0nvresqua", "i0nvresstate", "loopi0nv", "initestpost", "m0arg",
  "m0argseq", "commam0argseq", "m0acarg", "m0acargseq", "m0acdef",
  "andm0acdefseq", "v0aldec", "andv0aldecseq", "f0undec", "andf0undecseq",
  "v0arwth", "v0ardec", "andv0ardecseq", "i0mpdec", "d0ec", "d0ecarg",
  "d0ecargseq", "semicolonseq", "d0ec_sta", "guad0ec_sta", "d0ecseq_sta",
  "d0ecseq_sta_rev", "d0ec_dyn", "guad0ec_dyn", "d0ecseq_dyn",
  "d0ecseq_dyn_rev", 0
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311,   312,   313,   314,
     315,   316,   317,   318,   319,   320,   321,   322,   323,   324,
     325,   326,   327,   328,   329,   330,   331,   332,   333,   334,
     335,   336,   337,   338,   339,   340,   341,   342,   343,   344,
     345,   346,   347,   348,   349,   350,   351,   352,   353,   354,
     355,   356,   357,   358,   359,   360,   361,   362,   363,   364,
     365,   366,   367,   368,   369,   370,   371,   372,   373,   374,
     375,   376,   377,   378,   379,   380,   381,   382,   383,   384,
     385,   386,   387,   388,   389,   390,   391,   392,   393,   394,
     395,   396,   397,   398,   399,   400,   401,   402,   403,   404,
     405,   406,   407,   408,   409,   410,   411,   412,   413,   414,
     415,   416,   417,   418,   419,   420,   421,   422,   423,   424,
     425,   426,   427,   428,   429,   430,   431,   432,   433,   434,
     435,   436,   437,   438,   439,   440,   441,   442,   443,   444,
     445,   446,   447,   448,   449,   450,   451,   452,   453,   454,
     455,   456,   457,   458,   459,   460,   461,   462,   463,   464,
     465,   466,   467,   468,   469,   470,   471,   472,   473,   474,
     475,   476,   477,   478,   479,   480,   481,   482,   483,   484,
     485,   486,   487,   488,   489,   490,   491,   492,   493,   494,
     495,   496,   497,   498,   499,   500,   501
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint16 yyr1[] =
{
       0,   247,   248,   248,   248,   248,   248,   248,   248,   248,
     249,   249,   249,   249,   249,   249,   250,   250,   250,   250,
     250,   250,   251,   251,   251,   251,   252,   252,   252,   252,
     252,   253,   253,   253,   253,   254,   254,   254,   254,   254,
     254,   255,   255,   255,   255,   256,   256,   257,   257,   257,
     258,   258,   258,   259,   259,   260,   260,   260,   260,   260,
     260,   260,   260,   260,   260,   260,   260,   261,   262,   262,
     263,   263,   263,   264,   264,   264,   265,   266,   266,   266,
     266,   267,   267,   268,   268,   268,   268,   268,   268,   268,
     268,   268,   269,   269,   270,   270,   271,   271,   272,   273,
     273,   273,   273,   273,   274,   274,   275,   275,   276,   276,
     276,   277,   277,   278,   278,   279,   279,   279,   279,   279,
     279,   279,   280,   280,   280,   280,   281,   281,   282,   282,
     283,   283,   283,   283,   283,   283,   283,   283,   283,   283,
     283,   283,   283,   284,   284,   285,   285,   286,   286,   287,
     288,   288,   289,   289,   289,   290,   290,   290,   290,   290,
     291,   291,   291,   291,   291,   291,   291,   291,   291,   291,
     292,   292,   293,   293,   294,   294,   294,   294,   294,   294,
     294,   294,   294,   295,   295,   296,   296,   297,   297,   298,
     299,   299,   300,   301,   301,   302,   302,   303,   304,   304,
     305,   305,   306,   306,   306,   307,   307,   308,   308,   309,
     309,   310,   311,   311,   311,   311,   312,   312,   312,   312,
     312,   312,   312,   312,   312,   312,   312,   312,   312,   312,
     312,   312,   312,   312,   312,   312,   312,   312,   312,   312,
     312,   312,   312,   313,   313,   314,   314,   315,   315,   315,
     316,   316,   317,   317,   318,   318,   319,   319,   319,   320,
     320,   321,   321,   322,   322,   322,   323,   323,   324,   325,
     325,   326,   326,   327,   327,   328,   329,   329,   330,   330,
     331,   331,   332,   332,   333,   334,   334,   335,   335,   336,
     336,   337,   337,   338,   338,   338,   338,   339,   339,   340,
     340,   341,   341,   342,   343,   343,   344,   345,   345,   346,
     347,   347,   348,   348,   349,   349,   350,   351,   351,   352,
     352,   353,   353,   354,   354,   355,   355,   356,   357,   357,
     358,   358,   359,   359,   360,   360,   361,   361,   361,   361,
     362,   362,   363,   363,   364,   365,   365,   366,   366,   366,
     367,   367,   367,   368,   368,   369,   369,   369,   369,   369,
     370,   370,   370,   370,   370,   371,   371,   371,   371,   371,
     371,   371,   371,   371,   371,   371,   371,   371,   371,   371,
     371,   371,   371,   372,   372,   373,   373,   374,   374,   375,
     375,   376,   376,   377,   377,   377,   378,   378,   378,   378,
     379,   379,   380,   380,   381,   381,   382,   382,   382,   382,
     382,   382,   382,   382,   382,   382,   382,   382,   382,   382,
     382,   383,   383,   383,   383,   383,   383,   383,   383,   383,
     383,   383,   383,   383,   383,   383,   383,   383,   383,   383,
     383,   383,   383,   383,   383,   383,   383,   383,   383,   383,
     383,   383,   383,   383,   383,   383,   383,   383,   383,   383,
     383,   383,   383,   383,   383,   383,   383,   383,   383,   383,
     383,   383,   383,   383,   383,   383,   383,   383,   383,   384,
     385,   385,   386,   386,   387,   387,   388,   388,   389,   389,
     390,   390,   390,   391,   391,   392,   393,   394,   394,   394,
     395,   396,   396,   397,   398,   399,   399,   400,   400,   401,
     401,   401,   402,   403,   403,   404,   404,   405,   405,   406,
     407,   407,   408,   408,   409,   409,   409,   409,   410,   410,
     411,   411,   412,   413,   413,   414,   414,   415,   415,   416,
     416,   416,   417,   417,   418,   418,   419,   419,   420,   421,
     421,   422,   422,   423,   424,   425,   426,   426,   427,   427,
     428,   428,   429,   429,   430,   431,   431,   432,   433,   433,
     434,   434,   435,   435,   436,   436,   437,   437,   437,   437,
     438,   438,   439,   440,   440,   440,   440,   440,   440,   440,
     440,   440,   440,   440,   440,   440,   440,   440,   440,   440,
     440,   440,   440,   440,   440,   440,   440,   440,   440,   440,
     440,   440,   440,   440,   440,   441,   442,   442,   443,   443,
     444,   444,   444,   444,   444,   444,   445,   445,   445,   446,
     447,   447,   448,   448,   448,   448,   448,   448,   448,   448,
     448,   448,   448,   448,   448,   448,   448,   449,   449,   449,
     450,   451,   451
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     3,     3,     3,     3,     3,     3,     3,     3,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     0,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     0,     2,
       1,     1,     1,     1,     1,     3,     1,     0,     1,     3,
       5,     2,     1,     1,     1,     1,     1,     1,     1,     1,
       3,     3,     0,     2,     0,     3,     0,     1,     1,     2,
       2,     1,     1,     1,     0,     2,     0,     3,     1,     1,
       3,     2,     1,     2,     3,     1,     1,     1,     1,     1,
       1,     1,     1,     2,     3,     3,     0,     2,     0,     3,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     3,     1,     2,     0,     3,     3,
       0,     3,     2,     2,     3,     2,     2,     3,     3,     4,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     2,     0,     3,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     2,     1,     1,     1,     2,     1,
       1,     2,     1,     1,     2,     0,     2,     2,     0,     2,
       0,     3,     0,     2,     4,     0,     2,     0,     3,     0,
       4,     4,     1,     1,     3,     5,     1,     1,     1,     1,
       2,     2,     3,     5,     3,     3,     4,     4,     5,     5,
       6,     6,     3,     3,     4,     4,     6,     5,     3,     1,
       3,     3,     3,     2,     1,     2,     2,     0,     3,     3,
       2,     4,     1,     4,     0,     2,     0,     3,     3,     1,
       8,     0,     1,     0,     3,     3,     0,     3,     2,     0,
       4,     0,     5,     1,     2,     1,     0,     2,     0,     3,
       0,     3,     1,     4,     3,     0,     3,     1,     3,     0,
       2,     0,     3,     1,     4,     3,     6,     0,     3,     3,
       6,     0,     3,     3,     0,     3,     5,     0,     3,     5,
       0,     4,     0,     3,     0,     2,     4,     1,     2,     0,
       3,     3,     6,     0,     3,     0,     3,     3,     0,     3,
       1,     3,     0,     2,     0,     3,     1,     3,     5,     3,
       0,     2,     0,     2,     5,     0,     3,     1,     1,     1,
       1,     1,     1,     1,     1,     0,     2,     2,     2,     2,
       2,     3,     3,     4,     2,     1,     1,     1,     1,     1,
       2,     2,     2,     3,     5,     3,     3,     3,     5,     5,
       3,     3,     3,     1,     3,     0,     2,     0,     2,     0,
       3,     1,     4,     0,     2,     5,     3,     1,     3,     1,
       0,     2,     3,     1,     0,     2,     2,     3,     4,     6,
       6,     4,     4,     5,     6,     3,     3,     2,     2,     4,
       5,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       2,     2,     1,     1,     1,     1,     2,     2,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     6,     9,
       5,     2,     2,     3,     4,     5,     3,     5,     5,     5,
       3,     3,     3,     3,     3,     4,     4,     5,     5,     3,
       3,     4,     4,     6,     3,     3,     3,     5,     3,     3,
       0,     2,     1,     1,     0,     2,     2,     4,     0,     2,
       1,     1,     3,     0,     2,     2,     2,     2,     2,     2,
       2,     1,     3,     3,     1,     0,     2,     0,     3,     0,
       1,     3,     3,     0,     4,     0,     5,     1,     3,     2,
       0,     3,     1,     3,     3,     3,     3,     3,     1,     2,
       0,     3,     3,     1,     2,     0,     3,     0,     3,     0,
       3,     1,     2,     3,     0,     2,     0,     3,     3,     0,
       3,     0,     5,     4,     7,     1,     0,     2,     0,     3,
       1,     3,     0,     2,     4,     0,     3,     4,     0,     3,
       5,     7,     0,     3,     0,     2,     4,     5,     4,     6,
       0,     3,     5,     3,     3,     3,     3,     3,     2,     2,
       2,     3,     2,     2,     2,     3,     3,     3,     3,     3,
       3,     3,     2,     4,     3,     2,     4,     4,     5,     3,
       4,     3,     4,     2,     4,     3,     0,     2,     0,     2,
       1,     4,     1,     2,     2,     5,     4,     6,     5,     1,
       0,     3,     1,     5,     5,     5,     3,     4,     4,     4,
       3,     3,     5,     1,     2,     2,     2,     4,     6,     5,
       1,     0,     3
};

/* YYDEFACT[STATE-NAME] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint16 yydefact[] =
{
       0,     0,     0,     0,     0,     0,     0,   630,   651,     0,
      55,    56,    57,    58,    59,    60,    63,    61,    66,    62,
      64,    65,     0,   115,   116,   117,   118,   119,   120,   121,
       0,   160,   161,   162,   163,   164,   165,   167,   166,   169,
     168,     0,   174,   175,   176,   177,   178,   181,   179,   182,
     180,     0,   216,   217,   218,    67,   202,     0,     0,   104,
     239,     0,     0,     0,     0,     0,     0,   261,   254,   254,
     261,     0,   269,   261,   269,   254,     0,     0,   219,     0,
     244,   212,   213,   421,   422,   423,   424,   425,   426,   189,
     192,    70,    42,    44,    46,   509,   434,   493,   493,   493,
     435,    71,    45,   501,   537,   493,    41,   651,    43,     0,
     493,   493,   504,    72,   537,   433,   353,     0,   354,   509,
       0,     0,   247,   247,   247,     0,     0,     0,     0,   441,
     442,   443,   444,   445,   446,   447,   439,   440,     0,     0,
       0,   427,   428,   480,   480,   438,   505,   651,   505,     0,
     513,   505,   505,   513,     0,   400,     0,     0,   432,     0,
     429,   190,   505,   193,   276,     0,     0,   484,     0,     0,
       0,     0,     0,     0,   509,     0,   629,     0,   650,     1,
       4,     5,     6,     7,   198,   202,   195,   220,     0,   103,
      98,   102,     0,     0,   101,   106,     0,   269,   269,   261,
     261,   245,     0,   266,     0,   262,   219,   252,   256,     0,
       0,     0,     0,    74,     0,    73,     0,     0,     0,     0,
       0,   153,   152,   221,     8,     0,   243,   246,   510,     0,
     549,   497,     0,   498,   499,   254,   539,     0,   495,     0,
     430,   500,   496,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   513,   513,   505,   505,     0,   417,   418,
       0,   480,   436,   437,   507,     0,     0,     0,   507,     0,
       0,     0,     0,     0,     0,     0,   350,   351,   352,     0,
     365,   367,   366,   368,   185,   186,     0,     0,   261,   399,
     387,   198,   254,   387,     0,   387,   387,     0,     0,   369,
     397,   400,   488,   400,   156,   155,     0,   431,   191,   194,
     451,     0,   273,   275,   278,   280,   505,   452,     9,     0,
       0,   651,   482,   483,   484,   406,     0,     0,     0,     0,
     505,     0,     0,     0,     2,   622,    10,    11,    12,    13,
      14,    15,     0,    18,     0,     0,     0,    22,    23,    24,
      25,   310,    16,    77,    77,    77,   630,     0,     0,    68,
       0,    77,    19,    77,    20,    27,    21,     0,     0,    26,
       0,     0,    68,    28,    17,    29,    30,     0,     0,     0,
      47,    48,    49,     0,     0,     0,     0,   616,     0,     0,
       0,   620,   618,     3,   643,    38,     0,     0,    35,    36,
      37,   209,   651,    39,    40,    34,    31,    32,    33,     0,
       0,     0,   616,     0,   632,   618,   195,   200,     0,   203,
       0,     0,   154,    99,   100,     0,   105,   238,     0,     0,
       0,     0,     0,     0,   268,   261,   222,     0,     0,     0,
       0,   255,   241,   240,   261,   224,     0,     0,     0,   232,
     261,   225,   233,   242,     0,   126,   126,     0,   214,     0,
     122,   112,   509,   461,   254,     0,   494,     0,   261,   541,
       0,   502,   509,   503,   158,     0,   476,   475,   474,     0,
       0,   505,   505,   505,     0,     0,     0,     0,     0,     0,
     481,     0,   509,   506,   505,   456,   462,   478,   505,   463,
       0,     0,   469,   505,   464,   460,   470,     0,   371,   370,
       0,     0,     0,   369,   389,   385,     0,     0,     0,     0,
     391,     0,     0,     0,     0,     0,   372,   401,     0,     0,
     488,   157,   486,   274,     0,   277,   276,     0,   453,   651,
     407,   485,     0,     0,   530,   535,     0,   415,   416,   530,
       0,   170,   202,   602,   605,     0,   150,   150,   254,     0,
     328,    78,     0,    68,    68,    68,     0,     0,   562,   565,
       0,   565,    68,   588,     0,     0,    68,    68,     0,   285,
       0,   301,   613,    76,     0,     0,   304,   589,    83,    84,
      85,    86,     0,    87,    88,    92,    89,   592,    82,    96,
     593,   624,   594,   590,   293,   297,   254,   616,     0,     0,
     323,   202,   307,    53,   623,   631,   646,     0,    17,   616,
     205,     0,     0,     0,     0,     0,   574,   580,   645,     0,
     568,     0,    53,   644,   652,   197,     0,   199,   202,   196,
       0,   106,   234,   235,   261,   226,   261,   227,   269,   266,
       0,   172,     0,   256,   256,     0,   261,    75,   271,     0,
       0,   128,     0,     0,   113,   111,   123,   511,     0,   544,
     538,     0,   544,   551,     0,   159,   249,   248,     0,     0,
       0,   471,   472,   465,   466,     0,   479,   507,   512,     0,
       0,   505,     0,   515,     0,     0,   398,   370,   364,     0,
       0,     0,   388,   198,   383,   385,   360,   387,   373,   382,
     396,   387,   376,     0,   380,   387,   377,   375,   381,   489,
     104,   490,   491,     0,     0,   505,   278,   280,   454,     0,
     408,     0,     0,   522,     0,   530,   411,   528,     0,     0,
       0,   535,   412,   533,   505,   419,   171,   195,     0,   147,
       0,   596,   597,     0,   314,   310,   604,     0,   583,   584,
     585,   630,   565,   556,   555,   560,   562,     0,     0,   609,
     565,   611,    69,     0,     0,   587,   586,     0,     0,   595,
       0,   289,     0,   599,     0,     0,     0,   600,     0,    94,
       0,    81,    97,   591,     0,   289,     0,   598,     0,   617,
     340,   345,   319,   289,     0,   325,   195,     0,   601,    54,
     630,   619,     0,     0,     0,   207,     0,     0,   183,   282,
     276,   404,   641,   651,   568,   568,   574,     0,     0,     0,
       0,   640,     0,     0,   636,     0,   187,   400,   572,   651,
     200,   204,   215,   107,     0,     0,     0,   267,   223,   173,
       0,   259,   253,   257,   258,   228,   237,     0,     0,   270,
     229,   114,     0,   127,   124,   125,   550,     0,   546,     0,
     540,     0,   553,   477,   450,   458,   459,     0,   508,   457,
     467,     0,     0,     0,   514,   468,   455,     0,   362,   389,
     361,   347,   348,   349,     0,   386,     0,     0,   393,     0,
       0,   413,     0,   487,   279,   281,   420,     0,     0,   530,
       0,     0,     0,     0,     0,   529,   535,   198,     0,   534,
       0,     0,   606,     0,   143,   147,   149,   145,   150,   310,
       0,   327,   328,     0,    79,     0,   610,   558,     0,   563,
       0,   565,   612,     0,     0,   607,   284,   285,   299,   115,
     116,   131,   132,   133,   134,   135,   136,   137,   138,   139,
     140,   141,   142,   119,   120,   121,     0,   130,   287,   291,
       0,   301,   614,   303,   304,    91,     0,    93,    90,   295,
       0,   297,   615,   332,   254,   336,   340,     0,     0,   621,
     310,     0,   319,   321,   317,     0,   323,     0,   603,     0,
     307,     0,     0,     0,   345,     0,   206,   209,   184,   280,
     198,   403,   404,   488,     0,   637,   638,     0,   575,   574,
       0,   580,   355,   568,   188,     0,     0,   639,     0,   201,
     230,   231,   236,     0,   250,     0,   128,   542,     0,   545,
     552,   548,   473,   448,     0,     0,   363,   390,   384,   374,
     378,     0,   392,   379,   492,   414,   409,   410,   531,   517,
     520,   523,   524,   525,   526,   527,   536,     0,   532,   505,
       0,   147,     0,   146,   151,   311,   315,   329,     0,   625,
       0,   557,   561,   564,   566,   608,   286,     0,     0,   290,
       0,   302,   305,    94,   294,   298,   330,   334,     0,     0,
     341,   108,   104,   109,     0,   345,   319,   312,   318,     0,
     324,   307,     0,   308,   630,    50,    51,    52,   626,     0,
     634,   635,   633,   207,   210,     0,     0,   405,     0,   642,
       0,   578,   576,   581,     0,     0,     0,     0,   567,   569,
       0,     0,   572,   651,   647,     0,     0,   261,     0,   129,
     543,   546,   505,     0,   394,     0,     0,     0,   519,   211,
       0,   309,   148,   144,    80,   558,   288,   291,     0,    95,
       0,     0,     0,   333,   332,   337,   339,     0,   342,   346,
     320,   261,   314,   319,   326,   306,     0,   628,   208,   283,
     402,     0,   577,     0,   356,   357,   358,   359,   355,     0,
     573,     0,   649,     0,   251,   271,   547,     0,   515,     0,
     518,   520,   554,   559,   292,   300,   296,   331,   334,     0,
     110,     0,   344,     0,   316,   322,   627,   582,   579,   570,
       0,   648,     0,   272,   449,   516,   393,   521,   335,   338,
     343,   313,   355,   263,   395,   571,     0,     0,     0,   263,
     263,   260,   264,   265
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     9,   386,   387,   388,   389,   411,   412,   155,   156,
     390,  1119,   810,   596,   157,   573,   158,   216,   584,   563,
     613,   598,   790,   977,   793,   194,   195,   196,   426,  1104,
     967,   459,   460,   461,   662,   863,   968,   925,   926,   927,
     556,   751,    77,   159,    78,   739,   438,   160,   819,   513,
     837,   161,   162,   163,   164,   421,   417,   418,   637,   186,
     816,  1006,   621,   740,   203,    80,    81,    82,   250,   856,
     208,   209,   441,   852,   857,  1248,   434,   205,   217,   859,
     313,   314,   315,   535,   537,   821,   579,   779,   969,   970,
    1089,   605,   797,   581,   783,   586,   787,   612,   808,   553,
     991,  1182,   931,   992,   993,   994,   610,   805,   998,   560,
     756,  1097,  1098,  1173,   986,   987,  1222,   801,   989,   894,
     489,   165,  1138,   514,   515,   705,   706,   516,   702,   522,
    1052,   301,   302,  1012,  1013,   268,   167,   261,   262,   324,
     325,   310,   529,   723,   231,   168,   169,   170,   171,   172,
     173,   174,   311,   493,   229,   266,   272,   884,  1060,  1061,
    1158,   734,   735,   736,   737,   741,   742,   743,   236,   470,
     868,   869,  1039,   673,   465,   232,   237,   331,   765,   938,
    1081,   766,   767,   569,   769,   630,   834,   838,  1027,   829,
     627,   831,   822,   391,   607,   608,   615,   392,   614,   175,
     176,   415,   633,   267,   178
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -1078
static const yytype_int16 yypact[] =
{
    1244,  2431,   188,  1365,  1312,  2187,  1585, -1078, -1078,   127,
   -1078, -1078, -1078, -1078, -1078, -1078, -1078, -1078, -1078, -1078,
   -1078, -1078,   149, -1078, -1078, -1078, -1078, -1078, -1078, -1078,
     185, -1078, -1078, -1078, -1078, -1078, -1078, -1078, -1078, -1078,
   -1078,   301, -1078, -1078, -1078, -1078, -1078, -1078, -1078, -1078,
   -1078,   308, -1078, -1078, -1078, -1078,   588,  1365,   154,   329,
   -1078,   115,   121,   132,   137,   357,   369,  2187,   694,   694,
    2187,  2187,  1257,  2187,  1257,   694,    82,  1365, -1078,    86,
   -1078,   694,   694, -1078, -1078, -1078, -1078, -1078, -1078, -1078,
   -1078, -1078, -1078, -1078, -1078,  1585, -1078,   -16,   -16,   -16,
   -1078, -1078, -1078, -1078,   206,   -16, -1078, -1078, -1078,  1312,
     -16,   -16, -1078, -1078,   206, -1078, -1078,   377, -1078,  1585,
    1585,  1585,   122,   122,   122,   224,   226,   217,   232, -1078,
   -1078, -1078, -1078, -1078, -1078, -1078, -1078, -1078,   234,  1585,
    1585, -1078, -1078,   239,   239, -1078,  1585, -1078,  1585,  2187,
    1257,  1585,  1585,  1257,  1317,  1214,  1312,    65, -1078,  1761,
   -1078, -1078,  1585, -1078,  2283,  1973,    80,  1835,  1585,  2187,
    1585,  2187,   238,  2049,  1585,   450,  2841,   464,  2656, -1078,
   -1078, -1078, -1078, -1078,  1365,   588,   339, -1078,   340, -1078,
   -1078, -1078,   470,   470, -1078,   353,   351,  1257,  1257,  2187,
    2187, -1078,   420,    -7,   -17, -1078,    16,   694,   181,   295,
     300,    20,    19, -1078,  1257, -1078,   380,   307,    89,   309,
     313, -1078, -1078, -1078, -1078,   882, -1078, -1078,    37,   476,
     325, -1078,   393, -1078, -1078,   694,   200,   395, -1078,   481,
   -1078, -1078, -1078,   403,    51,   343,    -1,   102,  2187,  2187,
     346,   350,   352,  1257,  1257,  1585,  1585,  2187,     0,     0,
    1317,   239, -1078, -1078,   396,   105,   364,   387,   316,   151,
     150,   454,   397,   156,   382,   402, -1078, -1078, -1078,   500,
   -1078, -1078, -1078, -1078, -1078, -1078,   388,   388,  2187, -1078,
    1348,  1365,   694,  1348,   816,  1348,  1348,   816,   388, -1078,
   -1078,  1214,   490,  1214, -1078, -1078,   499, -1078, -1078, -1078,
   -1078,   423, -1078,  2283,   505,   486,  1585, -1078, -1078,   426,
    2187,  1317, -1078, -1078,  1835, -1078,   222,    11,    50,    48,
    1585,  1585,  1585,   517, -1078, -1078, -1078, -1078, -1078, -1078,
   -1078, -1078,  2015, -1078,  1365,  2431,  2431, -1078, -1078, -1078,
   -1078,   431, -1078,    45,    45,    45, -1078,  2646,  2669,  2431,
    1058,    45, -1078,    45, -1078, -1078, -1078,   188,  1365, -1078,
     491,  1365,  2431, -1078, -1078, -1078, -1078,  2453,  2431,  2453,
   -1078, -1078, -1078,   632,  2453,  2431,  1365,   437,  1365,  1365,
    2453, -1078, -1078, -1078, -1078, -1078,   639,   394, -1078, -1078,
   -1078,   440, -1078, -1078, -1078, -1078,    93, -1078, -1078,    88,
     642,  1348,   437,  2453, -1078, -1078,   339,   523,   452, -1078,
     882,   518, -1078, -1078, -1078,   329, -1078, -1078,   451,   458,
     157,   158,   460,  2187, -1078,  2187, -1078,  1365,   542,   694,
     694, -1078, -1078, -1078,  2187, -1078,   468,   471,  2187, -1078,
    2187, -1078, -1078, -1078,   670,   882,   882,   556,   882,   188,
   -1078, -1078,  1585, -1078,   694,   484, -1078,   482,  2187, -1078,
     488, -1078,  1585, -1078, -1078,   561, -1078, -1078, -1078,   164,
     -39,  1585,  1585,  1585,   493,   498,   507,   512,   378,   501,
   -1078,  1585,  1585, -1078,  1585, -1078, -1078, -1078,  1585, -1078,
     187,  1585, -1078,  1585, -1078, -1078, -1078,  1585, -1078, -1078,
     549,   388,  1348,   675,   386,  1570,   177,   511,   510,   189,
   -1078,   596,   521,   190,   513,   522, -1078, -1078,  2187,   335,
     490, -1078,   526, -1078,   694, -1078,  2283,   600, -1078, -1078,
     608, -1078,  1585,  1585,  1042,  2346,   611,     0,     0,  1042,
    1365, -1078,   588, -1078,   614,   612,   723,   723,   694,  1312,
     724, -1078,  2431,  2431,  2431,  2431,   690,  1312,    76,   728,
    1312,   728,  2431, -1078,   541,   633,  2431,  2431,   621,   732,
     -36,   733, -1078, -1078,   624,   630,   738, -1078, -1078, -1078,
   -1078, -1078,  2453, -1078, -1078,  2453, -1078,  2453, -1078,  2453,
    2453, -1078,  2453, -1078,   -23,   745,   694,   437,  1312,   202,
     747,   588,   751,  2376, -1078,   647, -1078,   770,   773,   437,
    1365,  1680,   725,  1348,  1348,   388,    90,   763, -1078,   214,
     764,  1496,  2376, -1078,   647, -1078,  1365, -1078,   588,   882,
    2187,   353, -1078, -1078,  2187, -1078,  2187, -1078,  1257,    -7,
     582,   665,   564,   181,   181,   590,  2187, -1078,   438,   591,
     668,   726,   595,   597, -1078, -1078, -1078, -1078,   594,  1312,
   -1078,   655,  1312,   679,   758, -1078, -1078, -1078,   604,   605,
     606, -1078, -1078, -1078, -1078,   804, -1078,   316, -1078,   609,
     610,  1585,  1585,   344,   613,    17, -1078,   793,   692,  1348,
    1348,  2187, -1078,   875, -1078,  1570, -1078,  1348, -1078, -1078,
   -1078,  1348, -1078,  1348, -1078,  1348, -1078, -1078, -1078,   608,
     329, -1078, -1078,  1585,   335,  1585,   505,   486, -1078,   625,
      43,    54,  1348,    -2,   416,   703, -1078, -1078,  2015,   629,
     697,   708, -1078, -1078,  1585, -1078, -1078,   339,  2187,  2010,
    2431, -1078, -1078,   631,   771,   431, -1078,    64, -1078, -1078,
   -1078, -1078,   728,   388, -1078, -1078,    76,   709,  1312, -1078,
     728, -1078, -1078,   730,  1378, -1078, -1078,   564,   188, -1078,
     882,  2515,  1365, -1078,   834,   882,  1365, -1078,  2149,  2415,
     644, -1078,  2453, -1078,  2187,  2515,  1365, -1078,   641, -1078,
      40,   831,   371,  2515,  1365,   744,   339,  1365, -1078, -1078,
   -1078, -1078,   731,   734,  1312,   737,   651,  2305, -1078, -1078,
    2283,  1668, -1078, -1078,   764,   764,   750,   388,  2187,   740,
      88, -1078,  1585,  1348, -1078,  1312, -1078,  1214,   840, -1078,
     523, -1078,   608, -1078,   664,   671,   666, -1078, -1078, -1078,
    1365,   882, -1078, -1078, -1078, -1078, -1078,   672,  1257, -1078,
   -1078, -1078,   882, -1078, -1078, -1078, -1078,   752,   755,   683,
   -1078,   685, -1078, -1078, -1078, -1078, -1078,   688, -1078, -1078,
   -1078,   689,    61,  1257, -1078, -1078, -1078,  1348,   692,   386,
     608, -1078, -1078, -1078,   686, -1078,   698,   705,   447,   707,
     739,     0,  1585, -1078, -1078, -1078, -1078,  1585,  1585,   703,
    1585,  1585,  1585,  1585,  1585, -1078,   708,  1365,  1585, -1078,
     767,   748,   608,  2431,   845,   772, -1078, -1078,   723,   431,
    2187, -1078,   724,   902, -1078,   868, -1078,   788,   713, -1078,
    1585,   728, -1078,  1378,  1312, -1078, -1078,   732,   882,   792,
     794, -1078, -1078, -1078, -1078, -1078, -1078, -1078, -1078, -1078,
   -1078, -1078, -1078,   795,   796,   797,   800,   882, -1078,   807,
     727,   733, -1078,   882,   738, -1078,  2453, -1078, -1078,   608,
     735,   745, -1078,   388,   694, -1078,    40,   225,  1312, -1078,
     431,  1312,   810, -1078, -1078,   741,   747,  1365, -1078,   811,
     751,   392,  2187,  1585,   831,  1365, -1078,   440, -1078,   486,
    1365, -1078,  1668,   490,   898, -1078, -1078,   813, -1078,   174,
    1585,   763,   534,   764, -1078,   213,  1496, -1078,   492, -1078,
   -1078, -1078, -1078,   818,   753,   819,   726,  2187,  1312, -1078,
   -1078, -1078, -1078, -1078,   756,   822,   692, -1078, -1078, -1078,
   -1078,  2103, -1078, -1078, -1078,     0,     0,     0, -1078,    72,
     939, -1078,     0,     0,     0,     0, -1078,   759,     0,  1585,
    2187,   772,   882, -1078, -1078, -1078,   608, -1078,   760, -1078,
     388, -1078, -1078,     0, -1078, -1078, -1078,  1824,  2515, -1078,
     837, -1078, -1078,  2415,   838, -1078,   842,   835,   191,   776,
   -1078, -1078,   329, -1078,  2187,   831,   810,   768, -1078,   841,
   -1078,   751,  2187, -1078, -1078, -1078, -1078, -1078, -1078,  2453,
     608,     0, -1078,   737, -1078,   847,   777, -1078,   850, -1078,
    1585,   858,     0, -1078,  2187,  2187,  2187,  2187, -1078, -1078,
    1585,  2187,   840, -1078, -1078,  2453,   564,  2187,  2187, -1078,
     608,   755,  1585,  1585, -1078,   859,  1348,  1585, -1078, -1078,
     774,   608, -1078,   882, -1078,   788, -1078,   807,   882, -1078,
    2187,  2187,   388, -1078,   388, -1078, -1078,   860,   240, -1078,
   -1078,  2187,   771,   371, -1078,   608,   803, -1078, -1078, -1078,
   -1078,  1585,     0,  1585,   608,   608,   608,   608,   534,   294,
   -1078,   805, -1078,   865, -1078,   438, -1078,   798,   344,  1348,
     692,   939, -1078, -1078, -1078,   882,   608,   608,   835,   799,
   -1078,   991, -1078,   806, -1078, -1078, -1078,     0,     0, -1078,
    1585, -1078,  2187, -1078, -1078, -1078,   447, -1078, -1078, -1078,
   -1078, -1078,   534,   363, -1078, -1078,  2187,  2187,   801,   363,
     363, -1078, -1078, -1078
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
   -1078, -1078, -1078,   618, -1078, -1078, -1078, -1078, -1078, -1078,
     848,    -3,   401,   422,    -5,  -266, -1078,  -124, -1078,   184,
    -346,  -519, -1078,   -65, -1078,   418,   615,  -680,   398,     4,
    -180, -1078,     7,  -411,   578,     1,   -45,   112, -1078,  -854,
    -321,  -515,  -312,  -150,  1035,   699,   399,   539,  -686,   111,
   -1078,   886, -1078,  -143,   425,  -379,  -567,  -271,   207,  -141,
   -1078,   -75,    42, -1078,    14,   -46,   -54, -1078,   489,   -95,
     178,   -47,   -26,  -726,   -66,  -618,   404,   -61,   -50,  -148,
   -1078,   530,  -484,   354,  -677, -1078,   277,   129,     2,  -473,
     -86,   289,   106,   304,   117,   303,   119,  -750,  -901, -1078,
    -334, -1078,   -82,   118,   -88,  -905,   310,   109, -1078,   356,
     192,   -59,   -58,  -101, -1078,   133, -1078,  -756,  -902, -1078,
     966, -1078, -1077,  -408,  -132, -1078,   417,  -247,   236,   830,
    -108, -1078,  -269, -1078,   123,   161,   -56,   -87,   -52, -1078,
     809,  -306,  -512,   410,   504, -1078, -1078, -1078, -1078, -1078,
   -1078, -1078,  -140,   453,   -92, -1078,   -41,   -70,   -18, -1078,
     -67, -1078,   413,   603,  -625,   408, -1078,  -685, -1078, -1078,
     116,   485,     5, -1078, -1078,   480,  1045, -1078,  -720, -1078,
      -4, -1078,   407,  -319,  -485,  -569,  -751,   141,    26,  -754,
     345,   148, -1078,   996, -1078,  -333,   762, -1078,    63,  -343,
   -1078, -1078,    35,    -6, -1078
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -552
static const yytype_int16 yytable[] =
{
      76,   204,   177,   629,   211,   298,   265,   218,   269,    30,
     538,   273,   274,   566,   207,   207,   309,   559,   724,    79,
     517,   207,   210,   300,   219,   557,   271,   245,   220,   271,
     550,   597,   527,   600,   530,   226,   227,   635,   602,   571,
     900,   317,   752,   937,   419,   458,   519,   665,   523,   524,
     905,   946,   727,   815,   824,   825,   919,  1000,  1004,   284,
     285,   561,    76,    76,    76,    76,    76,   632,    76,   840,
      76,  1073,  1017,  1015,  1016,    55,    76,    76,   791,   631,
     323,   791,   333,   791,   933,   212,   771,  1108,   945,    55,
     447,   318,   263,   278,   791,   284,   285,   224,   907,  1113,
     225,   239,  1122,   780,   698,  1156,   587,   284,   285,   908,
     915,   322,   275,   791,   543,   486,   487,   332,   312,   794,
     435,  1229,   910,   230,   319,   319,   545,   179,   544,   271,
     271,   433,   225,   430,   431,  -551,   733,   701,   320,   320,
     298,   733,   319,   298,    76,   298,   298,   428,   429,    76,
     225,   298,   306,   298,   437,  -172,   320,   444,   225,    76,
     180,   226,   319,   270,    76,  1245,    76,   166,   319,   300,
     521,   300,   188,   521,   623,   319,   320,   462,   781,   319,
     677,   207,   320,   327,   624,   329,   319,   225,   467,   320,
     546,   795,   474,   320,    76,    76,   181,   319,   436,   278,
     320,  1180,    76,  1179,   304,   319,   305,    23,    24,   490,
    1184,   320,   484,   485,   477,   629,   629,  1162,   827,   320,
     457,   221,   510,   222,   625,   225,   450,   319,   665,   828,
      76,  1066,  1105,   550,   886,   445,   446,   323,   207,   475,
     639,   320,   494,    76,    76,   518,   788,  1111,   762,   789,
     665,   770,    76,   792,   983,    76,   228,  1085,   984,   562,
     278,   298,   479,   480,  1023,  1131,   299,   533,   322,   791,
     791,   488,  1139,   791,   799,   661,   661,   936,  1044,   934,
     228,   246,   247,    76,  1058,   942,   814,    76,   498,   225,
     763,   888,   889,   503,   644,   646,    25,   758,   759,   760,
     258,   259,   827,   225,   451,   898,   772,   264,    76,    26,
     775,   776,   182,   225,   707,    76,    76,   478,   439,   183,
     495,   440,   980,    27,   733,   542,   711,   715,  1174,   326,
     995,   328,  1125,   197,   540,   228,  1009,    76,   248,   198,
     249,   678,   679,   680,   802,   189,   199,   319,   190,    28,
      29,   200,  1101,   701,   689,  1140,   832,   468,   690,   469,
    1165,   320,   298,   694,  1101,   298,   499,   500,   921,   650,
     667,   504,   645,   647,   578,   201,  1102,  1103,   655,   225,
     674,   676,  1221,   704,   659,   207,   207,   202,  1102,  1103,
    -310,  -310,   708,   191,   298,   244,   622,   508,   509,   298,
     688,   691,   671,   692,   712,   716,  1175,   284,   285,   526,
     207,   747,   299,  1074,   299,   457,   803,   668,   935,   903,
    1203,   559,  1177,    22,   235,   629,   550,   999,    76,   928,
      76,   255,   893,   225,    76,    76,  1230,   343,  1123,    76,
     665,   319,   253,    76,   254,    76,   256,   649,   257,   941,
     457,   457,   330,   457,   491,   320,  1084,   260,   352,    76,
     896,   334,   658,    76,   897,   192,   666,  1001,   899,   319,
     806,   817,   851,   298,   298,   393,   193,   362,   420,  1046,
     364,   422,   883,   320,   366,   720,   721,   722,   312,   190,
     312,   425,   547,   548,   215,   427,   215,   841,   432,   617,
    1246,  1128,   225,  1247,   207,   618,  -310,  -310,   990,   582,
     583,   753,   442,  -310,  -310,  -310,   685,   225,  -310,   443,
     626,   319,   448,    76,   700,   701,   449,  -310,   452,    76,
     453,    76,   463,   729,   491,   320,   492,   665,   564,   565,
      76,   464,   719,    51,   466,   576,   471,   577,   472,   298,
     298,   881,   207,    76,   473,   298,   665,   298,   476,   798,
     481,   298,   665,   298,   482,   298,   483,   911,  1025,   912,
     913,   914,   215,   704,   791,   215,   858,   225,   844,   496,
     845,   307,   298,    23,    24,  1051,   701,   215,    55,   558,
    1114,  1115,  1116,  1117,  1118,  1075,   501,   851,   846,   505,
     948,    76,   233,   234,   920,   973,   497,    31,    32,   238,
     423,   424,   251,   252,   241,   242,   502,   653,   654,   215,
     215,   506,   697,   228,   944,   665,   299,   853,   854,   528,
    1093,  1252,  1253,   228,   457,    76,   215,   507,   531,    76,
     532,    76,   536,   534,   539,   549,  1067,   457,   240,   558,
     601,    76,   687,   228,   842,   606,   457,   616,   620,   319,
     628,   636,   693,  1134,  1135,  1136,  1137,   638,   695,   640,
     642,   298,    25,   320,   309,   215,   215,   643,   648,   764,
      33,   652,  1036,   298,   656,    26,   657,   298,   660,  1011,
    1143,  1115,  1116,  1117,  1144,   303,    76,   664,   669,    27,
     675,   670,   672,   730,   731,   300,    52,   696,   699,   454,
      53,    54,   681,    31,    32,   890,   215,   682,    55,   215,
     686,    34,   683,    35,    36,    28,    29,   684,   709,   710,
     717,    37,    38,    76,  1035,    39,   826,   298,   713,  1126,
     714,   718,   725,    76,   728,    23,    24,   225,  1210,    40,
      55,   744,   665,   748,   749,   750,   755,   761,   773,  1045,
     768,   774,   922,   777,   778,   782,   784,   555,   555,   785,
     786,  1186,   457,    57,   312,   457,   457,   796,   455,   804,
     457,   572,   850,   807,   456,   578,    33,   811,   812,    76,
     457,   813,   823,   944,   572,   830,   833,   848,   457,   632,
     599,  1236,   184,   437,   665,   855,   860,   603,   979,   861,
     864,   866,   865,   870,   873,    76,   299,  1014,   230,   874,
     875,   876,   877,    76,   879,   880,   887,    34,   885,    35,
      36,   701,   213,  1028,    25,    10,    11,    37,    38,    58,
     732,    39,  1019,   917,   906,   738,   457,    26,   918,   930,
     929,   940,   972,   882,    59,    40,    60,   457,   943,   978,
     982,    27,   298,   988,   862,    61,    62,    63,    64,   997,
    1007,   454,  1026,  1002,   764,  1005,  1003,   764,   827,  1030,
    1011,    66,  1020,  1054,   901,  1032,  1031,    28,    29,  1034,
    1070,  1037,  1163,  1038,    31,    32,   568,   568,  1040,   575,
    1041,    23,    24,  1042,  1043,  1048,    55,  1069,    67,   923,
      68,   985,    69,  1049,    70,    71,    72,    73,  1078,    74,
    1050,    75,  1053,  1072,  1079,    76,  1080,  1155,  1082,  1160,
     207,   -55,   299,   -56,   -58,   -64,   -65,  1099,  1018,  1087,
     455,   626,  1090,   457,  1076,  1088,   456,   990,   299,    12,
    1094,    13,    14,  1112,  1129,  1130,  1109,  1146,    15,    16,
      17,  1148,   457,    18,  1153,   520,   851,    33,   457,  1147,
    1152,  1157,    19,  1172,  1159,  1164,  1168,    20,    21,    76,
    1170,  1171,  1181,  1183,   757,   572,   572,   572,  1215,  1212,
      25,  1189,  1191,  1022,   572,  1176,  1190,    76,   572,   572,
    1193,  1209,  1232,    26,  1220,  1226,   298,  1231,    34,  1240,
      35,    36,  1207,  1234,  1239,   619,  1120,    27,    37,    38,
    1251,  1241,    39,   891,   892,  1145,   413,   454,  1169,  1141,
     214,   457,    76,   839,   663,  1071,    40,  1149,    41,   843,
     641,   552,  1166,    28,    29,   308,   820,  1029,  1188,  1124,
     849,  1150,  1204,   847,   280,   947,   281,  1233,   282,   298,
     283,   284,   285,  1055,   726,    76,    55,   457,  1056,  1057,
     215,  1059,  1062,  1063,  1064,  1065,  1086,    42,    43,  1068,
     904,  1214,   457,   457,  1161,   981,   971,  1095,  1091,   974,
    1167,   185,   187,  1092,  1096,  1225,   455,   985,   754,    76,
    1224,  1083,   456,   206,   206,  1110,   568,    76,  1106,   568,
     206,   932,   223,  1218,   996,  1223,  1219,  1238,  1178,  1100,
     279,   286,   895,   299,  1077,  1047,  1185,   525,  1244,    76,
      76,    76,    76,   541,   902,  1127,    76,  1201,  1235,  1211,
     878,   457,    76,    76,  1237,   909,   916,   800,  1194,  1195,
    1196,  1197,   745,   872,  1151,  1199,  1206,   871,   457,   243,
     818,  1213,  1205,   457,  1121,    76,    76,  1142,  1200,  1133,
     836,   924,   555,   939,   414,  1021,    76,   634,   511,   732,
    1202,  1132,  1187,     0,  1216,  1217,     0,   117,     0,   512,
       0,   764,     0,    44,    45,     0,     0,     0,     0,     0,
      46,    47,    48,   966,     0,    49,     0,     0,   867,     0,
     457,   867,     0,     0,    50,     0,     0,   966,     0,   416,
     185,     0,     0,     0,     0,   966,   280,    76,   281,     0,
     282,     0,   283,   284,   285,     0,     0,     0,    55,     0,
       0,    76,    76,     0,     0,     0,  1243,     1,     2,     3,
       4,     5,     6,     7,     8,     0,   290,     0,   291,     0,
    1249,  1250,   293,     0,   294,   295,   296,   297,     0,     0,
     206,     0,     0,   213,   574,     0,    10,    11,     0,     0,
     215,     0,     0,  1096,     0,  1096,     0,     0,     0,     0,
       0,  1192,     0,   286,     0,     0,     0,     0,     0,     0,
       0,  1198,     0,     0,     0,   215,     0,   568,     0,     0,
       0,     0,     0,   818,  1208,     0,     0,     0,  1059,     0,
       0,     0,     0,     0,     0,     0,   416,   206,     0,    52,
       0,    42,    43,    53,    54,     0,    31,    32,     0,     0,
       0,    55,     0,     0,     0,   924,     0,     0,     0,     0,
     287,     0,  1227,   800,  1228,     0,  1008,     0,     0,   117,
     280,     0,   281,     0,   282,     0,   283,   284,   285,     0,
       0,   288,    55,   289,  1024,     0,     0,   551,     0,   554,
       0,     0,     0,     0,    31,    32,     0,     0,    56,     0,
      12,  1242,    13,    14,     0,     0,    57,    42,    43,    15,
      16,    17,    55,   580,    18,     0,   585,     0,     0,    33,
       0,     0,     0,    19,     0,     0,     0,     0,    20,    21,
       0,   604,     0,   609,   611,     0,     0,   286,   290,     0,
     291,     0,   292,     0,   293,     0,   294,   295,   296,   297,
       0,     0,     0,     0,     0,     0,     0,    44,    45,     0,
      34,     0,    35,    36,    46,    47,    48,    33,     0,    49,
      37,    38,    58,     0,    39,   276,   277,     0,    50,     0,
       0,   214,   651,   215,   206,   206,     0,    59,    40,    60,
       0,     0,   818,  1008,   511,     0,     0,     0,    61,    62,
      63,    64,     0,   117,     0,   512,     0,     0,    34,   206,
      35,    36,     0,    65,    66,     0,     0,     0,    37,    38,
     966,     0,    39,    44,    45,    42,    43,     0,     0,     0,
      46,    47,    48,   117,     0,    49,    40,   800,     0,     0,
    1107,    67,     0,    68,    50,    69,     0,    70,    71,    72,
      73,     0,    74,     0,    75,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   290,     0,   291,   836,     0,     0,   293,     0,
     294,   295,   296,   297,     0,   835,     0,   867,     0,     0,
     551,     0,   280,     0,   281,   746,   282,   185,   283,   284,
     285,     0,     0,   206,    55,     0,     0,    83,     0,    84,
      85,    86,    87,    88,    42,    43,    89,    90,    91,    55,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      92,    93,    94,    95,    96,    97,    98,    99,     0,     0,
     100,    44,    45,     0,     0,     0,     0,   101,    46,    47,
      48,   206,     0,    49,   102,     0,   185,   103,   104,   286,
     105,     0,    50,     0,     0,   416,   106,   107,   108,     0,
       0,     0,     0,     0,   109,     0,     0,     0,     0,     0,
       0,   416,     0,   185,     0,     0,     0,     0,   110,   111,
     280,     0,   281,     0,   282,     0,   283,   284,   285,   112,
       0,     0,    55,     0,     0,     0,     0,     0,     0,    42,
      43,     0,    90,     0,    55,     0,   287,     0,     0,     0,
       0,   113,   114,     0,     0,   117,     0,     0,   115,     0,
      44,    45,     0,     0,     0,     0,   116,    46,    47,    48,
     117,     0,    49,     0,     0,     0,     0,     0,   416,     0,
       0,    50,     0,     0,     0,     0,   118,   286,     0,     0,
     119,   120,   121,   122,   123,   124,   125,   126,   127,   128,
     129,   130,   131,   132,   133,   134,   135,   136,   137,     0,
     138,     0,     0,   551,     0,   139,   140,   141,   142,     0,
      10,    11,    89,    90,   290,     0,   291,     0,   703,     0,
     293,     0,   294,   295,   296,   297,   143,   144,   145,   146,
       0,     0,     0,   147,   287,   148,   149,   150,   151,   152,
     153,     0,   154,   117,     0,    44,    45,   580,     0,     0,
       0,   585,    46,    47,    48,   117,     0,    49,     0,     0,
       0,   604,     0,     0,     0,     0,    50,     0,     0,   609,
       0,     0,   611,    23,    24,     0,     0,    83,    55,    84,
      85,    86,    87,    88,    42,    43,    89,    90,    91,    55,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    95,    96,     0,     0,     0,     0,     0,
     100,     0,   290,     0,   291,  1033,  1010,   101,   293,     0,
     294,   295,   296,   297,    12,     0,    13,    14,     0,     0,
       0,     0,     0,    15,    16,    17,     0,   107,    18,     0,
       0,     0,   951,   952,   109,     0,     0,    19,     0,     0,
       0,     0,    20,    21,     0,     0,     0,     0,     0,     0,
     953,   954,    25,   955,   956,     0,     0,     0,     0,     0,
     957,   958,     0,   959,   960,    26,   961,   962,     0,     0,
       0,     0,   416,     0,     0,     0,     0,     0,     0,    27,
       0,   113,     0,     0,     0,     0,     0,     0,   115,   454,
      44,    45,     0,     0,     0,     0,   116,    46,    47,    48,
     117,     0,    49,     0,     0,    28,    29,     0,     0,   213,
       0,    50,    10,    11,     0,     0,   118,     0,     0,     0,
     119,   120,   121,   122,   123,   124,   125,   126,   127,   128,
     129,   130,   131,   132,   133,   134,   135,   136,   137,   206,
     138,     0,     0,     0,     0,     0,     0,   141,   142,    10,
      11,     0,   611,     0,    31,    32,     0,     0,   455,    55,
     416,     0,     0,     0,   456,   416,   143,   144,   145,   146,
       0,     0,     0,   321,     0,   148,   149,   150,   151,   152,
     153,    83,   154,    84,    85,    86,    87,    88,    42,    43,
      89,    90,    91,    55,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    95,    96,     0,
       0,     0,     0,     0,   100,     0,     0,     0,     0,     0,
       0,   101,     0,     0,     0,     0,    12,    33,    13,    14,
       0,     0,     0,     0,     0,    15,    16,    17,     0,   213,
      18,   107,    10,    11,     0,     0,     0,     0,   109,    19,
       0,     0,     0,     0,    20,    21,     0,     0,     0,     0,
       0,     0,     0,    12,     0,    13,    14,   923,    34,     0,
      35,    36,    15,    16,    17,     0,     0,    18,    37,    38,
      58,   588,    39,   589,     0,   590,    19,   591,    10,    11,
       0,    20,    21,     0,     0,   113,    40,     0,     0,     0,
       0,     0,   115,     0,    44,    45,     0,   214,     0,   316,
     116,    46,    47,    48,   117,     0,    49,     0,     0,    52,
       0,     0,     0,    53,    54,    50,    31,    32,     0,     0,
     118,    55,     0,     0,   119,   120,   121,   122,   123,   124,
     125,   126,   127,   128,   129,   130,   131,   132,   133,   134,
     135,   136,   137,     0,   138,     0,    12,     0,    13,    14,
       0,   141,   142,     0,     0,    15,    16,    17,     0,     0,
      18,     0,  1154,     0,     0,     0,     0,     0,    56,    19,
     143,   144,   145,   146,    20,    21,    57,   147,     0,   148,
     149,   150,   151,   152,   153,     0,   154,     0,     0,    33,
       0,     0,    12,     0,    13,    14,     0,     0,     0,     0,
       0,    15,    16,    17,     0,    52,    18,     0,     0,    53,
      54,     0,    31,    32,     0,    19,     0,    55,     0,     0,
      20,    21,     0,     0,     0,     0,   592,   214,     0,     0,
      34,     0,    35,    36,    42,    43,     0,    90,     0,     0,
      37,    38,    58,     0,    39,     0,     0,     0,     0,     0,
       0,   593,   594,     0,     0,     0,     0,    59,    40,    60,
       0,     0,     0,     0,     0,     0,     0,     0,    61,    62,
      63,    64,    57,   595,   975,    31,    32,     0,     0,     0,
      55,     0,     0,    65,    66,    33,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   588,     0,
     589,     0,   590,     0,   591,    10,    11,     0,     0,     0,
       0,    67,     0,    68,     0,    69,     0,    70,    71,    72,
      73,     0,    74,     0,    75,     0,    34,     0,    35,    36,
       0,     0,     0,     0,     0,     0,    37,   588,    58,   589,
      39,   590,     0,   591,    10,    11,     0,     0,    33,     0,
      44,    45,     0,    59,    40,    60,     0,    46,    47,    48,
      10,    11,    49,     0,    61,    62,    63,    64,     0,     0,
       0,    50,     0,     0,     0,   588,     0,   589,     0,   590,
      66,   591,    10,    11,     0,     0,     0,     0,     0,    34,
       0,    35,    36,   738,     0,     0,     0,     0,     0,    37,
      38,    58,     0,    39,     0,     0,     0,    67,     0,    68,
       0,    69,     0,    70,    71,    72,    73,    40,    74,    12,
      75,    13,    14,     0,     0,     0,     0,     0,    15,    16,
      17,     0,     0,    18,     0,     0,     0,     0,     0,     0,
       0,     0,    19,     0,   949,   950,     0,    20,    21,    55,
       0,     0,     0,   592,     0,     0,     0,     0,    12,     0,
      13,    14,     0,   976,     0,     0,     0,    15,    16,    17,
       0,     0,    18,     0,    12,     0,    13,    14,   593,   594,
       0,    19,     0,    15,    16,    17,    20,    21,    18,     0,
       0,     0,   592,     0,     0,   809,    12,    19,    13,    14,
     595,     0,    20,    21,     0,    15,    16,    17,     0,     0,
      18,     0,     0,   951,   952,     0,     0,   593,   594,    19,
       0,     0,     0,     0,    20,    21,     0,     0,     0,     0,
     592,   953,   954,    25,   955,   956,     0,     0,     0,   595,
       0,   957,   958,     0,   959,   960,    26,   961,   962,     0,
       0,     0,     0,     0,     0,   593,   594,     0,    12,     0,
     963,    14,     0,     0,     0,     0,     0,    15,    16,    17,
     454,     0,    18,     0,     0,    42,    43,   595,     0,   394,
       0,    19,     0,     0,     0,     0,   964,   965,     0,     0,
       0,     0,   336,   337,   338,   339,   340,   341,    42,    43,
     342,     0,     0,     0,     0,     0,     0,     0,     0,   395,
     344,     0,   345,   346,   347,   348,   349,   350,     0,     0,
     396,     0,     0,   351,   397,     0,   398,   399,     0,     0,
     400,     0,   401,     0,   353,   354,   355,     0,     0,   455,
     402,   357,   358,   359,     0,   456,   360,   567,   361,     0,
     363,   403,   404,   365,     0,     0,   405,     0,     0,     0,
       0,   367,   368,   369,     0,   370,   371,     0,   372,     0,
     570,   373,     0,     0,     0,     0,     0,   406,   407,   408,
     409,   375,     0,     0,   376,     0,     0,     0,     0,     0,
       0,    44,    45,     0,     0,     0,     0,     0,    46,    47,
      48,     0,     0,    49,     0,     0,     0,     0,     0,     0,
       0,     0,    50,     0,    44,    45,     0,     0,     0,     0,
       0,    46,    47,    48,     0,     0,    49,     0,     0,     0,
       0,     0,     0,     0,     0,    50,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   377,   378,   335,     0,     0,     0,     0,   379,
     380,   381,   382,   410,   384,     0,   385,   336,   337,   338,
     339,   340,   341,     0,     0,   342,     0,     0,     0,     0,
       0,     0,     0,     0,   343,   344,     0,   345,   346,   347,
     348,   349,   350,     0,     0,     0,     0,     0,   351,     0,
       0,     0,     0,     0,     0,   352,     0,     0,     0,   353,
     354,   355,     0,     0,     0,   356,   357,   358,   359,     0,
       0,   360,     0,   361,   362,   363,     0,   364,   365,     0,
       0,   366,     0,     0,     0,     0,   367,   368,   369,     0,
     370,   371,     0,   372,     0,     0,   373,     0,     0,     0,
       0,     0,   374,     0,     0,     0,   375,     0,     0,   376,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   377,   378,     0,
       0,     0,     0,     0,   379,   380,   381,   382,   383,   384,
       0,   385
};

#define yypact_value_is_default(yystate) \
  ((yystate) == (-1078))

#define yytable_value_is_error(yytable_value) \
  YYID (0)

static const yytype_int16 yycheck[] =
{
       5,    67,     8,   411,    70,   155,   146,    73,   148,     2,
     316,   151,   152,   356,    68,    69,   159,   351,   530,     5,
     291,    75,    69,   155,    74,   346,   150,   119,    75,   153,
     342,   377,   301,   379,   303,    81,    82,   416,   384,   358,
     720,   165,   557,   763,   185,   225,   293,   458,   295,   296,
     727,   777,   536,   620,   623,   624,   741,   807,   814,    19,
      20,    16,    67,    68,    69,    70,    71,   413,    73,   636,
      75,   925,   826,   824,   825,    24,    81,    82,   597,   412,
     167,   600,   174,   602,    20,    71,   571,   992,   774,    24,
     214,    11,   144,   154,   613,    19,    20,    11,    55,  1000,
     139,   107,  1004,   139,   512,    33,   372,    19,    20,    55,
     735,   167,   153,   632,   103,   255,   256,   173,   164,   142,
     137,  1198,   124,   139,   125,   125,    78,     0,    78,   253,
     254,   138,   139,   199,   200,   151,   544,   139,   139,   139,
     290,   549,   125,   293,   149,   295,   296,   197,   198,   154,
     139,   301,   157,   303,   138,   139,   139,   137,   139,   164,
      11,   207,   125,   149,   169,  1242,   171,     6,   125,   301,
     294,   303,    18,   297,    81,   125,   139,   140,   214,   125,
     219,   235,   139,   169,    91,   171,   125,   139,   235,   139,
     330,   214,   141,   139,   199,   200,    11,   125,   215,   260,
     139,  1106,   207,  1105,   139,   125,   141,    19,    20,   261,
    1111,   139,   253,   254,   215,   623,   624,  1071,   128,   139,
     225,   139,   288,   141,   136,   139,   137,   125,   639,   139,
     235,   916,   988,   545,   217,   215,   217,   324,   292,   244,
     420,   139,   137,   248,   249,   292,   592,   997,   567,   595,
     661,   570,   257,   599,   214,   260,    95,   943,   218,   214,
     321,   411,   248,   249,   833,  1019,   155,   313,   324,   788,
     789,   257,  1023,   792,   607,   455,   456,   762,   217,   215,
     119,   120,   121,   288,   909,   770,   619,   292,   137,   139,
     214,   699,   700,   137,   137,   137,   108,   563,   564,   565,
     139,   140,   128,   139,   215,   713,   572,   146,   313,   121,
     576,   577,    11,   139,   137,   320,   321,   215,   137,    11,
     215,   140,   795,   135,   732,   103,   137,   137,   137,   168,
     803,   170,  1009,   218,   320,   174,   820,   342,   216,   218,
     218,   481,   482,   483,   142,    16,   214,   125,    19,   161,
     162,   214,   139,   139,   494,   142,   142,   157,   498,   159,
    1080,   139,   512,   503,   139,   515,   215,   217,   747,   435,
     462,   215,   215,   215,   367,    18,   163,   164,   444,   139,
     472,   217,   142,   515,   450,   439,   440,    18,   163,   164,
      19,    20,   215,    64,   544,    18,   402,   286,   287,   549,
     492,   214,   468,   216,   215,   215,   215,    19,    20,   298,
     464,   552,   301,   928,   303,   420,   214,   464,   761,   725,
    1146,   755,  1102,     1,   218,   833,   738,   806,   433,   750,
     435,   214,   703,   139,   439,   440,   142,    43,  1005,   444,
     851,   125,   218,   448,   218,   450,   214,   433,   214,   768,
     455,   456,   214,   458,   138,   139,   941,   218,    64,   464,
     707,    11,   448,   468,   711,   136,   459,   810,   715,   125,
     611,   621,   652,   623,   624,    11,   147,    83,   139,   887,
      86,   141,   138,   139,    90,   150,   151,   152,   534,    19,
     536,   138,   331,   332,    72,   144,    74,   638,    78,   105,
     137,  1013,   139,   140,   558,   111,   135,   136,   137,    18,
      19,   558,   217,   142,   143,   144,   138,   139,   147,   219,
     409,   125,   142,   528,   138,   139,   219,   156,   219,   534,
     217,   536,    56,   539,   138,   139,   140,   948,   354,   355,
     545,   216,   528,     4,   151,   361,   151,   363,    67,   699,
     700,   691,   606,   558,   151,   705,   967,   707,   215,   606,
     214,   711,   973,   713,   214,   715,   214,   151,   837,   153,
     154,   155,   150,   705,  1093,   153,   138,   139,   644,   215,
     646,   159,   732,    19,    20,   138,   139,   165,    24,   218,
     198,   199,   200,   201,   202,   929,   142,   777,   648,   217,
     780,   606,    98,    99,   744,   785,   219,    19,    20,   105,
     192,   193,   123,   124,   110,   111,   219,   439,   440,   197,
     198,   219,   511,   462,   774,  1036,   515,   653,   654,   139,
     976,  1249,  1250,   472,   639,   640,   214,   137,   139,   644,
     217,   646,   156,   138,   218,   128,   917,   652,   109,   218,
      18,   656,   491,   492,   640,   218,   661,    18,   218,   125,
      18,   138,   501,   129,   130,   131,   132,   215,   507,   151,
     219,   821,   108,   139,   817,   253,   254,   219,   218,   568,
      92,   139,   862,   833,   216,   121,   215,   837,    18,   821,
     198,   199,   200,   201,   202,   156,   701,   141,   214,   135,
     139,   219,   214,   542,   543,   837,    12,   158,    33,   145,
      16,    17,   219,    19,    20,   701,   294,   219,    24,   297,
     219,   133,   215,   135,   136,   161,   162,   215,   217,   219,
     217,   143,   144,   738,   858,   147,   625,   887,   142,  1010,
     219,   219,   216,   748,   144,    19,    20,   139,  1156,   161,
      24,   140,  1163,   139,   142,    32,    32,    67,   217,   883,
      32,   128,   748,   142,    32,    32,   142,   345,   346,   139,
      32,  1114,   777,    79,   820,   780,   781,    32,   214,    32,
     785,   359,   218,    32,   220,   778,    92,   140,    18,   794,
     795,    18,    67,   943,   372,    32,    32,   215,   803,  1145,
     378,  1209,   214,   138,  1215,   215,   215,   385,   794,   141,
     215,   217,   215,   158,    56,   820,   705,   823,   139,   215,
     215,   215,    18,   828,   215,   215,    33,   133,   215,   135,
     136,   139,    16,   839,   108,    19,    20,   143,   144,   145,
     137,   147,   828,   214,   219,   137,   851,   121,   151,    78,
     219,   142,    18,   692,   160,   161,   162,   862,   128,   215,
     219,   135,  1012,    32,   138,   171,   172,   173,   174,   125,
     219,   145,    32,   142,   763,   138,   142,   766,   128,   215,
    1012,   187,   142,   144,   723,   219,   215,   161,   162,   217,
     142,   139,  1072,   138,    19,    20,   357,   358,   215,   360,
     215,    19,    20,   215,   215,   219,    24,   140,   214,   137,
     216,   800,   218,   215,   220,   221,   222,   223,    16,   225,
     215,   227,   215,    78,    56,   930,   138,  1051,   215,  1069,
     984,   139,   821,   139,   139,   139,   139,   984,   827,   139,
     214,   830,   215,   948,   930,   138,   220,   137,   837,   133,
     215,   135,   136,   142,    56,   142,   215,   139,   142,   143,
     144,   142,   967,   147,   142,   149,  1146,    92,   973,   216,
     214,    32,   156,   138,   215,   215,   139,   161,   162,   984,
     142,   139,   214,   142,   562,   563,   564,   565,  1168,   215,
     108,   144,   142,   832,   572,   219,   219,  1002,   576,   577,
     142,   142,   137,   121,   144,   202,  1156,   202,   133,    18,
     135,   136,  1152,   215,   215,   397,  1002,   135,   143,   144,
     219,   215,   147,   148,   149,  1028,   178,   145,  1093,  1025,
     214,  1036,  1037,   632,   456,   923,   161,  1036,     3,   641,
     425,   342,  1087,   161,   162,   159,   621,   840,  1123,  1007,
     651,  1037,  1147,   649,    12,   778,    14,  1205,    16,  1209,
      18,    19,    20,   902,   534,  1070,    24,  1072,   907,   908,
     648,   910,   911,   912,   913,   914,   947,    19,    20,   918,
     726,  1167,  1087,  1088,  1070,   796,   782,   981,   971,   786,
    1088,    56,    57,   974,   983,  1183,   214,   986,   559,  1104,
    1182,   940,   220,    68,    69,   996,   567,  1112,   990,   570,
      75,   755,    77,  1172,   804,  1181,  1174,  1218,  1104,   986,
     154,    79,   705,  1012,   932,   889,  1112,   297,  1236,  1134,
    1135,  1136,  1137,   324,   724,  1012,  1141,  1143,  1208,  1157,
     687,  1146,  1147,  1148,  1211,   732,   738,   608,  1134,  1135,
    1136,  1137,   549,   673,  1038,  1141,  1151,   672,  1163,   114,
     621,  1165,  1148,  1168,  1003,  1170,  1171,  1026,  1142,  1021,
     631,   749,   750,   766,   178,   830,  1181,   415,   136,   137,
    1145,  1020,  1119,    -1,  1170,  1171,    -1,   145,    -1,   147,
      -1,  1080,    -1,   135,   136,    -1,    -1,    -1,    -1,    -1,
     142,   143,   144,   781,    -1,   147,    -1,    -1,   669,    -1,
    1215,   672,    -1,    -1,   156,    -1,    -1,   795,    -1,   184,
     185,    -1,    -1,    -1,    -1,   803,    12,  1232,    14,    -1,
      16,    -1,    18,    19,    20,    -1,    -1,    -1,    24,    -1,
      -1,  1246,  1247,    -1,    -1,    -1,  1232,     3,     4,     5,
       6,     7,     8,     9,    10,    -1,   214,    -1,   216,    -1,
    1246,  1247,   220,    -1,   222,   223,   224,   225,    -1,    -1,
     235,    -1,    -1,    16,   216,    -1,    19,    20,    -1,    -1,
     858,    -1,    -1,  1172,    -1,  1174,    -1,    -1,    -1,    -1,
      -1,  1130,    -1,    79,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,  1140,    -1,    -1,    -1,   883,    -1,   768,    -1,    -1,
      -1,    -1,    -1,   774,  1153,    -1,    -1,    -1,  1157,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   291,   292,    -1,    12,
      -1,    19,    20,    16,    17,    -1,    19,    20,    -1,    -1,
      -1,    24,    -1,    -1,    -1,   923,    -1,    -1,    -1,    -1,
     136,    -1,  1191,   814,  1193,    -1,   817,    -1,    -1,   145,
      12,    -1,    14,    -1,    16,    -1,    18,    19,    20,    -1,
      -1,   157,    24,   159,   835,    -1,    -1,   342,    -1,   344,
      -1,    -1,    -1,    -1,    19,    20,    -1,    -1,    71,    -1,
     133,  1230,   135,   136,    -1,    -1,    79,    19,    20,   142,
     143,   144,    24,   368,   147,    -1,   371,    -1,    -1,    92,
      -1,    -1,    -1,   156,    -1,    -1,    -1,    -1,   161,   162,
      -1,   386,    -1,   388,   389,    -1,    -1,    79,   214,    -1,
     216,    -1,   218,    -1,   220,    -1,   222,   223,   224,   225,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   135,   136,    -1,
     133,    -1,   135,   136,   142,   143,   144,    92,    -1,   147,
     143,   144,   145,    -1,   147,   148,   149,    -1,   156,    -1,
      -1,   214,   437,  1051,   439,   440,    -1,   160,   161,   162,
      -1,    -1,   943,   944,   136,    -1,    -1,    -1,   171,   172,
     173,   174,    -1,   145,    -1,   147,    -1,    -1,   133,   464,
     135,   136,    -1,   186,   187,    -1,    -1,    -1,   143,   144,
    1088,    -1,   147,   135,   136,    19,    20,    -1,    -1,    -1,
     142,   143,   144,   145,    -1,   147,   161,   988,    -1,    -1,
     991,   214,    -1,   216,   156,   218,    -1,   220,   221,   222,
     223,    -1,   225,    -1,   227,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   214,    -1,   216,  1026,    -1,    -1,   220,    -1,
     222,   223,   224,   225,    -1,    79,    -1,  1038,    -1,    -1,
     545,    -1,    12,    -1,    14,   550,    16,   552,    18,    19,
      20,    -1,    -1,   558,    24,    -1,    -1,    12,    -1,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      35,    36,    37,    38,    39,    40,    41,    42,    -1,    -1,
      45,   135,   136,    -1,    -1,    -1,    -1,    52,   142,   143,
     144,   606,    -1,   147,    59,    -1,   611,    62,    63,    79,
      65,    -1,   156,    -1,    -1,   620,    71,    72,    73,    -1,
      -1,    -1,    -1,    -1,    79,    -1,    -1,    -1,    -1,    -1,
      -1,   636,    -1,   638,    -1,    -1,    -1,    -1,    93,    94,
      12,    -1,    14,    -1,    16,    -1,    18,    19,    20,   104,
      -1,    -1,    24,    -1,    -1,    -1,    -1,    -1,    -1,    19,
      20,    -1,    22,    -1,    24,    -1,   136,    -1,    -1,    -1,
      -1,   126,   127,    -1,    -1,   145,    -1,    -1,   133,    -1,
     135,   136,    -1,    -1,    -1,    -1,   141,   142,   143,   144,
     145,    -1,   147,    -1,    -1,    -1,    -1,    -1,   703,    -1,
      -1,   156,    -1,    -1,    -1,    -1,   161,    79,    -1,    -1,
     165,   166,   167,   168,   169,   170,   171,   172,   173,   174,
     175,   176,   177,   178,   179,   180,   181,   182,   183,    -1,
     185,    -1,    -1,   738,    -1,   190,   191,   192,   193,    -1,
      19,    20,    21,    22,   214,    -1,   216,    -1,   218,    -1,
     220,    -1,   222,   223,   224,   225,   211,   212,   213,   214,
      -1,    -1,    -1,   218,   136,   220,   221,   222,   223,   224,
     225,    -1,   227,   145,    -1,   135,   136,   782,    -1,    -1,
      -1,   786,   142,   143,   144,   145,    -1,   147,    -1,    -1,
      -1,   796,    -1,    -1,    -1,    -1,   156,    -1,    -1,   804,
      -1,    -1,   807,    19,    20,    -1,    -1,    12,    24,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    38,    39,    -1,    -1,    -1,    -1,    -1,
      45,    -1,   214,    -1,   216,   850,   218,    52,   220,    -1,
     222,   223,   224,   225,   133,    -1,   135,   136,    -1,    -1,
      -1,    -1,    -1,   142,   143,   144,    -1,    72,   147,    -1,
      -1,    -1,    88,    89,    79,    -1,    -1,   156,    -1,    -1,
      -1,    -1,   161,   162,    -1,    -1,    -1,    -1,    -1,    -1,
     106,   107,   108,   109,   110,    -1,    -1,    -1,    -1,    -1,
     116,   117,    -1,   119,   120,   121,   122,   123,    -1,    -1,
      -1,    -1,   917,    -1,    -1,    -1,    -1,    -1,    -1,   135,
      -1,   126,    -1,    -1,    -1,    -1,    -1,    -1,   133,   145,
     135,   136,    -1,    -1,    -1,    -1,   141,   142,   143,   144,
     145,    -1,   147,    -1,    -1,   161,   162,    -1,    -1,    16,
      -1,   156,    19,    20,    -1,    -1,   161,    -1,    -1,    -1,
     165,   166,   167,   168,   169,   170,   171,   172,   173,   174,
     175,   176,   177,   178,   179,   180,   181,   182,   183,   984,
     185,    -1,    -1,    -1,    -1,    -1,    -1,   192,   193,    19,
      20,    -1,   997,    -1,    19,    20,    -1,    -1,   214,    24,
    1005,    -1,    -1,    -1,   220,  1010,   211,   212,   213,   214,
      -1,    -1,    -1,   218,    -1,   220,   221,   222,   223,   224,
     225,    12,   227,    14,    15,    16,    17,    18,    19,    20,
      21,    22,    23,    24,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    38,    39,    -1,
      -1,    -1,    -1,    -1,    45,    -1,    -1,    -1,    -1,    -1,
      -1,    52,    -1,    -1,    -1,    -1,   133,    92,   135,   136,
      -1,    -1,    -1,    -1,    -1,   142,   143,   144,    -1,    16,
     147,    72,    19,    20,    -1,    -1,    -1,    -1,    79,   156,
      -1,    -1,    -1,    -1,   161,   162,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   133,    -1,   135,   136,   137,   133,    -1,
     135,   136,   142,   143,   144,    -1,    -1,   147,   143,   144,
     145,    12,   147,    14,    -1,    16,   156,    18,    19,    20,
      -1,   161,   162,    -1,    -1,   126,   161,    -1,    -1,    -1,
      -1,    -1,   133,    -1,   135,   136,    -1,   214,    -1,   216,
     141,   142,   143,   144,   145,    -1,   147,    -1,    -1,    12,
      -1,    -1,    -1,    16,    17,   156,    19,    20,    -1,    -1,
     161,    24,    -1,    -1,   165,   166,   167,   168,   169,   170,
     171,   172,   173,   174,   175,   176,   177,   178,   179,   180,
     181,   182,   183,    -1,   185,    -1,   133,    -1,   135,   136,
      -1,   192,   193,    -1,    -1,   142,   143,   144,    -1,    -1,
     147,    -1,   149,    -1,    -1,    -1,    -1,    -1,    71,   156,
     211,   212,   213,   214,   161,   162,    79,   218,    -1,   220,
     221,   222,   223,   224,   225,    -1,   227,    -1,    -1,    92,
      -1,    -1,   133,    -1,   135,   136,    -1,    -1,    -1,    -1,
      -1,   142,   143,   144,    -1,    12,   147,    -1,    -1,    16,
      17,    -1,    19,    20,    -1,   156,    -1,    24,    -1,    -1,
     161,   162,    -1,    -1,    -1,    -1,   167,   214,    -1,    -1,
     133,    -1,   135,   136,    19,    20,    -1,    22,    -1,    -1,
     143,   144,   145,    -1,   147,    -1,    -1,    -1,    -1,    -1,
      -1,   192,   193,    -1,    -1,    -1,    -1,   160,   161,   162,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   171,   172,
     173,   174,    79,   214,   215,    19,    20,    -1,    -1,    -1,
      24,    -1,    -1,   186,   187,    92,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    12,    -1,
      14,    -1,    16,    -1,    18,    19,    20,    -1,    -1,    -1,
      -1,   214,    -1,   216,    -1,   218,    -1,   220,   221,   222,
     223,    -1,   225,    -1,   227,    -1,   133,    -1,   135,   136,
      -1,    -1,    -1,    -1,    -1,    -1,   143,    12,   145,    14,
     147,    16,    -1,    18,    19,    20,    -1,    -1,    92,    -1,
     135,   136,    -1,   160,   161,   162,    -1,   142,   143,   144,
      19,    20,   147,    -1,   171,   172,   173,   174,    -1,    -1,
      -1,   156,    -1,    -1,    -1,    12,    -1,    14,    -1,    16,
     187,    18,    19,    20,    -1,    -1,    -1,    -1,    -1,   133,
      -1,   135,   136,   137,    -1,    -1,    -1,    -1,    -1,   143,
     144,   145,    -1,   147,    -1,    -1,    -1,   214,    -1,   216,
      -1,   218,    -1,   220,   221,   222,   223,   161,   225,   133,
     227,   135,   136,    -1,    -1,    -1,    -1,    -1,   142,   143,
     144,    -1,    -1,   147,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   156,    -1,    19,    20,    -1,   161,   162,    24,
      -1,    -1,    -1,   167,    -1,    -1,    -1,    -1,   133,    -1,
     135,   136,    -1,   138,    -1,    -1,    -1,   142,   143,   144,
      -1,    -1,   147,    -1,   133,    -1,   135,   136,   192,   193,
      -1,   156,    -1,   142,   143,   144,   161,   162,   147,    -1,
      -1,    -1,   167,    -1,    -1,   209,   133,   156,   135,   136,
     214,    -1,   161,   162,    -1,   142,   143,   144,    -1,    -1,
     147,    -1,    -1,    88,    89,    -1,    -1,   192,   193,   156,
      -1,    -1,    -1,    -1,   161,   162,    -1,    -1,    -1,    -1,
     167,   106,   107,   108,   109,   110,    -1,    -1,    -1,   214,
      -1,   116,   117,    -1,   119,   120,   121,   122,   123,    -1,
      -1,    -1,    -1,    -1,    -1,   192,   193,    -1,   133,    -1,
     135,   136,    -1,    -1,    -1,    -1,    -1,   142,   143,   144,
     145,    -1,   147,    -1,    -1,    19,    20,   214,    -1,    13,
      -1,   156,    -1,    -1,    -1,    -1,   161,   162,    -1,    -1,
      -1,    -1,    26,    27,    28,    29,    30,    31,    19,    20,
      34,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    43,
      44,    -1,    46,    47,    48,    49,    50,    51,    -1,    -1,
      54,    -1,    -1,    57,    58,    -1,    60,    61,    -1,    -1,
      64,    -1,    66,    -1,    68,    69,    70,    -1,    -1,   214,
      74,    75,    76,    77,    -1,   220,    80,    91,    82,    -1,
      84,    85,    86,    87,    -1,    -1,    90,    -1,    -1,    -1,
      -1,    95,    96,    97,    -1,    99,   100,    -1,   102,    -1,
      91,   105,    -1,    -1,    -1,    -1,    -1,   111,   112,   113,
     114,   115,    -1,    -1,   118,    -1,    -1,    -1,    -1,    -1,
      -1,   135,   136,    -1,    -1,    -1,    -1,    -1,   142,   143,
     144,    -1,    -1,   147,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   156,    -1,   135,   136,    -1,    -1,    -1,    -1,
      -1,   142,   143,   144,    -1,    -1,   147,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   156,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   196,   197,    13,    -1,    -1,    -1,    -1,   203,
     204,   205,   206,   207,   208,    -1,   210,    26,    27,    28,
      29,    30,    31,    -1,    -1,    34,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    43,    44,    -1,    46,    47,    48,
      49,    50,    51,    -1,    -1,    -1,    -1,    -1,    57,    -1,
      -1,    -1,    -1,    -1,    -1,    64,    -1,    -1,    -1,    68,
      69,    70,    -1,    -1,    -1,    74,    75,    76,    77,    -1,
      -1,    80,    -1,    82,    83,    84,    -1,    86,    87,    -1,
      -1,    90,    -1,    -1,    -1,    -1,    95,    96,    97,    -1,
      99,   100,    -1,   102,    -1,    -1,   105,    -1,    -1,    -1,
      -1,    -1,   111,    -1,    -1,    -1,   115,    -1,    -1,   118,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   196,   197,    -1,
      -1,    -1,    -1,    -1,   203,   204,   205,   206,   207,   208,
      -1,   210
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint16 yystos[] =
{
       0,     3,     4,     5,     6,     7,     8,     9,    10,   248,
      19,    20,   133,   135,   136,   142,   143,   144,   147,   156,
     161,   162,   260,    19,    20,   108,   121,   135,   161,   162,
     279,    19,    20,    92,   133,   135,   136,   143,   144,   147,
     161,   291,    19,    20,   135,   136,   142,   143,   144,   147,
     156,   294,    12,    16,    17,    24,    71,    79,   145,   160,
     162,   171,   172,   173,   174,   186,   187,   214,   216,   218,
     220,   221,   222,   223,   225,   227,   261,   289,   291,   311,
     312,   313,   314,    12,    14,    15,    16,    17,    18,    21,
      22,    23,    35,    36,    37,    38,    39,    40,    41,    42,
      45,    52,    59,    62,    63,    65,    71,    72,    73,    79,
      93,    94,   104,   126,   127,   133,   141,   145,   161,   165,
     166,   167,   168,   169,   170,   171,   172,   173,   174,   175,
     176,   177,   178,   179,   180,   181,   182,   183,   185,   190,
     191,   192,   193,   211,   212,   213,   214,   218,   220,   221,
     222,   223,   224,   225,   227,   255,   256,   261,   263,   290,
     294,   298,   299,   300,   301,   368,   382,   383,   392,   393,
     394,   395,   396,   397,   398,   446,   447,   450,   451,     0,
      11,    11,    11,    11,   214,   291,   306,   291,    18,    16,
      19,    64,   136,   147,   272,   273,   274,   218,   218,   214,
     214,    18,    18,   311,   321,   324,   291,   313,   317,   318,
     318,   321,   311,    16,   214,   260,   264,   325,   321,   325,
     318,   139,   141,   291,    11,   139,   312,   312,   382,   401,
     139,   391,   422,   391,   391,   218,   415,   423,   391,   450,
     294,   391,   391,   423,    18,   401,   382,   382,   216,   218,
     315,   315,   315,   218,   218,   214,   214,   214,   382,   382,
     218,   384,   385,   385,   382,   399,   402,   450,   382,   399,
     311,   264,   403,   399,   399,   403,   148,   149,   324,   367,
      12,    14,    16,    18,    19,    20,    79,   136,   157,   159,
     214,   216,   218,   220,   222,   223,   224,   225,   290,   296,
     371,   378,   379,   294,   139,   141,   261,   260,   298,   300,
     388,   399,   312,   327,   328,   329,   216,   264,    11,   125,
     139,   218,   383,   384,   386,   387,   382,   311,   382,   311,
     214,   424,   383,   401,    11,    13,    26,    27,    28,    29,
      30,    31,    34,    43,    44,    46,    47,    48,    49,    50,
      51,    57,    64,    68,    69,    70,    74,    75,    76,    77,
      80,    82,    83,    84,    86,    87,    90,    95,    96,    97,
      99,   100,   102,   105,   111,   115,   118,   196,   197,   203,
     204,   205,   206,   207,   208,   210,   249,   250,   251,   252,
     257,   440,   444,    11,    13,    43,    54,    58,    60,    61,
      64,    66,    74,    85,    86,    90,   111,   112,   113,   114,
     207,   253,   254,   257,   440,   448,   291,   303,   304,   306,
     139,   302,   141,   272,   272,   138,   275,   144,   325,   325,
     321,   321,    78,   138,   323,   137,   215,   138,   293,   137,
     140,   319,   217,   219,   137,   215,   217,   264,   142,   219,
     137,   215,   219,   217,   145,   214,   220,   261,   277,   278,
     279,   280,   140,    56,   216,   421,   151,   318,   157,   159,
     416,   151,    67,   151,   141,   261,   215,   215,   215,   311,
     311,   214,   214,   214,   403,   403,   399,   399,   311,   367,
     385,   138,   140,   400,   137,   215,   215,   219,   137,   215,
     217,   142,   219,   137,   215,   217,   219,   137,   296,   296,
     321,   136,   147,   296,   370,   371,   374,   304,   318,   374,
     149,   264,   376,   374,   374,   376,   296,   379,   139,   389,
     379,   139,   217,   312,   138,   330,   156,   331,   388,   218,
     311,   387,   103,   103,    78,    78,   399,   382,   382,   128,
     289,   291,   292,   346,   291,   260,   287,   287,   218,   347,
     356,    16,   214,   266,   266,   266,   446,    91,   294,   430,
      91,   430,   260,   262,   216,   294,   266,   266,   279,   333,
     291,   340,    18,    19,   265,   291,   342,   262,    12,    14,
      16,    18,   167,   192,   193,   214,   260,   267,   268,   260,
     267,    18,   267,   260,   291,   338,   218,   441,   442,   291,
     353,   291,   344,   267,   445,   443,    18,   105,   111,   250,
     218,   309,   450,    81,    91,   136,   296,   437,    18,   370,
     432,   442,   267,   449,   443,   302,   138,   305,   215,   277,
     151,   273,   219,   219,   137,   215,   137,   215,   218,   311,
     321,   291,   139,   317,   317,   321,   216,   215,   311,   321,
      18,   277,   281,   281,   141,   280,   279,   401,   318,   214,
     219,   321,   214,   420,   401,   139,   217,   219,   399,   399,
     399,   219,   219,   215,   215,   138,   219,   382,   401,   399,
     399,   214,   216,   382,   399,   382,   158,   296,   370,    33,
     138,   139,   375,   218,   371,   372,   373,   137,   215,   217,
     219,   137,   215,   142,   219,   137,   215,   217,   219,   311,
     150,   151,   152,   390,   389,   216,   328,   329,   144,   450,
     382,   382,   137,   370,   408,   409,   410,   411,   137,   292,
     310,   412,   413,   414,   140,   410,   291,   306,   139,   142,
      32,   288,   288,   318,   294,    32,   357,   260,   262,   262,
     262,    67,   430,   214,   296,   425,   428,   429,    32,   431,
     430,   431,   262,   217,   128,   262,   262,   142,    32,   334,
     139,   214,    32,   341,   142,   139,    32,   343,   267,   267,
     269,   268,   267,   271,   142,   214,    32,   339,   318,   442,
     294,   364,   142,   214,    32,   354,   306,    32,   345,   209,
     259,   140,    18,    18,   442,   303,   307,   290,   294,   295,
     301,   332,   439,    67,   432,   432,   296,   128,   139,   436,
      32,   438,   142,    32,   433,    79,   294,   297,   434,   259,
     303,   306,   311,   275,   321,   321,   325,   323,   215,   293,
     218,   277,   320,   319,   319,   215,   316,   321,   138,   326,
     215,   141,   138,   282,   215,   215,   217,   294,   417,   418,
     158,   418,   422,    56,   215,   215,   215,    18,   400,   215,
     215,   399,   382,   138,   404,   215,   217,    33,   370,   370,
     311,   148,   149,   304,   366,   373,   374,   374,   370,   374,
     274,   382,   390,   388,   330,   331,   219,    55,    55,   409,
     124,   151,   153,   154,   155,   411,   412,   214,   151,   414,
     399,   302,   311,   137,   260,   284,   285,   286,   287,   219,
      78,   349,   356,    20,   215,   446,   431,   425,   426,   429,
     142,   430,   431,   128,   290,   295,   320,   333,   277,    19,
      20,    88,    89,   106,   107,   109,   110,   116,   117,   119,
     120,   122,   123,   135,   161,   162,   260,   277,   283,   335,
     336,   340,    18,   277,   342,   215,   138,   270,   215,   311,
     336,   338,   219,   214,   218,   296,   361,   362,    32,   365,
     137,   347,   350,   351,   352,   336,   353,   125,   355,   302,
     344,   446,   142,   142,   364,   138,   308,   219,   294,   329,
     218,   371,   380,   381,   450,   433,   433,   436,   296,   311,
     142,   437,   382,   432,   294,   379,    32,   435,   450,   305,
     215,   215,   219,   291,   217,   264,   277,   139,   138,   419,
     215,   215,   215,   215,   217,   264,   370,   375,   219,   215,
     215,   138,   377,   215,   144,   382,   382,   382,   411,   382,
     405,   406,   382,   382,   382,   382,   414,   304,   382,   140,
     142,   284,    78,   286,   288,   347,   311,   357,    16,    56,
     138,   427,   215,   382,   431,   295,   334,   139,   138,   337,
     215,   341,   343,   267,   215,   339,   296,   358,   359,   318,
     362,   139,   163,   164,   276,   364,   350,   294,   352,   215,
     354,   344,   142,   345,   198,   199,   200,   201,   202,   258,
     311,   382,   365,   303,   309,   331,   304,   381,   389,    56,
     142,   436,   382,   438,   129,   130,   131,   132,   369,   433,
     142,   276,   434,   198,   202,   258,   139,   216,   142,   282,
     311,   417,   214,   142,   149,   264,    33,    32,   407,   215,
     399,   311,   286,   277,   215,   425,   283,   335,   139,   270,
     142,   139,   138,   360,   137,   215,   219,   274,   311,   365,
     352,   214,   348,   142,   345,   311,   446,   445,   308,   144,
     219,   142,   382,   142,   311,   311,   311,   311,   382,   311,
     435,   450,   449,   320,   316,   311,   419,   399,   382,   142,
     370,   405,   215,   427,   337,   277,   311,   311,   358,   359,
     144,   142,   363,   321,   349,   351,   202,   382,   382,   369,
     142,   202,   137,   326,   215,   404,   370,   407,   360,   215,
      18,   215,   382,   311,   377,   369,   137,   140,   322,   311,
     311,   219,   322,   322
};

#define yyerrok		(yyerrstatus = 0)
#define yyclearin	(yychar = YYEMPTY)
#define YYEMPTY		(-2)
#define YYEOF		0

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrorlab


/* Like YYERROR except do call yyerror.  This remains here temporarily
   to ease the transition to the new meaning of YYERROR, for GCC.
   Once GCC version 2 has supplanted version 1, this can go.  However,
   YYFAIL appears to be in use.  Nevertheless, it is formally deprecated
   in Bison 2.4.2's NEWS entry, where a plan to phase it out is
   discussed.  */

#define YYFAIL		goto yyerrlab
#if defined YYFAIL
  /* This is here to suppress warnings from the GCC cpp's
     -Wunused-macros.  Normally we don't worry about that warning, but
     some users do, and we want to make it easy for users to remove
     YYFAIL uses, which will produce warnings from Bison 2.5.  */
#endif

#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)					\
do								\
  if (yychar == YYEMPTY && yylen == 1)				\
    {								\
      yychar = (Token);						\
      yylval = (Value);						\
      YYPOPSTACK (1);						\
      goto yybackup;						\
    }								\
  else								\
    {								\
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;							\
    }								\
while (YYID (0))


#define YYTERROR	1
#define YYERRCODE	256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#define YYRHSLOC(Rhs, K) ((Rhs)[K])
#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)				\
    do									\
      if (YYID (N))                                                    \
	{								\
	  (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;	\
	  (Current).first_column = YYRHSLOC (Rhs, 1).first_column;	\
	  (Current).last_line    = YYRHSLOC (Rhs, N).last_line;		\
	  (Current).last_column  = YYRHSLOC (Rhs, N).last_column;	\
	}								\
      else								\
	{								\
	  (Current).first_line   = (Current).last_line   =		\
	    YYRHSLOC (Rhs, 0).last_line;				\
	  (Current).first_column = (Current).last_column =		\
	    YYRHSLOC (Rhs, 0).last_column;				\
	}								\
    while (YYID (0))
#endif


/* This macro is provided for backward compatibility. */

#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


/* YYLEX -- calling `yylex' with the right arguments.  */

#ifdef YYLEX_PARAM
# define YYLEX yylex (YYLEX_PARAM)
#else
# define YYLEX yylex ()
#endif

/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)			\
do {						\
  if (yydebug)					\
    YYFPRINTF Args;				\
} while (YYID (0))

# define YY_SYMBOL_PRINT(Title, Type, Value, Location)			  \
do {									  \
  if (yydebug)								  \
    {									  \
      YYFPRINTF (stderr, "%s ", Title);					  \
      yy_symbol_print (stderr,						  \
		  Type, Value); \
      YYFPRINTF (stderr, "\n");						  \
    }									  \
} while (YYID (0))


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_value_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# else
  YYUSE (yyoutput);
# endif
  switch (yytype)
    {
      default:
	break;
    }
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (yytype < YYNTOKENS)
    YYFPRINTF (yyoutput, "token %s (", yytname[yytype]);
  else
    YYFPRINTF (yyoutput, "nterm %s (", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
#else
static void
yy_stack_print (yybottom, yytop)
    yytype_int16 *yybottom;
    yytype_int16 *yytop;
#endif
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)				\
do {								\
  if (yydebug)							\
    yy_stack_print ((Bottom), (Top));				\
} while (YYID (0))


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_reduce_print (YYSTYPE *yyvsp, int yyrule)
#else
static void
yy_reduce_print (yyvsp, yyrule)
    YYSTYPE *yyvsp;
    int yyrule;
#endif
{
  int yynrhs = yyr2[yyrule];
  int yyi;
  unsigned long int yylno = yyrline[yyrule];
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
	     yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr, yyrhs[yyprhs[yyrule] + yyi],
		       &(yyvsp[(yyi + 1) - (yynrhs)])
		       		       );
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (yydebug)				\
    yy_reduce_print (yyvsp, Rule); \
} while (YYID (0))

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static YYSIZE_T
yystrlen (const char *yystr)
#else
static YYSIZE_T
yystrlen (yystr)
    const char *yystr;
#endif
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static char *
yystpcpy (char *yydest, const char *yysrc)
#else
static char *
yystpcpy (yydest, yysrc)
    char *yydest;
    const char *yysrc;
#endif
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
	switch (*++yyp)
	  {
	  case '\'':
	  case ',':
	    goto do_not_strip_quotes;

	  case '\\':
	    if (*++yyp != '\\')
	      goto do_not_strip_quotes;
	    /* Fall through.  */
	  default:
	    if (yyres)
	      yyres[yyn] = *yyp;
	    yyn++;
	    break;

	  case '"':
	    if (yyres)
	      yyres[yyn] = '\0';
	    return yyn;
	  }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (0, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  YYSIZE_T yysize1;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = 0;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - Assume YYFAIL is not used.  It's too flawed to consider.  See
       <http://lists.gnu.org/archive/html/bison-patches/2009-12/msg00024.html>
       for details.  YYERROR is fine as it does not invoke this
       function.
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                yysize1 = yysize + yytnamerr (0, yytname[yyx]);
                if (! (yysize <= yysize1
                       && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                  return 2;
                yysize = yysize1;
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  yysize1 = yysize + yystrlen (yyformat);
  if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
    return 2;
  yysize = yysize1;

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
#else
static void
yydestruct (yymsg, yytype, yyvaluep)
    const char *yymsg;
    int yytype;
    YYSTYPE *yyvaluep;
#endif
{
  YYUSE (yyvaluep);

  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  switch (yytype)
    {

      default:
	break;
    }
}


/* Prevent warnings from -Wmissing-prototypes.  */
#ifdef YYPARSE_PARAM
#if defined __STDC__ || defined __cplusplus
int yyparse (void *YYPARSE_PARAM);
#else
int yyparse ();
#endif
#else /* ! YYPARSE_PARAM */
#if defined __STDC__ || defined __cplusplus
int yyparse (void);
#else
int yyparse ();
#endif
#endif /* ! YYPARSE_PARAM */


/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;

/* Number of syntax errors so far.  */
int yynerrs;


/*----------.
| yyparse.  |
`----------*/

#ifdef YYPARSE_PARAM
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void *YYPARSE_PARAM)
#else
int
yyparse (YYPARSE_PARAM)
    void *YYPARSE_PARAM;
#endif
#else /* ! YYPARSE_PARAM */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void)
#else
int
yyparse ()

#endif
#endif
{
    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       `yyss': related to states.
       `yyvs': related to semantic values.

       Refer to the stacks thru separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yytoken = 0;
  yyss = yyssa;
  yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */

  /* Initialize stack pointers.
     Waste one element of value and location stack
     so that they stay on the same level as the state stack.
     The wasted elements are never initialized.  */
  yyssp = yyss;
  yyvsp = yyvs;

  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
	/* Give user a chance to reallocate the stack.  Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	YYSTYPE *yyvs1 = yyvs;
	yytype_int16 *yyss1 = yyss;

	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if yyoverflow is a macro.  */
	yyoverflow (YY_("memory exhausted"),
		    &yyss1, yysize * sizeof (*yyssp),
		    &yyvs1, yysize * sizeof (*yyvsp),
		    &yystacksize);

	yyss = yyss1;
	yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
	goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
	yystacksize = YYMAXDEPTH;

      {
	yytype_int16 *yyss1 = yyss;
	union yyalloc *yyptr =
	  (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
	if (! yyptr)
	  goto yyexhaustedlab;
	YYSTACK_RELOCATE (yyss_alloc, yyss);
	YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
	if (yyss1 != yyssa)
	  YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
		  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
	YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = YYLEX;
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  *++yyvsp = yylval;

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     `$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:

/* Line 1806 of yacc.c  */
#line 1560 "ats_grammar.yats"
    { theYYVALyyres = atsopt_yyres_d0eclst((yyvsp[(2) - (3)].d0eclst)) ; return 0 ; }
    break;

  case 3:

/* Line 1806 of yacc.c  */
#line 1561 "ats_grammar.yats"
    { theYYVALyyres = atsopt_yyres_d0eclst((yyvsp[(2) - (3)].d0eclst)) ; return 0 ; }
    break;

  case 4:

/* Line 1806 of yacc.c  */
#line 1562 "ats_grammar.yats"
    { theYYVALyyres = atsopt_yyres_i0de((yyvsp[(2) - (3)].i0de)) ; return 0 ; }
    break;

  case 5:

/* Line 1806 of yacc.c  */
#line 1563 "ats_grammar.yats"
    { theYYVALyyres = atsopt_yyres_i0de((yyvsp[(2) - (3)].i0de)) ; return 0 ; }
    break;

  case 6:

/* Line 1806 of yacc.c  */
#line 1564 "ats_grammar.yats"
    { theYYVALyyres = atsopt_yyres_i0de((yyvsp[(2) - (3)].i0de)) ; return 0 ; }
    break;

  case 7:

/* Line 1806 of yacc.c  */
#line 1565 "ats_grammar.yats"
    { theYYVALyyres = atsopt_yyres_i0de((yyvsp[(2) - (3)].i0de)) ; return 0 ; }
    break;

  case 8:

/* Line 1806 of yacc.c  */
#line 1566 "ats_grammar.yats"
    { theYYVALyyres = atsopt_yyres_s0exp((yyvsp[(2) - (3)].s0exp)) ; return 0 ; }
    break;

  case 9:

/* Line 1806 of yacc.c  */
#line 1567 "ats_grammar.yats"
    { theYYVALyyres = atsopt_yyres_d0exp((yyvsp[(2) - (3)].d0exp)) ; return 0 ; }
    break;

  case 10:

/* Line 1806 of yacc.c  */
#line 1571 "ats_grammar.yats"
    { (yyval.abskind) = abskind_prop () ; }
    break;

  case 11:

/* Line 1806 of yacc.c  */
#line 1572 "ats_grammar.yats"
    { (yyval.abskind) = abskind_type () ; }
    break;

  case 12:

/* Line 1806 of yacc.c  */
#line 1573 "ats_grammar.yats"
    { (yyval.abskind) = abskind_t0ype () ; }
    break;

  case 13:

/* Line 1806 of yacc.c  */
#line 1574 "ats_grammar.yats"
    { (yyval.abskind) = abskind_view () ; }
    break;

  case 14:

/* Line 1806 of yacc.c  */
#line 1575 "ats_grammar.yats"
    { (yyval.abskind) = abskind_viewtype () ; }
    break;

  case 15:

/* Line 1806 of yacc.c  */
#line 1576 "ats_grammar.yats"
    { (yyval.abskind) = abskind_viewt0ype () ; }
    break;

  case 16:

/* Line 1806 of yacc.c  */
#line 1580 "ats_grammar.yats"
    { (yyval.dcstkind) = dcstkind_fun () ; }
    break;

  case 17:

/* Line 1806 of yacc.c  */
#line 1581 "ats_grammar.yats"
    { (yyval.dcstkind) = dcstkind_val () ; }
    break;

  case 18:

/* Line 1806 of yacc.c  */
#line 1582 "ats_grammar.yats"
    { (yyval.dcstkind) = dcstkind_castfn () ; }
    break;

  case 19:

/* Line 1806 of yacc.c  */
#line 1583 "ats_grammar.yats"
    { (yyval.dcstkind) = dcstkind_praxi () ; }
    break;

  case 20:

/* Line 1806 of yacc.c  */
#line 1584 "ats_grammar.yats"
    { (yyval.dcstkind) = dcstkind_prfun () ; }
    break;

  case 21:

/* Line 1806 of yacc.c  */
#line 1585 "ats_grammar.yats"
    { (yyval.dcstkind) = dcstkind_prval () ; }
    break;

  case 22:

/* Line 1806 of yacc.c  */
#line 1589 "ats_grammar.yats"
    { (yyval.datakind) = datakind_prop () ; }
    break;

  case 23:

/* Line 1806 of yacc.c  */
#line 1590 "ats_grammar.yats"
    { (yyval.datakind) = datakind_type () ; }
    break;

  case 24:

/* Line 1806 of yacc.c  */
#line 1591 "ats_grammar.yats"
    { (yyval.datakind) = datakind_view () ; }
    break;

  case 25:

/* Line 1806 of yacc.c  */
#line 1592 "ats_grammar.yats"
    { (yyval.datakind) = datakind_viewtype () ; }
    break;

  case 26:

/* Line 1806 of yacc.c  */
#line 1596 "ats_grammar.yats"
    { (yyval.stadefkind) = stadefkind_generic () ; }
    break;

  case 27:

/* Line 1806 of yacc.c  */
#line 1597 "ats_grammar.yats"
    { (yyval.stadefkind) = stadefkind_prop ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 28:

/* Line 1806 of yacc.c  */
#line 1598 "ats_grammar.yats"
    { (yyval.stadefkind) = stadefkind_type ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 29:

/* Line 1806 of yacc.c  */
#line 1599 "ats_grammar.yats"
    { (yyval.stadefkind) = stadefkind_view ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 30:

/* Line 1806 of yacc.c  */
#line 1600 "ats_grammar.yats"
    { (yyval.stadefkind) = stadefkind_viewtype ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 31:

/* Line 1806 of yacc.c  */
#line 1604 "ats_grammar.yats"
    { (yyval.valkind) = valkind_val () ; }
    break;

  case 32:

/* Line 1806 of yacc.c  */
#line 1605 "ats_grammar.yats"
    { (yyval.valkind) = valkind_valminus () ; }
    break;

  case 33:

/* Line 1806 of yacc.c  */
#line 1606 "ats_grammar.yats"
    { (yyval.valkind) = valkind_valplus () ; }
    break;

  case 34:

/* Line 1806 of yacc.c  */
#line 1607 "ats_grammar.yats"
    { (yyval.valkind) = valkind_prval () ; }
    break;

  case 35:

/* Line 1806 of yacc.c  */
#line 1611 "ats_grammar.yats"
    { (yyval.funkind) = funkind_fn () ; }
    break;

  case 36:

/* Line 1806 of yacc.c  */
#line 1612 "ats_grammar.yats"
    { (yyval.funkind) = funkind_fnstar () ; }
    break;

  case 37:

/* Line 1806 of yacc.c  */
#line 1613 "ats_grammar.yats"
    { (yyval.funkind) = funkind_fun () ; }
    break;

  case 38:

/* Line 1806 of yacc.c  */
#line 1614 "ats_grammar.yats"
    { (yyval.funkind) = funkind_castfn () ; }
    break;

  case 39:

/* Line 1806 of yacc.c  */
#line 1615 "ats_grammar.yats"
    { (yyval.funkind) = funkind_prfn () ; }
    break;

  case 40:

/* Line 1806 of yacc.c  */
#line 1616 "ats_grammar.yats"
    { (yyval.funkind) = funkind_prfun () ; }
    break;

  case 41:

/* Line 1806 of yacc.c  */
#line 1620 "ats_grammar.yats"
    { (yyval.lamkind) = lamkind_lam ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 42:

/* Line 1806 of yacc.c  */
#line 1621 "ats_grammar.yats"
    { (yyval.lamkind) = lamkind_atlam ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 43:

/* Line 1806 of yacc.c  */
#line 1622 "ats_grammar.yats"
    { (yyval.lamkind) = lamkind_llam ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 44:

/* Line 1806 of yacc.c  */
#line 1623 "ats_grammar.yats"
    { (yyval.lamkind) = lamkind_atllam ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 45:

/* Line 1806 of yacc.c  */
#line 1627 "ats_grammar.yats"
    { (yyval.fixkind) = fixkind_fix ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 46:

/* Line 1806 of yacc.c  */
#line 1628 "ats_grammar.yats"
    { (yyval.fixkind) = fixkind_atfix ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 47:

/* Line 1806 of yacc.c  */
#line 1632 "ats_grammar.yats"
    { (yyval.srpifkindtok) = srpifkindtok_if ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 48:

/* Line 1806 of yacc.c  */
#line 1633 "ats_grammar.yats"
    { (yyval.srpifkindtok) = srpifkindtok_ifdef ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 49:

/* Line 1806 of yacc.c  */
#line 1634 "ats_grammar.yats"
    { (yyval.srpifkindtok) = srpifkindtok_ifndef ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 50:

/* Line 1806 of yacc.c  */
#line 1638 "ats_grammar.yats"
    { (yyval.srpifkindtok) = srpifkindtok_if ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 51:

/* Line 1806 of yacc.c  */
#line 1639 "ats_grammar.yats"
    { (yyval.srpifkindtok) = srpifkindtok_ifdef ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 52:

/* Line 1806 of yacc.c  */
#line 1640 "ats_grammar.yats"
    { (yyval.srpifkindtok) = srpifkindtok_ifndef ((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 53:

/* Line 1806 of yacc.c  */
#line 1644 "ats_grammar.yats"
    { ; }
    break;

  case 54:

/* Line 1806 of yacc.c  */
#line 1645 "ats_grammar.yats"
    { ; }
    break;

  case 55:

/* Line 1806 of yacc.c  */
#line 1649 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 56:

/* Line 1806 of yacc.c  */
#line 1650 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 57:

/* Line 1806 of yacc.c  */
#line 1651 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_ampersand((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 58:

/* Line 1806 of yacc.c  */
#line 1652 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_backslash((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 59:

/* Line 1806 of yacc.c  */
#line 1653 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_bang((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 60:

/* Line 1806 of yacc.c  */
#line 1654 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_eq((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 61:

/* Line 1806 of yacc.c  */
#line 1655 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_gt((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 62:

/* Line 1806 of yacc.c  */
#line 1656 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_gtlt((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 63:

/* Line 1806 of yacc.c  */
#line 1657 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_lt((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 64:

/* Line 1806 of yacc.c  */
#line 1658 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_minusgt((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 65:

/* Line 1806 of yacc.c  */
#line 1659 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_minusltgt((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 66:

/* Line 1806 of yacc.c  */
#line 1660 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_tilde((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 67:

/* Line 1806 of yacc.c  */
#line 1664 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 68:

/* Line 1806 of yacc.c  */
#line 1668 "ats_grammar.yats"
    { (yyval.i0delst) = i0delst_nil() ; }
    break;

  case 69:

/* Line 1806 of yacc.c  */
#line 1669 "ats_grammar.yats"
    { (yyval.i0delst) = i0delst_cons((yyvsp[(1) - (2)].i0de), (yyvsp[(2) - (2)].i0delst)) ; }
    break;

  case 70:

/* Line 1806 of yacc.c  */
#line 1673 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 71:

/* Line 1806 of yacc.c  */
#line 1674 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_DO((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 72:

/* Line 1806 of yacc.c  */
#line 1675 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_WHILE((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 73:

/* Line 1806 of yacc.c  */
#line 1679 "ats_grammar.yats"
    { (yyval.l0ab) = l0ab_ide((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 74:

/* Line 1806 of yacc.c  */
#line 1680 "ats_grammar.yats"
    { (yyval.l0ab) = l0ab_int((yyvsp[(1) - (1)].i0nt)) ; }
    break;

  case 75:

/* Line 1806 of yacc.c  */
#line 1681 "ats_grammar.yats"
    { (yyval.l0ab) = (yyvsp[(2) - (3)].l0ab) ; }
    break;

  case 76:

/* Line 1806 of yacc.c  */
#line 1685 "ats_grammar.yats"
    { (yyval.i0de) = stai0de_make((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 77:

/* Line 1806 of yacc.c  */
#line 1689 "ats_grammar.yats"
    { (yyval.p0rec) = p0rec_emp() ; }
    break;

  case 78:

/* Line 1806 of yacc.c  */
#line 1690 "ats_grammar.yats"
    { (yyval.p0rec) = p0rec_int((yyvsp[(1) - (1)].i0nt)) ; }
    break;

  case 79:

/* Line 1806 of yacc.c  */
#line 1691 "ats_grammar.yats"
    { (yyval.p0rec) = p0rec_ide((yyvsp[(2) - (3)].i0de)) ; }
    break;

  case 80:

/* Line 1806 of yacc.c  */
#line 1692 "ats_grammar.yats"
    { (yyval.p0rec) = p0rec_opr((yyvsp[(2) - (5)].i0de), (yyvsp[(3) - (5)].i0de), (yyvsp[(4) - (5)].i0nt)) ; }
    break;

  case 81:

/* Line 1806 of yacc.c  */
#line 1696 "ats_grammar.yats"
    { (yyval.e0xp) = e0xp_app((yyvsp[(1) - (2)].e0xp), (yyvsp[(2) - (2)].e0xp)) ; }
    break;

  case 82:

/* Line 1806 of yacc.c  */
#line 1697 "ats_grammar.yats"
    { (yyval.e0xp) = (yyvsp[(1) - (1)].e0xp) ; }
    break;

  case 83:

/* Line 1806 of yacc.c  */
#line 1701 "ats_grammar.yats"
    { (yyval.e0xp) = e0xp_char((yyvsp[(1) - (1)].c0har)) ; }
    break;

  case 84:

/* Line 1806 of yacc.c  */
#line 1702 "ats_grammar.yats"
    { (yyval.e0xp) = e0xp_float((yyvsp[(1) - (1)].f0loat)) ; }
    break;

  case 85:

/* Line 1806 of yacc.c  */
#line 1703 "ats_grammar.yats"
    { (yyval.e0xp) = e0xp_int((yyvsp[(1) - (1)].i0nt)) ; }
    break;

  case 86:

/* Line 1806 of yacc.c  */
#line 1704 "ats_grammar.yats"
    { (yyval.e0xp) = e0xp_string((yyvsp[(1) - (1)].s0tring)) ; }
    break;

  case 87:

/* Line 1806 of yacc.c  */
#line 1705 "ats_grammar.yats"
    { (yyval.e0xp) = e0xp_FILENAME((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 88:

/* Line 1806 of yacc.c  */
#line 1706 "ats_grammar.yats"
    { (yyval.e0xp) = e0xp_LOCATION((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 89:

/* Line 1806 of yacc.c  */
#line 1707 "ats_grammar.yats"
    { (yyval.e0xp) = e0xp_ide((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 90:

/* Line 1806 of yacc.c  */
#line 1708 "ats_grammar.yats"
    { (yyval.e0xp) = e0xp_list((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].e0xplst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 91:

/* Line 1806 of yacc.c  */
#line 1709 "ats_grammar.yats"
    { (yyval.e0xp) = e0xp_eval((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].e0xp), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 92:

/* Line 1806 of yacc.c  */
#line 1713 "ats_grammar.yats"
    { (yyval.e0xplst) = e0xplst_nil() ; }
    break;

  case 93:

/* Line 1806 of yacc.c  */
#line 1714 "ats_grammar.yats"
    { (yyval.e0xplst) = e0xplst_cons((yyvsp[(1) - (2)].e0xp), (yyvsp[(2) - (2)].e0xplst)) ; }
    break;

  case 94:

/* Line 1806 of yacc.c  */
#line 1718 "ats_grammar.yats"
    { (yyval.e0xplst) = e0xplst_nil() ; }
    break;

  case 95:

/* Line 1806 of yacc.c  */
#line 1719 "ats_grammar.yats"
    { (yyval.e0xplst) = e0xplst_cons((yyvsp[(2) - (3)].e0xp), (yyvsp[(3) - (3)].e0xplst)) ; }
    break;

  case 96:

/* Line 1806 of yacc.c  */
#line 1723 "ats_grammar.yats"
    { (yyval.e0xpopt) = e0xpopt_none() ; }
    break;

  case 97:

/* Line 1806 of yacc.c  */
#line 1724 "ats_grammar.yats"
    { (yyval.e0xpopt) = e0xpopt_some((yyvsp[(1) - (1)].e0xp)) ; }
    break;

  case 98:

/* Line 1806 of yacc.c  */
#line 1728 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 99:

/* Line 1806 of yacc.c  */
#line 1732 "ats_grammar.yats"
    { (yyval.e0fftag) = e0fftag_cst (0, (yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 100:

/* Line 1806 of yacc.c  */
#line 1733 "ats_grammar.yats"
    { (yyval.e0fftag) = e0fftag_cst (1, (yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 101:

/* Line 1806 of yacc.c  */
#line 1734 "ats_grammar.yats"
    { (yyval.e0fftag) = e0fftag_var((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 102:

/* Line 1806 of yacc.c  */
#line 1735 "ats_grammar.yats"
    { (yyval.e0fftag) = e0fftag_var_fun((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 103:

/* Line 1806 of yacc.c  */
#line 1736 "ats_grammar.yats"
    { (yyval.e0fftag) = e0fftag_int((yyvsp[(1) - (1)].i0nt)) ; }
    break;

  case 104:

/* Line 1806 of yacc.c  */
#line 1740 "ats_grammar.yats"
    { (yyval.e0fftaglst) = e0fftaglst_nil() ; }
    break;

  case 105:

/* Line 1806 of yacc.c  */
#line 1741 "ats_grammar.yats"
    { (yyval.e0fftaglst) = e0fftaglst_cons((yyvsp[(1) - (2)].e0fftag), (yyvsp[(2) - (2)].e0fftaglst)) ; }
    break;

  case 106:

/* Line 1806 of yacc.c  */
#line 1745 "ats_grammar.yats"
    { (yyval.e0fftaglst) = e0fftaglst_nil() ; }
    break;

  case 107:

/* Line 1806 of yacc.c  */
#line 1746 "ats_grammar.yats"
    { (yyval.e0fftaglst) = e0fftaglst_cons((yyvsp[(2) - (3)].e0fftag), (yyvsp[(3) - (3)].e0fftaglst)) ; }
    break;

  case 108:

/* Line 1806 of yacc.c  */
#line 1750 "ats_grammar.yats"
    { (yyval.e0fftaglstopt) = e0fftaglstopt_none() ; }
    break;

  case 109:

/* Line 1806 of yacc.c  */
#line 1751 "ats_grammar.yats"
    { (yyval.e0fftaglstopt) = e0fftaglstopt_some(e0fftaglst_nil()) ; }
    break;

  case 110:

/* Line 1806 of yacc.c  */
#line 1752 "ats_grammar.yats"
    { (yyval.e0fftaglstopt) = e0fftaglstopt_some((yyvsp[(2) - (3)].e0fftaglst)) ; }
    break;

  case 111:

/* Line 1806 of yacc.c  */
#line 1756 "ats_grammar.yats"
    { (yyval.s0rt) = s0rt_app((yyvsp[(1) - (2)].s0rt), (yyvsp[(2) - (2)].s0rt)) ; }
    break;

  case 112:

/* Line 1806 of yacc.c  */
#line 1757 "ats_grammar.yats"
    { (yyval.s0rt) = (yyvsp[(1) - (1)].s0rt) ; }
    break;

  case 113:

/* Line 1806 of yacc.c  */
#line 1761 "ats_grammar.yats"
    { (yyval.s0rtq) = s0rtq_sym((yyvsp[(1) - (2)].i0de)) ; }
    break;

  case 114:

/* Line 1806 of yacc.c  */
#line 1762 "ats_grammar.yats"
    { (yyval.s0rtq) = s0rtq_str((yyvsp[(2) - (3)].s0tring)) ; }
    break;

  case 115:

/* Line 1806 of yacc.c  */
#line 1766 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 116:

/* Line 1806 of yacc.c  */
#line 1767 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 117:

/* Line 1806 of yacc.c  */
#line 1768 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_t0ype((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 118:

/* Line 1806 of yacc.c  */
#line 1769 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_viewt0ype((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 119:

/* Line 1806 of yacc.c  */
#line 1770 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_backslash((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 120:

/* Line 1806 of yacc.c  */
#line 1771 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_minusgt((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 121:

/* Line 1806 of yacc.c  */
#line 1772 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_minusltgt((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 122:

/* Line 1806 of yacc.c  */
#line 1776 "ats_grammar.yats"
    { (yyval.s0rt) = s0rt_ide((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 123:

/* Line 1806 of yacc.c  */
#line 1777 "ats_grammar.yats"
    { (yyval.s0rt) = s0rt_qid((yyvsp[(1) - (2)].s0rtq), (yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 124:

/* Line 1806 of yacc.c  */
#line 1778 "ats_grammar.yats"
    { (yyval.s0rt) = s0rt_list((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0rtlst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 125:

/* Line 1806 of yacc.c  */
#line 1779 "ats_grammar.yats"
    { (yyval.s0rt) = s0rt_tup((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0rtlst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 126:

/* Line 1806 of yacc.c  */
#line 1783 "ats_grammar.yats"
    { (yyval.s0rtlst) = s0rtlst_nil() ; }
    break;

  case 127:

/* Line 1806 of yacc.c  */
#line 1784 "ats_grammar.yats"
    { (yyval.s0rtlst) = s0rtlst_cons((yyvsp[(1) - (2)].s0rt), (yyvsp[(2) - (2)].s0rtlst)) ; }
    break;

  case 128:

/* Line 1806 of yacc.c  */
#line 1788 "ats_grammar.yats"
    { (yyval.s0rtlst) = s0rtlst_nil() ; }
    break;

  case 129:

/* Line 1806 of yacc.c  */
#line 1789 "ats_grammar.yats"
    { (yyval.s0rtlst) = s0rtlst_cons((yyvsp[(2) - (3)].s0rt), (yyvsp[(3) - (3)].s0rtlst)) ; }
    break;

  case 130:

/* Line 1806 of yacc.c  */
#line 1793 "ats_grammar.yats"
    { (yyval.s0rtpol) = s0rtpol_make((yyvsp[(1) - (1)].s0rt), 0) ; }
    break;

  case 131:

/* Line 1806 of yacc.c  */
#line 1794 "ats_grammar.yats"
    { (yyval.s0rtpol) = s0rtpol_make(s0rt_prop((yyvsp[(1) - (1)].t0kn)), -1) ; }
    break;

  case 132:

/* Line 1806 of yacc.c  */
#line 1795 "ats_grammar.yats"
    { (yyval.s0rtpol) = s0rtpol_make(s0rt_prop((yyvsp[(1) - (1)].t0kn)),  1) ; }
    break;

  case 133:

/* Line 1806 of yacc.c  */
#line 1796 "ats_grammar.yats"
    { (yyval.s0rtpol) = s0rtpol_make(s0rt_type((yyvsp[(1) - (1)].t0kn)), -1) ; }
    break;

  case 134:

/* Line 1806 of yacc.c  */
#line 1797 "ats_grammar.yats"
    { (yyval.s0rtpol) = s0rtpol_make(s0rt_type((yyvsp[(1) - (1)].t0kn)),  1) ; }
    break;

  case 135:

/* Line 1806 of yacc.c  */
#line 1798 "ats_grammar.yats"
    { (yyval.s0rtpol) = s0rtpol_make(s0rt_t0ype((yyvsp[(1) - (1)].t0kn)), -1) ; }
    break;

  case 136:

/* Line 1806 of yacc.c  */
#line 1799 "ats_grammar.yats"
    { (yyval.s0rtpol) = s0rtpol_make(s0rt_t0ype((yyvsp[(1) - (1)].t0kn)),  1) ; }
    break;

  case 137:

/* Line 1806 of yacc.c  */
#line 1800 "ats_grammar.yats"
    { (yyval.s0rtpol) = s0rtpol_make(s0rt_view((yyvsp[(1) - (1)].t0kn)), -1) ; }
    break;

  case 138:

/* Line 1806 of yacc.c  */
#line 1801 "ats_grammar.yats"
    { (yyval.s0rtpol) = s0rtpol_make(s0rt_view((yyvsp[(1) - (1)].t0kn)),  1) ; }
    break;

  case 139:

/* Line 1806 of yacc.c  */
#line 1802 "ats_grammar.yats"
    { (yyval.s0rtpol) = s0rtpol_make(s0rt_viewtype((yyvsp[(1) - (1)].t0kn)), -1) ; }
    break;

  case 140:

/* Line 1806 of yacc.c  */
#line 1803 "ats_grammar.yats"
    { (yyval.s0rtpol) = s0rtpol_make(s0rt_viewtype((yyvsp[(1) - (1)].t0kn)),  1) ; }
    break;

  case 141:

/* Line 1806 of yacc.c  */
#line 1804 "ats_grammar.yats"
    { (yyval.s0rtpol) = s0rtpol_make(s0rt_viewt0ype((yyvsp[(1) - (1)].t0kn)), -1) ; }
    break;

  case 142:

/* Line 1806 of yacc.c  */
#line 1805 "ats_grammar.yats"
    { (yyval.s0rtpol) = s0rtpol_make(s0rt_viewt0ype((yyvsp[(1) - (1)].t0kn)),  1) ; }
    break;

  case 143:

/* Line 1806 of yacc.c  */
#line 1809 "ats_grammar.yats"
    { (yyval.d0atsrtcon) = d0atsrtcon_make_none((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 144:

/* Line 1806 of yacc.c  */
#line 1810 "ats_grammar.yats"
    { (yyval.d0atsrtcon) = d0atsrtcon_make_some((yyvsp[(1) - (3)].i0de), (yyvsp[(3) - (3)].s0rt)) ; }
    break;

  case 145:

/* Line 1806 of yacc.c  */
#line 1814 "ats_grammar.yats"
    { (yyval.d0atsrtconlst) = (yyvsp[(1) - (1)].d0atsrtconlst) ; }
    break;

  case 146:

/* Line 1806 of yacc.c  */
#line 1815 "ats_grammar.yats"
    { (yyval.d0atsrtconlst) = d0atsrtconlst_cons((yyvsp[(1) - (2)].d0atsrtcon), (yyvsp[(2) - (2)].d0atsrtconlst)) ; }
    break;

  case 147:

/* Line 1806 of yacc.c  */
#line 1819 "ats_grammar.yats"
    { (yyval.d0atsrtconlst) = d0atsrtconlst_nil() ; }
    break;

  case 148:

/* Line 1806 of yacc.c  */
#line 1820 "ats_grammar.yats"
    { (yyval.d0atsrtconlst) = d0atsrtconlst_cons((yyvsp[(2) - (3)].d0atsrtcon), (yyvsp[(3) - (3)].d0atsrtconlst)) ; }
    break;

  case 149:

/* Line 1806 of yacc.c  */
#line 1824 "ats_grammar.yats"
    { (yyval.d0atsrtdec) = d0atsrtdec_make((yyvsp[(1) - (3)].i0de), (yyvsp[(3) - (3)].d0atsrtconlst)) ; }
    break;

  case 150:

/* Line 1806 of yacc.c  */
#line 1828 "ats_grammar.yats"
    { (yyval.d0atsrtdeclst) = d0atsrtdeclst_nil() ; }
    break;

  case 151:

/* Line 1806 of yacc.c  */
#line 1829 "ats_grammar.yats"
    { (yyval.d0atsrtdeclst) = d0atsrtdeclst_cons((yyvsp[(2) - (3)].d0atsrtdec), (yyvsp[(3) - (3)].d0atsrtdeclst)) ; }
    break;

  case 152:

/* Line 1806 of yacc.c  */
#line 1833 "ats_grammar.yats"
    { (yyval.s0taq) = s0taq_symdot((yyvsp[(1) - (2)].i0de)) ; }
    break;

  case 153:

/* Line 1806 of yacc.c  */
#line 1834 "ats_grammar.yats"
    { (yyval.s0taq) = s0taq_symcolon((yyvsp[(1) - (2)].i0de)) ; }
    break;

  case 154:

/* Line 1806 of yacc.c  */
#line 1835 "ats_grammar.yats"
    { (yyval.s0taq) = s0taq_fildot((yyvsp[(2) - (3)].s0tring)) ; }
    break;

  case 155:

/* Line 1806 of yacc.c  */
#line 1839 "ats_grammar.yats"
    { (yyval.d0ynq) = d0ynq_symdot((yyvsp[(1) - (2)].i0de)) ; }
    break;

  case 156:

/* Line 1806 of yacc.c  */
#line 1840 "ats_grammar.yats"
    { (yyval.d0ynq) = d0ynq_symcolon((yyvsp[(1) - (2)].i0de)) ; }
    break;

  case 157:

/* Line 1806 of yacc.c  */
#line 1841 "ats_grammar.yats"
    { (yyval.d0ynq) = d0ynq_symdot_symcolon ((yyvsp[(1) - (3)].i0de), (yyvsp[(2) - (3)].i0de)) ; }
    break;

  case 158:

/* Line 1806 of yacc.c  */
#line 1842 "ats_grammar.yats"
    { (yyval.d0ynq) = d0ynq_fildot((yyvsp[(2) - (3)].s0tring)) ; }
    break;

  case 159:

/* Line 1806 of yacc.c  */
#line 1843 "ats_grammar.yats"
    { (yyval.d0ynq) = d0ynq_fildot_symcolon((yyvsp[(2) - (4)].s0tring), (yyvsp[(3) - (4)].i0de)) ; }
    break;

  case 160:

/* Line 1806 of yacc.c  */
#line 1847 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 161:

/* Line 1806 of yacc.c  */
#line 1848 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 162:

/* Line 1806 of yacc.c  */
#line 1849 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_r0ead((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 163:

/* Line 1806 of yacc.c  */
#line 1850 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_ampersand((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 164:

/* Line 1806 of yacc.c  */
#line 1851 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_backslash((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 165:

/* Line 1806 of yacc.c  */
#line 1852 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_bang((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 166:

/* Line 1806 of yacc.c  */
#line 1853 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_gt((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 167:

/* Line 1806 of yacc.c  */
#line 1854 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_lt((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 168:

/* Line 1806 of yacc.c  */
#line 1855 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_minusgt((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 169:

/* Line 1806 of yacc.c  */
#line 1856 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_tilde((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 170:

/* Line 1806 of yacc.c  */
#line 1860 "ats_grammar.yats"
    { (yyval.sqi0de) = sqi0de_make_none((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 171:

/* Line 1806 of yacc.c  */
#line 1861 "ats_grammar.yats"
    { (yyval.sqi0de) = sqi0de_make_some((yyvsp[(1) - (2)].s0taq), (yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 172:

/* Line 1806 of yacc.c  */
#line 1865 "ats_grammar.yats"
    { (yyval.i0delst) = i0delst_nil() ; }
    break;

  case 173:

/* Line 1806 of yacc.c  */
#line 1866 "ats_grammar.yats"
    { (yyval.i0delst) = i0delst_cons((yyvsp[(2) - (3)].i0de), (yyvsp[(3) - (3)].i0delst)) ; }
    break;

  case 174:

/* Line 1806 of yacc.c  */
#line 1870 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 175:

/* Line 1806 of yacc.c  */
#line 1871 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 176:

/* Line 1806 of yacc.c  */
#line 1872 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_backslash((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 177:

/* Line 1806 of yacc.c  */
#line 1873 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_bang((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 178:

/* Line 1806 of yacc.c  */
#line 1874 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_eq((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 179:

/* Line 1806 of yacc.c  */
#line 1875 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_gt((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 180:

/* Line 1806 of yacc.c  */
#line 1876 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_gtlt((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 181:

/* Line 1806 of yacc.c  */
#line 1877 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_lt((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 182:

/* Line 1806 of yacc.c  */
#line 1878 "ats_grammar.yats"
    { (yyval.i0de) = i0de_make_tilde((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 183:

/* Line 1806 of yacc.c  */
#line 1882 "ats_grammar.yats"
    { (yyval.dqi0de) = dqi0de_make_none((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 184:

/* Line 1806 of yacc.c  */
#line 1883 "ats_grammar.yats"
    { (yyval.dqi0de) = dqi0de_make_some((yyvsp[(1) - (2)].d0ynq), (yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 185:

/* Line 1806 of yacc.c  */
#line 1887 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 186:

/* Line 1806 of yacc.c  */
#line 1888 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 187:

/* Line 1806 of yacc.c  */
#line 1892 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 188:

/* Line 1806 of yacc.c  */
#line 1893 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(2) - (2)].i0de) ; }
    break;

  case 189:

/* Line 1806 of yacc.c  */
#line 1897 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 190:

/* Line 1806 of yacc.c  */
#line 1901 "ats_grammar.yats"
    { (yyval.arrqi0de) = arrqi0de_make_none((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 191:

/* Line 1806 of yacc.c  */
#line 1902 "ats_grammar.yats"
    { (yyval.arrqi0de) = arrqi0de_make_some((yyvsp[(1) - (2)].d0ynq), (yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 192:

/* Line 1806 of yacc.c  */
#line 1906 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 193:

/* Line 1806 of yacc.c  */
#line 1910 "ats_grammar.yats"
    { (yyval.tmpqi0de) = tmpqi0de_make_none((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 194:

/* Line 1806 of yacc.c  */
#line 1911 "ats_grammar.yats"
    { (yyval.tmpqi0de) = tmpqi0de_make_some((yyvsp[(1) - (2)].d0ynq), (yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 195:

/* Line 1806 of yacc.c  */
#line 1915 "ats_grammar.yats"
    { (yyval.s0rtopt) = s0rtopt_none() ; }
    break;

  case 196:

/* Line 1806 of yacc.c  */
#line 1916 "ats_grammar.yats"
    { (yyval.s0rtopt) = s0rtopt_some((yyvsp[(2) - (2)].s0rt)) ; }
    break;

  case 197:

/* Line 1806 of yacc.c  */
#line 1920 "ats_grammar.yats"
    { (yyval.s0arg) = s0arg_make((yyvsp[(1) - (2)].i0de), (yyvsp[(2) - (2)].s0rtopt)) ; }
    break;

  case 198:

/* Line 1806 of yacc.c  */
#line 1924 "ats_grammar.yats"
    { (yyval.s0arglst) = s0arglst_nil() ; }
    break;

  case 199:

/* Line 1806 of yacc.c  */
#line 1925 "ats_grammar.yats"
    { (yyval.s0arglst) = s0arglst_cons((yyvsp[(1) - (2)].s0arg), (yyvsp[(2) - (2)].s0arglst)) ; }
    break;

  case 200:

/* Line 1806 of yacc.c  */
#line 1929 "ats_grammar.yats"
    { (yyval.s0arglst) = s0arglst_nil() ; }
    break;

  case 201:

/* Line 1806 of yacc.c  */
#line 1930 "ats_grammar.yats"
    { (yyval.s0arglst) = s0arglst_cons((yyvsp[(2) - (3)].s0arg), (yyvsp[(3) - (3)].s0arglst)) ; }
    break;

  case 202:

/* Line 1806 of yacc.c  */
#line 1934 "ats_grammar.yats"
    { (yyval.s0arglstlst) = s0arglstlst_nil() ; }
    break;

  case 203:

/* Line 1806 of yacc.c  */
#line 1935 "ats_grammar.yats"
    { (yyval.s0arglstlst) = s0arglstlst_cons_ide((yyvsp[(1) - (2)].i0de), (yyvsp[(2) - (2)].s0arglstlst)) ; }
    break;

  case 204:

/* Line 1806 of yacc.c  */
#line 1936 "ats_grammar.yats"
    { (yyval.s0arglstlst) = s0arglstlst_cons((yyvsp[(2) - (4)].s0arglst), (yyvsp[(4) - (4)].s0arglstlst)); }
    break;

  case 205:

/* Line 1806 of yacc.c  */
#line 1940 "ats_grammar.yats"
    { (yyval.s0arglst) = s0arglst_nil() ; }
    break;

  case 206:

/* Line 1806 of yacc.c  */
#line 1941 "ats_grammar.yats"
    { (yyval.s0arglst) = s0arglst_cons((yyvsp[(1) - (2)].s0arg), (yyvsp[(2) - (2)].s0arglst)) ; }
    break;

  case 207:

/* Line 1806 of yacc.c  */
#line 1945 "ats_grammar.yats"
    { (yyval.s0arglst) = s0arglst_nil() ; }
    break;

  case 208:

/* Line 1806 of yacc.c  */
#line 1946 "ats_grammar.yats"
    { (yyval.s0arglst) = s0arglst_cons((yyvsp[(2) - (3)].s0arg), (yyvsp[(3) - (3)].s0arglst)) ; }
    break;

  case 209:

/* Line 1806 of yacc.c  */
#line 1950 "ats_grammar.yats"
    { (yyval.s0arglstlst) = s0arglstlst_nil() ; }
    break;

  case 210:

/* Line 1806 of yacc.c  */
#line 1951 "ats_grammar.yats"
    { (yyval.s0arglstlst) = s0arglstlst_cons((yyvsp[(2) - (4)].s0arglst), (yyvsp[(4) - (4)].s0arglstlst)) ; }
    break;

  case 211:

/* Line 1806 of yacc.c  */
#line 1955 "ats_grammar.yats"
    { (yyval.sp0at) = sp0at_con((yyvsp[(1) - (4)].sqi0de), (yyvsp[(3) - (4)].s0arglst), (yyvsp[(4) - (4)].t0kn)) ; }
    break;

  case 212:

/* Line 1806 of yacc.c  */
#line 1959 "ats_grammar.yats"
    { (yyval.s0exp) = (yyvsp[(1) - (1)].s0exp) ; }
    break;

  case 213:

/* Line 1806 of yacc.c  */
#line 1960 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_extern((yyvsp[(1) - (1)].s0expext)) ; }
    break;

  case 214:

/* Line 1806 of yacc.c  */
#line 1961 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_ann((yyvsp[(1) - (3)].s0exp), (yyvsp[(3) - (3)].s0rt)) ; }
    break;

  case 215:

/* Line 1806 of yacc.c  */
#line 1962 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_lams((yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].s0arglstlst), (yyvsp[(3) - (5)].s0rtopt), (yyvsp[(5) - (5)].s0exp)) ; }
    break;

  case 216:

/* Line 1806 of yacc.c  */
#line 1966 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_char((yyvsp[(1) - (1)].c0har)) ; }
    break;

  case 217:

/* Line 1806 of yacc.c  */
#line 1967 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_int((yyvsp[(1) - (1)].i0nt)) ; }
    break;

  case 218:

/* Line 1806 of yacc.c  */
#line 1968 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_intsp_err((yyvsp[(1) - (1)].i0ntsp)) ; }
    break;

  case 219:

/* Line 1806 of yacc.c  */
#line 1969 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_ide((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 220:

/* Line 1806 of yacc.c  */
#line 1970 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_opide((yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 221:

/* Line 1806 of yacc.c  */
#line 1971 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_qid((yyvsp[(1) - (2)].s0taq), (yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 222:

/* Line 1806 of yacc.c  */
#line 1972 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_list((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0explst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 223:

/* Line 1806 of yacc.c  */
#line 1973 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_list2((yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].s0explst), (yyvsp[(4) - (5)].s0explst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 224:

/* Line 1806 of yacc.c  */
#line 1974 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_tytup(0, (yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0explst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 225:

/* Line 1806 of yacc.c  */
#line 1975 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_tytup(1, (yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0explst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 226:

/* Line 1806 of yacc.c  */
#line 1976 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_tytup(2, (yyvsp[(1) - (4)].t0kn), (yyvsp[(3) - (4)].s0explst), (yyvsp[(4) - (4)].t0kn)) ; }
    break;

  case 227:

/* Line 1806 of yacc.c  */
#line 1977 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_tytup(3, (yyvsp[(1) - (4)].t0kn), (yyvsp[(3) - (4)].s0explst), (yyvsp[(4) - (4)].t0kn)) ; }
    break;

  case 228:

/* Line 1806 of yacc.c  */
#line 1978 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_tytup2(0, (yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].s0explst), (yyvsp[(4) - (5)].s0explst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 229:

/* Line 1806 of yacc.c  */
#line 1979 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_tytup2(1, (yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].s0explst), (yyvsp[(4) - (5)].s0explst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 230:

/* Line 1806 of yacc.c  */
#line 1980 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_tytup2(2, (yyvsp[(1) - (6)].t0kn), (yyvsp[(3) - (6)].s0explst), (yyvsp[(5) - (6)].s0explst), (yyvsp[(6) - (6)].t0kn)) ; }
    break;

  case 231:

/* Line 1806 of yacc.c  */
#line 1981 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_tytup2(3, (yyvsp[(1) - (6)].t0kn), (yyvsp[(3) - (6)].s0explst), (yyvsp[(5) - (6)].s0explst), (yyvsp[(6) - (6)].t0kn)) ; }
    break;

  case 232:

/* Line 1806 of yacc.c  */
#line 1982 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_tyrec(0, (yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].labs0explst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 233:

/* Line 1806 of yacc.c  */
#line 1983 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_tyrec(1, (yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].labs0explst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 234:

/* Line 1806 of yacc.c  */
#line 1984 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_tyrec(2, (yyvsp[(1) - (4)].t0kn), (yyvsp[(3) - (4)].labs0explst), (yyvsp[(4) - (4)].t0kn)) ; }
    break;

  case 235:

/* Line 1806 of yacc.c  */
#line 1985 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_tyrec(3, (yyvsp[(1) - (4)].t0kn), (yyvsp[(3) - (4)].labs0explst), (yyvsp[(4) - (4)].t0kn)) ; }
    break;

  case 236:

/* Line 1806 of yacc.c  */
#line 1986 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_tyrec_ext((yyvsp[(1) - (6)].t0kn), (yyvsp[(2) - (6)].s0tring), (yyvsp[(5) - (6)].labs0explst), (yyvsp[(6) - (6)].t0kn)) ; }
    break;

  case 237:

/* Line 1806 of yacc.c  */
#line 1987 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_tyarr((yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].s0exp), (yyvsp[(5) - (5)].s0arrind)) ; }
    break;

  case 238:

/* Line 1806 of yacc.c  */
#line 1988 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_imp((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].e0fftaglst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 239:

/* Line 1806 of yacc.c  */
#line 1989 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_imp_emp((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 240:

/* Line 1806 of yacc.c  */
#line 1990 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_uni((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0qualst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 241:

/* Line 1806 of yacc.c  */
#line 1991 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_exi((yyvsp[(1) - (3)].t0kn), 0/*funres*/, (yyvsp[(2) - (3)].s0qualst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 242:

/* Line 1806 of yacc.c  */
#line 1992 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_exi((yyvsp[(1) - (3)].t0kn), 1/*funres*/, (yyvsp[(2) - (3)].s0qualst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 243:

/* Line 1806 of yacc.c  */
#line 1996 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_app((yyvsp[(1) - (2)].s0exp), (yyvsp[(2) - (2)].s0exp)) ; }
    break;

  case 244:

/* Line 1806 of yacc.c  */
#line 1997 "ats_grammar.yats"
    { (yyval.s0exp) = (yyvsp[(1) - (1)].s0exp) ; }
    break;

  case 245:

/* Line 1806 of yacc.c  */
#line 2001 "ats_grammar.yats"
    { (yyval.s0expext) = s0expext_nam((yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].s0tring)) ; }
    break;

  case 246:

/* Line 1806 of yacc.c  */
#line 2002 "ats_grammar.yats"
    { (yyval.s0expext) = s0expext_app((yyvsp[(1) - (2)].s0expext), (yyvsp[(2) - (2)].s0exp)) ; }
    break;

  case 247:

/* Line 1806 of yacc.c  */
#line 2006 "ats_grammar.yats"
    { (yyval.s0expopt) = s0expopt_none () ; }
    break;

  case 248:

/* Line 1806 of yacc.c  */
#line 2007 "ats_grammar.yats"
    { (yyval.s0expopt) = s0expopt_some ((yyvsp[(2) - (3)].s0exp)) ; }
    break;

  case 249:

/* Line 1806 of yacc.c  */
#line 2008 "ats_grammar.yats"
    { (yyval.s0expopt) = s0expopt_some ((yyvsp[(2) - (3)].s0exp)) ; }
    break;

  case 250:

/* Line 1806 of yacc.c  */
#line 2012 "ats_grammar.yats"
    { (yyval.s0arrind) = s0arrind_make_sing((yyvsp[(1) - (2)].s0explst), (yyvsp[(2) - (2)].t0kn)) ; }
    break;

  case 251:

/* Line 1806 of yacc.c  */
#line 2013 "ats_grammar.yats"
    { (yyval.s0arrind) = s0arrind_make_cons((yyvsp[(1) - (4)].s0explst), (yyvsp[(4) - (4)].s0arrind)) ; }
    break;

  case 252:

/* Line 1806 of yacc.c  */
#line 2017 "ats_grammar.yats"
    { (yyval.s0qua) = s0qua_prop((yyvsp[(1) - (1)].s0exp)) ; }
    break;

  case 253:

/* Line 1806 of yacc.c  */
#line 2018 "ats_grammar.yats"
    { (yyval.s0qua) = s0qua_vars((yyvsp[(1) - (4)].i0de), (yyvsp[(2) - (4)].i0delst), (yyvsp[(4) - (4)].s0rtext)) ; }
    break;

  case 254:

/* Line 1806 of yacc.c  */
#line 2022 "ats_grammar.yats"
    { (yyval.s0qualst) = s0qualst_nil() ; }
    break;

  case 255:

/* Line 1806 of yacc.c  */
#line 2023 "ats_grammar.yats"
    { (yyval.s0qualst) = s0qualst_cons((yyvsp[(1) - (2)].s0qua), (yyvsp[(2) - (2)].s0qualst)) ; }
    break;

  case 256:

/* Line 1806 of yacc.c  */
#line 2027 "ats_grammar.yats"
    { (yyval.s0qualst) = s0qualst_nil() ; }
    break;

  case 257:

/* Line 1806 of yacc.c  */
#line 2028 "ats_grammar.yats"
    { (yyval.s0qualst) = s0qualst_cons((yyvsp[(2) - (3)].s0qua), (yyvsp[(3) - (3)].s0qualst)) ; }
    break;

  case 258:

/* Line 1806 of yacc.c  */
#line 2029 "ats_grammar.yats"
    { (yyval.s0qualst) = s0qualst_cons((yyvsp[(2) - (3)].s0qua), (yyvsp[(3) - (3)].s0qualst)) ; }
    break;

  case 259:

/* Line 1806 of yacc.c  */
#line 2033 "ats_grammar.yats"
    { (yyval.s0rtext) = s0rtext_srt((yyvsp[(1) - (1)].s0rt)) ; }
    break;

  case 260:

/* Line 1806 of yacc.c  */
#line 2034 "ats_grammar.yats"
    { (yyval.s0rtext) = s0rtext_sub((yyvsp[(1) - (8)].t0kn), (yyvsp[(2) - (8)].i0de), (yyvsp[(4) - (8)].s0rtext), (yyvsp[(6) - (8)].s0exp), (yyvsp[(7) - (8)].s0explst), (yyvsp[(8) - (8)].t0kn)) ; }
    break;

  case 261:

/* Line 1806 of yacc.c  */
#line 2038 "ats_grammar.yats"
    { (yyval.s0explst) = s0explst_nil() ; }
    break;

  case 262:

/* Line 1806 of yacc.c  */
#line 2039 "ats_grammar.yats"
    { (yyval.s0explst) = (yyvsp[(1) - (1)].s0explst) ; }
    break;

  case 263:

/* Line 1806 of yacc.c  */
#line 2043 "ats_grammar.yats"
    { (yyval.s0explst) = s0explst_nil() ; }
    break;

  case 264:

/* Line 1806 of yacc.c  */
#line 2044 "ats_grammar.yats"
    { (yyval.s0explst) = s0explst_cons((yyvsp[(2) - (3)].s0exp), (yyvsp[(3) - (3)].s0explst)) ; }
    break;

  case 265:

/* Line 1806 of yacc.c  */
#line 2045 "ats_grammar.yats"
    { (yyval.s0explst) = s0explst_cons((yyvsp[(2) - (3)].s0exp), (yyvsp[(3) - (3)].s0explst)) ; }
    break;

  case 266:

/* Line 1806 of yacc.c  */
#line 2049 "ats_grammar.yats"
    { (yyval.s0explst) = s0explst_nil() ; }
    break;

  case 267:

/* Line 1806 of yacc.c  */
#line 2050 "ats_grammar.yats"
    { (yyval.s0explst) = s0explst_cons((yyvsp[(2) - (3)].s0exp), (yyvsp[(3) - (3)].s0explst)) ; }
    break;

  case 268:

/* Line 1806 of yacc.c  */
#line 2054 "ats_grammar.yats"
    { (yyval.s0explst) = s0explst_cons((yyvsp[(1) - (2)].s0exp), (yyvsp[(2) - (2)].s0explst)) ; }
    break;

  case 269:

/* Line 1806 of yacc.c  */
#line 2058 "ats_grammar.yats"
    { (yyval.labs0explst) = labs0explst_nil() ; }
    break;

  case 270:

/* Line 1806 of yacc.c  */
#line 2059 "ats_grammar.yats"
    { (yyval.labs0explst) = labs0explst_cons((yyvsp[(1) - (4)].l0ab), (yyvsp[(3) - (4)].s0exp), (yyvsp[(4) - (4)].labs0explst)) ; }
    break;

  case 271:

/* Line 1806 of yacc.c  */
#line 2063 "ats_grammar.yats"
    { (yyval.labs0explst) = labs0explst_nil() ; }
    break;

  case 272:

/* Line 1806 of yacc.c  */
#line 2064 "ats_grammar.yats"
    { (yyval.labs0explst) = labs0explst_cons((yyvsp[(2) - (5)].l0ab), (yyvsp[(4) - (5)].s0exp), (yyvsp[(5) - (5)].labs0explst)) ; }
    break;

  case 273:

/* Line 1806 of yacc.c  */
#line 2068 "ats_grammar.yats"
    { (yyval.s0exp) = (yyvsp[(1) - (1)].s0exp) ; }
    break;

  case 274:

/* Line 1806 of yacc.c  */
#line 2069 "ats_grammar.yats"
    { (yyval.s0exp) = s0exp_app((yyvsp[(1) - (2)].s0exp), (yyvsp[(2) - (2)].s0exp)) ; }
    break;

  case 275:

/* Line 1806 of yacc.c  */
#line 2073 "ats_grammar.yats"
    { (yyval.s0exp) = (yyvsp[(1) - (1)].s0exp) ; }
    break;

  case 276:

/* Line 1806 of yacc.c  */
#line 2077 "ats_grammar.yats"
    { (yyval.s0explst) = s0explst_nil() ; }
    break;

  case 277:

/* Line 1806 of yacc.c  */
#line 2078 "ats_grammar.yats"
    { (yyval.s0explst) = s0explst_cons((yyvsp[(1) - (2)].s0exp), (yyvsp[(2) - (2)].s0explst)) ; }
    break;

  case 278:

/* Line 1806 of yacc.c  */
#line 2082 "ats_grammar.yats"
    { (yyval.s0explst) = s0explst_nil() ; }
    break;

  case 279:

/* Line 1806 of yacc.c  */
#line 2083 "ats_grammar.yats"
    { (yyval.s0explst) = s0explst_cons((yyvsp[(2) - (3)].s0exp), (yyvsp[(3) - (3)].s0explst)) ; }
    break;

  case 280:

/* Line 1806 of yacc.c  */
#line 2087 "ats_grammar.yats"
    { (yyval.t1mps0explstlst) = gtlt_t1mps0expseqseq_nil() ; }
    break;

  case 281:

/* Line 1806 of yacc.c  */
#line 2088 "ats_grammar.yats"
    { (yyval.t1mps0explstlst) = gtlt_t1mps0expseqseq_cons_tok((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0explst), (yyvsp[(3) - (3)].t1mps0explstlst)) ; }
    break;

  case 282:

/* Line 1806 of yacc.c  */
#line 2092 "ats_grammar.yats"
    { (yyval.impqi0de) = impqi0de_make_none((yyvsp[(1) - (1)].dqi0de)) ; }
    break;

  case 283:

/* Line 1806 of yacc.c  */
#line 2093 "ats_grammar.yats"
    { (yyval.impqi0de) = impqi0de_make_some((yyvsp[(1) - (4)].tmpqi0de), (yyvsp[(2) - (4)].s0explst), (yyvsp[(3) - (4)].t1mps0explstlst), (yyvsp[(4) - (4)].t0kn)) ; }
    break;

  case 284:

/* Line 1806 of yacc.c  */
#line 2097 "ats_grammar.yats"
    { (yyval.s0rtdef) = s0rtdef_make((yyvsp[(1) - (3)].i0de), (yyvsp[(3) - (3)].s0rtext)) ; }
    break;

  case 285:

/* Line 1806 of yacc.c  */
#line 2101 "ats_grammar.yats"
    { (yyval.s0rtdeflst) = s0rtdeflst_nil() ; }
    break;

  case 286:

/* Line 1806 of yacc.c  */
#line 2102 "ats_grammar.yats"
    { (yyval.s0rtdeflst) = s0rtdeflst_cons((yyvsp[(2) - (3)].s0rtdef), (yyvsp[(3) - (3)].s0rtdeflst)) ; }
    break;

  case 287:

/* Line 1806 of yacc.c  */
#line 2106 "ats_grammar.yats"
    { (yyval.d0atarg) = d0atarg_srt((yyvsp[(1) - (1)].s0rtpol)) ; }
    break;

  case 288:

/* Line 1806 of yacc.c  */
#line 2107 "ats_grammar.yats"
    { (yyval.d0atarg) = d0atarg_id_srt((yyvsp[(1) - (3)].i0de), (yyvsp[(3) - (3)].s0rtpol)) ; }
    break;

  case 289:

/* Line 1806 of yacc.c  */
#line 2111 "ats_grammar.yats"
    { (yyval.d0atarglst) = d0atarglst_nil() ; }
    break;

  case 290:

/* Line 1806 of yacc.c  */
#line 2112 "ats_grammar.yats"
    { (yyval.d0atarglst) = d0atarglst_cons((yyvsp[(1) - (2)].d0atarg), (yyvsp[(2) - (2)].d0atarglst)) ; }
    break;

  case 291:

/* Line 1806 of yacc.c  */
#line 2116 "ats_grammar.yats"
    { (yyval.d0atarglst) = d0atarglst_nil() ; }
    break;

  case 292:

/* Line 1806 of yacc.c  */
#line 2117 "ats_grammar.yats"
    { (yyval.d0atarglst) = d0atarglst_cons((yyvsp[(2) - (3)].d0atarg), (yyvsp[(3) - (3)].d0atarglst)) ; }
    break;

  case 293:

/* Line 1806 of yacc.c  */
#line 2121 "ats_grammar.yats"
    { (yyval.s0tacon) = s0tacon_make_none_none((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 294:

/* Line 1806 of yacc.c  */
#line 2122 "ats_grammar.yats"
    { (yyval.s0tacon) = s0tacon_make_some_none((yyvsp[(1) - (4)].i0de), (yyvsp[(3) - (4)].d0atarglst), (yyvsp[(4) - (4)].t0kn)) ; }
    break;

  case 295:

/* Line 1806 of yacc.c  */
#line 2123 "ats_grammar.yats"
    { (yyval.s0tacon) = s0tacon_make_none_some((yyvsp[(1) - (3)].i0de), (yyvsp[(3) - (3)].s0exp)) ; }
    break;

  case 296:

/* Line 1806 of yacc.c  */
#line 2124 "ats_grammar.yats"
    { (yyval.s0tacon) = s0tacon_make_some_some((yyvsp[(1) - (6)].i0de), (yyvsp[(3) - (6)].d0atarglst), (yyvsp[(6) - (6)].s0exp)) ; }
    break;

  case 297:

/* Line 1806 of yacc.c  */
#line 2128 "ats_grammar.yats"
    { (yyval.s0taconlst) = s0taconlst_nil() ; }
    break;

  case 298:

/* Line 1806 of yacc.c  */
#line 2129 "ats_grammar.yats"
    { (yyval.s0taconlst) = s0taconlst_cons((yyvsp[(2) - (3)].s0tacon), (yyvsp[(3) - (3)].s0taconlst)) ; }
    break;

  case 299:

/* Line 1806 of yacc.c  */
#line 2133 "ats_grammar.yats"
    { (yyval.s0tacst) = s0tacst_make_none((yyvsp[(1) - (3)].i0de), (yyvsp[(3) - (3)].s0rt)) ; }
    break;

  case 300:

/* Line 1806 of yacc.c  */
#line 2134 "ats_grammar.yats"
    { (yyval.s0tacst) = s0tacst_make_some((yyvsp[(1) - (6)].i0de), (yyvsp[(3) - (6)].d0atarglst), (yyvsp[(6) - (6)].s0rt)) ; }
    break;

  case 301:

/* Line 1806 of yacc.c  */
#line 2138 "ats_grammar.yats"
    { (yyval.s0tacstlst) = s0tacstlst_nil() ; }
    break;

  case 302:

/* Line 1806 of yacc.c  */
#line 2139 "ats_grammar.yats"
    { (yyval.s0tacstlst) = s0tacstlst_cons((yyvsp[(2) - (3)].s0tacst), (yyvsp[(3) - (3)].s0tacstlst)) ; }
    break;

  case 303:

/* Line 1806 of yacc.c  */
#line 2143 "ats_grammar.yats"
    { (yyval.s0tavar) = s0tavar_make((yyvsp[(1) - (3)].i0de), (yyvsp[(3) - (3)].s0rt)) ; }
    break;

  case 304:

/* Line 1806 of yacc.c  */
#line 2147 "ats_grammar.yats"
    { (yyval.s0tavarlst) = s0tavarlst_nil() ; }
    break;

  case 305:

/* Line 1806 of yacc.c  */
#line 2148 "ats_grammar.yats"
    { (yyval.s0tavarlst) = s0tavarlst_cons((yyvsp[(2) - (3)].s0tavar), (yyvsp[(3) - (3)].s0tavarlst)) ; }
    break;

  case 306:

/* Line 1806 of yacc.c  */
#line 2152 "ats_grammar.yats"
    { (yyval.s0expdef) = s0expdef_make ((yyvsp[(1) - (5)].i0de), (yyvsp[(2) - (5)].s0arglstlst), (yyvsp[(3) - (5)].s0rtopt), (yyvsp[(5) - (5)].s0exp)) ; }
    break;

  case 307:

/* Line 1806 of yacc.c  */
#line 2156 "ats_grammar.yats"
    { (yyval.s0expdeflst) = s0expdeflst_nil() ; }
    break;

  case 308:

/* Line 1806 of yacc.c  */
#line 2157 "ats_grammar.yats"
    { (yyval.s0expdeflst) = s0expdeflst_cons((yyvsp[(2) - (3)].s0expdef), (yyvsp[(3) - (3)].s0expdeflst)) ; }
    break;

  case 309:

/* Line 1806 of yacc.c  */
#line 2161 "ats_grammar.yats"
    { (yyval.s0aspdec) = s0aspdec_make((yyvsp[(1) - (5)].sqi0de), (yyvsp[(2) - (5)].s0arglstlst), (yyvsp[(3) - (5)].s0rtopt), (yyvsp[(5) - (5)].s0exp)) ; }
    break;

  case 310:

/* Line 1806 of yacc.c  */
#line 2165 "ats_grammar.yats"
    { (yyval.s0qualstlst) = s0qualstlst_nil() ; }
    break;

  case 311:

/* Line 1806 of yacc.c  */
#line 2166 "ats_grammar.yats"
    { (yyval.s0qualstlst) = s0qualstlst_cons((yyvsp[(2) - (4)].s0qualst), (yyvsp[(4) - (4)].s0qualstlst)) ; }
    break;

  case 312:

/* Line 1806 of yacc.c  */
#line 2170 "ats_grammar.yats"
    { (yyval.s0expopt) = s0expopt_none() ; }
    break;

  case 313:

/* Line 1806 of yacc.c  */
#line 2171 "ats_grammar.yats"
    { (yyval.s0expopt) = s0expopt_some(s0exp_list((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0explst), (yyvsp[(3) - (3)].t0kn))) ; }
    break;

  case 314:

/* Line 1806 of yacc.c  */
#line 2175 "ats_grammar.yats"
    { (yyval.s0expopt) = s0expopt_none() ; }
    break;

  case 315:

/* Line 1806 of yacc.c  */
#line 2176 "ats_grammar.yats"
    { (yyval.s0expopt) = s0expopt_some((yyvsp[(2) - (2)].s0exp)) ; }
    break;

  case 316:

/* Line 1806 of yacc.c  */
#line 2180 "ats_grammar.yats"
    { (yyval.d0atcon) = d0atcon_make((yyvsp[(1) - (4)].s0qualstlst), (yyvsp[(2) - (4)].i0de), (yyvsp[(3) - (4)].s0expopt), (yyvsp[(4) - (4)].s0expopt)) ; }
    break;

  case 317:

/* Line 1806 of yacc.c  */
#line 2184 "ats_grammar.yats"
    { (yyval.d0atconlst) = (yyvsp[(1) - (1)].d0atconlst) ; }
    break;

  case 318:

/* Line 1806 of yacc.c  */
#line 2185 "ats_grammar.yats"
    { (yyval.d0atconlst) = d0atconlst_cons((yyvsp[(1) - (2)].d0atcon), (yyvsp[(2) - (2)].d0atconlst)) ; }
    break;

  case 319:

/* Line 1806 of yacc.c  */
#line 2189 "ats_grammar.yats"
    { (yyval.d0atconlst) = d0atconlst_nil() ; }
    break;

  case 320:

/* Line 1806 of yacc.c  */
#line 2190 "ats_grammar.yats"
    { (yyval.d0atconlst) = d0atconlst_cons((yyvsp[(2) - (3)].d0atcon), (yyvsp[(3) - (3)].d0atconlst)) ; }
    break;

  case 321:

/* Line 1806 of yacc.c  */
#line 2194 "ats_grammar.yats"
    { (yyval.d0atdec) = d0atdec_make_none((yyvsp[(1) - (3)].i0de), (yyvsp[(3) - (3)].d0atconlst)) ; }
    break;

  case 322:

/* Line 1806 of yacc.c  */
#line 2195 "ats_grammar.yats"
    { (yyval.d0atdec) = d0atdec_make_some((yyvsp[(1) - (6)].i0de), (yyvsp[(3) - (6)].d0atarglst), (yyvsp[(4) - (6)].t0kn), (yyvsp[(6) - (6)].d0atconlst)) ; }
    break;

  case 323:

/* Line 1806 of yacc.c  */
#line 2199 "ats_grammar.yats"
    { (yyval.d0atdeclst) = d0atdeclst_nil() ; }
    break;

  case 324:

/* Line 1806 of yacc.c  */
#line 2200 "ats_grammar.yats"
    { (yyval.d0atdeclst) = d0atdeclst_cons((yyvsp[(2) - (3)].d0atdec), (yyvsp[(3) - (3)].d0atdeclst)) ; }
    break;

  case 325:

/* Line 1806 of yacc.c  */
#line 2204 "ats_grammar.yats"
    { (yyval.s0expdeflst) = s0expdeflst_nil() ; }
    break;

  case 326:

/* Line 1806 of yacc.c  */
#line 2205 "ats_grammar.yats"
    { (yyval.s0expdeflst) = s0expdeflst_cons((yyvsp[(2) - (3)].s0expdef), (yyvsp[(3) - (3)].s0expdeflst)) ; }
    break;

  case 327:

/* Line 1806 of yacc.c  */
#line 2209 "ats_grammar.yats"
    { (yyval.e0xndec) = e0xndec_make((yyvsp[(1) - (3)].s0qualstlst), (yyvsp[(2) - (3)].i0de), (yyvsp[(3) - (3)].s0expopt)) ; }
    break;

  case 328:

/* Line 1806 of yacc.c  */
#line 2213 "ats_grammar.yats"
    { (yyval.e0xndeclst) = e0xndeclst_nil() ; }
    break;

  case 329:

/* Line 1806 of yacc.c  */
#line 2214 "ats_grammar.yats"
    { (yyval.e0xndeclst) = e0xndeclst_cons((yyvsp[(2) - (3)].e0xndec), (yyvsp[(3) - (3)].e0xndeclst)) ; }
    break;

  case 330:

/* Line 1806 of yacc.c  */
#line 2218 "ats_grammar.yats"
    { (yyval.p0arg) = p0arg_make_none((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 331:

/* Line 1806 of yacc.c  */
#line 2219 "ats_grammar.yats"
    { (yyval.p0arg) = p0arg_make_some((yyvsp[(1) - (3)].i0de), (yyvsp[(3) - (3)].s0exp)) ; }
    break;

  case 332:

/* Line 1806 of yacc.c  */
#line 2223 "ats_grammar.yats"
    { (yyval.p0arglst) = p0arglst_nil() ; }
    break;

  case 333:

/* Line 1806 of yacc.c  */
#line 2224 "ats_grammar.yats"
    { (yyval.p0arglst) = p0arglst_cons((yyvsp[(1) - (2)].p0arg), (yyvsp[(2) - (2)].p0arglst)) ; }
    break;

  case 334:

/* Line 1806 of yacc.c  */
#line 2228 "ats_grammar.yats"
    { (yyval.p0arglst) = p0arglst_nil() ; }
    break;

  case 335:

/* Line 1806 of yacc.c  */
#line 2229 "ats_grammar.yats"
    { (yyval.p0arglst) = p0arglst_cons((yyvsp[(2) - (3)].p0arg), (yyvsp[(3) - (3)].p0arglst)) ; }
    break;

  case 336:

/* Line 1806 of yacc.c  */
#line 2233 "ats_grammar.yats"
    { (yyval.d0arg) = d0arg_var((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 337:

/* Line 1806 of yacc.c  */
#line 2234 "ats_grammar.yats"
    { (yyval.d0arg) = d0arg_dyn((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].p0arglst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 338:

/* Line 1806 of yacc.c  */
#line 2235 "ats_grammar.yats"
    { (yyval.d0arg) = d0arg_dyn2((yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].p0arglst), (yyvsp[(4) - (5)].p0arglst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 339:

/* Line 1806 of yacc.c  */
#line 2236 "ats_grammar.yats"
    { (yyval.d0arg) = d0arg_sta((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0qualst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 340:

/* Line 1806 of yacc.c  */
#line 2240 "ats_grammar.yats"
    { (yyval.d0arglst) = d0arglst_nil() ; }
    break;

  case 341:

/* Line 1806 of yacc.c  */
#line 2241 "ats_grammar.yats"
    { (yyval.d0arglst) = d0arglst_cons((yyvsp[(1) - (2)].d0arg), (yyvsp[(2) - (2)].d0arglst)) ; }
    break;

  case 342:

/* Line 1806 of yacc.c  */
#line 2245 "ats_grammar.yats"
    { (yyval.extnamopt) = extnamopt_none() ; }
    break;

  case 343:

/* Line 1806 of yacc.c  */
#line 2246 "ats_grammar.yats"
    { (yyval.extnamopt) = extnamopt_some((yyvsp[(2) - (2)].s0tring)) ; }
    break;

  case 344:

/* Line 1806 of yacc.c  */
#line 2250 "ats_grammar.yats"
    { (yyval.d0cstdec) = d0cstdec_make((yyvsp[(1) - (5)].i0de), (yyvsp[(2) - (5)].d0arglst), (yyvsp[(3) - (5)].e0fftaglstopt), (yyvsp[(4) - (5)].s0exp), (yyvsp[(5) - (5)].extnamopt)) ; }
    break;

  case 345:

/* Line 1806 of yacc.c  */
#line 2254 "ats_grammar.yats"
    { (yyval.d0cstdeclst) = d0cstdeclst_nil() ; }
    break;

  case 346:

/* Line 1806 of yacc.c  */
#line 2255 "ats_grammar.yats"
    { (yyval.d0cstdeclst) = d0cstdeclst_cons((yyvsp[(2) - (3)].d0cstdec), (yyvsp[(3) - (3)].d0cstdeclst)) ; }
    break;

  case 347:

/* Line 1806 of yacc.c  */
#line 2259 "ats_grammar.yats"
    { (yyval.s0vararg) = s0vararg_one() ; }
    break;

  case 348:

/* Line 1806 of yacc.c  */
#line 2260 "ats_grammar.yats"
    { (yyval.s0vararg) = s0vararg_all() ; }
    break;

  case 349:

/* Line 1806 of yacc.c  */
#line 2261 "ats_grammar.yats"
    { (yyval.s0vararg) = s0vararg_seq((yyvsp[(1) - (1)].s0arglst)) ; }
    break;

  case 350:

/* Line 1806 of yacc.c  */
#line 2265 "ats_grammar.yats"
    { (yyval.s0exparg) = s0exparg_one() ; }
    break;

  case 351:

/* Line 1806 of yacc.c  */
#line 2266 "ats_grammar.yats"
    { (yyval.s0exparg) = s0exparg_all() ; }
    break;

  case 352:

/* Line 1806 of yacc.c  */
#line 2267 "ats_grammar.yats"
    { (yyval.s0exparg) = s0exparg_seq((yyvsp[(1) - (1)].s0explst)) ; }
    break;

  case 353:

/* Line 1806 of yacc.c  */
#line 2271 "ats_grammar.yats"
    { (yyval.s0elop) = s0elop_make (0, (yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 354:

/* Line 1806 of yacc.c  */
#line 2272 "ats_grammar.yats"
    { (yyval.s0elop) = s0elop_make (1, (yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 355:

/* Line 1806 of yacc.c  */
#line 2276 "ats_grammar.yats"
    { (yyval.witht0ype) = witht0ype_none() ; }
    break;

  case 356:

/* Line 1806 of yacc.c  */
#line 2277 "ats_grammar.yats"
    { (yyval.witht0ype) = witht0ype_prop((yyvsp[(2) - (2)].s0exp)) ; }
    break;

  case 357:

/* Line 1806 of yacc.c  */
#line 2278 "ats_grammar.yats"
    { (yyval.witht0ype) = witht0ype_type((yyvsp[(2) - (2)].s0exp)) ; }
    break;

  case 358:

/* Line 1806 of yacc.c  */
#line 2279 "ats_grammar.yats"
    { (yyval.witht0ype) = witht0ype_view((yyvsp[(2) - (2)].s0exp)) ; }
    break;

  case 359:

/* Line 1806 of yacc.c  */
#line 2280 "ats_grammar.yats"
    { (yyval.witht0ype) = witht0ype_viewtype((yyvsp[(2) - (2)].s0exp)) ; }
    break;

  case 360:

/* Line 1806 of yacc.c  */
#line 2284 "ats_grammar.yats"
    { (yyval.p0at) = p0at_apps((yyvsp[(1) - (2)].p0at), (yyvsp[(2) - (2)].p0atlst)) ; }
    break;

  case 361:

/* Line 1806 of yacc.c  */
#line 2285 "ats_grammar.yats"
    { (yyval.p0at) = p0at_ann((yyvsp[(1) - (3)].p0at), (yyvsp[(3) - (3)].s0exp)) ; }
    break;

  case 362:

/* Line 1806 of yacc.c  */
#line 2286 "ats_grammar.yats"
    { (yyval.p0at) = p0at_as((yyvsp[(1) - (3)].i0de), (yyvsp[(3) - (3)].p0at)) ; }
    break;

  case 363:

/* Line 1806 of yacc.c  */
#line 2287 "ats_grammar.yats"
    { (yyval.p0at) = p0at_refas((yyvsp[(1) - (4)].t0kn), (yyvsp[(2) - (4)].i0de), (yyvsp[(4) - (4)].p0at)) ; }
    break;

  case 364:

/* Line 1806 of yacc.c  */
#line 2288 "ats_grammar.yats"
    { (yyval.p0at) = p0at_free((yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].p0at)) ; }
    break;

  case 365:

/* Line 1806 of yacc.c  */
#line 2292 "ats_grammar.yats"
    { (yyval.p0at) = p0at_char((yyvsp[(1) - (1)].c0har)) ; }
    break;

  case 366:

/* Line 1806 of yacc.c  */
#line 2293 "ats_grammar.yats"
    { (yyval.p0at) = p0at_int((yyvsp[(1) - (1)].i0nt)) ; }
    break;

  case 367:

/* Line 1806 of yacc.c  */
#line 2294 "ats_grammar.yats"
    { (yyval.p0at) = p0at_float((yyvsp[(1) - (1)].f0loat)) ; }
    break;

  case 368:

/* Line 1806 of yacc.c  */
#line 2295 "ats_grammar.yats"
    { (yyval.p0at) = p0at_string((yyvsp[(1) - (1)].s0tring)) ; }
    break;

  case 369:

/* Line 1806 of yacc.c  */
#line 2296 "ats_grammar.yats"
    { (yyval.p0at) = p0at_ide((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 370:

/* Line 1806 of yacc.c  */
#line 2297 "ats_grammar.yats"
    { (yyval.p0at) = p0at_ref((yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 371:

/* Line 1806 of yacc.c  */
#line 2298 "ats_grammar.yats"
    { (yyval.p0at) = p0at_opide((yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 372:

/* Line 1806 of yacc.c  */
#line 2299 "ats_grammar.yats"
    { (yyval.p0at) = p0at_qid((yyvsp[(1) - (2)].d0ynq), (yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 373:

/* Line 1806 of yacc.c  */
#line 2300 "ats_grammar.yats"
    { (yyval.p0at) = p0at_list((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].p0atlst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 374:

/* Line 1806 of yacc.c  */
#line 2301 "ats_grammar.yats"
    { (yyval.p0at) = p0at_list2((yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].p0atlst), (yyvsp[(4) - (5)].p0atlst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 375:

/* Line 1806 of yacc.c  */
#line 2302 "ats_grammar.yats"
    { (yyval.p0at) = p0at_lst((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].p0atlst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 376:

/* Line 1806 of yacc.c  */
#line 2303 "ats_grammar.yats"
    { (yyval.p0at) = p0at_tup(0, (yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].p0atlst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 377:

/* Line 1806 of yacc.c  */
#line 2304 "ats_grammar.yats"
    { (yyval.p0at) = p0at_tup(1, (yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].p0atlst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 378:

/* Line 1806 of yacc.c  */
#line 2305 "ats_grammar.yats"
    { (yyval.p0at) = p0at_tup2(0, (yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].p0atlst), (yyvsp[(4) - (5)].p0atlst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 379:

/* Line 1806 of yacc.c  */
#line 2306 "ats_grammar.yats"
    { (yyval.p0at) = p0at_tup2(1, (yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].p0atlst), (yyvsp[(4) - (5)].p0atlst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 380:

/* Line 1806 of yacc.c  */
#line 2307 "ats_grammar.yats"
    { (yyval.p0at) = p0at_rec(0, (yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].labp0atlst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 381:

/* Line 1806 of yacc.c  */
#line 2308 "ats_grammar.yats"
    { (yyval.p0at) = p0at_rec(1, (yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].labp0atlst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 382:

/* Line 1806 of yacc.c  */
#line 2309 "ats_grammar.yats"
    { (yyval.p0at) = p0at_exist((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0arglst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 383:

/* Line 1806 of yacc.c  */
#line 2313 "ats_grammar.yats"
    { (yyval.p0at) = (yyvsp[(1) - (1)].p0at) ; }
    break;

  case 384:

/* Line 1806 of yacc.c  */
#line 2314 "ats_grammar.yats"
    { (yyval.p0at) = p0at_svararg((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0vararg), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 385:

/* Line 1806 of yacc.c  */
#line 2318 "ats_grammar.yats"
    { (yyval.p0atlst) = p0atlst_nil() ; }
    break;

  case 386:

/* Line 1806 of yacc.c  */
#line 2319 "ats_grammar.yats"
    { (yyval.p0atlst) = p0atlst_cons((yyvsp[(1) - (2)].p0at), (yyvsp[(2) - (2)].p0atlst)) ; }
    break;

  case 387:

/* Line 1806 of yacc.c  */
#line 2323 "ats_grammar.yats"
    { (yyval.p0atlst) = p0atlst_nil() ; }
    break;

  case 388:

/* Line 1806 of yacc.c  */
#line 2324 "ats_grammar.yats"
    { (yyval.p0atlst) = p0atlst_cons((yyvsp[(1) - (2)].p0at), (yyvsp[(2) - (2)].p0atlst)) ; }
    break;

  case 389:

/* Line 1806 of yacc.c  */
#line 2328 "ats_grammar.yats"
    { (yyval.p0atlst) = p0atlst_nil() ; }
    break;

  case 390:

/* Line 1806 of yacc.c  */
#line 2329 "ats_grammar.yats"
    { (yyval.p0atlst) = p0atlst_cons((yyvsp[(2) - (3)].p0at), (yyvsp[(3) - (3)].p0atlst)) ; }
    break;

  case 391:

/* Line 1806 of yacc.c  */
#line 2333 "ats_grammar.yats"
    { (yyval.labp0atlst) = labp0atlst_dot() ; }
    break;

  case 392:

/* Line 1806 of yacc.c  */
#line 2334 "ats_grammar.yats"
    { (yyval.labp0atlst) = labp0atlst_cons((yyvsp[(1) - (4)].l0ab), (yyvsp[(3) - (4)].p0at), (yyvsp[(4) - (4)].labp0atlst)) ; }
    break;

  case 393:

/* Line 1806 of yacc.c  */
#line 2338 "ats_grammar.yats"
    { (yyval.labp0atlst) = labp0atlst_nil() ; }
    break;

  case 394:

/* Line 1806 of yacc.c  */
#line 2339 "ats_grammar.yats"
    { (yyval.labp0atlst) = labp0atlst_dot() ; }
    break;

  case 395:

/* Line 1806 of yacc.c  */
#line 2340 "ats_grammar.yats"
    { (yyval.labp0atlst) = labp0atlst_cons((yyvsp[(2) - (5)].l0ab), (yyvsp[(4) - (5)].p0at), (yyvsp[(5) - (5)].labp0atlst)) ; }
    break;

  case 396:

/* Line 1806 of yacc.c  */
#line 2344 "ats_grammar.yats"
    { (yyval.f0arg) = f0arg_sta1((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0qualst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 397:

/* Line 1806 of yacc.c  */
#line 2345 "ats_grammar.yats"
    { (yyval.f0arg) = f0arg_dyn((yyvsp[(1) - (1)].p0at)) ; }
    break;

  case 398:

/* Line 1806 of yacc.c  */
#line 2346 "ats_grammar.yats"
    { (yyval.f0arg) = f0arg_met_some((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0explst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 399:

/* Line 1806 of yacc.c  */
#line 2347 "ats_grammar.yats"
    { (yyval.f0arg) = f0arg_met_none((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 400:

/* Line 1806 of yacc.c  */
#line 2351 "ats_grammar.yats"
    { (yyval.f0arglst) = f0arglst_nil() ; }
    break;

  case 401:

/* Line 1806 of yacc.c  */
#line 2352 "ats_grammar.yats"
    { (yyval.f0arglst) = f0arglst_cons((yyvsp[(1) - (2)].f0arg), (yyvsp[(2) - (2)].f0arglst)) ; }
    break;

  case 402:

/* Line 1806 of yacc.c  */
#line 2356 "ats_grammar.yats"
    { (yyval.f0arg) = f0arg_sta2((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0arglst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 403:

/* Line 1806 of yacc.c  */
#line 2357 "ats_grammar.yats"
    { (yyval.f0arg) = f0arg_dyn((yyvsp[(1) - (1)].p0at)) ; }
    break;

  case 404:

/* Line 1806 of yacc.c  */
#line 2361 "ats_grammar.yats"
    { (yyval.f0arglst) = f0arglst_nil() ; }
    break;

  case 405:

/* Line 1806 of yacc.c  */
#line 2362 "ats_grammar.yats"
    { (yyval.f0arglst) = f0arglst_cons((yyvsp[(1) - (2)].f0arg), (yyvsp[(2) - (2)].f0arglst)) ; }
    break;

  case 406:

/* Line 1806 of yacc.c  */
#line 2366 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_apps((yyvsp[(1) - (2)].d0exp), (yyvsp[(2) - (2)].d0explst)) ; }
    break;

  case 407:

/* Line 1806 of yacc.c  */
#line 2367 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_ann((yyvsp[(1) - (3)].d0exp), (yyvsp[(3) - (3)].s0exp)) ; }
    break;

  case 408:

/* Line 1806 of yacc.c  */
#line 2368 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_if_none((yyvsp[(1) - (4)].ifhead), (yyvsp[(2) - (4)].d0exp), (yyvsp[(4) - (4)].d0exp)) ; }
    break;

  case 409:

/* Line 1806 of yacc.c  */
#line 2369 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_if_some((yyvsp[(1) - (6)].ifhead), (yyvsp[(2) - (6)].d0exp), (yyvsp[(4) - (6)].d0exp), (yyvsp[(6) - (6)].d0exp)) ; }
    break;

  case 410:

/* Line 1806 of yacc.c  */
#line 2370 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_sif((yyvsp[(1) - (6)].ifhead), (yyvsp[(2) - (6)].s0exp), (yyvsp[(4) - (6)].d0exp), (yyvsp[(6) - (6)].d0exp)) ; }
    break;

  case 411:

/* Line 1806 of yacc.c  */
#line 2371 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_caseof((yyvsp[(1) - (4)].casehead), (yyvsp[(2) - (4)].d0exp), (yyvsp[(3) - (4)].t0kn), (yyvsp[(4) - (4)].c0laulst)) ; }
    break;

  case 412:

/* Line 1806 of yacc.c  */
#line 2372 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_scaseof((yyvsp[(1) - (4)].casehead), (yyvsp[(2) - (4)].s0exp), (yyvsp[(3) - (4)].t0kn), (yyvsp[(4) - (4)].sc0laulst)) ; }
    break;

  case 413:

/* Line 1806 of yacc.c  */
#line 2373 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_lam((yyvsp[(1) - (5)].lamkind), (yyvsp[(2) - (5)].f0arglst), (yyvsp[(3) - (5)].s0expopt), (yyvsp[(4) - (5)].e0fftaglstopt), (yyvsp[(5) - (5)].d0exp) ) ; }
    break;

  case 414:

/* Line 1806 of yacc.c  */
#line 2374 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_fix((yyvsp[(1) - (6)].fixkind), (yyvsp[(2) - (6)].i0de), (yyvsp[(3) - (6)].f0arglst), (yyvsp[(4) - (6)].s0expopt), (yyvsp[(5) - (6)].e0fftaglstopt), (yyvsp[(6) - (6)].d0exp)) ; }
    break;

  case 415:

/* Line 1806 of yacc.c  */
#line 2375 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_for_itp ((yyvsp[(1) - (3)].loophead), (yyvsp[(2) - (3)].initestpost), (yyvsp[(3) - (3)].d0exp)) ; }
    break;

  case 416:

/* Line 1806 of yacc.c  */
#line 2376 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_while ((yyvsp[(1) - (3)].loophead), (yyvsp[(2) - (3)].d0exp), (yyvsp[(3) - (3)].d0exp)) ; }
    break;

  case 417:

/* Line 1806 of yacc.c  */
#line 2377 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_raise((yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].d0exp)) ; }
    break;

  case 418:

/* Line 1806 of yacc.c  */
#line 2378 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_showtype((yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].d0exp)) ; }
    break;

  case 419:

/* Line 1806 of yacc.c  */
#line 2379 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_trywith_seq((yyvsp[(1) - (4)].tryhead), (yyvsp[(2) - (4)].d0explst), (yyvsp[(3) - (4)].t0kn), (yyvsp[(4) - (4)].c0laulst)) ; }
    break;

  case 420:

/* Line 1806 of yacc.c  */
#line 2380 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_where ((yyvsp[(1) - (5)].d0exp), (yyvsp[(4) - (5)].d0eclst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 421:

/* Line 1806 of yacc.c  */
#line 2384 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_char((yyvsp[(1) - (1)].c0har)) ; }
    break;

  case 422:

/* Line 1806 of yacc.c  */
#line 2385 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_float((yyvsp[(1) - (1)].f0loat)) ; }
    break;

  case 423:

/* Line 1806 of yacc.c  */
#line 2386 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_floatsp((yyvsp[(1) - (1)].f0loatsp)) ; }
    break;

  case 424:

/* Line 1806 of yacc.c  */
#line 2387 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_int((yyvsp[(1) - (1)].i0nt)) ; }
    break;

  case 425:

/* Line 1806 of yacc.c  */
#line 2388 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_intsp((yyvsp[(1) - (1)].i0ntsp)) ; }
    break;

  case 426:

/* Line 1806 of yacc.c  */
#line 2389 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_string((yyvsp[(1) - (1)].s0tring)) ; }
    break;

  case 427:

/* Line 1806 of yacc.c  */
#line 2390 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_FILENAME((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 428:

/* Line 1806 of yacc.c  */
#line 2391 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_LOCATION((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 429:

/* Line 1806 of yacc.c  */
#line 2392 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_ide((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 430:

/* Line 1806 of yacc.c  */
#line 2393 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_opide((yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 431:

/* Line 1806 of yacc.c  */
#line 2394 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_qid((yyvsp[(1) - (2)].d0ynq), (yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 432:

/* Line 1806 of yacc.c  */
#line 2395 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_idext((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 433:

/* Line 1806 of yacc.c  */
#line 2396 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_ptrof((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 434:

/* Line 1806 of yacc.c  */
#line 2397 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_loopexn(0, (yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 435:

/* Line 1806 of yacc.c  */
#line 2398 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_loopexn(1, (yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 436:

/* Line 1806 of yacc.c  */
#line 2399 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_foldat((yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].d0explst)) ; }
    break;

  case 437:

/* Line 1806 of yacc.c  */
#line 2400 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_freeat((yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].d0explst)) ; }
    break;

  case 438:

/* Line 1806 of yacc.c  */
#line 2401 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_viewat((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 439:

/* Line 1806 of yacc.c  */
#line 2402 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_crypt (-1, (yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 440:

/* Line 1806 of yacc.c  */
#line 2403 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_crypt ( 1, (yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 441:

/* Line 1806 of yacc.c  */
#line 2404 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_delay(0, (yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 442:

/* Line 1806 of yacc.c  */
#line 2405 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_delay(1, (yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 443:

/* Line 1806 of yacc.c  */
#line 2406 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_dynload((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 444:

/* Line 1806 of yacc.c  */
#line 2407 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_effmask_all((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 445:

/* Line 1806 of yacc.c  */
#line 2408 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_effmask_exn((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 446:

/* Line 1806 of yacc.c  */
#line 2409 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_effmask_ntm((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 447:

/* Line 1806 of yacc.c  */
#line 2410 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_effmask_ref((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 448:

/* Line 1806 of yacc.c  */
#line 2411 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_arrinit_none ((yyvsp[(1) - (6)].t0kn), (yyvsp[(2) - (6)].s0exp), (yyvsp[(5) - (6)].d0explst), (yyvsp[(6) - (6)].t0kn)) ; }
    break;

  case 449:

/* Line 1806 of yacc.c  */
#line 2412 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_arrinit_some ((yyvsp[(1) - (9)].t0kn), (yyvsp[(2) - (9)].s0exp), (yyvsp[(5) - (9)].d0exp), (yyvsp[(8) - (9)].d0explst), (yyvsp[(9) - (9)].t0kn)) ; }
    break;

  case 450:

/* Line 1806 of yacc.c  */
#line 2413 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_arrpsz ((yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].s0expopt), (yyvsp[(3) - (5)].t0kn), (yyvsp[(4) - (5)].d0explst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 451:

/* Line 1806 of yacc.c  */
#line 2414 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_arrsub ((yyvsp[(1) - (2)].arrqi0de), (yyvsp[(2) - (2)].d0arrind)) ; }
    break;

  case 452:

/* Line 1806 of yacc.c  */
#line 2415 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_sel_lab ((yyvsp[(1) - (2)].s0elop), (yyvsp[(2) - (2)].l0ab)) ; }
    break;

  case 453:

/* Line 1806 of yacc.c  */
#line 2416 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_sel_ind ((yyvsp[(1) - (3)].s0elop), (yyvsp[(3) - (3)].d0arrind)) ; }
    break;

  case 454:

/* Line 1806 of yacc.c  */
#line 2417 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_tmpid ((yyvsp[(1) - (4)].tmpqi0de), (yyvsp[(2) - (4)].s0explst), (yyvsp[(3) - (4)].t1mps0explstlst), (yyvsp[(4) - (4)].t0kn)) ; }
    break;

  case 455:

/* Line 1806 of yacc.c  */
#line 2418 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_exist ((yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].s0exparg), (yyvsp[(3) - (5)].t0kn), (yyvsp[(4) - (5)].d0exp), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 456:

/* Line 1806 of yacc.c  */
#line 2419 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_list ((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].d0explst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 457:

/* Line 1806 of yacc.c  */
#line 2420 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_list2 ((yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].d0explst), (yyvsp[(4) - (5)].d0explst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 458:

/* Line 1806 of yacc.c  */
#line 2421 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_lst (0, (yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].s0expopt), (yyvsp[(3) - (5)].t0kn), (yyvsp[(4) - (5)].d0explst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 459:

/* Line 1806 of yacc.c  */
#line 2422 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_lst (1, (yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].s0expopt), (yyvsp[(3) - (5)].t0kn), (yyvsp[(4) - (5)].d0explst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 460:

/* Line 1806 of yacc.c  */
#line 2423 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_lst_quote ((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].d0explst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 461:

/* Line 1806 of yacc.c  */
#line 2424 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_seq ((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].d0explst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 462:

/* Line 1806 of yacc.c  */
#line 2425 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_seq ((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].d0explst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 463:

/* Line 1806 of yacc.c  */
#line 2426 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_tup (0, (yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].d0explst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 464:

/* Line 1806 of yacc.c  */
#line 2427 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_tup (1, (yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].d0explst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 465:

/* Line 1806 of yacc.c  */
#line 2428 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_tup (2, (yyvsp[(1) - (4)].t0kn), (yyvsp[(3) - (4)].d0explst), (yyvsp[(4) - (4)].t0kn)) ; }
    break;

  case 466:

/* Line 1806 of yacc.c  */
#line 2429 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_tup (3, (yyvsp[(1) - (4)].t0kn), (yyvsp[(3) - (4)].d0explst), (yyvsp[(4) - (4)].t0kn)) ; }
    break;

  case 467:

/* Line 1806 of yacc.c  */
#line 2430 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_tup2 (0, (yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].d0explst), (yyvsp[(4) - (5)].d0explst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 468:

/* Line 1806 of yacc.c  */
#line 2431 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_tup2 (1, (yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].d0explst), (yyvsp[(4) - (5)].d0explst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 469:

/* Line 1806 of yacc.c  */
#line 2432 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_rec (0, (yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].labd0explst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 470:

/* Line 1806 of yacc.c  */
#line 2433 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_rec (1, (yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].labd0explst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 471:

/* Line 1806 of yacc.c  */
#line 2434 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_rec (2, (yyvsp[(1) - (4)].t0kn), (yyvsp[(3) - (4)].labd0explst), (yyvsp[(4) - (4)].t0kn)) ; }
    break;

  case 472:

/* Line 1806 of yacc.c  */
#line 2435 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_rec (3, (yyvsp[(1) - (4)].t0kn), (yyvsp[(3) - (4)].labd0explst), (yyvsp[(4) - (4)].t0kn)) ; }
    break;

  case 473:

/* Line 1806 of yacc.c  */
#line 2436 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_extval((yyvsp[(1) - (6)].t0kn), (yyvsp[(3) - (6)].s0exp), (yyvsp[(5) - (6)].s0tring), (yyvsp[(6) - (6)].t0kn)) ; }
    break;

  case 474:

/* Line 1806 of yacc.c  */
#line 2437 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_macsyn_cross((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].d0exp), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 475:

/* Line 1806 of yacc.c  */
#line 2438 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_macsyn_decode((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].d0exp), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 476:

/* Line 1806 of yacc.c  */
#line 2439 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_macsyn_encode_seq((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].d0explst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 477:

/* Line 1806 of yacc.c  */
#line 2440 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_let_seq((yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].d0eclst), (yyvsp[(3) - (5)].t0kn), (yyvsp[(4) - (5)].d0explst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 478:

/* Line 1806 of yacc.c  */
#line 2441 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_decseq((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].d0eclst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 479:

/* Line 1806 of yacc.c  */
#line 2445 "ats_grammar.yats"
    { (yyval.d0exp) = d0exp_sexparg((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0exparg), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 480:

/* Line 1806 of yacc.c  */
#line 2449 "ats_grammar.yats"
    { (yyval.d0explst) = d0explst_nil() ; }
    break;

  case 481:

/* Line 1806 of yacc.c  */
#line 2450 "ats_grammar.yats"
    { (yyval.d0explst) = d0explst_cons((yyvsp[(1) - (2)].d0exp), (yyvsp[(2) - (2)].d0explst)) ;  }
    break;

  case 482:

/* Line 1806 of yacc.c  */
#line 2454 "ats_grammar.yats"
    { (yyval.d0exp) = (yyvsp[(1) - (1)].d0exp) ; }
    break;

  case 483:

/* Line 1806 of yacc.c  */
#line 2455 "ats_grammar.yats"
    { (yyval.d0exp) = (yyvsp[(1) - (1)].d0exp) ; }
    break;

  case 484:

/* Line 1806 of yacc.c  */
#line 2459 "ats_grammar.yats"
    { (yyval.d0explst) = d0explst_nil() ; }
    break;

  case 485:

/* Line 1806 of yacc.c  */
#line 2460 "ats_grammar.yats"
    { (yyval.d0explst) = d0explst_cons((yyvsp[(1) - (2)].d0exp), (yyvsp[(2) - (2)].d0explst)) ; }
    break;

  case 486:

/* Line 1806 of yacc.c  */
#line 2464 "ats_grammar.yats"
    { (yyval.d0arrind) = d0arrind_make_sing((yyvsp[(1) - (2)].d0explst), (yyvsp[(2) - (2)].t0kn)) ; }
    break;

  case 487:

/* Line 1806 of yacc.c  */
#line 2465 "ats_grammar.yats"
    { (yyval.d0arrind) = d0arrind_make_cons((yyvsp[(1) - (4)].d0explst), (yyvsp[(4) - (4)].d0arrind)) ; }
    break;

  case 488:

/* Line 1806 of yacc.c  */
#line 2469 "ats_grammar.yats"
    { (yyval.s0expopt) = s0expopt_none() ; }
    break;

  case 489:

/* Line 1806 of yacc.c  */
#line 2470 "ats_grammar.yats"
    { (yyval.s0expopt) = s0expopt_some((yyvsp[(2) - (2)].s0exp)) ; }
    break;

  case 490:

/* Line 1806 of yacc.c  */
#line 2474 "ats_grammar.yats"
    { (yyval.e0fftaglstopt) = e0fftaglstopt_none() ; }
    break;

  case 491:

/* Line 1806 of yacc.c  */
#line 2475 "ats_grammar.yats"
    { (yyval.e0fftaglstopt) = e0fftaglstopt_some(e0fftaglst_nil()) ; }
    break;

  case 492:

/* Line 1806 of yacc.c  */
#line 2476 "ats_grammar.yats"
    { (yyval.e0fftaglstopt) = e0fftaglstopt_some((yyvsp[(2) - (3)].e0fftaglst)) ; }
    break;

  case 493:

/* Line 1806 of yacc.c  */
#line 2480 "ats_grammar.yats"
    { (yyval.i0nvresstate) = i0nvresstate_none() ; }
    break;

  case 494:

/* Line 1806 of yacc.c  */
#line 2481 "ats_grammar.yats"
    { (yyval.i0nvresstate) = (yyvsp[(1) - (2)].i0nvresstate) ; }
    break;

  case 495:

/* Line 1806 of yacc.c  */
#line 2485 "ats_grammar.yats"
    { (yyval.ifhead) = ifhead_make((yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].i0nvresstate)) ; }
    break;

  case 496:

/* Line 1806 of yacc.c  */
#line 2489 "ats_grammar.yats"
    { (yyval.ifhead) = ifhead_make((yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].i0nvresstate)) ; }
    break;

  case 497:

/* Line 1806 of yacc.c  */
#line 2493 "ats_grammar.yats"
    { (yyval.casehead) = casehead_make(0, (yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].i0nvresstate)) ; }
    break;

  case 498:

/* Line 1806 of yacc.c  */
#line 2494 "ats_grammar.yats"
    { (yyval.casehead) = casehead_make(-1, (yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].i0nvresstate)) ; }
    break;

  case 499:

/* Line 1806 of yacc.c  */
#line 2495 "ats_grammar.yats"
    { (yyval.casehead) = casehead_make(1, (yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].i0nvresstate)) ; }
    break;

  case 500:

/* Line 1806 of yacc.c  */
#line 2499 "ats_grammar.yats"
    { (yyval.casehead) = casehead_make(0, (yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].i0nvresstate)) ; }
    break;

  case 501:

/* Line 1806 of yacc.c  */
#line 2503 "ats_grammar.yats"
    { (yyval.loophead) = loophead_make_none((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 502:

/* Line 1806 of yacc.c  */
#line 2504 "ats_grammar.yats"
    { (yyval.loophead) = loophead_make_some((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].loopi0nv), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 503:

/* Line 1806 of yacc.c  */
#line 2508 "ats_grammar.yats"
    { (yyval.loophead) = loophead_make_some((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].loopi0nv), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 504:

/* Line 1806 of yacc.c  */
#line 2512 "ats_grammar.yats"
    { (yyval.tryhead) = tryhead_make((yyvsp[(1) - (1)].t0kn)) ; }
    break;

  case 505:

/* Line 1806 of yacc.c  */
#line 2516 "ats_grammar.yats"
    { (yyval.d0explst) = d0explst_nil() ; }
    break;

  case 506:

/* Line 1806 of yacc.c  */
#line 2517 "ats_grammar.yats"
    { (yyval.d0explst) = d0explst_cons((yyvsp[(1) - (2)].d0exp), (yyvsp[(2) - (2)].d0explst)) ; }
    break;

  case 507:

/* Line 1806 of yacc.c  */
#line 2521 "ats_grammar.yats"
    { (yyval.d0explst) = d0explst_nil() ; }
    break;

  case 508:

/* Line 1806 of yacc.c  */
#line 2522 "ats_grammar.yats"
    { (yyval.d0explst) = d0explst_cons((yyvsp[(2) - (3)].d0exp), (yyvsp[(3) - (3)].d0explst)) ; }
    break;

  case 509:

/* Line 1806 of yacc.c  */
#line 2526 "ats_grammar.yats"
    { (yyval.d0explst) = d0explst_nil() ; }
    break;

  case 510:

/* Line 1806 of yacc.c  */
#line 2527 "ats_grammar.yats"
    { (yyval.d0explst) = d0explst_sing((yyvsp[(1) - (1)].d0exp)) ; }
    break;

  case 511:

/* Line 1806 of yacc.c  */
#line 2528 "ats_grammar.yats"
    { (yyval.d0explst) = d0explst_cons((yyvsp[(1) - (3)].d0exp), (yyvsp[(3) - (3)].d0explst)) ; }
    break;

  case 512:

/* Line 1806 of yacc.c  */
#line 2532 "ats_grammar.yats"
    { (yyval.d0explst) = d0explst_cons((yyvsp[(1) - (3)].d0exp), (yyvsp[(3) - (3)].d0explst)) ; }
    break;

  case 513:

/* Line 1806 of yacc.c  */
#line 2536 "ats_grammar.yats"
    { (yyval.labd0explst) = labd0explst_nil() ; }
    break;

  case 514:

/* Line 1806 of yacc.c  */
#line 2537 "ats_grammar.yats"
    { (yyval.labd0explst) = labd0explst_cons((yyvsp[(1) - (4)].l0ab), (yyvsp[(3) - (4)].d0exp), (yyvsp[(4) - (4)].labd0explst)) ; }
    break;

  case 515:

/* Line 1806 of yacc.c  */
#line 2541 "ats_grammar.yats"
    { (yyval.labd0explst) = labd0explst_nil() ; }
    break;

  case 516:

/* Line 1806 of yacc.c  */
#line 2542 "ats_grammar.yats"
    { (yyval.labd0explst) = labd0explst_cons((yyvsp[(2) - (5)].l0ab), (yyvsp[(4) - (5)].d0exp), (yyvsp[(5) - (5)].labd0explst)) ; }
    break;

  case 517:

/* Line 1806 of yacc.c  */
#line 2546 "ats_grammar.yats"
    { (yyval.m0atch) = m0atch_make_none ((yyvsp[(1) - (1)].d0exp)) ; }
    break;

  case 518:

/* Line 1806 of yacc.c  */
#line 2547 "ats_grammar.yats"
    { (yyval.m0atch) = m0atch_make_some ((yyvsp[(1) - (3)].d0exp), (yyvsp[(3) - (3)].p0at)) ; }
    break;

  case 519:

/* Line 1806 of yacc.c  */
#line 2551 "ats_grammar.yats"
    { (yyval.m0atchlst) = m0atchlst_cons ((yyvsp[(1) - (2)].m0atch), (yyvsp[(2) - (2)].m0atchlst) ) ; }
    break;

  case 520:

/* Line 1806 of yacc.c  */
#line 2555 "ats_grammar.yats"
    { (yyval.m0atchlst) = m0atchlst_nil () ; }
    break;

  case 521:

/* Line 1806 of yacc.c  */
#line 2556 "ats_grammar.yats"
    { (yyval.m0atchlst) = m0atchlst_cons ((yyvsp[(2) - (3)].m0atch), (yyvsp[(3) - (3)].m0atchlst) ) ; }
    break;

  case 522:

/* Line 1806 of yacc.c  */
#line 2560 "ats_grammar.yats"
    { (yyval.guap0at) = guap0at_make_none((yyvsp[(1) - (1)].p0at)) ; }
    break;

  case 523:

/* Line 1806 of yacc.c  */
#line 2561 "ats_grammar.yats"
    { (yyval.guap0at) = guap0at_make_some((yyvsp[(1) - (3)].p0at), (yyvsp[(3) - (3)].m0atchlst)) ; }
    break;

  case 524:

/* Line 1806 of yacc.c  */
#line 2565 "ats_grammar.yats"
    { (yyval.c0lau) = c0lau_make ((yyvsp[(1) - (3)].guap0at), 0, 0, (yyvsp[(3) - (3)].d0exp)) ; }
    break;

  case 525:

/* Line 1806 of yacc.c  */
#line 2566 "ats_grammar.yats"
    { (yyval.c0lau) = c0lau_make ((yyvsp[(1) - (3)].guap0at), 1, 0, (yyvsp[(3) - (3)].d0exp)) ; }
    break;

  case 526:

/* Line 1806 of yacc.c  */
#line 2567 "ats_grammar.yats"
    { (yyval.c0lau) = c0lau_make ((yyvsp[(1) - (3)].guap0at), 0, 1, (yyvsp[(3) - (3)].d0exp)) ; }
    break;

  case 527:

/* Line 1806 of yacc.c  */
#line 2568 "ats_grammar.yats"
    { (yyval.c0lau) = c0lau_make ((yyvsp[(1) - (3)].guap0at), 1, 1, (yyvsp[(3) - (3)].d0exp)) ; }
    break;

  case 528:

/* Line 1806 of yacc.c  */
#line 2572 "ats_grammar.yats"
    { (yyval.c0laulst) = (yyvsp[(1) - (1)].c0laulst) ; }
    break;

  case 529:

/* Line 1806 of yacc.c  */
#line 2573 "ats_grammar.yats"
    { (yyval.c0laulst) = c0laulst_cons((yyvsp[(1) - (2)].c0lau), (yyvsp[(2) - (2)].c0laulst)) ; }
    break;

  case 530:

/* Line 1806 of yacc.c  */
#line 2577 "ats_grammar.yats"
    { (yyval.c0laulst) = c0laulst_nil() ; }
    break;

  case 531:

/* Line 1806 of yacc.c  */
#line 2578 "ats_grammar.yats"
    { (yyval.c0laulst) = c0laulst_cons((yyvsp[(2) - (3)].c0lau), (yyvsp[(3) - (3)].c0laulst)) ; }
    break;

  case 532:

/* Line 1806 of yacc.c  */
#line 2582 "ats_grammar.yats"
    { (yyval.sc0lau) = sc0lau_make((yyvsp[(1) - (3)].sp0at), (yyvsp[(3) - (3)].d0exp)) ; }
    break;

  case 533:

/* Line 1806 of yacc.c  */
#line 2586 "ats_grammar.yats"
    { (yyval.sc0laulst) = (yyvsp[(1) - (1)].sc0laulst) ; }
    break;

  case 534:

/* Line 1806 of yacc.c  */
#line 2587 "ats_grammar.yats"
    { (yyval.sc0laulst) = sc0laulst_cons((yyvsp[(1) - (2)].sc0lau), (yyvsp[(2) - (2)].sc0laulst)) ; }
    break;

  case 535:

/* Line 1806 of yacc.c  */
#line 2591 "ats_grammar.yats"
    { (yyval.sc0laulst) = sc0laulst_nil() ; }
    break;

  case 536:

/* Line 1806 of yacc.c  */
#line 2592 "ats_grammar.yats"
    { (yyval.sc0laulst) = sc0laulst_cons((yyvsp[(2) - (3)].sc0lau), (yyvsp[(3) - (3)].sc0laulst)) ; }
    break;

  case 537:

/* Line 1806 of yacc.c  */
#line 2596 "ats_grammar.yats"
    { (yyval.s0qualstopt) = s0qualstopt_none() ; }
    break;

  case 538:

/* Line 1806 of yacc.c  */
#line 2597 "ats_grammar.yats"
    { (yyval.s0qualstopt) = s0qualstopt_some((yyvsp[(2) - (3)].s0qualst)) ; }
    break;

  case 539:

/* Line 1806 of yacc.c  */
#line 2601 "ats_grammar.yats"
    { (yyval.s0qualstopt) = s0explstopt_none() ; }
    break;

  case 540:

/* Line 1806 of yacc.c  */
#line 2602 "ats_grammar.yats"
    { (yyval.s0qualstopt) = s0explstopt_some((yyvsp[(2) - (3)].s0explst)) ; }
    break;

  case 541:

/* Line 1806 of yacc.c  */
#line 2603 "ats_grammar.yats"
    { (yyval.s0qualstopt) = s0explstopt_some(s0explst_nil()) ; }
    break;

  case 542:

/* Line 1806 of yacc.c  */
#line 2607 "ats_grammar.yats"
    { (yyval.i0nvarg) = i0nvarg_make_none((yyvsp[(1) - (2)].i0de)) ; }
    break;

  case 543:

/* Line 1806 of yacc.c  */
#line 2608 "ats_grammar.yats"
    { (yyval.i0nvarg) = i0nvarg_make_some((yyvsp[(1) - (3)].i0de), (yyvsp[(3) - (3)].s0exp)) ; }
    break;

  case 544:

/* Line 1806 of yacc.c  */
#line 2612 "ats_grammar.yats"
    { (yyval.i0nvarglst) = i0nvarglst_nil() ; }
    break;

  case 545:

/* Line 1806 of yacc.c  */
#line 2613 "ats_grammar.yats"
    { (yyval.i0nvarglst) = i0nvarglst_cons((yyvsp[(1) - (2)].i0nvarg), (yyvsp[(2) - (2)].i0nvarglst)) ; }
    break;

  case 546:

/* Line 1806 of yacc.c  */
#line 2617 "ats_grammar.yats"
    { (yyval.i0nvarglst) = i0nvarglst_nil() ; }
    break;

  case 547:

/* Line 1806 of yacc.c  */
#line 2618 "ats_grammar.yats"
    { (yyval.i0nvarglst) = i0nvarglst_cons((yyvsp[(2) - (3)].i0nvarg), (yyvsp[(3) - (3)].i0nvarglst)) ; }
    break;

  case 548:

/* Line 1806 of yacc.c  */
#line 2622 "ats_grammar.yats"
    { (yyval.i0nvarglst) = (yyvsp[(2) - (3)].i0nvarglst) ; }
    break;

  case 549:

/* Line 1806 of yacc.c  */
#line 2626 "ats_grammar.yats"
    { (yyval.s0qualstopt) = s0qualstopt_none() ; }
    break;

  case 550:

/* Line 1806 of yacc.c  */
#line 2627 "ats_grammar.yats"
    { (yyval.s0qualstopt) = s0qualstopt_some((yyvsp[(2) - (3)].s0qualst)) ; }
    break;

  case 551:

/* Line 1806 of yacc.c  */
#line 2631 "ats_grammar.yats"
    { (yyval.i0nvresstate) = i0nvresstate_none() ; }
    break;

  case 552:

/* Line 1806 of yacc.c  */
#line 2632 "ats_grammar.yats"
    { (yyval.i0nvresstate) = i0nvresstate_some((yyvsp[(2) - (5)].s0qualstopt), (yyvsp[(4) - (5)].i0nvarglst)) ; }
    break;

  case 553:

/* Line 1806 of yacc.c  */
#line 2636 "ats_grammar.yats"
    { (yyval.loopi0nv) = loopi0nv_make((yyvsp[(1) - (4)].s0qualstopt), (yyvsp[(2) - (4)].s0qualstopt), (yyvsp[(3) - (4)].i0nvarglst), (yyvsp[(4) - (4)].i0nvresstate)) ; }
    break;

  case 554:

/* Line 1806 of yacc.c  */
#line 2640 "ats_grammar.yats"
    { (yyval.initestpost) = initestpost_make ((yyvsp[(1) - (7)].t0kn),(yyvsp[(2) - (7)].d0explst),(yyvsp[(3) - (7)].t0kn),(yyvsp[(4) - (7)].d0explst),(yyvsp[(5) - (7)].t0kn),(yyvsp[(6) - (7)].d0explst),(yyvsp[(7) - (7)].t0kn)) ; }
    break;

  case 555:

/* Line 1806 of yacc.c  */
#line 2644 "ats_grammar.yats"
    { (yyval.i0de) = (yyvsp[(1) - (1)].i0de) ; }
    break;

  case 556:

/* Line 1806 of yacc.c  */
#line 2648 "ats_grammar.yats"
    { (yyval.i0delst) = i0delst_nil() ; }
    break;

  case 557:

/* Line 1806 of yacc.c  */
#line 2649 "ats_grammar.yats"
    { (yyval.i0delst) = i0delst_cons((yyvsp[(1) - (2)].i0de), (yyvsp[(2) - (2)].i0delst)) ; }
    break;

  case 558:

/* Line 1806 of yacc.c  */
#line 2653 "ats_grammar.yats"
    { (yyval.i0delst) = i0delst_nil() ; }
    break;

  case 559:

/* Line 1806 of yacc.c  */
#line 2654 "ats_grammar.yats"
    { (yyval.i0delst) = i0delst_cons((yyvsp[(2) - (3)].i0de), (yyvsp[(3) - (3)].i0delst)) ; }
    break;

  case 560:

/* Line 1806 of yacc.c  */
#line 2658 "ats_grammar.yats"
    { (yyval.m0acarg) = m0acarg_one ((yyvsp[(1) - (1)].i0de)) ; }
    break;

  case 561:

/* Line 1806 of yacc.c  */
#line 2659 "ats_grammar.yats"
    { (yyval.m0acarg) = m0acarg_lst ((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].i0delst), (yyvsp[(3) - (3)].t0kn)) ; }
    break;

  case 562:

/* Line 1806 of yacc.c  */
#line 2663 "ats_grammar.yats"
    { (yyval.m0acarglst) = m0acarglst_nil () ; }
    break;

  case 563:

/* Line 1806 of yacc.c  */
#line 2664 "ats_grammar.yats"
    { (yyval.m0acarglst) = m0acarglst_cons ((yyvsp[(1) - (2)].m0acarg), (yyvsp[(2) - (2)].m0acarglst)) ; }
    break;

  case 564:

/* Line 1806 of yacc.c  */
#line 2668 "ats_grammar.yats"
    { (yyval.m0acdef) = m0acdef_make((yyvsp[(1) - (4)].i0de), (yyvsp[(2) - (4)].m0acarglst), (yyvsp[(4) - (4)].d0exp)) ; }
    break;

  case 565:

/* Line 1806 of yacc.c  */
#line 2672 "ats_grammar.yats"
    { (yyval.m0acdeflst) = m0acdeflst_nil() ; }
    break;

  case 566:

/* Line 1806 of yacc.c  */
#line 2673 "ats_grammar.yats"
    { (yyval.m0acdeflst) = m0acdeflst_cons((yyvsp[(2) - (3)].m0acdef), (yyvsp[(3) - (3)].m0acdeflst)) ; }
    break;

  case 567:

/* Line 1806 of yacc.c  */
#line 2677 "ats_grammar.yats"
    { (yyval.v0aldec) = v0aldec_make ((yyvsp[(1) - (4)].p0at), (yyvsp[(3) - (4)].d0exp), (yyvsp[(4) - (4)].witht0ype)) ; }
    break;

  case 568:

/* Line 1806 of yacc.c  */
#line 2681 "ats_grammar.yats"
    { (yyval.v0aldeclst) = v0aldeclst_nil() ; }
    break;

  case 569:

/* Line 1806 of yacc.c  */
#line 2682 "ats_grammar.yats"
    { (yyval.v0aldeclst) = v0aldeclst_cons((yyvsp[(2) - (3)].v0aldec), (yyvsp[(3) - (3)].v0aldeclst)) ; }
    break;

  case 570:

/* Line 1806 of yacc.c  */
#line 2686 "ats_grammar.yats"
    { (yyval.f0undec) = f0undec_make_none((yyvsp[(1) - (5)].i0de), (yyvsp[(2) - (5)].f0arglst), (yyvsp[(4) - (5)].d0exp), (yyvsp[(5) - (5)].witht0ype)) ; }
    break;

  case 571:

/* Line 1806 of yacc.c  */
#line 2687 "ats_grammar.yats"
    { (yyval.f0undec) = f0undec_make_some((yyvsp[(1) - (7)].i0de), (yyvsp[(2) - (7)].f0arglst), (yyvsp[(3) - (7)].e0fftaglstopt), (yyvsp[(4) - (7)].s0exp), (yyvsp[(6) - (7)].d0exp), (yyvsp[(7) - (7)].witht0ype)) ; }
    break;

  case 572:

/* Line 1806 of yacc.c  */
#line 2691 "ats_grammar.yats"
    { (yyval.f0undeclst) = f0undeclst_nil() ; }
    break;

  case 573:

/* Line 1806 of yacc.c  */
#line 2692 "ats_grammar.yats"
    { (yyval.f0undeclst) = f0undeclst_cons((yyvsp[(2) - (3)].f0undec), (yyvsp[(3) - (3)].f0undeclst)) ; }
    break;

  case 574:

/* Line 1806 of yacc.c  */
#line 2696 "ats_grammar.yats"
    { (yyval.v0arwth) = v0arwth_none () ; }
    break;

  case 575:

/* Line 1806 of yacc.c  */
#line 2697 "ats_grammar.yats"
    { (yyval.v0arwth) = v0arwth_some ((yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 576:

/* Line 1806 of yacc.c  */
#line 2701 "ats_grammar.yats"
    { (yyval.v0ardec) = v0ardec_make_none_some(0, (yyvsp[(1) - (4)].i0de), (yyvsp[(2) - (4)].v0arwth), (yyvsp[(4) - (4)].d0exp)) ; }
    break;

  case 577:

/* Line 1806 of yacc.c  */
#line 2702 "ats_grammar.yats"
    { (yyval.v0ardec) = v0ardec_make_none_some(1, (yyvsp[(2) - (5)].i0de), (yyvsp[(3) - (5)].v0arwth), (yyvsp[(5) - (5)].d0exp)) ; }
    break;

  case 578:

/* Line 1806 of yacc.c  */
#line 2703 "ats_grammar.yats"
    { (yyval.v0ardec) = v0ardec_make_some_none(0, (yyvsp[(1) - (4)].i0de), (yyvsp[(3) - (4)].s0exp), (yyvsp[(4) - (4)].v0arwth)) ; }
    break;

  case 579:

/* Line 1806 of yacc.c  */
#line 2704 "ats_grammar.yats"
    { (yyval.v0ardec) = v0ardec_make_some_some(0, (yyvsp[(1) - (6)].i0de), (yyvsp[(3) - (6)].s0exp), (yyvsp[(4) - (6)].v0arwth), (yyvsp[(6) - (6)].d0exp)) ; }
    break;

  case 580:

/* Line 1806 of yacc.c  */
#line 2708 "ats_grammar.yats"
    { (yyval.v0ardeclst) = v0ardeclst_nil() ; }
    break;

  case 581:

/* Line 1806 of yacc.c  */
#line 2709 "ats_grammar.yats"
    { (yyval.v0ardeclst) = v0ardeclst_cons((yyvsp[(2) - (3)].v0ardec), (yyvsp[(3) - (3)].v0ardeclst)) ; }
    break;

  case 582:

/* Line 1806 of yacc.c  */
#line 2713 "ats_grammar.yats"
    { (yyval.i0mpdec) = i0mpdec_make((yyvsp[(1) - (5)].impqi0de), (yyvsp[(2) - (5)].f0arglst), (yyvsp[(3) - (5)].s0expopt), (yyvsp[(5) - (5)].d0exp)) ; }
    break;

  case 583:

/* Line 1806 of yacc.c  */
#line 2717 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_infix((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].p0rec),  0, (yyvsp[(3) - (3)].i0delst)) ; }
    break;

  case 584:

/* Line 1806 of yacc.c  */
#line 2718 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_infix((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].p0rec), -1, (yyvsp[(3) - (3)].i0delst)) ; }
    break;

  case 585:

/* Line 1806 of yacc.c  */
#line 2719 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_infix((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].p0rec),  1, (yyvsp[(3) - (3)].i0delst)) ; }
    break;

  case 586:

/* Line 1806 of yacc.c  */
#line 2720 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_prefix((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].p0rec), (yyvsp[(3) - (3)].i0delst)) ; }
    break;

  case 587:

/* Line 1806 of yacc.c  */
#line 2721 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_postfix((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].p0rec), (yyvsp[(3) - (3)].i0delst)) ; }
    break;

  case 588:

/* Line 1806 of yacc.c  */
#line 2722 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_nonfix((yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].i0delst)) ; }
    break;

  case 589:

/* Line 1806 of yacc.c  */
#line 2723 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_symintr((yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].i0delst)) ; }
    break;

  case 590:

/* Line 1806 of yacc.c  */
#line 2724 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_e0xpundef((yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 591:

/* Line 1806 of yacc.c  */
#line 2725 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_e0xpdef((yyvsp[(2) - (3)].i0de), (yyvsp[(3) - (3)].e0xpopt)) ; }
    break;

  case 592:

/* Line 1806 of yacc.c  */
#line 2726 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_e0xpact_assert((yyvsp[(2) - (2)].e0xp)) ; }
    break;

  case 593:

/* Line 1806 of yacc.c  */
#line 2727 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_e0xpact_error((yyvsp[(2) - (2)].e0xp)) ; }
    break;

  case 594:

/* Line 1806 of yacc.c  */
#line 2728 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_e0xpact_print((yyvsp[(2) - (2)].e0xp)) ; }
    break;

  case 595:

/* Line 1806 of yacc.c  */
#line 2729 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_srtdefs((yyvsp[(2) - (3)].s0rtdef), (yyvsp[(3) - (3)].s0rtdeflst)) ; }
    break;

  case 596:

/* Line 1806 of yacc.c  */
#line 2730 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_datsrts(0, (yyvsp[(2) - (3)].d0atsrtdec), (yyvsp[(3) - (3)].d0atsrtdeclst)) ; }
    break;

  case 597:

/* Line 1806 of yacc.c  */
#line 2731 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_datsrts(1, (yyvsp[(2) - (3)].d0atsrtdec), (yyvsp[(3) - (3)].d0atsrtdeclst)) ; }
    break;

  case 598:

/* Line 1806 of yacc.c  */
#line 2732 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_stacons((yyvsp[(1) - (3)].abskind), (yyvsp[(2) - (3)].s0tacon), (yyvsp[(3) - (3)].s0taconlst)) ; }
    break;

  case 599:

/* Line 1806 of yacc.c  */
#line 2733 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_stacsts((yyvsp[(2) - (3)].s0tacst), (yyvsp[(3) - (3)].s0tacstlst)) ; }
    break;

  case 600:

/* Line 1806 of yacc.c  */
#line 2734 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_stavars((yyvsp[(2) - (3)].s0tavar), (yyvsp[(3) - (3)].s0tavarlst)) ; }
    break;

  case 601:

/* Line 1806 of yacc.c  */
#line 2735 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_sexpdefs((yyvsp[(1) - (3)].stadefkind), (yyvsp[(2) - (3)].s0expdef), (yyvsp[(3) - (3)].s0expdeflst)) ; }
    break;

  case 602:

/* Line 1806 of yacc.c  */
#line 2736 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_saspdec((yyvsp[(2) - (2)].s0aspdec)) ; }
    break;

  case 603:

/* Line 1806 of yacc.c  */
#line 2737 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_datdecs((yyvsp[(1) - (4)].datakind), (yyvsp[(2) - (4)].d0atdec), (yyvsp[(3) - (4)].d0atdeclst), (yyvsp[(4) - (4)].s0expdeflst)) ; }
    break;

  case 604:

/* Line 1806 of yacc.c  */
#line 2738 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_exndecs((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].e0xndec), (yyvsp[(3) - (3)].e0xndeclst)) ; }
    break;

  case 605:

/* Line 1806 of yacc.c  */
#line 2739 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_classdec_none ((yyvsp[(1) - (2)].t0kn), (yyvsp[(2) - (2)].i0de)) ; }
    break;

  case 606:

/* Line 1806 of yacc.c  */
#line 2740 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_classdec_some ((yyvsp[(1) - (4)].t0kn), (yyvsp[(2) - (4)].i0de), (yyvsp[(4) - (4)].s0exp)) ; }
    break;

  case 607:

/* Line 1806 of yacc.c  */
#line 2741 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_overload((yyvsp[(1) - (4)].t0kn), (yyvsp[(2) - (4)].i0de), (yyvsp[(4) - (4)].dqi0de)) ; }
    break;

  case 608:

/* Line 1806 of yacc.c  */
#line 2742 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_overload_lrbrackets((yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].t0kn), (yyvsp[(3) - (5)].t0kn), (yyvsp[(5) - (5)].dqi0de)) ; }
    break;

  case 609:

/* Line 1806 of yacc.c  */
#line 2743 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_macdefs(0, (yyvsp[(2) - (3)].m0acdef), (yyvsp[(3) - (3)].m0acdeflst)) ; }
    break;

  case 610:

/* Line 1806 of yacc.c  */
#line 2744 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_macdefs(-1/*error*/, (yyvsp[(3) - (4)].m0acdef), (yyvsp[(4) - (4)].m0acdeflst)) ; }
    break;

  case 611:

/* Line 1806 of yacc.c  */
#line 2745 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_macdefs(1, (yyvsp[(2) - (3)].m0acdef), (yyvsp[(3) - (3)].m0acdeflst)) ; }
    break;

  case 612:

/* Line 1806 of yacc.c  */
#line 2746 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_macdefs(2, (yyvsp[(3) - (4)].m0acdef), (yyvsp[(4) - (4)].m0acdeflst)) ; }
    break;

  case 613:

/* Line 1806 of yacc.c  */
#line 2747 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_staload_none((yyvsp[(2) - (2)].s0tring)) ; }
    break;

  case 614:

/* Line 1806 of yacc.c  */
#line 2748 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_staload_some((yyvsp[(2) - (4)].i0de), (yyvsp[(4) - (4)].s0tring)) ; }
    break;

  case 615:

/* Line 1806 of yacc.c  */
#line 2752 "ats_grammar.yats"
    { (yyval.s0qualst) = (yyvsp[(2) - (3)].s0qualst) ; }
    break;

  case 616:

/* Line 1806 of yacc.c  */
#line 2756 "ats_grammar.yats"
    { (yyval.s0qualstlst) = s0qualstlst_nil() ; }
    break;

  case 617:

/* Line 1806 of yacc.c  */
#line 2757 "ats_grammar.yats"
    { (yyval.s0qualstlst) = s0qualstlst_cons((yyvsp[(1) - (2)].s0qualst), (yyvsp[(2) - (2)].s0qualstlst)) ; }
    break;

  case 618:

/* Line 1806 of yacc.c  */
#line 2761 "ats_grammar.yats"
    { ; }
    break;

  case 619:

/* Line 1806 of yacc.c  */
#line 2762 "ats_grammar.yats"
    { ; }
    break;

  case 620:

/* Line 1806 of yacc.c  */
#line 2766 "ats_grammar.yats"
    { (yyval.d0ec) = (yyvsp[(1) - (1)].d0ec) ; }
    break;

  case 621:

/* Line 1806 of yacc.c  */
#line 2767 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_dcstdecs((yyvsp[(1) - (4)].dcstkind), (yyvsp[(2) - (4)].s0qualstlst), (yyvsp[(3) - (4)].d0cstdec), (yyvsp[(4) - (4)].d0cstdeclst)) ; }
    break;

  case 622:

/* Line 1806 of yacc.c  */
#line 2768 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_extcode_sta((yyvsp[(1) - (1)].e0xtcode)) ; }
    break;

  case 623:

/* Line 1806 of yacc.c  */
#line 2769 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_guadec((yyvsp[(1) - (2)].srpifkindtok), (yyvsp[(2) - (2)].d0eclst)) ; }
    break;

  case 624:

/* Line 1806 of yacc.c  */
#line 2770 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_include(0/*sta*/, (yyvsp[(2) - (2)].s0tring)) ; }
    break;

  case 625:

/* Line 1806 of yacc.c  */
#line 2771 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_local((yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].d0eclst), (yyvsp[(4) - (5)].d0eclst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 626:

/* Line 1806 of yacc.c  */
#line 2775 "ats_grammar.yats"
    { (yyval.d0eclst) = guad0ec_one((yyvsp[(1) - (4)].e0xp), (yyvsp[(3) - (4)].d0eclst), (yyvsp[(4) - (4)].t0kn)) ; }
    break;

  case 627:

/* Line 1806 of yacc.c  */
#line 2776 "ats_grammar.yats"
    { (yyval.d0eclst) = guad0ec_two((yyvsp[(1) - (6)].e0xp), (yyvsp[(3) - (6)].d0eclst), (yyvsp[(5) - (6)].d0eclst), (yyvsp[(6) - (6)].t0kn)) ; }
    break;

  case 628:

/* Line 1806 of yacc.c  */
#line 2777 "ats_grammar.yats"
    { (yyval.d0eclst) = guad0ec_cons((yyvsp[(1) - (5)].e0xp), (yyvsp[(3) - (5)].d0eclst), (yyvsp[(4) - (5)].srpifkindtok), (yyvsp[(5) - (5)].d0eclst)) ; }
    break;

  case 629:

/* Line 1806 of yacc.c  */
#line 2781 "ats_grammar.yats"
    { (yyval.d0eclst) = d0ecllst_reverse((yyvsp[(1) - (1)].d0eclst)) ; }
    break;

  case 630:

/* Line 1806 of yacc.c  */
#line 2785 "ats_grammar.yats"
    { (yyval.d0eclst) = d0ecllst_nil() ; }
    break;

  case 631:

/* Line 1806 of yacc.c  */
#line 2786 "ats_grammar.yats"
    { (yyval.d0eclst) = d0ecllst_cons((yyvsp[(1) - (3)].d0eclst), (yyvsp[(2) - (3)].d0ec)) ; }
    break;

  case 632:

/* Line 1806 of yacc.c  */
#line 2790 "ats_grammar.yats"
    { (yyval.d0ec) = (yyvsp[(1) - (1)].d0ec) ; }
    break;

  case 633:

/* Line 1806 of yacc.c  */
#line 2791 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_dcstdecs((yyvsp[(2) - (5)].dcstkind), (yyvsp[(3) - (5)].s0qualstlst), (yyvsp[(4) - (5)].d0cstdec), (yyvsp[(5) - (5)].d0cstdeclst)) ; }
    break;

  case 634:

/* Line 1806 of yacc.c  */
#line 2792 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_extype((yyvsp[(3) - (5)].s0tring), (yyvsp[(5) - (5)].s0exp)) ; }
    break;

  case 635:

/* Line 1806 of yacc.c  */
#line 2793 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_extval((yyvsp[(3) - (5)].s0tring), (yyvsp[(5) - (5)].d0exp)) ; }
    break;

  case 636:

/* Line 1806 of yacc.c  */
#line 2794 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_valdecs((yyvsp[(1) - (3)].valkind), (yyvsp[(2) - (3)].v0aldec), (yyvsp[(3) - (3)].v0aldeclst)) ; }
    break;

  case 637:

/* Line 1806 of yacc.c  */
#line 2795 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_valdecs_par((yyvsp[(3) - (4)].v0aldec), (yyvsp[(4) - (4)].v0aldeclst)) ; }
    break;

  case 638:

/* Line 1806 of yacc.c  */
#line 2796 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_valdecs_rec((yyvsp[(3) - (4)].v0aldec), (yyvsp[(4) - (4)].v0aldeclst)) ; }
    break;

  case 639:

/* Line 1806 of yacc.c  */
#line 2797 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_fundecs((yyvsp[(1) - (4)].funkind), (yyvsp[(2) - (4)].s0qualstlst), (yyvsp[(3) - (4)].f0undec), (yyvsp[(4) - (4)].f0undeclst)) ; }
    break;

  case 640:

/* Line 1806 of yacc.c  */
#line 2798 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_vardecs((yyvsp[(2) - (3)].v0ardec), (yyvsp[(3) - (3)].v0ardeclst)) ; }
    break;

  case 641:

/* Line 1806 of yacc.c  */
#line 2799 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_impdec((yyvsp[(1) - (3)].t0kn), (yyvsp[(2) - (3)].s0arglstlst), (yyvsp[(3) - (3)].i0mpdec)) ; }
    break;

  case 642:

/* Line 1806 of yacc.c  */
#line 2800 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_local((yyvsp[(1) - (5)].t0kn), (yyvsp[(2) - (5)].d0eclst), (yyvsp[(4) - (5)].d0eclst), (yyvsp[(5) - (5)].t0kn)) ; }
    break;

  case 643:

/* Line 1806 of yacc.c  */
#line 2801 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_extcode_dyn((yyvsp[(1) - (1)].e0xtcode)) ; }
    break;

  case 644:

/* Line 1806 of yacc.c  */
#line 2802 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_guadec((yyvsp[(1) - (2)].srpifkindtok), (yyvsp[(2) - (2)].d0eclst)) ; }
    break;

  case 645:

/* Line 1806 of yacc.c  */
#line 2803 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_include(1/*dyn*/, (yyvsp[(2) - (2)].s0tring)) ; }
    break;

  case 646:

/* Line 1806 of yacc.c  */
#line 2804 "ats_grammar.yats"
    { (yyval.d0ec) = d0ec_dynload((yyvsp[(2) - (2)].s0tring)) ; }
    break;

  case 647:

/* Line 1806 of yacc.c  */
#line 2808 "ats_grammar.yats"
    { (yyval.d0eclst) = guad0ec_one((yyvsp[(1) - (4)].e0xp), (yyvsp[(3) - (4)].d0eclst), (yyvsp[(4) - (4)].t0kn)) ; }
    break;

  case 648:

/* Line 1806 of yacc.c  */
#line 2809 "ats_grammar.yats"
    { (yyval.d0eclst) = guad0ec_two((yyvsp[(1) - (6)].e0xp), (yyvsp[(3) - (6)].d0eclst), (yyvsp[(5) - (6)].d0eclst), (yyvsp[(6) - (6)].t0kn)) ; }
    break;

  case 649:

/* Line 1806 of yacc.c  */
#line 2810 "ats_grammar.yats"
    { (yyval.d0eclst) = guad0ec_cons((yyvsp[(1) - (5)].e0xp), (yyvsp[(3) - (5)].d0eclst), (yyvsp[(4) - (5)].srpifkindtok), (yyvsp[(5) - (5)].d0eclst)) ; }
    break;

  case 650:

/* Line 1806 of yacc.c  */
#line 2814 "ats_grammar.yats"
    { (yyval.d0eclst) = d0ecllst_reverse((yyvsp[(1) - (1)].d0eclst)) ; }
    break;

  case 651:

/* Line 1806 of yacc.c  */
#line 2818 "ats_grammar.yats"
    { (yyval.d0eclst) = d0ecllst_nil() ; }
    break;

  case 652:

/* Line 1806 of yacc.c  */
#line 2819 "ats_grammar.yats"
    { (yyval.d0eclst) = d0ecllst_cons((yyvsp[(1) - (3)].d0eclst), (yyvsp[(2) - (3)].d0ec)) ; }
    break;



/* Line 1806 of yacc.c  */
#line 8782 "ats_grammar_yats.c"
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;

  /* Now `shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*------------------------------------.
| yyerrlab -- here on detecting error |
`------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
	 error, discard it.  */

      if (yychar <= YYEOF)
	{
	  /* Return failure if at end of input.  */
	  if (yychar == YYEOF)
	    YYABORT;
	}
      else
	{
	  yydestruct ("Error: discarding",
		      yytoken, &yylval);
	  yychar = YYEMPTY;
	}
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule which action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;	/* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
	{
	  yyn += YYTERROR;
	  if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
	    {
	      yyn = yytable[yyn];
	      if (0 < yyn)
		break;
	    }
	}

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
	YYABORT;


      yydestruct ("Error: popping",
		  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  *++yyvsp = yylval;


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined(yyoverflow) || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval);
    }
  /* Do not reclaim the symbols of the rule which action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
		  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  /* Make sure YYID is used.  */
  return YYID (yyresult);
}



/* Line 2067 of yacc.c  */
#line 2825 "ats_grammar.yats"


/* ****** ****** */

int
yylex_tok0 = -1 ;

int
yylex() {
//
  int tok ;
//
  if (yylex_tok0 >= 0) {
    tok = yylex_tok0 ; yylex_tok0 = -1 ;
  } else {
    tok = atsopt_lexer_token_get () ;
  } // end of [if]
/*
** fprintf (stdout, "tok = %i\n", tok) ;
*/
  return tok ;
//
} /* end of [yylex_tok0] */

//
// HX: needed in [ats_lexer.lats]
//
ats_void_type
yylval_char_set(c0har_t val)
  { yylval.c0har = val ; return ; }

ats_void_type
yylval_extcode_set(e0xtcode_t val)
  { yylval.e0xtcode = val ; return ; }

ats_void_type
yylval_float_set(f0loat_t val)
  { yylval.f0loat = val ; return ; }

ats_void_type
yylval_floatsp_set(f0loatsp_t val)
  { yylval.f0loatsp = val ; return ; }

ats_void_type
yylval_ide_set(i0de_t val)
  { yylval.i0de = val ; return ; }

ats_void_type
yylval_int_set(i0nt_t val)
  { yylval.i0nt = val ; return ; }

ats_void_type
yylval_intsp_set(i0ntsp_t val)
  { yylval.i0ntsp = val ; return ; }

ats_void_type
yylval_string_set(s0tring_t val)
  { yylval.s0tring = val ; return ; }

ats_void_type
yylval_token_set(t0kn_t val)
  { yylval.t0kn = val ; return ; }

// HX: see [stdlib.h]
extern void exit (int) ;
//
// HX: implemented in [ats_filename.dats]
extern ats_void_type atsopt_filename_prerr () ;
//
extern ats_ptr_type lexing_fstpos_get () ;
extern ats_void_type lexing_prerr_position (ats_ptr_type) ;
//
void
yyerror (char *s) {
  fprintf (stderr, "%s: ", s) ;
  atsopt_filename_prerr () ;
  fprintf (stderr, ": [") ;
  lexing_prerr_position (lexing_fstpos_get ()) ;
  fprintf (stderr, "]\n") ;
  exit (1) ; // HX: no error recovery yet; maybe in future
  return ;
} /* end of [yyerror] */

yyres_t
yyparse_main (
  ats_int_type tok0
) {
/*
** HX: we must take care of garbage collection!
*/
  // fprintf (stderr, "yyparse_main: &yyss = %p\n", &yyss) ;
  // ATS_GC_MARKROOT (&yyss, sizeof(short*)) ; // [ats_malloc_ngc] is used
  // fprintf (stderr, "yyparse_main: &yyvs = %p\n", &yyvs) ;
  // ATS_GC_MARKROOT (&yyvs, sizeof(YYSTYPE*)) ;  // [ats_malloc_ngc] is used
/*
** HX-2010-02-25:
** if BISON is used then [yyval] is a stack variable and
** thus there is no need to treat it as a GC root explicitly
*/
//
#ifndef _ATS_YYVALISLOCAL
  extern YYSTYPE yyval;
  // fprintf (stderr, "yyparse_main: &yyval = %p\n", &yyval) ;
  ATS_GC_MARKROOT (&yyval, sizeof(YYSTYPE)) ;
#endif // end of [_ATS_YYVALISLOCAL]
//
  extern YYSTYPE yylval;
  // fprintf (stderr, "yyparse_main: &yylval = %p\n", &yylval) ;
  ATS_GC_MARKROOT (&yylval, sizeof(YYSTYPE)) ;
//
#ifdef YYPATCH
#if (YYPATCH >= 20101229)
  // fprintf (stderr, "yyparse_main: &yystack = %p\n", &yystack) ;
  ATS_GC_MARKROOT (&yystack, sizeof(YYSTACKDATA)) ;
#endif
#endif
//
  yylex_tok0 = tok0 ;
//
  yyparse () ;
//
  return theYYVALyyres ;
} /* end of [yyparse_main] */

/* ****** ****** */

// end of [ats_grammar.yats]

