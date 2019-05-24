/***********************************************************************/
/*                                                                     */
/*                         Applied Type System                         */
/*                                                                     */
/*                              Hongwei Xi                             */
/*                                                                     */
/***********************************************************************/

/*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 */

/* ****** ****** */

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

/* ats_grammar.mly: the grammar for the ATS programming language */

%{

open Ats_misc
open Ats_syntax

module Fil = Ats_filename
module Fix = Ats_fixity
module Lab = Ats_label
module Loc = Ats_location
module Sym = Ats_symbol

%}

/* literal constants */

%token EOF

%token <string> ALPHANUM  /* letter identifier */
%token <string> SYMBOLIC /* symbolic identifier */
%token <string> ARRAYIDENT /* array identifier */
%token <string> TEMPLATEIDENT /* array identifier */
%token <char> Lchar /* char literal */
%token <string> Lfloat /* float literal */
%token <Big_int.big_int> Lint /* integer literal */
%token <Big_int.big_int> Llint /* long integer literal */
%token <Big_int.big_int> Luint /* unsigned integer literal */
%token <Big_int.big_int> Lulint /* unsigned long integer literal */
%token <string> Lstring /* string literal */
%token <int * string> Lextern /* external code: front or end */

/* keywords */

%token ABSPROP
%token ABSTYPE ABST0YPE
%token ABSVIEW
%token ABSVIEWTYPE ABSVIEWT0YPE
%token AND
%token AS /* AS pattern */
%token ASSUME /* local binding for abstract static constants */
%token BEGIN BREAK
%token CASE CASEPLUS CASEMINUS /* pattern matching */
%token CASTFN
%token CLASS /* object-oriented programming */
%token CONTINUE
%token DATAPROP DATAPROPLT /* dataprop declaration */
%token DATASORT /* datasort declaration */
%token DATATYPE DATATYPELT /* datatype declaration */
%token DATAVIEW DATAVIEWLT /* dataview declaration */
%token DATAVIEWTYPE DATAVIEWTYPELT /* dataviewtype declaration */
%token DYN /* dynamic definition */
%token DYNLOAD /* dynamic loading */
%token ELSE
%token END
%token EXCEPTION
%token EXTERN
%token EXPORT /* exporting constants */
%token FIX /* fixed point operator */
%token FN /* function declaration: non-recursive */
%token FNSTAR /* function declaration: tail-recursive */
%token FUN /* function declaration: recursive */
%token FOR FORSTAR /* for loop */
%token IF
%token IMPLEMENT /* implementing a dynamic constant */
%token IN
%token INCLUDE
%token INFIX /* fixity introduction: no association */
%token INFIXL /* fixity introduction: left association */
%token INFIXR /* fixity introduction: right association */
%token LAM LAMPARA /* lambda abstraction */
%token LAZYCASE LAZYIF LAZYVAL
%token LET
%token LLAM /* linear lambda abstraction */
%token LOAD /* loading files */
%token LOCAL /* local declaration */
%token MACDEF /* simple macro definition */
%token MACRODEF /* regular macro definition */
%token METHOD METHODSTAR /* method declaration and definition */
%token MODPROP /* module props */
%token MODTYPE /* module types */
%token MODULE /* module declaration */
%token NONFIX /* fixity revocation */
%token OBJECT /* object declaration */
%token OF OP
%token OVERLOAD
%token PAR
%token POSTFIX
%token PREFIX
%token PROPDEF PROPPLUS PROPMINUS
%token PRAXI PRFN PRFUN PRVAL
%token REC /* recursion */
%token SIF /* static conditional */
%token SORTDEF /* sort definition */
%token STA
%token STALOAD /* static loading */
%token STADEF /* static definition */
%token STAVAR /* static existential variable */
%token STRUCT /* C-style struct */
%token SYMELIM SYMINTR
%token SUPER
%token THEN
%token TRY /* handling exceptions */
%token TYPEDEF
%token TYPEPLUS TYPEMINUS
%token T0YPE T0YPEPLUS T0YPEMINUS
%token VIEWT0YPE VIEWT0YPEPLUS VIEWT0YPEMINUS
%token UNION /* C-style union */
%token VAL VALPLUS VALMINUS
%token VALBANG VALBANGPLUS VALBANGMINUS
%token VAR VARSTAR
%token VIEWDEF VIEWPLUS VIEWMINUS
%token VIEWTYPEDEF VIEWTYPEPLUS VIEWTYPEMINUS
%token WHEN WHERE
%token WHILE WHILESTAR
%token WITH
%token WITHPROP /* prop annotations */
%token WITHTYPE /* type annotations */
%token WITHVIEW /* view annotations */
%token WITHVIEWTYPE /* viewtype annotations */

%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LBRACE RBRACE
%token QUOTELPAREN
%token QUOTELBRACKET
%token QUOTELBRACE
%token AMPER
%token BACKQUOTE BACKSLASH
%token BANG BAR COMMA SEMICOLON
%token COLON COLONLT COLONLTGT
%token DOT DOLLAR EQ QUOTE HASH TILDA
%token EQGT EQLT EQLTGT
%token EQGTGT EQSLASHEQGT EQSLASHEQGTGT
%token LT GT GTLT DOTLT GTDOT DOTLTGTDOT
%token ATLPAREN ATLBRACE ATLBRACKET
%token DOLLARLPAREN DOLLARLBRACKET DOLLARLBRACE
%token HASHLPAREN HASHLBRACE HASHLBRACKET
%token DOTDOT DOTDOTDOT
%token MINUSGT MINUSLT MINUSLTGT
%token SHARPDEFINE SHARPUNDEFINE
%token SHARPIF SHARPTHEN
%token SHARPELSE SHARPELSIF SHARPENDIF
%token SHARPERROR SHARPPRINT
%token SHARPINCLUDE
%token DOLLAREXEC /* code execution for meta-programming */
%token DOLLAREXTYPE /* external type */
%token DOLLAREXTVAL /* external value */
%token DOLLARDELAY DOLLARFORCE
%token DOLLARDYNLOAD
%token DOLLAREFFMASK_ALL DOLLAREFFMASK_EXN DOLLAREFFMASK_REF
%token DOLLARFOLD DOLLARUNFOLD
%token DOLLARPARALLEL /* parallel evaluation */
%token DOLLARRAISE /* raising exceptions */
%token DOLLARTYPEOF
%token DOLLARARRT DOLLARARRVT
%token DOLLARLSTT DOLLARLSTVT
%token DOLLARRECT DOLLARRECVT
%token DOLLARTUPT DOLLARTUPVT
%token DOLLARENCRYPT DOLLARDECRYPT
%token FOLDAT FREEAT VIEWAT

/* macro syntax */

%token BACKQUOTELPAREN
%token COMMALPAREN

/* meta-programming syntax */

%token BARMINUS
%token BACKQUOTELBRACKET
%token COMMALBRACKET

/* distributed meta-programming syntax */

%token BARMINUSLBRACKET
%token BACKQUOTELBRACE
%token COMMALBRACE

/* precedence */

%nonassoc PATAS PATFREE PATREF
%nonassoc SEXPLAM DEXPFIX DEXPLAM
%nonassoc COLONLT COLONLTGT
%nonassoc DEXPCOLON
%right COLON  /* support: <dexp> : <sexp> : <srt> */
%nonassoc SEXPEXI SEXPUNI
%nonassoc CLAS
%nonassoc WHERE
%nonassoc DEXPCASE DEXPFOR DEXPIF DEXPRAISE DEXPTRY DEXPWHILE
%nonassoc ELSE
%nonassoc BARSEQNONE
%nonassoc BAR

%nonassoc DIDALPHANUM
%nonassoc EQ

%nonassoc DARRINDSEQ
%nonassoc SARRINDSEQ
%nonassoc LBRACKET

%nonassoc GT
%nonassoc GTLT
%nonassoc TMPARGSEXPSEQ

%type <Ats_syntax.dec list> sdecseqeof
%type <Ats_syntax.dec list> ddecseqeof
%type <Ats_syntax.dexp> dexpeof

%start sdecseqeof ddecseqeof dexpeof

%%

sdecseqeof: sdecseq EOF			{ $1 }
;

ddecseqeof: ddecseq EOF			{ $1 }
;

semicolonseq:
  | /* empty */                         { () }
  | semicolonseq SEMICOLON              { () }
;

d0ec:
  /* fixity introduction and elimination */
  | INFIX prec idseq    		{ dec_infix $2 Fix.N $3 }
  | INFIXL prec idseq  			{ dec_infix $2 Fix.L $3 }
  | INFIXR prec idseq  			{ dec_infix $2 Fix.R $3 }
  | POSTFIX prec idseq               	{ dec_postfix $2 $3 }
  | PREFIX prec idseq                	{ dec_prefix $2 $3 }
  | NONFIX idseq                        { dec_nonfix $2 }
  /* overloaded symbol introduction and elimination */
  | SYMINTR idseq                       { dec_symintr $2 }
  | SYMELIM idseq                       { dec_symelim $2 }
  /* sort declarations */
  | SORTDEF srtdefdecseq		{ dec_srtdefs $2 }
  | DATASORT datsrtdecseq		{ dec_datsrts $2 }
   /* static constant and constructor declaration */
  | STA stacstseq			{ dec_stacsts $2 }
  | STAVAR stavarseq                    { dec_stavars $2 }
   /* abstract constant declaration */
  | ABSPROP staconseq		        { dec_absprops $2 }
  | ABSTYPE staconseq		        { dec_abstypes $2 }
  | ABST0YPE staconseq		        { dec_abst0ypes $2 }
  | ABSVIEW staconseq		        { dec_absviews $2 }
  | ABSVIEWTYPE staconseq		{ dec_absviewtypes $2 } 
  | ABSVIEWT0YPE staconseq		{ dec_absviewt0ypes $2 }
 /* static declarations */
  | STADEF sexpdefdecseq                { dec_sexpdefs $2 }
  | PROPDEF sexpdefdecseq               { dec_propdefs $2 }
  | TYPEDEF sexpdefdecseq               { dec_typedefs $2 }
/*
  | TYPEDEF REC sexpdefdecseq           { dec_typedefrecs $3 }
*/
  | VIEWDEF sexpdefdecseq               { dec_viewdefs $2 }
  | VIEWTYPEDEF sexpdefdecseq           { dec_viewtypedefs $2 }
/*
  | VIEWTYPEDEF REC sexpdefdecseq       { dec_viewtypedefrecs $3 }
*/
  | datakind datdecseq sexpdefdecseqopt	{ dec_data $1 $2 $3 }
  | EXCEPTION exndecseq			{ dec_exns $2 }
  | MODPROP mtdecseq			{ dec_modtypes true $2 }
  | MODTYPE mtdecseq			{ dec_modtypes false $2 }
  | ASSUME saspdecseq			{ dec_sasps $2 }
  /* ****** ****** */
  | SHARPDEFINE id e0xpopt              { dec_e0xpdef $2 $3 }
  | SHARPERROR e0xp                     { dec_e0xperr $2 }
  | SHARPPRINT e0xp                     { dec_e0xpprt $2 }
  /* overload declaration */
  | OVERLOAD did WITH doqid             { dec_overload $2 $4 }
  | OVERLOAD LBRACKET RBRACKET WITH doqid /* overload [] with ... */
                                        { dec_overload_brackets $5 }
  /* macro declarations */
  | MACDEF macdefdecseq			{ dec_macdefs true $2 }
  | MACRODEF macdefdecseq		{ dec_macdefs false $2 }
  /* statically loading file */
  | STALOAD filename                    { dec_staload None $2 }
  | STALOAD sid EQ filename		{ dec_staload (Some $2) $4 }
  /* external code */
  | Lextern                             { dec_extern $1 }

d1ec:
  /* variable declaration */
  | VAR vardecseq			{ dec_vars true  (*stack*) $2 }
  | VARSTAR vardecseq			{ dec_vars false (*stack*) $2 }
  /* dynamic value declarations */
  | valkind valdecseq                   { dec_vals $1 $2 }
  | VAL PAR valdecseq                   { dec_valpars $3 }
  | VAL REC valdecseq                   { dec_valrecs $3 }
  /* dynamic function declarations */
  | funkind decargseq fundecseq		{ dec_funs $1 $2 $3 }
  | MODULE decargseq moddecseq		{ dec_mods $2 $3 }
  /* local declarations */
  | LOCAL ddecseq IN ddecseq END        { dec_local $2 $4 }
  /* dynamic implementations */
  | IMPLEMENT decsargseqseq impldecseq	{ dec_impls $2 $3 }
  /* including file */
  | SHARPINCLUDE filename               { dec_include 1(*dyn*) $2 }
  /* dynamically loading file */
  | DYNLOAD filename			{ dec_dynload $2 }
;

sdec:
  | d0ec				{ $1 }
   /* dynamic constant declaration */
  | VAL decargseq dyncstextseq          { dec_dyncsts DCKval $2 $3 }
  | FUN decargseq dyncstextseq          { dec_dyncsts DCKfun $2 $3 }
  | CASTFN dyncstseq                    { dec_dyncsts DCKcastfn [] $2 }
  | PRVAL dyncstseq			{ dec_dyncsts DCKprval [] $2 }
  | PRFUN dyncstseq			{ dec_dyncsts DCKprfun [] $2 }
  | PRAXI dyncstseq			{ dec_dyncsts DCKpraxi [] $2 }
  | SHARPIF sdeccondthenelse            { dec_ifthenelse $2 }
  /* including file */
  | SHARPINCLUDE filename               { dec_include 0(*sta*) $2 }
  | LOCAL sdecseq IN sdecseq END        { dec_local $2 $4 }
;

sdecthen:
  | sdecseq                             { $1 }
  | SHARPTHEN sdecseq                   { $2 }
;

sdeccondthenelse:
  | e0xp sdecthen SHARPENDIF            { ($1, $2) :: [] }
  | e0xp sdecthen SHARPELSE sdecseq SHARPENDIF
                                        { ($1, $2) :: [ (e0xp_true, $4) ] }
  | e0xp sdecthen SHARPELSIF sdeccondthenelse
                                        { ($1, $2) :: $4 }
;

sdecseq:
  | /* empty */				{ [] }
  | sdec semicolonseq sdecseq		{ $1 :: $3 }
;

ddec:
  | d0ec				{ $1 }
  | d1ec				{ $1 }
  | EXTERN TYPEDEF Lstring EQ sexp      { dec_extype $3 $5 }
  | EXTERN VAL Lstring EQ dexp          { dec_extval $3 $5 }
  | EXTERN VAL decargseq dyncstextseq	{ dec_dyncsts DCKval $3 $4 }
  | EXTERN FUN decargseq dyncstextseq	{ dec_dyncsts DCKfun $3 $4 }
  | EXTERN CASTFN dyncstseq             { dec_dyncsts DCKcastfn [] $3 }
  | EXTERN PRVAL dyncstseq		{ dec_dyncsts DCKprval [] $3 }
  | EXTERN PRFUN dyncstseq		{ dec_dyncsts DCKprfun [] $3 }
  | EXTERN PRAXI dyncstseq		{ dec_dyncsts DCKpraxi [] $3 }
  | SHARPIF ddecthenelse                { dec_ifthenelse $2 }
;

ddecthenelse:
  | e0xp SHARPTHEN ddecseq SHARPENDIF   { ($1, $3) :: [] }
  | e0xp SHARPTHEN ddecseq SHARPELSE ddecseq SHARPENDIF
                                        { ($1, $3) :: [ (e0xp_true, $5) ] }
  | e0xp SHARPTHEN ddecseq SHARPELSIF ddecthenelse
                                        { ($1, $3) :: $5 }
;

ddecseq: /* declaration sequence */
  | /* empty */				{ [] }
  | ddec semicolonseq ddecseq   	{ $1 :: $3 }
;

/* ****** ****** */

id: /* identifier */
  | ALPHANUM                            { make_id_with_string $1 }
  | SYMBOLIC                            { make_id_with_string $1 }
  | AMPER				{ make_id_with_symbol Sym.symAMPER }
  | BANG				{ make_id_with_symbol Sym.symBANG }
  | EQ                                  { make_id_with_symbol Sym.symEQ }
  | GT                                  { make_id_with_symbol Sym.symGT }
  | LT                                  { make_id_with_symbol Sym.symLT }
  | MINUSGT                           	{ make_id_with_symbol Sym.symMINUSGT }
  | TILDA                               { make_id_with_symbol Sym.symTILDA }
;

idseq: /* identifier sequence */
  | /* empty */				{ [] }
  | id idseq				{ $1 :: $2 }
;

lab: /* label */
  | ALPHANUM                            { Lab.make_with_string $1 }
  | SYMBOLIC                            { Lab.make_with_string $1 }
  | Lint                                { Lab.make_with_intinf $1 } 
  | LPAREN lab RPAREN			{ $2 }
;

filename: /* filename */
  | Lstring                             { Fil.filename_make $1 }
;

fileid: /* file identifier */
  | ALPHANUM                            { Sym.make_with_string $1 }
;

arrayid: /* array identifier */
  | ARRAYIDENT                          { Sym.make_with_string $1 }
;

tmpid: /* template identifier */
  | TEMPLATEIDENT                       { Sym.make_with_string $1 }
;

/* syntax for simple expressions */

ate0xp:
  | Lint				{ e0xp_int $1 }
  | Lchar                               { e0xp_char $1 }
  | Lfloat                              { e0xp_float $1 }
  | Lstring                             { e0xp_str $1 }
  | id					{ e0xp_id $1 }
  | LPAREN e0xpseq RPAREN               { e0xp_list $2 }
;

arge0xpseq:
  | /* empty */                         { [] }
  | ate0xp arge0xpseq                   { $1 :: $2 }
;

e0xp:
  | ate0xp arge0xpseq                   { e0xp_apps $1 $2 }
;

commae0xpseq:
  | /* empty */                         { [] }
  | COMMA e0xp commae0xpseq             { $2 :: $3 }
;
  
e0xpseq:
  | /* empty */                         { [] }
  | e0xp commae0xpseq                   { $1 :: $2 }
;

e0xpopt:
  | /* empty */                         { None }
  | e0xp                                { Some $1 }

/* syntax for sorts */

srtqual:
  | DOLLAR filename DOT	                { STQ_filedot $2 }
  | DOLLAR fileid DOT  		        { STQ_symdot $2 }
; 

srtid: /* sort identifier */
  | ALPHANUM                            { make_srt_id_with_string $1 }
  | SYMBOLIC                            { make_srt_id_with_string $1 }
  | T0YPE                               { make_srt_id_with_symbol Sym.symT0YPE }
  | VIEWT0YPE                           { make_srt_id_with_symbol Sym.symVIEWT0YPE }
  | MINUSGT                             { make_srt_id_with_symbol Sym.symMINUSGT }
;

srtidseq:
  | /* empty */                         { [] }
  | srtid commasrtidseq                 { $1 :: $2 }
;

commasrtidseq:
  | /* empty */                         { [] }
  | COMMA srtid commasrtidseq           { $2 :: $3 }
;  

srtqid: /* qualified sort identifier */
  | srtqual srtid			{ ($1, $2) }
;

squal: /* static qualifier */
  | DOLLAR filename DOT                    { SQ_filedot $2 }
  | DOLLAR fileid DOT                      { SQ_symdot $2 }
  | DOLLAR srtid COLON			   { SQ_symcolon (sym_of_srt_id $2) }
; 

atsrt: /* atomic sort */
  | srtid                               { srt_id $1 }
  | srtqid                              { srt_qid $1 }
  | LPAREN srtseq RPAREN                { srt_list $2 }
  | QUOTELPAREN srtseq RPAREN           { srt_tup $2 }
;

atsrtseq: /* atomic sort sequence */
  | /* empty */				{ [] }
  | atsrt atsrtseq			{ $1 :: $2 }
;

srt: /* sort */
  | atsrt atsrtseq                      { srt_apps $1 $2 }
;

srtseq:
  | /* empty */				{ [] }
  | srt commasrtseq			{ $1 :: $2 }
;

commasrtseq:
  | /* empty */                         { [] }
  | COMMA srt commasrtseq               { $2 :: $3 }
;

prec: /* precedence */
  | /* empty */				{ PRECint intinf_zero }
  | Lint                                { PRECint $1 }
  | LPAREN id RPAREN			{ PRECopr ($2) }
;

/* sort with polarity */

srtpol:
  | srt                                 { ($1, 0) }
  | PROPPLUS                            { (srt_prop, 1) }
  | PROPMINUS                           { (srt_prop, -1) }
  | TYPEPLUS                            { (srt_type, 1) }
  | TYPEMINUS                           { (srt_type, -1) }
  | T0YPEPLUS                           { (srt_t0ype, 1) }
  | T0YPEMINUS                          { (srt_t0ype, -1) }
  | VIEWPLUS                            { (srt_view, 1) }
  | VIEWMINUS                           { (srt_view, -1) }
  | VIEWTYPEPLUS                        { (srt_viewtype, 1) }
  | VIEWTYPEMINUS                       { (srt_viewtype, -1) }
  | VIEWT0YPEPLUS                      { (srt_viewt0ype, 1) }
  | VIEWT0YPEMINUS                     { (srt_viewt0ype, -1) }
;

srtarg:
  | srtid				{ $1 }
;

commasrtargseq:
  | /* empty */				{ [] }
  | COMMA srtarg srtargseq		{ $2 :: $3 }
;

srtargseq:
  | srtarg				{ [$1] }
  | LPAREN srtarg commasrtargseq RPAREN { $2 :: $3 }
;

srtargseqseq:
  | /* empty */				{ [] }
  | srtargseq srtargseqseq		{ $1 :: $2 }
;

colonsrtopt: /* optional sort annotation */
  | /* empty */				{ None }
  | COLON srt				{ Some $2 }
;

sarg: /* static variable with optional sort annotation */
  | sid colonsrtopt			{ ($1, $2) }
;

commasargseq:
  | /* empty */                         { [] }
  | COMMA sarg commasargseq             { $2 :: $3 }
;

sargseq: /* static variable sequence */
  | /* empty */				{ [] }
  | sarg commasargseq			{ $1 :: $2 }
;

sargseqseq: /* static variables sequence */
  | /* empty */                         { [] }
  | sid sargseqseq			{ [ ($1, None) ] :: $2 }
  | LPAREN sargseq RPAREN sargseqseq	{ $2 :: $4 }
;

decarg:
  | LBRACE squaseq RBRACE               { $2 }
;

decargseq:
  | /* empty */                         { [] }
  | decarg decargseq                    { $1 :: $2 }
;

decsargseqseq:
  | /* empty */                         { [] }
  | LBRACE sargseq RBRACE decsargseqseq	{ $2 :: $4 }
;

/* datasort declaration */

datsrtdec: /* datasort declaration */
  | srtid EQ datsrtconseq               { dec_datsrt $1 None $3 }
  | srtid srtargseq EQ datsrtconseq     { dec_datsrt $1 (Some $2) $4 }
;

anddatsrtdecseq: /* additional datasort declarations */
  | /* empty */                         { [] }
  | AND datsrtdec anddatsrtdecseq       { $2 :: $3 }
;

datsrtdecseq: /* datasort declarations */
  | datsrtdec anddatsrtdecseq           { $1 :: $2 }
;

datsrtcon: /* constructor associated with datasort */
  | sid 	                        { datsrtcon $1 None }
  | sid OF srt	                        { datsrtcon $1 (Some $3) }
;

bardatsrtconseq: /* additional constructors associated with datasort */
  | /* empty */                         { [] }
  | BAR datsrtcon bardatsrtconseq       { $2 :: $3 }
;

datsrtconseq: /* constructors associated with datasort */
  | bardatsrtconseq                     { $1 }
  | datsrtcon bardatsrtconseq           { $1 :: $2 }
;

/* abstract constant declaration */

sid: /* static identifier */
  | ALPHANUM                            { make_sid_with_string $1 }
  | SYMBOLIC                            { make_sid_with_string $1 }
  | AMPER                               { make_sid_with_symbol Sym.symAMPER }
  | BANG                                { make_sid_with_symbol Sym.symBANG }
  | GT                                  { make_sid_with_symbol Sym.symGT }
  | LT                                  { make_sid_with_symbol Sym.symLT }
  | GTLT                                { make_sid_with_symbol Sym.symGTLT }
  | MINUSGT                           	{ make_sid_with_symbol Sym.symMINUSGT }
  | TILDA                               { make_sid_with_symbol Sym.symTILDA }
;

sqid:
  | squal sid                           { ($1, $2) }
;

soqid:
  | sid                                 { (None, $1) }
  | squal sid 	                        { (Some $1, $2) }
;

schar: /* static integer */
  | Lchar                               { $1 }
;

sint: /* static integer */
  | Lint                                { $1 }
;

/* ****** ****** */

efftag: /* identifier */
  | BANG ALPHANUM                       { efftag_cst $2 }
  | ALPHANUM                            { efftag_var $1 }
  | FUN                                 { efftag_var "fun" }
  | sint                                { efftag_int $1 }
;

commaefftagseq:
  | /* empty */				{ [] }
  | COMMA efftag commaefftagseq         { $2 :: $3 }
;

efftagseq: /* identifier sequence */
  | /* empty */				{ [] }
  | efftag commaefftagseq               { $1 :: $2 }
;

colonwith:
  | COLON                               { None }
  | COLONLTGT                           { Some [] }
  | COLONLT efftagseq GT                { Some $2 }
;

/* ****** ****** */

atsexp: /* atomic static expression */
  | sid                                 { sexp_id $1 }
  | OP sid                              { sexp_op $2 }
  | sqid                                { sexp_qid $1 }
  | soqid HASHLBRACE sexprec RBRACE     { sexp_mod $1 $3 }
  | DOLLAREXTYPE Lstring                { sexp_extype $2 }
  | schar                               { sexp_char $1 }
  | sint                                { sexp_int $1 }
  | LPAREN sexpseq RPAREN               { sexp_list $2 }
  | LPAREN sexpseq BAR sexpseq RPAREN   { sexp_list2 $2 $4 }

  | ATLBRACE sexprec RBRACE             { sexp_tyrec true (* is_flat *) $2 }
  | QUOTELBRACE sexprec RBRACE          { sexp_tyrec false (* is_flat *) $2 }

  | ATLPAREN sexpseq RPAREN             { sexp_tytup true (* is_flat *) $2 }
  | QUOTELPAREN sexpseq RPAREN          { sexp_tytup false (* is_flat *) $2 }

  | ATLPAREN sexpseq BAR sexpseq RPAREN { sexp_tytup2 true (* is_flat *) $2 $4 }
  | QUOTELPAREN sexpseq BAR sexpseq RPAREN
                                        { sexp_tytup2 false (* is_flat *) $2 $4 }

  | ATLBRACKET sexp RBRACKET LBRACKET sarrindseq
                                        { sexp_tyarr $2 $5 }
  | STRUCT LBRACE sexprec RBRACE        { sexp_struct $3 } 
  | UNION atsexp LBRACE sexprec RBRACE  { sexp_union $2 $4 }
  | MINUSLT efftagseq GT                { sexp_imp $2 }
  | MINUSLTGT                           { sexp_imp [] }
;

argsexp:
  | atsexp                              { $1 }
  | LAM sargseqseq colonsrtopt EQGT sexp %prec SEXPLAM
					{ sexp_lams $2 $3 $5 }
  | LBRACKET squaseq RBRACKET sexp %prec SEXPEXI
					{ sexp_exi $2 $4 }
  | LBRACE squaseq RBRACE sexp %prec SEXPUNI
					{ sexp_uni $2 $4 }
;

argsexpseq:
  | argsexp				{ [$1] }
  | atsexp argsexpseq			{ $1 :: $2 }
;

appsexp: /* static application */
  | atsexp argsexpseq                   { sexp_apps $1 $2 }
;

sarrindseq:
  | sexpseq RBRACKET %prec SARRINDSEQ   { [$1] }
  | sexpseq RBRACKET LBRACKET sarrindseq
                                        { $1 :: $4 }
;

tmpsexpseqseq:
  | tmpsexpseq                          { [$1] }
  | tmpsexpseq GTLT tmpsexpseqseq       { $1 :: $3 }
;

tmpsexpseq:
  | tmpsexp commatmpsexpseq             { $1 :: $2 }
;

commatmpsexpseq:
  | /* empty */                         { [] }
  | COMMA tmpsexp commatmpsexpseq       { $2 :: $3 }
;

tmpargsexpseq:
  | /* empty */	%prec TMPARGSEXPSEQ     { [] }
  | atsexp tmpargsexpseq                { $1 :: $2 }
;

tmpsexp:
  | atsexp tmpargsexpseq                { sexp_apps $1 $2 }
;


sexp: /* static expression */
  | argsexp                             { $1 }
  | appsexp				{ $1 }
  | sexp COLON srt			{ sexp_ann $1 $3 }
;

commasexpseq:
  | /* empty */				{ [] }
  | COMMA sexp commasexpseq		{ $2 :: $3 }
;

sexpseq:
  | /* empty */                         { [] }
  | sexp commasexpseq			{ $1 :: $2 }
;

labsexp: /* labelled static expression */
  | lab EQ sexp                         { ($1, None, $3) }
  | arrayid sarrindseq EQ sexp          { (Lab.make_with_symbol $1, Some $2, $4) }
;

commasexprec:
  | /* empty */                         { [] }
  | COMMA labsexp commasexprec		{ $2 :: $3 }
;

sexprec: /* static expressions row */
  | /* empty */                         { [] }
  | labsexp commasexprec		{ $1 :: $2 }
;

commasidseq:
  | /* empty */				{ [] }
  | COMMA sid commasidseq		{ $2 :: $3 }
;

sidseq:
  | sid commasidseq			{ $1 :: $2 }
;

squa: /* static context item */
  | argsexp				{ SQprop $1 }
  | appsexp                             { SQprop $1 }
  | sidseq COLON srtext                 { SQvars ($1, $3) }
;

semibarsquaseq:
  | /* empty */                         { [] }
  | SEMICOLON squa semibarsquaseq	{ $2 :: $3 }
  | BAR squa semibarsquaseq             { $2 :: $3 }
;

squaseq: /* static context item sequence */
  | /* empty */				{ squas [] }
  | squa semibarsquaseq                 { squas ($1 :: $2) }
;

barsexpseq:
  | /* empty */                         { [] }
  | BAR sexp barsexpseq                 { $2 :: $3}  
  | SEMICOLON sexp barsexpseq           { $2 :: $3}  
;

srtext: /* extended sort (sort and subset sort) */
  | srt                                 { srtext_srt $1 }
  | LBRACE sid COLON srtext BAR sexp barsexpseq RBRACE
                                        { srtext_sub $2 $4 ($6 :: $7) }
;

sexparg:
  | DOTDOT                              { SEXPARGone }
  | DOTDOTDOT                           { SEXPARGall }
  | sexpseq                             { SEXPARGseq $1 }
;

/* loop invariant */

loopinvqua:
  | /* empty */                         { None }
  | LBRACE squaseq RBRACE               { Some $2 }
;

loopinvmet:
  | /* empty */				{ None }
  | DOTLT sexpseq GTDOT			{ Some $2 }
  | DOTLTGTDOT			        { Some [] }
;

loopinvarg:
  | did COLON                           { ($1, None) }
  | did COLON sexp                      { ($1, Some $3) }
;

commaloopinvargseq:
  | /* empty */                         { [] }
  | COMMA loopinvarg commaloopinvargseq { $2 :: $3 }
;

loopinvargseq:
  | /* empty */                         { [] }
  | loopinvarg commaloopinvargseq       { $1 :: $2 }
;

loopinvargstate:
  | LPAREN loopinvargseq RPAREN         { $2 }
;

loopinvresqua:
  | /* empty */                         { None }
  | LBRACKET squaseq RBRACKET           { Some $2 }
;

loopinvresstate:
  | /* empty */                         { None }
  | COLON loopinvresqua LPAREN loopinvargseq RPAREN
                                        { Some ($2, $4) }
;

loopinv: /* invariant for <while> and <for> loops */
  | loopinvqua loopinvmet loopinvargstate loopinvresstate
			  		{ loopinv $1 $2 $3 $4 }
;

srtdefdec:
  | srtid srtargseqseq EQ srtext        { dec_srtdef $1 $2 $4 }
;

andsrtdefdecseq:
  | /* empty */                         { [] }
  | AND srtdefdec andsrtdefdecseq       { $2 :: $3 }
;

srtdefdecseq:
  | srtdefdec andsrtdefdecseq           { $1 :: $2 }
;

/* prop/type/view/viewtype constructor arguments */

datakind:
  | DATAPROP                            { (DKprop, []) }
  | DATAPROPLT srtidseq GT              { (DKprop, $2) }
  | DATATYPE                            { (DKtype, []) }
  | DATATYPELT srtidseq GT              { (DKtype, $2) }
  | DATAVIEW                            { (DKview, []) }
  | DATAVIEWLT srtidseq GT              { (DKview, $2) }
  | DATAVIEWTYPE                        { (DKviewtype, []) }
  | DATAVIEWTYPELT srtidseq GT          { (DKviewtype, $2) }
;

datarg:
  | srtpol                              { datarg_srt $1 }
  | sid COLON srtpol                    { datarg_id_srt $1 $3 }
;

commadatargseq:
  | /* empty */                          { [] }
  | COMMA datarg commadatargseq         { $2 :: $3 }
;

datargseq:
  | /* empty */                         { [] }
  | datarg commadatargseq               { $1 :: $2 }
;

/* abstract constructor declaration */

stacon:
  | sid                                 { ($1, None, None) }
  | sid LPAREN datargseq RPAREN         { ($1, Some $3, None) }
  | sid EQ sexp                         { ($1, None, Some $3) }
  | sid LPAREN datargseq RPAREN EQ sexp { ($1, Some $3, Some $6) }
;

andstaconseq:
  | /* empty */				{ [] }
  | AND stacon andstaconseq	        { $2 :: $3 }
;

staconseq:
  | stacon andstaconseq		        { $1 :: $2 }
;

stacst:
  | sid stacstargseq COLON srt          { dec_stacst $1 $2 $4 }
;
 
andstacstseq:
  | /* empty */                         { [] }
  | AND stacst andstacstseq             { $2 :: $3 }
;

stacstseq:
  | stacst andstacstseq                 { $1 :: $2 }
;

stacstarg:
  | LPAREN srtseq RPAREN                { $2 }
;

stacstargseq:
  | /* empty */                         { [] }
  | stacstarg stacstargseq              { $1 :: $2 }
;

stavar:
  | sid COLON srt                       { dec_stavar $1 $3 }
;

andstavarseq:
  | /* empty */                         { [] }
  | AND stavar andstavarseq             { $2 :: $3 }
;

stavarseq:
  | stavar andstavarseq                 { $1 :: $2 }
;

did: /* dynamic identifier */
  | ALPHANUM %prec DIDALPHANUM		{ make_did_with_string $1 }
  | SYMBOLIC                            { make_did_with_string $1 }
  | UNION                               { make_did_with_string "union" }
  | BANG				{ make_did_with_symbol Sym.symBANG }
  | BACKSLASH                           { make_did_with_symbol Sym.symBACKSLASH }
  | EQ		                        { make_did_with_symbol Sym.symEQ }
  | GT                                  { make_did_with_symbol Sym.symGT }
  | LT                                  { make_did_with_symbol Sym.symLT }
  | TILDA                               { make_did_with_symbol Sym.symTILDA }
;

arraydid: /* dynamic array identifier */
  | arrayid                             { make_did_with_symbol $1 }
;

tmpdid: /* dynamic template identifier */ 
  | tmpid                               { make_did_with_symbol $1 }
;

pid:
  | ALPHANUM                            { make_did_with_string $1 }
  | SYMBOLIC                            { make_did_with_string $1 }
;

dfarg0: /* dynamic variable with optional type annotation */
  | pid			                { dfarg0 $1 None }
  | pid COLON sexp			{ dfarg0 $1 (Some $3) }
;

commadfarg0seq:
  | /* empty */                         { [] }
  | COMMA dfarg0 commadfarg0seq      { $2 :: $3 }
;

dfarg0seq: /* static variable sequence */
  | /* empty */				{ [] }
  | dfarg0 commadfarg0seq		{ $1 :: $2 }
;

farg0:
  | pid					{ farg0dyn [(dfarg0 $1 None)] }
  | LPAREN dfarg0seq RPAREN		{ farg0dyn $2 }
  | LPAREN dfarg0seq BAR dfarg0seq RPAREN
                                        { farg0dyn2 $2 $4 }
  | LBRACE squaseq RBRACE		{ farg0sta $2 }
;

farg0seq: /* dynamic variables sequence */
  | /* empty */                         { [] }
  | farg0 farg0seq			{ $1 :: $2 }
;

dyncst:
  | did farg0seq colonwith sexp		{ dec_dyncst $1 $2 $3 $4 None }
;

anddyncstseq:
  | /* empty */                         { [] }
  | AND dyncst anddyncstseq           { $2 :: $3 }
;

dyncstseq:
  | dyncst anddyncstseq               { $1 :: $2 }
;

externopt :
  | /* none */                        { None }
  | EQ Lstring                        { Some $2 }
;

dyncstext:
  | did farg0seq colonwith sexp externopt
                                      { dec_dyncst $1 $2 $3 $4 $5 }
;

anddyncstextseq:
  | /* empty */                       { [] }
  | AND dyncstext anddyncstextseq     { $2 :: $3 }
;

dyncstextseq:
  | dyncstext anddyncstextseq         { $1 :: $2 }
;

/* static definition declaration */

sexpdefdec:
  | sid sargseqseq colonsrtopt EQ sexp	{ dec_sexpdef $1 $2 $3 $5 }
;

andsexpdefdecseq:
  | /* empty */				{ [] }
  | AND sexpdefdec andsexpdefdecseq	{ $2 :: $3 }
;

sexpdefdecseq:
  | sexpdefdec andsexpdefdecseq		{ $1 :: $2 }
;

/* dataprop/type/view/viewtype declarations */

conquaseq: /* quantifiers */
  | /* empty */                         { [] }
  | LBRACE squaseq RBRACE conquaseq     { $2 :: $4 }
;

conresopt: /* type indexes are optional */
  | /* empty */                         { None }
  | LPAREN sexpseq RPAREN               { Some $2 }
;

conargopt: /* arguments are optional */
  | /* empty */                         { None }
  | OF sexp                             { Some $2 }
;

datcon:
  | conquaseq did conresopt conargopt   { datcon $2 $1 $4 $3 }
;

bardatconseq:
  | /* empty */                         { [] }
  | BAR datcon bardatconseq		{ $2 :: $3 }
;

datconseq: /* the first bar is optional */
  | bardatconseq                	{ $1 }
  | datcon bardatconseq 		{ $1 :: $2 }
;

datdec:
  | sid EQ datconseq	                { dec_dat $1 None $3 }
  | sid LPAREN datargseq RPAREN EQ datconseq
				        { dec_dat $1 (Some $3) $6 }
;

anddatdecseq:
  | /* empty */                         { [] }
  | AND datdec anddatdecseq		{ $2 :: $3 }
;

datdecseq:
  | datdec anddatdecseq 		{ $1 :: $2 }
;

sexpdefdecseqopt:
  | /* empty */                         { [] }
  | WHERE sexpdefdecseq                 { $2 }
;

/* exception constructor declaration */

exndec:
  | conquaseq did conargopt             { dec_exn $2 $1 $3 }

andexndecseq:
  | /* empty */                         { [] }
  | AND exndec andexndecseq             { $2 :: $3 }
;

exndecseq:
  | exndec andexndecseq                 { $1 :: $2 }
;

/* module types */

mtdec:
  | sid EQ LBRACE mtitemdecseq RBRACE   { dec_modtype $1 $4 }
;

andmtdecseq:
  | /* empty */                         { [] }
  | AND mtdec andmtdecseq		{ $2 :: $3 }
;

mtdecseq:
  | mtdec andmtdecseq			{ $1 :: $2 }
;

mtitemdec:
  | STA sid COLON srt                   { mtitemdec_sta $2 $4 }
  | VAL did farg0seq colonwith sexp	{ mtitemdec_val false $2 $3 $4 $5 }
  | PRVAL did farg0seq colonwith sexp	{ mtitemdec_val true $2 $3 $4 $5 }
  | STADEF sexpdefdecseq                { mtitemdec_sexpdefs $2 }
  | TYPEDEF sexpdefdecseq               { mtitemdec_typedefs $2 }
  | TYPEDEF REC sexpdefdecseq           { mtitemdec_typedefrecs $3 }
;

mtitemdecseq:
  | /* empty */                         { [] }
  | mtitemdec mtitemdecseq		{ $1 :: $2 }
;

/* static assumption */

saspdec:
  | soqid sargseqseq colonsrtopt EQ sexp
					{ dec_sasp $1 $2 $3 $5 }
;

andsaspdecseq:
  | /* empty */                         { [] }
  | AND saspdec andsaspdecseq           { $2 :: $3 }

saspdecseq:
  | saspdec andsaspdecseq               { $1 :: $2 }
;

/* dynamic expressions */

dqual: /* dynamic qualifier */
  | DOLLAR sid COLON                 	{ DQ_symcolon (sym_of_sid $2) }
  | DOLLAR filename DOT                 { DQ_filedot $2 }
  | DOLLAR filename DOLLAR sid COLON	{ DQ_filedot_symcolon ($2, $4) }
  | DOLLAR fileid DOT                   { DQ_symdot $2 }
  | DOLLAR fileid DOLLAR sid COLON	{ DQ_symdot_symcolon ($2, $4) }
; 

dqid:
  | dqual did                         	{ ($1, $2) }
;

doqid:
  | did                                 { (None, $1) }
  | dqual did                         	{ (Some $1, $2) }
;

tmpdoqid:
  | tmpdid                              { (None, $1) }
  | dqual tmpdid                        { (Some $1, $2) }
;

selop:
  | DOT                                 { 0 }
  | MINUSGT                             { 1 }
;

atdexp:
  | Lchar				{ dexp_char $1 }
  | Lint				{ dexp_int IKint $1 }
  | Llint				{ dexp_int IKlint $1 }
  | Luint				{ dexp_int IKuint $1 }
  | Lulint				{ dexp_int IKulint $1 }
  | Lfloat                              { dexp_float $1 }
  | Lstring                             { dexp_string $1 }
  | BREAK                               { dexp_loopexn 0 }
  | CONTINUE                            { dexp_loopexn 1 }
  | did					{ dexp_id $1 }
  | dqid 				{ dexp_qid $1 }
  | OP did				{ dexp_op $2 }
  | selop lab                           { dexp_sel_lab $1 $2 }
  | selop LBRACKET darrindseq           { dexp_sel_ind $1 $3 }
  | selop arrayid darrindseq            { dexp_sel_lab_ind $1 (Lab.make_with_symbol $2) $3 }
  | AMPER atdexp			{ dexp_ptrof $2 }
  | arraydid darrindseq                 { dexp_arrsub (dexp_id $1) $2 }
  | tmpdoqid tmpsexpseqseq GT           { dexp_template $1 $2 }
  | HASH ALPHANUM EQ Lstring            { dexp_parse $2 $4 }
  | LET ddecseq IN dexpsemiseq1 END	{ dexp_let $2 (dexp_seq $4) }
  | LPAREN dexpcommaseq RPAREN	        { dexp_list $2 }
  | LPAREN dexpcommaseq BAR dexpcommaseq RPAREN
                                        { dexp_list2 $2 $4 }
  | LPAREN dexpsemiseq2 RPAREN          { dexp_seq $2 }
  | BEGIN dexpsemiseq1 END              { dexp_seq $2 }
  | HASHLBRACKET sexparg BAR dexp RBRACKET
                                        { dexp_exi $2 $4 }

  | QUOTELBRACKET dexpcommaseq RBRACKET	{ dexp_lst $2 } /* list */

  | ATLBRACE dexprow RBRACE             { dexp_rec true (* is_flat *) $2 }
  | QUOTELBRACE dexprow RBRACE          { dexp_rec false (* is_flat *) $2 }

  | ATLPAREN dexpcommaseq RPAREN        { dexp_tup true (* is_flat *) $2 }
  | QUOTELPAREN dexpcommaseq RPAREN  	{ dexp_tup false (* is_flat *) $2 }
  | ATLPAREN dexpcommaseq BAR dexpcommaseq RPAREN
                                        { dexp_tup2 true (* is_flat *) $2 $4 }
  | QUOTELPAREN dexpcommaseq BAR dexpcommaseq RPAREN
                                        { dexp_tup2 false (* is_flat *) $2 $4 }
  | ATLBRACKET sexp RBRACKET LBRACKET dexpcommaseq RBRACKET
                                        { dexp_arr $2 $5 } /* array */
  | STRUCT LBRACE dexprow RBRACE        { dexp_struct $3 } /* structure */
  | BACKQUOTELPAREN dexp RPAREN         { dexp_enmac $2 }
  | COMMALPAREN dexp RPAREN             { dexp_demac $2 }
  | DOLLAREXTVAL LPAREN sexp COMMA Lstring RPAREN
                                        { dexp_extval $3 $5 }
  | DOLLARFOLD LPAREN soqid COMMA dexp RPAREN
			                { dexp_fold $3 $5 }
  | DOLLARUNFOLD LPAREN soqid COMMA dexp RPAREN
			                { dexp_unfold $3 $5 }
  | FOLDAT sargdexpseq atdexp           { dexp_foldat $2 $3 }
  | FREEAT sargdexpseq atdexp           { dexp_freeat $2 $3 }
  | VIEWAT atdexp                       { dexp_viewat $2 }
    /* lazy evaluation */
  | DOLLARDELAY atdexp                  { dexp_delay $2 }
    /* dynamic loading */
  | DOLLARDYNLOAD atdexp                { dexp_dynload $2 }
    /* masking effects */
  | DOLLAREFFMASK_ALL atdexp            { dexp_effmask EFFall $2 }
  | DOLLAREFFMASK_EXN atdexp            { dexp_effmask EFFexn $2 }
  | DOLLAREFFMASK_REF atdexp            { dexp_effmask EFFref $2 }
    /* encrypt/decrypt */
  | DOLLARENCRYPT atdexp                { dexp_crypt ( 1)(*encrypt*) $2 }
  | DOLLARDECRYPT atdexp                { dexp_crypt (-1)(*decrypt*) $2 }
;

sargdexp:
  | LBRACE sexparg RBRACE               { $2 }
;

sargdexpseq:
  | /* empty */				{ [] }
  | sargdexp sargdexpseq                { $1 :: $2 }
;

argdexp:
  | atdexp				{ $1 }
  | sargdexp                            { dexp_sexparg $1 }
;

argdexpseq:
  | /* empty */				{ [] }
  | argdexp argdexpseq                  { $1 :: $2 }
;

darrindseq:
  | dexpcommaseq RBRACKET %prec DARRINDSEQ
                                        { [$1] }
  | dexpcommaseq RBRACKET LBRACKET darrindseq
                                        { $1 :: $4 }
;

farg1:
  | LBRACE squaseq RBRACE               { fargsta1 $2 }
  | atpat				{ fargdyn $1 }
  | DOTLT sexpseq GTDOT                 { fargmet $2 }
  | DOTLTGTDOT                          { fargmet [] }
;

farg1seq:
  | /* empty */                         { [] }
  | farg1 farg1seq			{ $1 :: $2 }
;

farg2:
  | LBRACE sargseq RBRACE               { fargsta2 $2 }
  | atpat				{ fargdyn $1 }
  | DOTLT sexpseq GTDOT                 { fargmet $2 }
  | DOTLTGTDOT                          { fargmet [] }
;

farg2seq:
  | /* empty */                         { [] }
  | farg2 farg2seq			{ $1 :: $2 }
;

funarrow:
  | EQGT                                { None }
  | EQLTGT                              { Some [] }
  | EQLT efftagseq GT                   { Some $2 }
;

colonsexpopt: /* optional prop/type annotation */
  | /* empty */				{ None }
  | COLON sexp			        { Some $2 }
;

colonwithsexpopt: /* optional prop/type annotation */
  | /* empty */				{ None }
  | colonwith sexp			{ Some ($1, $2) }
;

casehead:
  | CASE                                { 0 }
  | CASEPLUS                            { 1 }
  | CASEMINUS                           { -1 }
;

caseinv:
  | /* empty */                         { None }
  | loopinvresstate EQGT                { $1 }
;

forhead:
  | FOR                                 { None }
  | FORSTAR loopinv                     { Some $2 }
;

whilehead:
  | WHILE                               { None }
  | WHILESTAR loopinv EQGT              { Some $2 }
;

dexp:
  | atdexp argdexpseq			{ dexp_apps $1 $2 }
  | IF caseinv dexp THEN dexp %prec DEXPIF
                                        { dexp_if $2 $3 $5 None }
  | IF caseinv dexp THEN dexp ELSE dexp %prec DEXPIF
			   		{ dexp_if $2 $3 $5 (Some $7) }
  | SIF sexp THEN dexp ELSE dexp %prec DEXPIF
                                        { dexp_sif $2 $4 $6 }

  | casehead caseinv dexp OF claseq %prec DEXPCASE
                                        { dexp_case $1 $2 $3 $5 }
  | LAM farg1seq colonsexpopt funarrow dexp %prec DEXPLAM
					{ dexp_lam false $2 $3 $4 $5 }
  | LLAM farg1seq colonsexpopt funarrow dexp %prec DEXPLAM
					{ dexp_lam true $2 $3 $4 $5 }
  | LAMPARA farg1seq colonsexpopt EQGT dexp %prec DEXPLAM
                                        { dexp_lamparas $2 $3 $5 }
  | FIX did farg1seq colonsexpopt funarrow dexp %prec DEXPFIX
                                        { dexp_fix $2 $3 $4 $5 $6 }
  | forhead initestpost dexp %prec DEXPFOR
                                        { dexp_for $1 $2 $3 }
  | forhead initestpost LBRACE dexpsemiseq1 RBRACE
				 	{ dexp_for $1 $2 (dexp_seq $4) }
  | DOLLARRAISE dexp %prec DEXPRAISE    { dexp_raise $2 }

  | TRY dexpsemiseq1 WITH claseq %prec DEXPTRY
				        { dexp_trywith (dexp_seq $2) $4 }
  | whilehead atdexp dexp %prec DEXPWHILE
                                        { dexp_while $1 $2 $3 }
  | whilehead atdexp LBRACE dexpsemiseq1 RBRACE
					{ dexp_while $1 $2 (dexp_seq $4) }
  | MODULE LBRACE moditemdecseq RBRACE  { dexp_mod $3 }
  | dexp COLON sexp %prec DEXPCOLON
                                        { dexp_ann_type $1 $3 }
  | dexp WHERE BEGIN ddecseq END	{ dexp_where $1 $4 }
  | dexp WHERE LBRACE ddecseq RBRACE	{ dexp_where $1 $4 }
;

commadexpseq:
  | /* empty */				{ [] }
  | COMMA dexp commadexpseq		{ $2 :: $3 }
;

dexpcommaseq:
  | /* empty */				{ [] }
  | dexp commadexpseq			{ $1 :: $2 }
;

dexpsemiseq1:
  | dexp SEMICOLON dexpsemiseq1         { $1 :: $3 }
  | dexp                                { [$1] }
  | /* empty */                         { [dexp_empty ()] }
;

dexpsemiseq2:
  | dexp SEMICOLON dexpsemiseq1         { $1 :: $3 }
;

labdexp:
  | lab EQ dexp                         { ($1, $3) }
;

commadexprow:
  | /* empty */                         { [] }
  | COMMA labdexp commadexprow		{ $2 :: $3 }
;

dexprow:
  | /* empty */                         { [] }
  | labdexp commadexprow		{ $1 :: $2 }
;

initestpost: /* for loop triple */
  | LPAREN dexpcommaseq SEMICOLON dexpcommaseq SEMICOLON dexpcommaseq RPAREN
					{ (dexp_seq $2, dexp_seq $4, dexp_seq $6) }
;

dexpeof:
  | dexp EOF				{ $1 }
;

/* patterns */

pqid:
  | dqual pid                         	{ ($1, $2) }
;

atpat:
  | pid                                 { pat_id $1 } /* value variable */
  | pqid                                { pat_qid $1 } /* constructor */
  | BANG pid                            { pat_ref $2 } /* reference variable */
  | OP did				{ pat_op $2 }
  | Lchar                               { pat_char $1 }
  | Lint				{ pat_int $1 }
  | Lstring                             { pat_string $1 }

  | LPAREN patseq RPAREN                { pat_list $2 }
  | LPAREN patseq BAR patseq RPAREN     { pat_list2 $2 $4 }

  | QUOTELBRACKET patseq RBRACKET	{ pat_lst $2 }

  | ATLBRACE patrow RBRACE              { pat_rec true (* is_flat *) $2 }
  | QUOTELBRACE patrow RBRACE           { pat_rec false (* is_flat *) $2 }

  | ATLPAREN patseq RPAREN              { pat_tup true (* is_flat *) $2 }
  | QUOTELPAREN patseq RPAREN           { pat_tup false (* is_flat *) $2 }

  | ATLPAREN patseq BAR patseq RPAREN   { pat_tup2 true (* is_flat *) $2 $4 }
  | QUOTELPAREN patseq BAR patseq RPAREN
                                        { pat_tup2 false (* is_flat *) $2 $4 }

  | LBRACKET sargseq RBRACKET atpat     { pat_exi $2 $4 }
;

argpat:
  | atpat				{ $1 }
  | LBRACE DOTDOT RBRACE                { pat_svararg (SVARARGone) }
  | LBRACE DOTDOTDOT RBRACE             { pat_svararg (SVARARGall) }
  | LBRACE sargseq RBRACE               { pat_svararg (SVARARGseq $2) }
;

argpatseq:
  | /* empty */				{ [] }
  | argpat argpatseq                    { $1 :: $2 }
;

pat:
  | pat COLON sexp			{ pat_ann $1 $3 }
  | atpat argpatseq                     { pat_apps $1 $2 }
  | pid AS pat %prec PATAS		{ pat_as $1 $3 }
  | BANG pid AS pat %prec PATAS		{ pat_refas $2 $4 }
  | TILDA pat %prec PATFREE             { pat_free $2 }
;

commapatseq:
  | /* empty */				{ [] }
  | COMMA pat commapatseq		{ $2 :: $3 }
;

patseq:
  | /* empty */				{ [] }
  | pat commapatseq			{ $1 :: $2 }
;

labpat:
  | lab EQ pat				{ ($1, $3) }
;

commapatrow:
  | /* empty */				{ (0, []) }
  | COMMA DOTDOTDOT                     { (1, [])  }
  | COMMA labpat commapatrow		{ patrow_cons $2 $3 }
;

patrow:
  | /* empty */                         { (0, []) }
  | DOTDOTDOT                           { (1, []) }
  | labpat commapatrow			{ patrow_cons $1 $2 }
;

/* pattern matching clauses */

patguaopt:
  | pat                                 { ($1, None) }
  | pat WHEN dexp                       { ($1, Some $3) }
;

cla:
  | patguaopt EQGT dexp %prec CLAS      { cla $1 false false $3 }
  | patguaopt EQGTGT dexp %prec CLAS    { cla $1 true false $3 }
  | pat EQSLASHEQGT dexp %prec CLAS     { cla ($1, None) false true $3 }
  | pat EQSLASHEQGTGT dexp %prec CLAS   { cla ($1, None) true true $3 }
;

barclaseq:
  | /* empty */	%prec BARSEQNONE	{ [] }
  | BAR cla barclaseq			{ $2 :: $3 }
;

claseq:
  | barclaseq				{ $1 }
  | cla barclaseq			{ $1 :: $2 }
;

/* macro declartions */

macvar:
  | pid					{ $1 }
;

commamacvarseq:
  | /* empty */				{ [] }
  | COMMA macvar commamacvarseq		{ $2 :: $3 }
;

macvarseq:
  | /* empty */				{ [] }
  | macvar commamacvarseq		{ $1 :: $2 }
;

macvarseqseq:
  | /* empty */				{ [] }
  | macvar macvarseqseq			{ [$1] :: $2 }
  | LPAREN macvarseq RPAREN macvarseqseq
                                        { $2 :: $4 }
;

macdefdec:
  | did macvarseqseq EQ dexp            { dec_macdef $1 $2 $4 }
;

andmacdefdecseq:
  | /* empty */                         { [] }
  | AND macdefdec andmacdefdecseq       { $2 :: $3 }
; 

macdefdecseq:
  | macdefdec andmacdefdecseq           { $1 :: $2 }
;

/* variable declaration */

vardec:
  | did COLON sexp			{ dec_var $1 (Some $3) None }
  | did EQ dexp                         { dec_var $1 None (Some $3) }
  | did COLON sexp EQ dexp		{ dec_var $1 (Some $3) (Some $5) }
;

andvardecseq:
  | /* empty */				{ [] }
  | AND vardec andvardecseq		{ $2 :: $3 }
;

vardecseq:
  | vardec andvardecseq			{ $1 :: $2 }
;

/* dynamic value declaration */

withtypeopt:
  | /* empty */				{ None }
  | WITHPROP sexp			{ Some ($2, srt_prop) }
  | WITHTYPE sexp			{ Some ($2, srt_type) }
  | WITHVIEW sexp			{ Some ($2, srt_view) }
  | WITHVIEWTYPE sexp			{ Some ($2, srt_viewtype) }
;

valkind:
  | VAL                                 { VKval }
  | VALMINUS                            { VKvalminus }
  | VALPLUS                             { VKvalplus }
  | PRVAL                               { VKprval }
;

valdec:
  | pat EQ dexp withtypeopt             { dec_val $1 $3 $4 }
;

andvaldecseq:
  | /* empty */                         { [] }
  | AND valdec andvaldecseq             { $2 :: $3 }
;

valdecseq:
  | valdec andvaldecseq                 { $1 :: $2 }
;

funkind:
  | FN /* non-recursive */              { (FKfn, []) }
  | FNSTAR /* tail-recursive */         { (FKfnt, []) }
  | FUN /* general recursive */         { (FKfun, []) }
  | PRFN                                { (FKprfn, []) }
  | PRFUN                               { (FKprfun, []) }
;

funid:
  | did					{ $1 }
  | OP did				{ $2 }
;

fundec:
  | funid farg1seq colonwithsexpopt EQ dexp withtypeopt
					{ dec_fun $1 $2 $3 $5 $6 }
;

andfundecseq:
  | /* empty */				{ [] }
  | AND fundec andfundecseq		{ $2 :: $3 }
;

fundecseq:
  | fundec andfundecseq			{ $1 :: $2 }
;

/* module declaration */

moditemdec:
  /* infixity declarations */
  | INFIX prec idseq    		{ moditemdec_infix $2 Fix.N $3 }
  | INFIXL prec idseq  			{ moditemdec_infix $2 Fix.L $3 }
  | INFIXR prec idseq  			{ moditemdec_infix $2 Fix.R $3 }
  | POSTFIX prec idseq               	{ moditemdec_postfix $2 $3 }
  | PREFIX prec idseq                	{ moditemdec_prefix $2 $3 }
  | NONFIX idseq                        { moditemdec_nonfix $2 }
  /* static declarations */
  | STADEF sexpdefdecseq                { moditemdec_sexpdefs $2 }
  | TYPEDEF sexpdefdecseq               { moditemdec_typedefs $2 }
  | TYPEDEF REC sexpdefdecseq           { moditemdec_typedefrecs $3 }
  /* dynamic declarations */
  | valkind valdecseq                   { moditemdec_vals $1 $2 }
  | VAL REC valdecseq                   { moditemdec_valrecs $3 }
  | funkind fundecseq			{ moditemdec_funs $1 $2 }
;

moditemdecseq:
  | /* empty */				{ [] }
  | moditemdec moditemdecseq 		{ $1 :: $2 }
;

moddec:
  | did farg1seq colonwithsexpopt EQ LBRACE moditemdecseq RBRACE withtypeopt
                                        { dec_mod $1 $2 $3 $6 $8 }
;

andmoddecseq:
  | /* empty */                         { [] }
  | AND moddec andmoddecseq             { $2 :: $3 }
;

moddecseq:
  | moddec andmoddecseq                 { $1 :: $2 }
;

/* dynamic implementation */

implid:
  | doqid				{ ($1, []) }
  | tmpdoqid tmpsexpseqseq GT           { ($1, $2) }
;

impldec:
  | implid farg2seq colonsexpopt EQ dexp
                                        { dec_impl $1 $2 $3 $5 }
;

andimpldecseq:
  | /* empty */                         { [] }
  | AND impldec andimpldecseq           { $2 :: $3 }
;

impldecseq:
  | impldec andimpldecseq               { $1 :: $2 }
;

/* ****** ****** */

/* end of [ats_grammar.mly] */
