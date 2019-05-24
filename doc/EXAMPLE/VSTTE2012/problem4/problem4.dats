(*
**
** VSTTE 2012 Verification Competition
**
** Problem 4
**
** HX: All VTs are done.
**
*)

(* ****** ****** *)
//
staload "libats/SATS/ilistp.sats"
//
stadef nil = ilist_nil
stadef cons = ilist_cons
stadef sing = ilist_sing
//
(* ****** ****** *)

propdef ISCONS (xs:ilist) = ISEMP (xs, false)

(* ****** ****** *)

prfn
append_sing
  {x:int}{xs:ilist}
  (): APPEND (sing(x), xs, cons (x, xs)) = APPENDcons (APPENDnil)
// end of [append_sing]

propdef
REMOVE
  (xs:ilist, ys:ilist, zs:ilist) = APPEND (ys, zs, xs)
// end of [REMOVE]

extern
prfun
lemma_remove2
  {xs:ilist}{ys:ilist}{zs:ilist}{zs1:ilist}{zs2:ilist} (
  pf1: REMOVE (xs, ys, zs), pf2: REMOVE (zs, zs1, zs2)
) : [yszs1:ilist] (APPEND (ys, zs1, yszs1), REMOVE (xs, yszs1, zs2))

(* ****** ****** *)

datasort tree =
 | leaf of () | node of (tree, tree)
// end of [tree]

dataprop
treq (tree, tree) =
  | treq_leaf (leaf, leaf)
  | {t11,t12:tree}{t21,t22:tree}
    treq_node (node (t11, t12), node (t21, t22)) of (treq (t11, t21), treq (t12, t22))
// end of [treq]

dataprop TREQ (tree, tree) = {t:tree} TREQ (t, t) of ()

prfun treq_elim
  {t1,t2:tree} .<t1>. (pf: treq (t1, t2)): TREQ (t1, t2) =
  case+ pf of
  | treq_leaf () => TREQ ()
  | treq_node (pf1, pf2) => let
      prval TREQ () = treq_elim (pf1)
      prval TREQ () = treq_elim (pf2)
    in
      TREQ ()
    end // end of [treq_node]
// end of [treq_elim]

extern
prfun treq_symm {t1,t2:tree} (pf: treq (t1, t2)): treq (t2, t1)

dataprop
trsz (tree, int) =
  | trsz_leaf (leaf, 0)
  | {t1,t2:tree}{n1,n2:nat}
    trsz_node (node(t1, t2), n1+n2+1) of (trsz (t1, n1), trsz (t2, n2))
// end of [trsz]

extern
prfun trsz_istot {t:tree} (): [n:nat] trsz (t, n)
extern
prfun trsz_isfun {t:tree}{n1,n2:nat}
  (pf1: trsz (t, n1), pf2: trsz (t, n2)): [n1==n2] void

(* ****** ****** *)

datatype tree (tree) =
 | tleaf (leaf) of ()
 | {t1,t2:tree} tnode (node (t1,t2)) of (tree t1, tree t2)
// end of [tree]

(* ****** ****** *)

dataprop
TL (int, tree, ilist) =
 | {d:int}
   TLleaf (d, leaf, cons (d, nil)) of int(d)
 | {d:int} {t1,t2:tree} {xs1,xs2,xs3:ilist}
   TLnode (d, node (t1, t2), xs3) of (
     TL (d+1,t1,xs1), TL (d+1,t2, xs2), APPEND (xs1, xs2, xs3)
   ) // end [TLcons]
// end of [TL]

propdef TL0 (t:tree, xs:ilist) = TL (0, t, xs)

(* ****** ****** *)

prfun
lemma_tl_listpos
  {d:int}{t:tree}{xs:ilist} .<t>.
  (pftl: TL (d, t, xs)): [x:int;xs1:ilist | x >= d] ILISTEQ (xs, cons(x, xs1)) =
  case+ pftl of
  | TLleaf _ => ILISTEQ ()
  | TLnode (pf1tl, _, pfapp) => let
      prval ILISTEQ () = lemma_tl_listpos (pf1tl)
      prval APPENDcons _ = pfapp
    in
      ILISTEQ ()
    end // end of [TLnode]
// end of [lemma_tl_listpos]

(* ****** ****** *)

dataprop
NTL (d:int, xs: ilist) =
  NTL (d, xs) of {t:tree} TL (d, t, xs) -<prf> [false] void
// end of [NTL]

dataprop
PREFIX (xs: ilist, ys: ilist) =
  {xs2:ilist} PREFIX (xs, ys) of APPEND (xs, xs2, ys)
// end of [PREFIX]

dataprop
NTLP (d:int, xs:ilist) =
  NTLP (d, xs) of {t:tree}{fs:ilist} (PREFIX (fs, xs), TL (d, t, fs)) -<prf> [false] void
// end of [NTLP]

(* ****** ****** *)

extern
prfun
lemma_prefix_trans {xs1,xs2,xs3:ilist}
  (pf1: PREFIX (xs1, xs2), pf2: PREFIX (xs2, xs3)): PREFIX (xs1, xs3)
// end of [lemma_prefix_trans]


dataprop OR (P1: prop, P2: prop) =
  | ORleft (P1, P2) of P1 | ORright (P1, P2) of P2
// end of [OR]

extern
prfun lemma_prefix_prefix
  {xs1,xs2,xs3:ilist} (
  pf1: PREFIX (xs1, xs3), pf2: PREFIX (xs2, xs3)
) : OR (PREFIX (xs1, xs2), PREFIX (xs2, xs1))

extern
prfun lemma_remove_remove_prefix
  {xs:ilist}{fs0,rs0:ilist}{fs,fs2:ilist} (
  pf1: REMOVE (xs, fs0, rs0)
, pf2: REMOVE (fs, fs0, fs2)
, pf3: PREFIX (fs, xs)
) : PREFIX (fs2, rs0)

(* ****** ****** *)

prfun
TL_tree_isfun
  {d:int}{t:tree}{xs1,xs2:ilist} .<t>. (
  pf1: TL (d, t, xs1), pf2: TL (d, t, xs2)
) : ILISTEQ (xs1, xs2) =
  case+ (pf1, pf2) of
  | (TLleaf _, TLleaf _) => ILISTEQ ()
  | (TLnode (pf11, pf12, pf1app),
     TLnode (pf21, pf22, pf2app)) => let
      prval ILISTEQ () = TL_tree_isfun (pf11, pf21)
      prval ILISTEQ () = TL_tree_isfun (pf12, pf22)
    in
      append_isfun (pf1app, pf2app)
    end // end of [TLnode, TLnode]
// end of [TL_tree_isfun]

(* ****** ****** *)

prfun
lemma_tl_ntl_false
  {d:int}{xs:ilist}{t:tree} .<>. (
  pftl: TL (d, t, xs), pfntl: NTL (d, xs)
) : [false] void = let
  prval NTL (fpf) = pfntl in fpf (pftl)
end // end of [lemma_tl_ntl_false]

(* ****** ****** *)

prfun lemma_tl_nil_false
  {d:nat} {t:tree} .<t>.
  (pftl: TL (d, t, nil)): [false] void =
  case+ pftl of
  | TLleaf _ => ()
  | TLnode (
      pf1tl, pf2tl, pfapp
    ) => let
      prval APPENDnil () = pfapp in lemma_tl_nil_false (pf1tl)
    end // end of [TLnode]
// end of [lemma_tl_nil_false]

prfn lemma_ntlp_nil
  {d:nat} (): NTLP (d, nil) =
  NTLP {d,nil} (
    lam (pfpre, pftl) => let
      prval PREFIX pfapp = pfpre
      prval APPENDnil () = pfapp
    in
      lemma_tl_nil_false (pftl)
    end
  ) // end of [NTLP]
// end of [lemma_ntlp_nil]

(* ****** ****** *)

prfun lemma_tl_less_false
  {d:nat} {t:tree}
  {x:int | x < d} {xs:ilist} .<t>.
  (pftl: TL (d, t, cons (x, xs))): [false] void =
  case+ pftl of
  | TLleaf _ => ()
  | TLnode (
      pf1tl, pf2tl, pfapp
    ) => let
      prval ILISTEQ () = lemma_tl_listpos (pf1tl)
      prval APPENDcons _ = pfapp
    in
      lemma_tl_less_false (pf1tl)
    end // end of [TLnode]
// end of [lemma_tl_less_false]

(* ****** ****** *)

prfn lemma_ntlp_less
  {d0:nat}
  {x:int | x < d0}
  {xs:ilist}
  (): NTLP (d0, cons (x, xs)) =
  NTLP {d0,cons(x,xs)} (
    lam (pfpre, pftl) => let
      prval PREFIX pfapp = pfpre
    in
      case+ pfapp of
      | APPENDnil () => lemma_tl_nil_false (pftl)
      | APPENDcons _ => lemma_tl_less_false (pftl)
    end (* end of [lam] *)
  ) // end of [NTLP]
// end of [lemma_ntlp_less]

(* ****** ****** *)

prfun lemma_tl_prefix_trsz
  {d:int}
  {t1,t2:tree}
  {xs1,xs2:ilist}
  {n1,n2:nat} .<n1+n2>. (
  pf1sz: trsz (t1, n1), pf2sz: trsz (t2, n2)
, pf1tl: TL (d, t1, xs1), pf2tl: TL (d, t2, xs2)
, pfpre: PREFIX (xs1, xs2)
) : treq (t1, t2) =
  case+ pf1tl of
  | TLnode {d}{t11,t12}{fs11,fs12,fs1} (pf11tl, pf12tl, pf1app) => (
    case+ pf2tl of
    | TLnode {d}{t21,t22}{fs21,fs22,fs2} (pf21tl, pf22tl, pf2app) => let
        prval trsz_node (pf11sz, pf12sz) = pf1sz
        prval trsz_node (pf21sz, pf22sz) = pf2sz
        prval pf1pre = PREFIX (pf1app)
        prval pf1_treq = let
          prval pfor = lemma_prefix_prefix (lemma_prefix_trans (pf1pre, pfpre), PREFIX pf2app)
        in
          case+ pfor of
          | ORleft pfpre => // fs11 <= fs21
              lemma_tl_prefix_trsz (pf11sz, pf21sz, pf11tl, pf21tl, pfpre)
          | ORright pfpre =>
              treq_symm (lemma_tl_prefix_trsz (pf21sz, pf11sz, pf21tl, pf11tl, pfpre))
        end : treq (t11, t21)
        prval TREQ () = treq_elim (pf1_treq)
        prval ILISTEQ () = TL_tree_isfun (pf11tl, pf21tl)
        prval pf2pre = lemma_remove_remove_prefix (pf2app, pf1app, pfpre)
        prval pf2_treq = lemma_tl_prefix_trsz (pf12sz, pf22sz, pf12tl, pf22tl, pf2pre)
      in
        treq_node (pf1_treq, pf2_treq)
      end // end of [TLnode]
    | TLleaf (d) =/=> let
        prval pf11len = length_istot {fs11} ()
        prval ILISTEQ () = lemma_tl_listpos (pf11tl)
        prval LENGTHcons _ = pf11len
        prval pf12len = length_istot {fs12} ()
        prval ILISTEQ () = lemma_tl_listpos (pf12tl)
        prval LENGTHcons _ = pf12len
        prval pflen1 = append_length_lemma (pf1app, pf11len, pf12len)
        prval PREFIX pfapp = pfpre
        prval pflen2 = append_length_lemma (pfapp, pflen1, length_istot ())
        prval LENGTHcons (LENGTHnil ()) = pflen2
      in
        // nothing
      end // end of [TLnode]
    ) // end of [TLnode]
  | TLleaf (d) => (
    case+ pf2tl of
    | TLnode (pf21tl, pf22tl, pf2app) =/=> let
        prval PREFIX pfapp = pfpre
        prval APPENDcons _ = pfapp
        prval ILISTEQ () = lemma_tl_listpos (pf21tl)
        prval APPENDcons _ = pf2app
      in
        // nothing
      end // end of [TLnode]
    | TLleaf (d) => treq_leaf ()
    ) // end of [TLleaf]
// end of [lemma_tl_prefix_trsz]

prfn lemma_tl_prefix
  {d:int}
  {t1,t2:tree}
  {xs1,xs2:ilist} (
  pf1tl: TL (d, t1, xs1), pf2tl: TL (d, t2, xs2)
, pfpre: PREFIX (xs1, xs2)
) : treq (t1, t2) = lemma_tl_prefix_trsz (
  trsz_istot (), trsz_istot (), pf1tl, pf2tl, pfpre
) // end of [lemma_tl_prefix]

(* ****** ****** *)

prfn lemma_ntlp_fst
  {d:nat}
  {x:int | x > d}{xs:ilist}
  (pfntlp: NTLP (d+1, cons (x, xs))): NTLP (d, cons (x, xs)) = let
  prfn fpf {t:tree}{fs:ilist}
    (pfpre: PREFIX (fs, cons (x, xs)), pftl: TL (d, t, fs)): [false] void = let
    prval PREFIX (pfapp) = pfpre
  in
    case+ pftl of
    | TLnode (pf1tl, pf2tl, pf1app) => let
        prval pf1pre = PREFIX (pf1app)
        prval pf1pre_xs = lemma_prefix_trans (pf1pre, pfpre)
        prval NTLP (fpf1) = pfntlp
      in
        fpf1 (pf1pre_xs, pf1tl)
      end // end of [TLnode]
    | TLleaf (d) =/=> let
        prval APPENDcons _ = pfapp in (*nothing*)
      end // end of [TLleaf]
  end // end of [fpf]
in
  NTLP (fpf)
end // end of [lemma_ntlp_fst]

prfn lemma_ntlp_snd
  {d:nat}
  {xs:ilist}{t0:tree}{fs0,rs0:ilist} (
  pfrem0: REMOVE (xs, fs0, rs0), pftl0: TL (d+1, t0, fs0), pfntlp: NTLP (d+1, rs0)
) : NTLP (d, xs) = let
  prfn fpf {t:tree}{fs:ilist}
    (pfpre: PREFIX (fs, xs), pftl: TL (d, t, fs)): [false] void = let
    prval PREFIX (pfapp) = pfpre
  in
    case+ pftl of
    | TLnode
        {d}{t1,t2}{fs1,fs2,fs}
        (pf1tl, pf2tl, pf1app) => let
        prval pf1pre = PREFIX pf1app
        prval ILISTEQ () = let
          prval pfor = lemma_prefix_prefix (PREFIX pfrem0, lemma_prefix_trans (pf1pre, pfpre))
        in
          case+ pfor of
          | ORleft pfpre => let
              prval TREQ () = treq_elim (lemma_tl_prefix (pftl0, pf1tl, pfpre))
            in
              TL_tree_isfun (pftl0, pf1tl)
            end
          | ORright pfpre => let
              prval TREQ () = treq_elim (lemma_tl_prefix (pf1tl, pftl0, pfpre))
            in
              TL_tree_isfun (pftl0, pf1tl)
            end
        end : ILISTEQ (fs0, fs1)
        prval pf2pre = lemma_remove_remove_prefix (pfrem0, pf1app, pfpre)
        prval NTLP (fpf1) = pfntlp
      in
        fpf1 {..}{fs2} (pf2pre, pf2tl)
      end // end of [TLnode]
    | TLleaf (d) => let
        prval ILISTEQ () = lemma_tl_listpos (pftl0)
        prval APPENDcons _ = pfrem0
        prval APPENDcons _ = pfapp
      in
        (*nothing*)
      end // end of [TLleaf]
  end // end of [fpf]
in
  NTLP (fpf)
end // end of [lemma_ntlp_snd]

(* ****** ****** *)

prfun lemma_ntl_remainder
  {d:nat}{xs:ilist}{t:tree}{fs,rs:ilist} .<>. (
  pfrem: REMOVE (xs, fs, rs), pftl: TL (d, t, fs), pfpos: ISCONS (rs)
) : NTL (d, xs) = let
  prfn fpf {t1:tree}
    (pf1tl: TL (d, t1, xs)): [false] void = let
    prval pf_treq = lemma_tl_prefix (pftl, pf1tl, PREFIX pfrem)
    prval TREQ () = treq_elim (pf_treq)
    prval pflen_fs = length_istot {fs} ()
    prval pflen_rs = length_istot {rs} ()
    prval ILISTEQ () = TL_tree_isfun (pftl, pf1tl)
    prval ISEMPcons () = pfpos
    prval LENGTHcons _ = pflen_rs
    prval pflen_xs = append_length_lemma (pfrem, pflen_fs, pflen_rs)
    prval () = length_isfun (pflen_fs, pflen_xs)
  in
    // nothing
  end // end of [fpf]
in
  NTL (fpf)
end // end of [lemma_ntl_remainder]

(* ****** ****** *)
//
abstype list (ilist)
//
extern
fun list_is_empty {xs: ilist}
  (xs: list xs):<> [b: bool] (ISEMP (xs, b) | bool b)
extern
fun list_head
  {x:int}{xs1:ilist}
  (xs: list (cons (x, xs1))):<> int x
extern
fun list_pop {x:int}{xs1:ilist}
  (xs: list (cons (x, xs1))):<> list xs1
//
(* ****** ****** *)

datatype
bldres (
  d:int, xs: ilist, bool
) =
  | {t:tree}{fs,rs:ilist}
    bldres_succ (d, xs, true) of
      (ISCONS(fs), REMOVE (xs, fs, rs), TL (d, t, fs) | tree t, list (rs))
  | bldres_fail (d, xs, false) of (NTLP (d, xs) | (*none*))
// end of [bldres]

(* ****** ****** *)

fun build_rec
  {d:nat}{xs:ilist}{n:nat} .<n,1,0>. (
  pflen: LENGTH (xs, n) | d: int d, xs: list xs
) :<> [b:bool] bldres (d, xs, b) = let
  val (pf | isemp) = list_is_empty (xs)
in
//
if isemp then let
  prval ISEMPnil () = pf
  prval pfntlp = lemma_ntlp_nil ()
in
  bldres_fail (pfntlp | (*none*))
end else let
  prval ISEMPcons () = pf in bldr_cons (pflen | d, xs)
end // end of [if]
//
end // end of [build_rec]

and bldr_cons
  {d:nat}{x:int}{xs1:ilist}{n:nat} .<n,0,max(0,x-d)>. (
  pflen: LENGTH (cons(x,xs1), n) | d: int d, xs: list (cons(x, xs1))
) :<> [b:bool] bldres (d, cons(x,xs1), b) = let
  stadef xs = cons (x, xs1)
  val h = list_head (xs) // h: int(x)
in
//
if h < d then let
  prval pfntlp = lemma_ntlp_less ()
in
  bldres_fail (pfntlp | (*none*))
end else if h = d then let
  val xs = list_pop (xs)
  prval pfrem = append_sing {x}{xs1} ()
in
  bldres_succ (ISEMPcons(), pfrem, TLleaf (d) | tleaf (), xs)
end else let // h > d
  val [b1:bool] res1 = bldr_cons (pflen | d+1, xs)
in
//
case+ res1 of
| bldres_succ (
    pf1pos, pf1rem, pf1tl | t1, xs
  ) => let
//
    prval pf1len = length_istot ()
    prval pf2len = length_istot ()
    prval pflen_alt = append_length_lemma (pf1rem, pf1len, pf2len)
    prval ISEMPcons () = pf1pos
    prval LENGTHcons _ = pf1len
    prval () = length_isfun (pflen, pflen_alt)
//
    val [b2:bool] res2 = build_rec (pf2len | d+1, xs)
  in
    case+ res2 of
    | bldres_succ (pf2pos, pf2rem, pf2tl | t2, xs) => let
        prval (pfapp, pfrem) = lemma_remove2 (pf1rem, pf2rem)
        prval APPENDcons _ = pfapp
        prval pftl = TLnode (pf1tl, pf2tl, pfapp)
      in
        bldres_succ (ISEMPcons(), pfrem, pftl | tnode (t1, t2), xs)
      end // end of [bldres_succ]
    | bldres_fail (pf2ntlp | (*none*)) => let
        prval pfntlp = lemma_ntlp_snd (pf1rem, pf1tl, pf2ntlp)
      in
        bldres_fail (pfntlp | (*none*))
      end // end of [bldres_fail]
  end
| bldres_fail (pf1ntlp | (*none*)) =>
    bldres_fail (lemma_ntlp_fst (pf1ntlp) | (*none*))
  // end of [bldres_fail]
//
end // end of [if]
//
end // end of [bldr_cons]

(* ****** ****** *)

datatype
buildres (xs: ilist, bool) =
  | {t:tree}
    buildres_succ (xs, true) of (TL0 (t, xs) | tree (t))
  | buildres_fail (xs, false) of (NTL (0, xs) | (*none*))
// end of [buildres]

fun build
  {xs:ilist} .<>. (
  xs: list (xs)
) : [b:bool] buildres (xs, b) = let
  prval pflen = length_istot {xs} ()
  val res = build_rec (pflen | 0, xs)
in
  case+ res of
  | bldres_succ {..}{t} (
      pfpos, pfrem, pftl | t, rs
    ) => let
      val (pfemp | isemp) = list_is_empty (rs)
    in
      if isemp then let
        prval ISEMPnil () = pfemp
        prval ILISTEQ () = append_isfun (pfrem, append_unit2 ())
      in
        buildres_succ (pftl | t)
      end else let
        prval ISEMPcons () = pfemp
        prval pfntl = lemma_ntl_remainder (pfrem, pftl, ISEMPcons())
      in
        buildres_fail (pfntl | (*none*))
      end (* end of [if] *)
    end // end of [bldres_succ]
  | bldres_fail (pfntlp | (*none*)) => let
      prval NTLP {d,xs} (fpf) = pfntlp
      prval pfntl = NTL {d,xs} (lam (pftl) => fpf (PREFIX (append_unit2 ()), pftl))
    in
      buildres_fail (pfntl | (*none*))
    end // end of [bldres_fail]
end // end of [build]

(* ****** ****** *)
//
// The following code is solely for testing
// the functions implemented above; it is not
// needed if you do not want to test.
//
(* ****** ****** *)

extern
fun fprint_tree
  {t:tree} (out: FILEref, t: tree(t)): void
implement
fprint_tree
  (out, t) = case+ t of
  | tnode (t1, t2) => {
      val () = fprint_string (out, "node(")
      val () = fprint_tree (out, t1)
      val () = fprint_string (out, ", ")
      val () = fprint_tree (out, t2)
      val () = fprint_string (out, ")")
    } // end of [tnode]
  | tleaf () => fprint_string (out, "leaf")
// end of [fprint_tree]

(* ****** ****** *)

local

assume list (xs:ilist) = list0 (int)

in // in of [local]

implement
list_is_empty
  (xs) = let
  prval () = __assert () where {
    extern praxi __assert
      (): [false] void // abandoning constraint-solving
  } // end of [prval]
in
  case+ xs of
  | list0_cons _ => (ISEMPcons | false)
  | list0_nil () => (ISEMPnil () | true)
end // end of [list_is_empty]

implement
list_head
  {x}{xs1} (xs) = let
  val- list0_cons (x, _) = xs
  extern castfn __cast (x:int):<> int(x)
in
  __cast(x)
end // end of [list_head]

implement
list_pop
  {x}{xs1} (xs) = let
  val- list0_cons (_, xs1) = xs in xs1
end // end of [list_pop]

end // end of [local]

(* ****** ****** *)

implement
main () = () where {
//
// VT4-1: harnessing
//
  stadef t1 = node (leaf, node (node (leaf, leaf), leaf))
  stadef xs1 = cons (1, cons (3, cons (3, cons (2, nil))))
  prval pf0 = TLleaf (1)
  prval pf100 = TLleaf (3)
  prval pf101 = TLleaf (3)
  prval pf10 = TLnode (pf100, pf101, APPENDcons (APPENDnil))
  prval pf11 = TLleaf (2)
  prval pf1 = TLnode (pf10, pf11, APPENDcons (APPENDcons (APPENDnil)))
  prval pftl_xs1 = TLnode (pf0, pf1, APPENDcons (APPENDnil)): TL0 (t1, xs1)
//  
  val xs1 = list0_cons (1, list0_cons (3, list0_cons (3, list0_cons (2, list0_nil))))
  val xs1 = __cast (xs1) where {
    extern castfn __cast (xs: list0(int)): list (xs1)
  }
  val res1 = build (xs1)
  val t_xs1 = case+ res1 of
    | buildres_succ (pftl | t) => t // HX: it can only succeed
    | buildres_fail (pfntl | (*none*)) =/=> lemma_tl_ntl_false (pftl_xs1, pfntl) 
  // end of [val]
  val () = (print "t_xs1 = "; fprint_tree (stdout_ref, t_xs1); print_newline ())
//
// VT4-2: harnessing
//
  stadef xs2 = cons (1, cons (3, cons (2, cons (2, nil))))
  prval pf1_ntlp =
    lemma_ntlp_less {3} {2} {sing(2)} ()
  prval pf2_ntlp =
    lemma_ntlp_snd {2} (APPENDcons (APPENDnil), TLleaf (3), pf1_ntlp)
  prval pf3_ntlp = lemma_ntlp_fst {1} {3} (pf2_ntlp)
  prval pf4_ntlp =
    lemma_ntlp_snd {0} (APPENDcons (APPENDnil), TLleaf (1), pf3_ntlp)
//
  val xs2 = list0_cons (1, list0_cons (3, list0_cons (2, list0_cons (2, list0_nil))))
  val xs2 = __cast (xs2) where {
    extern castfn __cast (xs: list0(int)): list (xs2)
  }
  val res2 = build (xs2)
  prval pfntl = (
    case+ res2 of
    | buildres_fail (pfntl | (*none*)) => pfntl
    | buildres_succ (pftl | t) =/=> let
        prval NTLP (fpf) = pf4_ntlp
        prval pfapp = append_unit2 ()
        prval pfpre = PREFIX (pfapp) in fpf (pfpre, pftl)
      end // end of [buildres_succ]
  ) : NTL (0, xs2) // end of [prval]
//
} // end of [main]

(* ****** ****** *)

(* end of [problem4.dats] *)
