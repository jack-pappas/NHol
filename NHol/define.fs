(*

Copyright 1998 University of Cambridge
Copyright 1998-2007 John Harrison
Copyright 2013 Jack Pappas, Eric Taucher

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

#if INTERACTIVE
#else
// Support for general recursive definitions.
module NHol.define

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

open NHol
open lib
open fusion
open fusion.Hol_kernel
open basics
open nets
open printer
open preterm
open parser
open equal
open bool
open drule
open tactics
open itab
open simp
open theorems
open ind_defs
open ``class``
open trivia
open canon
open meson
open quot
open pair
open nums
open recursion
open arith
open wf
open calc_num
open normalizer
open grobner
open ind_types
open lists
open realax
open calc_int
open realarith
open real
open calc_rat
open int
open sets
open iterate
open cart
#endif

(* ------------------------------------------------------------------------- *)
(* Constant supporting casewise definitions.                                 *)
(* ------------------------------------------------------------------------- *)

let CASEWISE_DEF = 
 new_recursive_definition list_RECURSION (parse_term @"(CASEWISE [] f x = @y. T) /\
  (CASEWISE (CONS h t) f x =
        if ?y. FST h y = x then SND h f (@y. FST h y = x)
        else CASEWISE t f x)")

let CASEWISE = 
 prove ((parse_term @"(CASEWISE [] f x = @y. T) /\
   (CASEWISE (CONS (s,t) clauses) f x =
        if ?y. s y = x then t f (@y. s y = x) else CASEWISE clauses f x)"),
  REWRITE_TAC[CASEWISE_DEF])

(* ------------------------------------------------------------------------- *)
(* Conditions for all the clauses in a casewise definition to hold.          *)
(* ------------------------------------------------------------------------- *)

let CASEWISE_CASES = 
 prove ((parse_term @"!clauses c x.
    (?s t a. MEM (s,t) clauses /\ (s a = x) /\
             (CASEWISE clauses c x = t c a)) \/
    ~(?s t a. MEM (s,t) clauses /\ (s a = x)) /\
    (CASEWISE clauses c x = @y. T)"),
  MATCH_MP_TAC list_INDUCT |>THEN<|
  REWRITE_TAC[MEM; CASEWISE; FORALL_PAIR_THM; PAIR_EQ] |>THEN<|
  REPEAT STRIP_TAC |>THEN<| COND_CASES_TAC |>THEN<| ASM_MESON_TAC[])

let CASEWISE_WORKS = 
 prove ((parse_term @"!clauses c:C.
     (!s t s' t' x y. MEM (s,t) clauses /\ MEM (s',t') clauses /\ (s x = s' y)
                      ==> (t c x = t' c y))
     ==> ALL (\(s:P->A,t). !x. CASEWISE clauses c (s x) :B = t c x) clauses"),
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] |>THEN<|
  MESON_TAC[CASEWISE_CASES])

(* ------------------------------------------------------------------------- *)
(* Various notions of admissibility, with tail recursion and preconditions.  *)
(* ------------------------------------------------------------------------- *)

let admissible = 
 new_definition (parse_term @"admissible(<<) p s t <=>
        !f g a. p f a /\ p g a /\ (!z. z << s(a) ==> (f z = g z))
                ==> (t f a = t g a)")

let tailadmissible = 
 new_definition (parse_term @"tailadmissible(<<) p s t <=>
        ?P G H. (!f a y. P f a /\ y << G f a ==> y << s a) /\
                (!f g a. (!z. z << s(a) ==> (f z = g z))
                         ==> (P f a = P g a) /\
                             (G f a = G g a) /\ (H f a = H g a)) /\
                (!f a:P. p f a ==> (t (f:A->B) a =
                                    if P f a then f(G f a) else H f a))")

let superadmissible = 
 new_definition (parse_term @"superadmissible(<<) p s t <=>
        admissible(<<) (\f a. T) s p ==> tailadmissible(<<) p s t")

(* ------------------------------------------------------------------------- *)
(* A lemma.                                                                  *)
(* ------------------------------------------------------------------------- *)

let MATCH_SEQPATTERN = 
 prove ((parse_term @"_MATCH x (_SEQPATTERN r s) =
   if ?y. r x y then _MATCH x r else _MATCH x s"),
  REWRITE_TAC[_MATCH; _SEQPATTERN] |>THEN<| MESON_TAC[])

(* ------------------------------------------------------------------------- *)
(* Admissibility combinators.                                                *)
(* ------------------------------------------------------------------------- *)

let ADMISSIBLE_CONST = 
 prove ((parse_term @"!p s c. admissible(<<) p s (\f. c)"),
  REWRITE_TAC[admissible])

let ADMISSIBLE_BASE = 
 prove ((parse_term @"!(<<) p s t.
        (!f a. p f a ==> t a << s a)
        ==> admissible((<<):A->A->bool) p s (\f:A->B x:P. f(t x))"),
  REWRITE_TAC[admissible] |>THEN<| MESON_TAC[])

let ADMISSIBLE_COMB = 
 prove ((parse_term @"!(<<) p s:P->A g:(A->B)->P->C->D y:(A->B)->P->C.
        admissible(<<) p s g /\ admissible(<<) p s y
        ==> admissible(<<) p s (\f x. (g f x) (y f x))"),
  SIMP_TAC[admissible] |>THEN<| MESON_TAC[])

let ADMISSIBLE_RAND = 
 prove ((parse_term @"!(<<) p s:P->A g:P->C->D y:(A->B)->P->C.
        admissible(<<) p s y
        ==> admissible(<<) p s (\f x. (g x) (y f x))"),
  SIMP_TAC[admissible] |>THEN<| MESON_TAC[])

let ADMISSIBLE_LAMBDA = 
 prove ((parse_term @"!(<<) p s:P->A t:(A->B)->C->P->bool.
     admissible(<<) (\f (u,x). p f x) (\(u,x). s x) (\f (u,x). t f u x)
     ==> admissible(<<) p s (\f x. \u. t f u x)"),
  REWRITE_TAC[admissible; FUN_EQ_THM; FORALL_PAIR_THM] |>THEN<| MESON_TAC[])

let ADMISSIBLE_NEST = 
 prove ((parse_term @"!(<<) p s t.
        admissible(<<) p s t /\
        (!f a. p f a ==> t f a << s a)
        ==> admissible((<<):A->A->bool) p s (\f:A->B x:P. f(t f x))"),
  REWRITE_TAC[admissible] |>THEN<| MESON_TAC[])

let ADMISSIBLE_COND = 
 prove ((parse_term @"!(<<) p P s h k.
        admissible(<<) p s P /\
        admissible(<<) (\f x. p f x /\ P f x) s h /\
        admissible(<<) (\f x. p f x /\ ~P f x) s k
        ==> admissible(<<) p s (\f x:P. if P f x then h f x else k f x)"),
  REPEAT GEN_TAC |>THEN<|
  REWRITE_TAC[admissible; AND_FORALL_THM] |>THEN<|
  REPEAT(MATCH_MP_TAC MONO_FORALL |>THEN<| GEN_TAC) |>THEN<|
  DISCH_THEN(fun th -> STRIP_TAC |>THEN<| MP_TAC th) |>THEN<|
  ASM_REWRITE_TAC[] |>THEN<| ASM_MESON_TAC[])

let ADMISSIBLE_MATCH = 
 prove ((parse_term @"!(<<) p s e c.
        admissible(<<) p s e /\ admissible(<<) p s (\f x. c f x (e f x))
        ==> admissible(<<) p s (\f x:P. _MATCH (e f x) (c f x))"),
  REWRITE_TAC[admissible; _MATCH] |>THEN<|
  REPEAT STRIP_TAC |>THEN<| REPEAT COND_CASES_TAC |>THEN<| ASM_MESON_TAC[])

let ADMISSIBLE_SEQPATTERN = 
 prove ((parse_term @"!(<<) p s c1 c2 e.
        admissible(<<) p s (\f x:P. ?y. c1 f x (e f x) y) /\
        admissible(<<) (\f x. p f x /\ ?y. c1 f x (e f x) y) s
                       (\f x. c1 f x (e f x)) /\
        admissible(<<) (\f x. p f x /\ ~(?y. c1 f x (e f x) y)) s
                       (\f x. c2 f x (e f x))
        ==> admissible(<<) p s (\f x. _SEQPATTERN (c1 f x) (c2 f x) (e f x))"),
  REWRITE_TAC[_SEQPATTERN; admissible] |>THEN<| MESON_TAC[])

let ADMISSIBLE_UNGUARDED_PATTERN = 
 prove ((parse_term @"!(<<) p s pat e t y.
      admissible (<<) p s pat /\
      admissible (<<) p s e /\
      admissible (<<) (\f x. p f x /\ pat f x = e f x) s t /\
      admissible (<<) (\f x. p f x /\ pat f x = e f x) s y
        ==> admissible(<<) p s
             (\f x:P. _UNGUARDED_PATTERN (GEQ (pat f x) (e f x))
                                         (GEQ (t f x) (y f x)))"),
  REPEAT GEN_TAC |>THEN<|
  REWRITE_TAC[admissible; FORALL_PAIR_THM; _UNGUARDED_PATTERN] |>THEN<|
  REWRITE_TAC[GEQ_DEF] |>THEN<| REPEAT STRIP_TAC |>THEN<|
  MATCH_MP_TAC(TAUT (parse_term @"(a <=> a') /\ (a /\ a' ==> (b <=> b'))
                     ==> (a /\ b <=> a' /\ b')")) |>THEN<|
  ASM_MESON_TAC[])

let ADMISSIBLE_GUARDED_PATTERN = 
 prove ((parse_term @"!(<<) p s pat q e t y.
      admissible (<<) p s pat /\
      admissible (<<) p s e /\
      admissible (<<) (\f x. p f x /\ pat f x = e f x /\ q f x) s t /\
      admissible (<<) (\f x. p f x /\ pat f x = e f x) s q /\
      admissible (<<) (\f x. p f x /\ pat f x = e f x /\ q f x) s y
        ==> admissible(<<) p s
             (\f x:P. _GUARDED_PATTERN (GEQ (pat f x) (e f x))
                                       (q f x)
                                       (GEQ (t f x) (y f x)))"),
  REPEAT GEN_TAC |>THEN<|
  REWRITE_TAC[admissible; FORALL_PAIR_THM; _GUARDED_PATTERN] |>THEN<|
  REWRITE_TAC[GEQ_DEF] |>THEN<| REPEAT STRIP_TAC |>THEN<|
  REPEAT(MATCH_MP_TAC(TAUT (parse_term @"(a <=> a') /\ (a /\ a' ==> (b <=> b'))
                            ==> (a /\ b <=> a' /\ b')")) |>THEN<|
         REPEAT STRIP_TAC) |>THEN<|
  TRY(MATCH_MP_TAC(MESON[] (parse_term @"x = x' /\ y = y' ==> (x = y <=> x' = y')"))) |>THEN<|
  ASM_MESON_TAC[])

let ADMISSIBLE_NSUM = 
 prove ((parse_term @"!(<<) p:(B->C)->P->bool s:P->A h a b.
        admissible(<<) (\f (k,x). a(x) <= k /\ k <= b(x) /\ p f x)
                       (\(k,x). s x) (\f (k,x). h f x k)
   ==> admissible(<<) p s (\f x. nsum(a(x)..b(x)) (h f x))"),
  REWRITE_TAC[admissible; FORALL_PAIR_THM] |>THEN<| REPEAT STRIP_TAC |>THEN<|
  MATCH_MP_TAC NSUM_EQ_NUMSEG |>THEN<| ASM_MESON_TAC[])

let ADMISSIBLE_SUM = 
 prove ((parse_term @"!(<<) p:(B->C)->P->bool s:P->A h a b.
        admissible(<<) (\f (k,x). a(x) <= k /\ k <= b(x) /\ p f x)
                       (\(k,x). s x) (\f (k,x). h f x k)
   ==> admissible(<<) p s (\f x. sum(a(x)..b(x)) (h f x))"),
  REWRITE_TAC[admissible; FORALL_PAIR_THM] |>THEN<| REPEAT STRIP_TAC |>THEN<|
  MATCH_MP_TAC SUM_EQ_NUMSEG |>THEN<| ASM_MESON_TAC[])

let ADMISSIBLE_MAP = 
 prove ((parse_term @"!(<<) p s h l.
        admissible(<<) p s l /\
        admissible (<<) (\f (y,x). p f x /\ MEM y (l f x))
                        (\(y,x). s x) (\f (y,x). h f x y)
   ==> admissible (<<) p s (\f:A->B x:P. MAP (h f x) (l f x))"),
  REWRITE_TAC[admissible; FORALL_PAIR_THM] |>THEN<| REPEAT STRIP_TAC |>THEN<|
  MATCH_MP_TAC(MESON[] (parse_term @"x = y /\ MAP f x = MAP g x ==> MAP f x = MAP g y")) |>THEN<|
  CONJ_TAC |>THENL<| [ASM_MESON_TAC[]; ALL_TAC] |>THEN<|
  MATCH_MP_TAC MAP_EQ |>THEN<| REWRITE_TAC[GSYM ALL_MEM] |>THEN<|
  REPEAT STRIP_TAC |>THEN<| FIRST_X_ASSUM MATCH_MP_TAC |>THEN<|
  ASM_REWRITE_TAC[FORALL_PAIR_THM] |>THEN<| ASM_MESON_TAC[])

let ADMISSIBLE_MATCH_SEQPATTERN = 
 prove ((parse_term @"!(<<) p s c1 c2 e.
        admissible(<<) p s (\f x. ?y. c1 f x (e f x) y) /\
        admissible(<<) (\f x. p f x /\ ?y. c1 f x (e f x) y) s
                       (\f x. _MATCH (e f x) (c1 f x)) /\
        admissible(<<) (\f x. p f x /\ ~(?y. c1 f x (e f x) y)) s
                       (\f x. _MATCH (e f x) (c2 f x))
        ==> admissible(<<) p s
              (\f x:P. _MATCH (e f x) (_SEQPATTERN (c1 f x) (c2 f x)))"),
  REWRITE_TAC[MATCH_SEQPATTERN; ADMISSIBLE_COND])

(* ------------------------------------------------------------------------- *)
(* Superadmissible generalizations where applicable.                         *)
(*                                                                           *)
(* Note that we can't take the "higher type" route in the simple theorem     *)
(* ADMISSIBLE_MATCH because that isn't a context where tail recursion makes  *)
(* sense. Instead, we use specific theorems for the two _MATCH instances.    *)
(* Note that also, because of some delicacy over assessing welldefinedness   *)
(* of patterns, a special well-formedness hypothesis crops up here. (We need *)
(* to separate it from the function f or we lose the "tail" optimization.)   *)
(* ------------------------------------------------------------------------- *)

let ADMISSIBLE_IMP_SUPERADMISSIBLE = 
 prove ((parse_term @"!(<<) p s t:(A->B)->P->B.
      admissible(<<) p s t ==> superadmissible(<<) p s t"),
  REWRITE_TAC[admissible; superadmissible; tailadmissible] |>THEN<|
  REPEAT STRIP_TAC |>THEN<|
  MAP_EVERY EXISTS_TAC
   [(parse_term @"\f:A->B x:P. F");
    (parse_term @"\f:A->B. (anything:P->A)");
    (parse_term @"\f:A->B a:P. if p f a then t f a :B else fixed")] |>THEN<|
  ASM_REWRITE_TAC[] |>THEN<| ASM_MESON_TAC[])

let SUPERADMISSIBLE_CONST = 
 prove ((parse_term @"!p s c. superadmissible(<<) p s (\f. c)"),
  REPEAT GEN_TAC |>THEN<|
  MATCH_MP_TAC ADMISSIBLE_IMP_SUPERADMISSIBLE |>THEN<|
  REWRITE_TAC[ADMISSIBLE_CONST])

let SUPERADMISSIBLE_TAIL = 
 prove ((parse_term @"!(<<) p s t:(A->B)->P->A.
      admissible(<<) p s t /\
      (!f a. p f a ==> !y. y << t f a ==> y << s a)
      ==> superadmissible(<<) p s (\f x. f(t f x))"),
  REWRITE_TAC[admissible; superadmissible; tailadmissible] |>THEN<|
  REPEAT STRIP_TAC |>THEN<| MAP_EVERY EXISTS_TAC
   [(parse_term @"\f:A->B x:P. T");
    (parse_term @"\f:A->B a:P. if p f a then t f a :A else s a");
    (parse_term @"\f:A->B. anything:P->B")] |>THEN<|
  ASM_REWRITE_TAC[] |>THEN<| ASM_MESON_TAC[])

let SUPERADMISSIBLE_COND = 
 prove ((parse_term @"!(<<) p P s h k:(A->B)->P->B.
        admissible(<<) p s P /\
        superadmissible(<<) (\f x. p f x /\ P f x) s h /\
        superadmissible(<<) (\f x. p f x /\ ~P f x) s k
        ==> superadmissible(<<) p s (\f x. if P f x then h f x else k f x)"),
  REWRITE_TAC[superadmissible; admissible] |>THEN<| REPEAT GEN_TAC |>THEN<|
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) |>THEN<|
  DISCH_THEN(fun th -> DISCH_TAC |>THEN<| CONJUNCTS_THEN MP_TAC th) |>THEN<|
  ANTS_TAC |>THENL<| [ASM_MESON_TAC[]; ALL_TAC] |>THEN<|
  DISCH_THEN(fun th -> ANTS_TAC |>THENL<| [ASM_MESON_TAC[]; MP_TAC th]) |>THEN<|
  REWRITE_TAC[tailadmissible] |>THEN<|
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; RIGHT_IMP_FORALL_THM] |>THEN<|
  MAP_EVERY X_GEN_TAC
   [(parse_term @"P1:(A->B)->P->bool"); (parse_term @"G1:(A->B)->P->A"); (parse_term @"H1:(A->B)->P->B");
    (parse_term @"P2:(A->B)->P->bool"); (parse_term @"G2:(A->B)->P->A"); (parse_term @"H2:(A->B)->P->B")] |>THEN<|
  REWRITE_TAC[TAUT (parse_term @"(a1 /\ b1 /\ c1 ==> a2 /\ b2 /\ c2 ==> x) <=>
                    (a1 /\ a2) /\ (b1 /\ b2) /\ (c1 /\ c2) ==> x")] |>THEN<|
  DISCH_THEN(fun th ->
   MAP_EVERY EXISTS_TAC [(parse_term @"\f:A->B a:P. if p f a then if P f a then P2 f a else P1 f a else F");
    (parse_term @"\f:A->B a:P. if p f a then if P f a then G2 f a else G1 f a else z:A");
    (parse_term @"\f:A->B a:P. if p f a then if P f a then H2 f a else H1 f a else w:B")] |>THEN<|
    MP_TAC th) |>THEN<|
  REWRITE_TAC[] |>THEN<| REPEAT(MATCH_MP_TAC MONO_AND |>THEN<| CONJ_TAC) |>THENL<|
   [ASM_MESON_TAC [];
    POP_ASSUM_LIST (MP_TAC << end_itlist CONJ);
    ALL_TAC] |>THEN<|
   REWRITE_TAC[IMP_IMP; AND_FORALL_THM] |>THEN<|
   REPEAT(MATCH_MP_TAC MONO_FORALL |>THEN<| GEN_TAC) |>THEN<|
   DISCH_THEN(fun th -> DISCH_TAC |>THEN<| MP_TAC th) |>THEN<|
   ASM_REWRITE_TAC[] |>THEN<| ASM_MESON_TAC[])

let SUPERADMISSIBLE_MATCH_SEQPATTERN = 
 prove ((parse_term @"!(<<) p s c1 c2 e.
        admissible(<<) p s (\f x. ?y. c1 f x (e f x) y) /\
        superadmissible(<<) (\f x. p f x /\ ?y. c1 f x (e f x) y) s
                            (\f x. _MATCH (e f x) (c1 f x)) /\
        superadmissible(<<) (\f x. p f x /\ ~(?y. c1 f x (e f x) y)) s
                            (\f x. _MATCH (e f x) (c2 f x))
        ==> superadmissible(<<) p s
              (\f x:P. _MATCH (e f x) (_SEQPATTERN (c1 f x) (c2 f x)))"),
  REWRITE_TAC[MATCH_SEQPATTERN; SUPERADMISSIBLE_COND])

let SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN = 
 prove ((parse_term @"!(<<) p s e:P->D pat:Q->D arg.
      (!f a t u. p f a /\ pat t = e a /\ pat u = e a ==> arg a t = arg a u) /\
      (!f a t. p f a /\ pat t = e a ==> !y. y << arg a t ==> y << s a)
      ==> superadmissible(<<) p s
           (\f:A->B x. _MATCH (e x)
                    (\u v. ?t. _UNGUARDED_PATTERN (GEQ (pat t) u)
                                                  (GEQ (f(arg x t)) v)))"),
  REPEAT GEN_TAC |>THEN<| STRIP_TAC |>THEN<|
  REWRITE_TAC[superadmissible] |>THEN<| DISCH_TAC |>THEN<|
  REWRITE_TAC[_UNGUARDED_PATTERN; GEQ_DEF; _MATCH] |>THEN<|
  REWRITE_TAC[tailadmissible] |>THEN<|
  SUBGOAL_THEN
   (parse_term @"!f:A->B x:P.
     p f x ==> ((?!v. ?t:Q. pat t:D = e x /\ f(arg x t) = v) <=>
                ?t. pat t = e x)")
   (fun th -> SIMP_TAC[th]) |>THENL<| [ASM_MESON_TAC[]; ALL_TAC] |>THEN<|
  MAP_EVERY EXISTS_TAC
   [(parse_term @"\(f:A->B) x:P. p f x /\ ?t:Q. pat t:D = e x");
    (parse_term @"\f:A->B x:P. arg x (@t. (pat:Q->D) t = e x):A");
    (parse_term @"\(f:A->B) x:P. (@z:B. F)")] |>THEN<|
  RULE_ASSUM_TAC(REWRITE_RULE[admissible]) |>THEN<| SIMP_TAC[] |>THEN<|
  ASM_MESON_TAC[])

let SUPERADMISSIBLE_MATCH_GUARDED_PATTERN = 
 prove ((parse_term @"!(<<) p s e:P->D pat:Q->D q arg.
      (!f a t u. p f a /\ pat t = e a /\ q a t /\ pat u = e a /\ q a u
                 ==> arg a t = arg a u) /\
      (!f a t. p f a /\ q a t /\ pat t = e a ==> !y. y << arg a t ==> y << s a)
      ==> superadmissible(<<) p s
           (\f:A->B x. _MATCH (e x)
                    (\u v. ?t. _GUARDED_PATTERN (GEQ (pat t) u)
                                                (q x t)
                                                (GEQ (f(arg x t)) v)))"),
  REPEAT GEN_TAC |>THEN<| STRIP_TAC |>THEN<|
  REWRITE_TAC[superadmissible] |>THEN<| DISCH_TAC |>THEN<|
  REWRITE_TAC[_GUARDED_PATTERN; GEQ_DEF; _MATCH] |>THEN<|
  REWRITE_TAC[tailadmissible] |>THEN<|
  SUBGOAL_THEN
   (parse_term @"!f:A->B x:P.
     p f x ==> ((?!v. ?t:Q. pat t:D = e x /\ q x t /\ f(arg x t) = v) <=>
                ?t. pat t = e x /\ q x t)")
   (fun th -> SIMP_TAC[th]) |>THENL<| [ASM_MESON_TAC[]; ALL_TAC] |>THEN<|
  MAP_EVERY EXISTS_TAC
   [(parse_term @"\(f:A->B) x:P. p f x /\ ?t:Q. pat t:D = e x /\ q x t");
    (parse_term @"\f:A->B x:P. arg x (@t. (pat:Q->D) t = e x /\ q x t):A");
    (parse_term @"\(f:A->B) x:P. (@z:B. F)")] |>THEN<|
  RULE_ASSUM_TAC(REWRITE_RULE[admissible]) |>THEN<| SIMP_TAC[] |>THEN<|
  ASM_MESON_TAC[])

(* ------------------------------------------------------------------------- *)
(* Combine general WF/tail recursion theorem with casewise definitions.      *)
(* ------------------------------------------------------------------------- *)

let WF_REC_TAIL_GENERAL' = 
 prove ((parse_term @"!P G H H'.
         WF (<<) /\
         (!f g x. (!z. z << x ==> (f z = g z))
                  ==> (P f x <=> P g x) /\
                      (G f x = G g x) /\ (H' f x = H' g x)) /\
         (!f x y. P f x /\ y << G f x ==> y << x) /\
         (!f x. H f x = if P f x then f(G f x) else H' f x)
         ==> ?f. !x. f x = H f x"),
  REPEAT STRIP_TAC |>THEN<| ASM_REWRITE_TAC[] |>THEN<|
  MATCH_MP_TAC WF_REC_TAIL_GENERAL |>THEN<| ASM_MESON_TAC[])

let WF_REC_CASES = 
 prove ((parse_term @"!(<<) clauses.
        WF((<<):A->A->bool) /\
        ALL (\(s,t). ?P G H.
                     (!f a y. P f a /\ y << G f a ==> y << s a) /\
                     (!f g a. (!z. z << s(a) ==> (f z = g z))
                              ==> (P f a = P g a) /\
                                  (G f a = G g a) /\ (H f a = H g a)) /\
                     (!f a:P. t f a = if P f a then f(G f a) else H f a))
            clauses
        ==> ?f:A->B. !x. f x = CASEWISE clauses f x"),
  REPEAT STRIP_TAC |>THEN<| MATCH_MP_TAC WF_REC_TAIL_GENERAL' |>THEN<|
  FIRST_X_ASSUM(MP_TAC << check(is_binary "ALL" << concl <<Choice.get)) |>THEN<|
  SPEC_TAC((parse_term @"clauses:((P->A)#((A->B)->P->B))list"),
           (parse_term @"clauses:((P->A)#((A->B)->P->B))list")) |>THEN<|
  ASM_REWRITE_TAC[] |>THEN<| POP_ASSUM(K ALL_TAC) |>THEN<|
  MATCH_MP_TAC list_INDUCT |>THEN<|
  REWRITE_TAC[ALL; CASEWISE; FORALL_PAIR_THM] |>THEN<| CONJ_TAC |>THENL<|
  [MAP_EVERY EXISTS_TAC
    [(parse_term @"\f:A->B x:A. F"); (parse_term @"\f:A->B. anything:A->A"); (parse_term @"\f:A->B x:A. @y:B. T")] |>THEN<|
     REWRITE_TAC[];
     ALL_TAC] |>THEN<|
   MAP_EVERY X_GEN_TAC
    [(parse_term @"s:P->A"); (parse_term @"t:(A->B)->P->B"); (parse_term @"clauses:((P->A)#((A->B)->P->B))list")] |>THEN<|
   DISCH_THEN(fun th -> DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) |>THEN<| MP_TAC th) |>THEN<|
   ASM_REWRITE_TAC[] |>THEN<| POP_ASSUM_LIST(K ALL_TAC) |>THEN<|
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] |>THEN<| REWRITE_TAC[RIGHT_IMP_FORALL_THM] |>THEN<|
   MAP_EVERY X_GEN_TAC
    [(parse_term @"P1:(A->B)->A->bool"); (parse_term @"G1:(A->B)->A->A"); (parse_term @"H1:(A->B)->A->B");
     (parse_term @"P2:(A->B)->P->bool"); (parse_term @"G2:(A->B)->P->A"); (parse_term @"H2:(A->B)->P->B")] |>THEN<|
   REPEAT STRIP_TAC |>THEN<| ASM_REWRITE_TAC[] |>THEN<|
   EXISTS_TAC
    (parse_term @"\f:A->B x:A. if ?y:P. s y = x then P2 f (@y. s y = x) else P1 f x:bool") |>THEN<|
   EXISTS_TAC (parse_term @"\f:A->B x:A.
      if ?y:P. s y = x then G2 f (@y. s y = x) else G1 f x:A") |>THEN<|
   EXISTS_TAC (parse_term @"\f:A->B x:A. if ?y:P. s y = x
                            then H2 f (@y. s y = x) else H1 f x:B") |>THEN<|
   ASM_MESON_TAC[])

let WF_REC_CASES' = 
 prove ((parse_term @"!(<<) clauses.
        WF((<<):A->A->bool) /\
        ALL (\(s,t). tailadmissible(<<) (\f a. T) s t) clauses
        ==> ?f:A->B. !x. f x = CASEWISE clauses f x"),
  REWRITE_TAC[WF_REC_CASES; tailadmissible])

let RECURSION_CASEWISE = 
 prove ((parse_term @"!clauses.
   (?(<<). WF(<<) /\
           ALL (\(s:P->A,t). tailadmissible(<<) (\f a. T) s t) clauses) /\
   (!s t s' t' f x y. MEM (s,t) clauses /\ MEM (s',t') clauses
                      ==> (s x = s' y) ==> (t f x = t' f y))
   ==> ?f:A->B. ALL (\(s,t). !x. f (s x) = t f x) clauses"),
  REPEAT GEN_TAC |>THEN<| REWRITE_TAC[IMP_IMP; CONJ_ASSOC] |>THEN<|
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) |>THEN<|
  DISCH_THEN(CHOOSE_THEN (MP_TAC << MATCH_MP WF_REC_CASES')) |>THEN<|
  MATCH_MP_TAC MONO_EXISTS |>THEN<| REPEAT STRIP_TAC |>THEN<|
  ASM_REWRITE_TAC[] |>THEN<| ASM_MESON_TAC[CASEWISE_WORKS])

let RECURSION_CASEWISE_PAIRWISE = 
 prove ((parse_term @"!clauses.
        (?(<<). WF (<<) /\
                ALL (\(s,t). tailadmissible(<<) (\f a. T) s t) clauses) /\
        ALL (\(s,t). !f x y. (s x = s y) ==> (t f x = t f y)) clauses /\
        PAIRWISE (\(s,t) (s',t'). !f x y. (s x = s' y) ==> (t f x = t' f y))
                 clauses
        ==> (?f. ALL (\(s,t). !x. f (s x) = t f x) clauses)"),
  let lemma = 
   prove ((parse_term @"!P. (!x y. P x y ==> P y x)
         ==> !l. (!x y. MEM x l /\ MEM y l ==> P x y) <=>
                 ALL (\x. P x x) l /\ PAIRWISE P l"),
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; GSYM ALL_MEM] |>THEN<|
    REPEAT GEN_TAC |>THEN<| DISCH_TAC |>THEN<| LIST_INDUCT_TAC |>THEN<|
    REWRITE_TAC[PAIRWISE; MEM; GSYM ALL_MEM] |>THEN<| ASM_MESON_TAC[])
  let paired_lambda = 
   prove ((parse_term @"(\x. P x) = (\(a,b). P (a,b))"), REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM])
  let pth = 
   REWRITE_RULE[FORALL_PAIR_THM; paired_lambda] (ISPEC (parse_term @"\(s,t) (s',t'). !c x:A y:A. (s x = s' y) ==> (t c x = t' c y)") lemma)
  let cth = prove(Choice.get <| lhand(concl <| Choice.get pth),MESON_TAC[])
  REWRITE_TAC[GSYM(MATCH_MP pth cth); RIGHT_IMP_FORALL_THM] |>THEN<|
  REWRITE_TAC[RECURSION_CASEWISE])

let SUPERADMISSIBLE_T = 
 prove ((parse_term @"superadmissible(<<) (\f x. T) s t <=> tailadmissible(<<) (\f x. T) s t"),
  REWRITE_TAC[superadmissible; admissible])

let RECURSION_SUPERADMISSIBLE = 
 REWRITE_RULE[GSYM SUPERADMISSIBLE_T]
        RECURSION_CASEWISE_PAIRWISE

(* ------------------------------------------------------------------------- *)
(* The main suite of functions for justifying recursion.                     *)
(* ------------------------------------------------------------------------- *)

// instantiate_casewise_recursion: Instantiate the general scheme for a recursive function existence assertion.
// pure_prove_recursive_function_exists: Proves existence of general recursive function but leaves unproven assumptions.
// prove_general_recursive_function_exists: Proves existence of general recursive function.
let instantiate_casewise_recursion,
    pure_prove_recursive_function_exists,
    prove_general_recursive_function_exists =

(* ------------------------------------------------------------------------- *)
(* Make some basic simplification of conjunction of welldefinedness clauses. *)
(* ------------------------------------------------------------------------- *)

  let SIMPLIFY_WELLDEFINEDNESS_CONV =
    let LSYM =
      GEN_ALL << CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) << SPEC_ALL
    let evensimps = 
     prove ((parse_term @"((2 * m + 2 = 2 * n + 1) <=> F) /\
       ((2 * m + 1 = 2 * n + 2) <=> F) /\
       ((2 * m = 2 * n + 1) <=> F) /\
       ((2 * m + 1 = 2 * n) <=> F) /\
       ((2 * m = SUC(2 * n)) <=> F) /\
       ((SUC(2 * m) = 2 * n) <=> F)"),
      REWRITE_TAC[] |>THEN<| REPEAT CONJ_TAC |>THEN<|
      DISCH_THEN(MP_TAC << AP_TERM (parse_term @"EVEN")) |>THEN<|
      REWRITE_TAC[EVEN_MULT; EVEN_ADD; ARITH; EVEN])
    let allsimps = 
     itlist (mk_rewrites false) [EQ_ADD_RCANCEL; EQ_ADD_LCANCEL;
       EQ_ADD_RCANCEL_0; EQ_ADD_LCANCEL_0;
       LSYM EQ_ADD_RCANCEL_0; LSYM EQ_ADD_LCANCEL_0;
       EQ_MULT_RCANCEL; EQ_MULT_LCANCEL;
       EQT_INTRO(SPEC_ALL EQ_REFL);
       ADD_EQ_0; LSYM ADD_EQ_0;
       MULT_EQ_0; LSYM MULT_EQ_0;
       MULT_EQ_1; LSYM MULT_EQ_1;
       ARITH_RULE (parse_term @"(m + n = 1) <=> (m = 1) /\ (n = 0) \/ (m = 0) /\ (n = 1)");
       ARITH_RULE (parse_term @"(1 = m + n) <=> (m = 1) /\ (n = 0) \/ (m = 0) /\ (n = 1)");
       evensimps; ARITH_EQ] []
       
    let simp1, simp2, simp3 = 
        let simpFuncs =
            map MATCH_MP (CONJUNCTS (TAUT (parse_term @"((a <=> F) /\ (b <=> b) ==> ((a ==> b) <=> T)) /\
            ((a <=> a') /\ (a' ==> (b <=> T)) ==> ((a ==> b) <=> T)) /\
            ((a <=> a') /\ (a' ==> (b <=> b')) ==> ((a ==> b) <=> (a' ==> b')))")))
        match simpFuncs with
        | [simp1; simp2; simp3] -> simp1, simp2, simp3
        | _ -> failwith "simpFuncs: Unhandled case."

    let false_tm = (parse_term @"F") in 
    let and_tm = (parse_term @"(/\)")
    let eq_refl = EQT_INTRO(SPEC_ALL EQ_REFL)
    fun tm ->
      let net = itlist (net_of_thm false) allsimps (!basic_rectype_net)
      let RECTYPE_ARITH_EQ_CONV =
        TOP_SWEEP_CONV (REWRITES_CONV net) |>THENC<|
        GEN_REWRITE_CONV DEPTH_CONV [AND_CLAUSES; OR_CLAUSES]
      let SIMPLIFY_CASE_DISTINCTNESS_CLAUSE tm =
        let avs,bod = strip_forall tm
        let ant,cons = Choice.get <| dest_imp bod
        let ath = RECTYPE_ARITH_EQ_CONV ant
        let atm = Choice.get <| rand(concl <| Choice.get ath)
        let bth = 
         CONJ ath (if atm = false_tm then REFL cons
                    else DISCH atm
                          (PURE_REWRITE_CONV[eq_refl; ASSUME atm] cons))
        let cth = 
         try 
          simp1 bth 
         with 
         | Failure _ -> 
         try 
           simp2 bth
         with 
         | Failure _ -> simp3 bth
        itlist MK_FORALL avs cth
      (DEPTH_BINOP_CONV and_tm SIMPLIFY_CASE_DISTINCTNESS_CLAUSE |>THENC<|
       GEN_REWRITE_CONV DEPTH_CONV [FORALL_SIMP; AND_CLAUSES]) tm in

(* ------------------------------------------------------------------------- *)
(* Simplify an existential question about a pattern.                         *)
(* ------------------------------------------------------------------------- *)

  let EXISTS_PAT_CONV =
    let pth = 
     prove ((parse_term @"((?y. _UNGUARDED_PATTERN (GEQ s t) (GEQ z y)) <=> s = t) /\
       ((?y. _GUARDED_PATTERN (GEQ s t) g (GEQ z y)) <=> g /\ s = t)"),
      REWRITE_TAC[_UNGUARDED_PATTERN; _GUARDED_PATTERN; GEQ_DEF] |>THEN<|
      MESON_TAC[])
    let basecnv = GEN_REWRITE_CONV I [pth]
    in let pushcnv = GEN_REWRITE_CONV I [SWAP_EXISTS_THM]
    let rec EXISTS_PAT_CONV tm =
     ((pushcnv |>THENC<| BINDER_CONV EXISTS_PAT_CONV) |>ORELSEC<|
      basecnv) tm
    fun tm -> if is_exists tm then EXISTS_PAT_CONV tm
              else failwith "EXISTS_PAT_CONV" in

(* ------------------------------------------------------------------------- *)
(* Hack a proforma to introduce new pairing or pattern Choice.get <| variables.            *)
(* ------------------------------------------------------------------------- *)

  let HACK_PROFORMA,EACK_PROFORMA =
    let elemma0 = 
     prove ((parse_term @"((!z. GEQ (f z) (g z)) <=> (!x y. GEQ (f(x,y)) (g(x,y)))) /\ ((\p. P p) = (\(x,y). P(x,y)))"), REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM])
    let elemma1 = 
     prove ((parse_term @"(!P. (!t:A->B->C#D->E. P t) <=> (!t. P (\a b (c,d). t a b d c))) /\
       (!P. (!t:B->C#D->E. P t) <=> (!t. P (\b (c,d). t b d c))) /\
       (!P. (!t:C#D->E. P t) <=> (!t. P (\(c,d). t d c)))"),
      REPEAT STRIP_TAC |>THEN<| EQ_TAC |>THEN<| REPEAT STRIP_TAC |>THEN<|
      ASM_REWRITE_TAC[] |>THENL<|
       [FIRST_X_ASSUM(MP_TAC << SPEC (parse_term @"\a b d c. (t:A->B->C#D->E) a b (c,d)"));
        FIRST_X_ASSUM(MP_TAC << SPEC (parse_term @"\b d c. (t:B->C#D->E) b (c,d)"));
        FIRST_X_ASSUM(MP_TAC << SPEC (parse_term @"\d c. (t:C#D->E) (c,d)"))] |>THEN<|
       MATCH_MP_TAC EQ_IMP |>THEN<| AP_TERM_TAC |>THEN<|
       REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM])
    let HACK_PROFORMA n th =
      if n <= 1 then th else
      let mkname i = "_P"+string i
      let ty = end_itlist (fun s t -> Choice.get <| mk_type("prod",[s;t]))
                          (map (mk_vartype << mkname) (1--n))
      let conv i =
        let name = "x"+string i
        let cnv = ALPHA_CONV (mk_var(name,mk_vartype(mkname i)))
        fun tm -> if is_abs tm && name_of(Choice.get <| bndvar tm) <> name
                  then cnv tm else failwith "conv"
      let convs = FIRST_CONV (map conv (1--n))
      let th1 = INST_TYPE [ty,(parse_type @"P")] th
      let th2 = REWRITE_RULE [FORALL_PAIR_THM] th1
      let th3 = REWRITE_RULE [elemma0; elemma1] th2
      CONV_RULE(REDEPTH_CONV convs) th3
    let EACK_PROFORMA n th =
      if n <= 1 then th else
      let mkname i = "_Q"+string i
      let ty = end_itlist (fun s t -> Choice.get <| mk_type("prod",[s;t]))
                          (map (mk_vartype << mkname) (1--n))
      let conv i =
        let name = "t"+string i
        let cnv = ALPHA_CONV (mk_var(name,mk_vartype(mkname i)))
        fun tm -> if is_abs tm && name_of(Choice.get <| bndvar tm) <> name
                  then cnv tm else failwith "conv"
      let convs = FIRST_CONV (map conv (1--n))
      let th1 = INST_TYPE [ty,(parse_type @"Q")] th
      let th2 = REWRITE_RULE[EXISTS_PAIR_THM] th1
      let th3 = REWRITE_RULE[elemma1] th2
      let th4 = REWRITE_RULE[FORALL_PAIR_THM] th3
      CONV_RULE(REDEPTH_CONV convs) th4
    HACK_PROFORMA,EACK_PROFORMA in

(* ------------------------------------------------------------------------- *)
(* Hack and apply.                                                           *)
(* ------------------------------------------------------------------------- *)

  let APPLY_PROFORMA_TAC th (asl,w as gl) =
    let vs = fst(Choice.get <| dest_gabs(Choice.get <| body(Choice.get <| rand w)))
    let n = 1 + length(fst(splitlist (Some << dest_pair) vs))
    (MATCH_MP_TAC(HACK_PROFORMA n th) |>THEN<| BETA_TAC) gl in

  let is_pattern p n tm =
    try let f,args = strip_comb(snd(strip_exists (Choice.get <| body(Choice.get <| body tm))))
        is_const f && name_of f = p && length args = n
    with Failure _ -> false in

  let SIMPLIFY_MATCH_WELLDEFINED_TAC =
    let pth0 = 
     MESON[] (parse_term @"(a /\ x = k ==> x = y ==> d) ==> (a /\ x = k /\ y = k ==> d)")
    let pth1 = 
     MESON[] (parse_term @"(a /\ b /\ c /\ x = k ==> x = y ==> d)
      ==> (a /\ x = k /\ b /\ y = k /\ c ==> d)")
    REPEAT GEN_TAC |>THEN<|
    (MATCH_MP_TAC pth1 |>ORELSE<| MATCH_MP_TAC pth0) |>THEN<|
    CONV_TAC(RAND_CONV SIMPLIFY_WELLDEFINEDNESS_CONV) |>THEN<|
    PURE_REWRITE_TAC
      [AND_CLAUSES; IMP_CLAUSES; OR_CLAUSES; EQ_CLAUSES; NOT_CLAUSES] in

  let rec headonly f tm =
    match tm with
      Comb(s,t) -> headonly f s && headonly f t && not(t = f)
    | Abs(x,t) -> headonly f t
    | _ -> true in

  let MAIN_ADMISS_TAC (asl,w as gl) =
    let had,args = strip_comb w
    if not(is_const had) then failwith "ADMISS_TAC" else
    let f,fbod = Choice.get <| dest_abs(last args)
    let xtup,bod = Choice.get <| dest_gabs fbod
    let hop,args = strip_comb bod
    match (name_of had,name_of hop) with
      "superadmissible","COND"
          -> APPLY_PROFORMA_TAC SUPERADMISSIBLE_COND gl
    | "superadmissible","_MATCH" when
          name_of(repeat (Choice.get << rator) (last args)) = "_SEQPATTERN"
          -> (APPLY_PROFORMA_TAC SUPERADMISSIBLE_MATCH_SEQPATTERN |>THEN<|
              CONV_TAC(ONCE_DEPTH_CONV EXISTS_PAT_CONV)) gl
    | "superadmissible","_MATCH" when
         is_pattern "_UNGUARDED_PATTERN" 2 (last args)
          -> let n = length(fst(strip_exists(Choice.get <| body(Choice.get <| body(last args)))))
             let th = EACK_PROFORMA n SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN
             (APPLY_PROFORMA_TAC th |>THEN<| CONJ_TAC |>THENL<|
               [SIMPLIFY_MATCH_WELLDEFINED_TAC; ALL_TAC]) gl
    | "superadmissible","_MATCH" when
         is_pattern "_GUARDED_PATTERN" 3 (last args)
          -> let n = length(fst(strip_exists(Choice.get <| body(Choice.get <| body(last args)))))
             let th = EACK_PROFORMA n SUPERADMISSIBLE_MATCH_GUARDED_PATTERN
             (APPLY_PROFORMA_TAC th |>THEN<| CONJ_TAC |>THENL<|
               [SIMPLIFY_MATCH_WELLDEFINED_TAC; ALL_TAC]) gl
    | "superadmissible",_ when is_comb bod && Choice.get <| rator bod = f
          -> APPLY_PROFORMA_TAC SUPERADMISSIBLE_TAIL gl
    | "admissible","sum"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_SUM gl
    | "admissible","nsum"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_NSUM gl
    | "admissible","MAP"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_MAP gl
    | "admissible","_MATCH" when
          name_of(repeat (Choice.get << rator) (last args)) = "_SEQPATTERN"
          -> (APPLY_PROFORMA_TAC ADMISSIBLE_MATCH_SEQPATTERN |>THEN<|
              CONV_TAC(ONCE_DEPTH_CONV EXISTS_PAT_CONV)) gl
    | "admissible","_MATCH"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_MATCH gl
    | "admissible","_UNGUARDED_PATTERN"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_UNGUARDED_PATTERN gl
    | "admissible","_GUARDED_PATTERN"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_GUARDED_PATTERN gl
    | "admissible",_ when is_abs bod
          -> APPLY_PROFORMA_TAC ADMISSIBLE_LAMBDA gl
    | "admissible",_ when is_comb bod && Choice.get <| rator bod = f
          -> if free_in f (Choice.get <| rand bod) then
               APPLY_PROFORMA_TAC ADMISSIBLE_NEST gl
             else
               APPLY_PROFORMA_TAC ADMISSIBLE_BASE gl
    | "admissible",_ when is_comb bod && headonly f bod
          -> APPLY_PROFORMA_TAC ADMISSIBLE_COMB gl
    | _ -> failwith "MAIN_ADMISS_TAC" in

  let ADMISS_TAC =
    CONJ_TAC |>ORELSE<|
    MATCH_ACCEPT_TAC ADMISSIBLE_CONST |>ORELSE<|
    MATCH_ACCEPT_TAC SUPERADMISSIBLE_CONST |>ORELSE<|
    MAIN_ADMISS_TAC |>ORELSE<|
    MATCH_MP_TAC ADMISSIBLE_IMP_SUPERADMISSIBLE in

(* ------------------------------------------------------------------------- *)
(* Instantiate the casewise recursion theorem for existential claim.         *)
(* Also make a first attempt to simplify the distinctness clause. This may   *)
(* yield a theorem with just the wellfoundedness "?(<<)" assumption, or it   *)
(* may be that and an additional distinctness one.                           *)
(* ------------------------------------------------------------------------- *)

  let instantiate_casewise_recursion =
    let EXPAND_PAIRED_ALL_CONV =
      let pth0,pth1 = 
       (CONJ_PAIR << prove) ((parse_term @"(ALL (\(s,t). P s t) [a,b] <=> P a b) /\
         (ALL (\(s,t). P s t) (CONS (a,b) l) <=>
          P a b /\ ALL (\(s,t). P s t) l)"), REWRITE_TAC[ALL])
      let conv0 = REWR_CONV pth0 in let conv1 = REWR_CONV pth1
      let rec conv tm =
        try conv0 tm with Failure _ ->
        let th = conv1 tm in CONV_RULE (funpow 2 RAND_CONV conv) th
      conv
    let LAMBDA_PAIR_CONV =
      let rewr1 =  GEN_REWRITE_RULE I [GSYM FORALL_PAIR_THM]
      in let rewr2 = GEN_REWRITE_CONV I [FUN_EQ_THM]
      fun parms tm ->
        let parm = end_itlist (curry mk_pair) parms
        let x,bod = Choice.get <| dest_abs tm
        let tm' = Choice.get <| mk_gabs(parm,Choice.get <| vsubst[parm,x] bod)
        let th1 = BETA_CONV(Choice.get <| mk_comb(tm,parm))
        in let th2 = GEN_BETA_CONV (Choice.get <| mk_comb(tm',parm))
        let th3 = TRANS th1 (SYM th2)
        let th4 = itlist (fun v th -> rewr1 (GEN v th))
                         (butlast parms) (GEN (last parms) th3)
        EQ_MP (SYM(rewr2(Choice.get <| mk_eq(tm,tm')))) th4
    let FORALL_PAIR_CONV =
      let rule = GEN_REWRITE_RULE RAND_CONV [GSYM FORALL_PAIR_THM]
      let rec depair l t =
        match l with
        | [v] -> REFL t
        | v::vs -> rule(BINDER_CONV (depair vs) t)
        | [] -> failwith "depair: Unhandled case."
      fun parm parms ->
        let p = mk_var("P", Choice.get <| mk_fun_ty (Choice.get <| type_of parm) bool_ty)
        let tm = list_mk_forall(parms,Choice.get <| mk_comb(p,parm))
        GEN p (SYM(depair parms tm))
    let ELIM_LISTOPS_CONV =
      PURE_REWRITE_CONV[PAIRWISE; ALL; GSYM CONJ_ASSOC; AND_CLAUSES] |>THENC<|
      TOP_DEPTH_CONV GEN_BETA_CONV
    let tuple_function_existence tm =
      let f,def = Choice.get <| dest_exists tm
      let domtys0,ranty0 = splitlist (Choice.toOption << dest_fun_ty) (Choice.get <| type_of f)
      let nargs =
        itlist
         (max << length << snd << strip_comb << Choice.get << lhs << snd << strip_forall)
         (conjuncts(snd(strip_forall def))) 0
      let domtys,midtys = chop_list nargs domtys0
      let ranty = itlist (fun ty -> Choice.get << mk_fun_ty ty) midtys ranty0
      if length domtys <= 1 then ASSUME tm else
      let dty = end_itlist (fun ty1 ty2 -> Choice.get <| mk_type("prod",[ty1;ty2])) domtys
      let f' = Choice.get <| variant (frees tm)
                       (mk_var(fst(Choice.get <| dest_var f), Choice.get <| mk_fun_ty dty ranty))
      let gvs = map genvar domtys
      let f'' = list_mk_abs(gvs,Choice.get <| mk_comb(f',end_itlist (curry mk_pair) gvs))
      let def' = Choice.get <| subst [f'',f] def
      let th1 = EXISTS (tm,f'') (ASSUME def')
      in let bth = BETAS_CONV (list_mk_comb(f'',gvs))
      let th2 = GEN_REWRITE_CONV TOP_DEPTH_CONV [bth] (hd(hyp <| Choice.get th1))
      SIMPLE_CHOOSE f' (PROVE_HYP (UNDISCH(snd(EQ_IMP_RULE th2))) th1)
    let pinstantiate_casewise_recursion def =
      try PART_MATCH Choice.succeed EXISTS_REFL def 
      with 
      Failure _ ->
      let f,bod = Choice.get <| dest_exists def
      let cjs = conjuncts bod
      let eqs = map (snd << strip_forall) cjs
      let lefts,rights = unzip(map (Choice.get << dest_eq) eqs)
      let arglists = map (snd << strip_comb) lefts
      let parms0 = freesl(unions arglists)
      let parms = if parms0 <> [] then parms0 else [genvar aty]
      let parm = end_itlist (curry mk_pair) parms
      let ss = map (fun a -> Choice.get <| mk_gabs(parm,end_itlist (curry mk_pair) a)) arglists
      in let ts = map (fun a -> Choice.get <| mk_abs(f,Choice.get <| mk_gabs(parm,a))) rights
      let clauses = mk_flist(map2 (curry mk_pair) ss ts)
      let pth = ISPEC clauses RECURSION_SUPERADMISSIBLE
      let FIDDLE_CONV =
        (LAND_CONV << LAND_CONV << BINDER_CONV << RAND_CONV << LAND_CONV <<
         GABS_CONV << RATOR_CONV << LAND_CONV << ABS_CONV)
      let th0 = UNDISCH(CONV_RULE(FIDDLE_CONV(LAMBDA_PAIR_CONV parms)) pth)
      let th1 = EQ_MP (GEN_ALPHA_CONV f (concl <| Choice.get th0)) th0
      let rewr_forall_th = REWR_CONV(FORALL_PAIR_CONV parm parms)
      let th2 = CONV_RULE (BINDER_CONV
                    (LAND_CONV(GABS_CONV rewr_forall_th) |>THENC<|
                     EXPAND_PAIRED_ALL_CONV)) th1
      let f2,bod2 = Choice.get <| dest_exists(concl <| Choice.get th2)
      let ths3 = 
        map (CONV_RULE (COMB2_CONV (funpow 2 RAND_CONV GEN_BETA_CONV) (RATOR_CONV BETA_CONV |>THENC<| GEN_BETA_CONV)) << SPEC_ALL) (CONJUNCTS(ASSUME bod2))
      let ths4 = 
       map2 (fun th t -> 
               let avs,tbod = strip_forall t
               itlist GEN avs (PART_MATCH Choice.succeed th tbod)) ths3 cjs
      let th5 = SIMPLE_EXISTS f (end_itlist CONJ ths4)
      let th6 = PROVE_HYP th2 (SIMPLE_CHOOSE f th5)
      let th7 =
       (RAND_CONV (COMB2_CONV
            (RAND_CONV (LAND_CONV (GABS_CONV (BINDER_CONV (BINDER_CONV (rewr_forall_th) |>THENC<| rewr_forall_th)))))
            (LAND_CONV (funpow 2 GABS_CONV (BINDER_CONV (BINDER_CONV (rewr_forall_th) |>THENC<|  rewr_forall_th)) ))) |>THENC<|
        ELIM_LISTOPS_CONV) (hd(hyp <| Choice.get th6))
      let th8 = PROVE_HYP (UNDISCH(snd(EQ_IMP_RULE th7))) th6
      let wfasm,cdasm = Choice.get <| dest_conj(hd(hyp <| Choice.get th8))
      let th9 = PROVE_HYP (CONJ (ASSUME wfasm) (ASSUME cdasm)) th8
      let th10 = SIMPLIFY_WELLDEFINEDNESS_CONV cdasm
      let th11 = PROVE_HYP (UNDISCH(snd(EQ_IMP_RULE th10))) th9
      PROVE_HYP TRUTH th11
    fun etm ->
      let eth = tuple_function_existence etm
      let dtm = hd(hyp <| Choice.get eth)
      let dth = pinstantiate_casewise_recursion dtm
      PROVE_HYP dth eth in

(* ------------------------------------------------------------------------- *)
(* Justify existence assertion and try to simplify/remove side-conditions.   *)
(* ------------------------------------------------------------------------- *)

  let pure_prove_recursive_function_exists =
    let break_down_admissibility th1 =
      if hyp <| Choice.get th1 = [] then th1 else
      let def = concl <| Choice.get th1
      let f,bod = Choice.get <| dest_exists def
      let cjs = conjuncts bod
      let eqs = map (snd << strip_forall) cjs
      let lefts,rights = unzip(map (Choice.get << dest_eq) eqs)
      let arglists = map (snd << strip_comb) lefts
      let parms0 = freesl(unions arglists)
      let parms = if parms0 <> [] then parms0 else [genvar aty]
      let wfasm = Option.get <| find is_exists (hyp <| Choice.get th1)
      let ord,bod = Choice.get <| dest_exists wfasm
      let SIMP_ADMISS_TAC =
        REWRITE_TAC[LET_DEF; LET_END_DEF] |>THEN<|
        REPEAT ADMISS_TAC |>THEN<|
        TRY(W(fun (asl,w) -> 
                let v = fst(Choice.get <| dest_forall w)
                X_GEN_TAC v |>THEN<|
                MAP_EVERY
                  (fun v -> TRY(GEN_REWRITE_TAC I [FORALL_PAIR_THM]) |>THEN<|
                            X_GEN_TAC v)
                  parms |>THEN<|
                CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) |>THEN<|
                MAP_EVERY (fun v -> SPEC_TAC(v,v)) (rev parms @ [v]))) |>THEN<|
        PURE_REWRITE_TAC[FORALL_SIMP] |>THEN<|
        W(fun (asl,w) -> MAP_EVERY (fun t -> SPEC_TAC(t,t))
                                   (subtract (frees w) [ord])) |>THEN<|
        W(fun (asl,w) -> ACCEPT_TAC(ASSUME w))
      let th2 = prove(bod,SIMP_ADMISS_TAC)
      let th3 = SIMPLE_EXISTS ord th2
      let allasms = hyp <| Choice.get th3 in let wfasm = Choice.get <| lhand(concl <| Choice.get th2)
      let th4 = ASSUME(list_mk_conj(wfasm::subtract allasms [wfasm]))
      let th5 = SIMPLE_CHOOSE ord (itlist PROVE_HYP (CONJUNCTS th4) th3)
      PROVE_HYP th5 th1
    fun dtm ->
      let th =  break_down_admissibility(instantiate_casewise_recursion dtm)
      if concl <| Choice.get th = dtm then th
      else failwith "prove_general_recursive_function_exists: sanity" in

(* ------------------------------------------------------------------------- *)
(* Same, but attempt to prove the wellfoundedness hyp <| Choice.get by good guesses.       *)
(* ------------------------------------------------------------------------- *)

  let prove_general_recursive_function_exists =
    let prove_depth_measure_exists =
      let num_ty = (parse_type @"num")
      fun tyname ->
        let _,_,sth =
            assoc tyname (!inductive_type_store)
            |> Option.getOrFailWith "find"
        let ty,zty = Choice.get <| dest_fun_ty (Choice.get <| type_of(fst(Choice.get <| dest_exists(snd(strip_forall(concl <| Choice.get sth))))))
        let rth = INST_TYPE [num_ty,zty] sth
        let avs,bod = strip_forall(concl <| Choice.get rth)
        let ev,cbod = Choice.get <| dest_exists bod
        let process_clause k t =
          let avs,eq = strip_forall t
          let l,r = Choice.get <| dest_eq eq
          let fn,cargs = Choice.get <| dest_comb l
          let con,args = strip_comb cargs
          let bargs = filter (fun t -> Choice.get <| type_of t = ty) args
          let r' = list_mk_binop (parse_term @"(+):num->num->num")
                    (mk_small_numeral k :: map (curry (Choice.get << mk_comb) fn) bargs)
          list_mk_forall(avs,Choice.get <| mk_eq(l,r'))
        let cjs = conjuncts cbod
        let def = map2 process_clause (1--length cjs) cjs
        prove_recursive_functions_exist sth (list_mk_conj def)
    let INDUCTIVE_MEASURE_THEN tac (asl,w) =
      let ev,bod = Choice.get <| dest_exists w
      let ty = fst(Choice.get <| dest_type(fst(Choice.get <| dest_fun_ty(Choice.get <| type_of ev))))
      let th = prove_depth_measure_exists ty
      let ev',bod' = Choice.get <| dest_exists(concl <| Choice.get th)
      let th' = INST_TYPE(Choice.get <| type_match (Choice.get <| type_of ev') (Choice.get <| type_of ev) []) th
      (MP_TAC th' |>THEN<| MATCH_MP_TAC MONO_EXISTS |>THEN<|
       GEN_TAC |>THEN<| DISCH_THEN(fun th -> REWRITE_TAC[th]) |>THEN<| tac) (asl,w)
    let CONSTANT_MEASURE_THEN =
      let one_tm = (parse_term @"1")
      fun tac (asl,w) ->
        let ev,bod = Choice.get <| dest_exists w
        let ty = fst(Choice.get <| dest_fun_ty(Choice.get <| type_of ev))
        (EXISTS_TAC(Choice.get <| mk_abs(genvar ty,one_tm)) |>THEN<| tac) (asl,w)
    let GUESS_MEASURE_THEN tac =
      (EXISTS_TAC (parse_term @"\n. n + 1") |>THEN<| tac) |>ORELSE<|
      (INDUCTIVE_MEASURE_THEN tac) |>ORELSE<|
      CONSTANT_MEASURE_THEN tac
    let pth_lexleft = 
     prove ((parse_term @"(?r. WF(r) /\
            ?s. WF(s) /\
                P(\(x1,y1) (x2,y2). r x1 x2 \/ (x1 = x2) /\ s y1 y2))
       ==> ?t:A#B->A#B->bool. WF(t) /\ P t"),
      REPEAT STRIP_TAC |>THEN<| EXISTS_TAC
       (parse_term @"\(x1:A,y1:B) (x2:A,y2:B). r x1 x2 \/ (x1 = x2) /\ s y1 y2") |>THEN<|
      ASM_SIMP_TAC[WF_LEX])
    let pth_lexright = 
     prove ((parse_term @"(?r. WF(r) /\
            ?s. WF(s) /\
                P(\(x1,y1) (x2,y2). r y1 y2 \/ (y1 = y2) /\ s x1 x2))
       ==> ?t:A#B->A#B->bool. WF(t) /\ P t"),
      REPEAT STRIP_TAC |>THEN<|
      EXISTS_TAC (parse_term @"\u:A#B v:A#B.
                    (\(x1:B,y1:A) (x2:B,y2:A). r x1 x2 \/ (x1 = x2) /\ s y1 y2)
                     ((\(a,b). b,a) u) ((\(a,b). b,a) v)") |>THEN<|
      ASM_SIMP_TAC[ISPEC (parse_term @"\(a,b). b,a") WF_MEASURE_GEN; WF_LEX; ETA_AX] |>THEN<|
      FIRST_X_ASSUM(fun th -> MP_TAC th |>THEN<|
                              MATCH_MP_TAC EQ_IMP |>THEN<|
                              AP_TERM_TAC) |>THEN<|
      REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM])
    let pth_measure = 
     prove ((parse_term @"(?m:A->num. P(MEASURE m)) ==> ?r:A->A->bool. WF(r) /\ P r"),
      MESON_TAC[WF_MEASURE])
    let rec GUESS_WF_THEN tac (asl,w) =
     ((MATCH_MP_TAC pth_lexleft |>THEN<| GUESS_WF_THEN (GUESS_WF_THEN tac)) |>ORELSE<|
      (MATCH_MP_TAC pth_lexright |>THEN<| GUESS_WF_THEN (GUESS_WF_THEN tac)) |>ORELSE<|
      (MATCH_MP_TAC pth_measure |>THEN<|
       REWRITE_TAC[MEASURE; MEASURE_LE] |>THEN<|
       REWRITE_TAC[FORALL_PAIR_THM] |>THEN<|
       GUESS_MEASURE_THEN tac)) (asl,w)
    let PRE_GUESS_TAC =
      CONV_TAC(BINDER_CONV(DEPTH_BINOP_CONV (parse_term @"(/\)") (TRY_CONV SIMPLIFY_WELLDEFINEDNESS_CONV |>THENC<| TRY_CONV FORALL_UNWIND_CONV)))
    let GUESS_ORDERING_TAC =
      let false_tm = (parse_term @"\x:A y:A. F")
      W(fun (asl,w) ->
            let ty = fst(Choice.get <| dest_fun_ty(Choice.get <| type_of(fst(Choice.get <| dest_exists w))))
            EXISTS_TAC(Choice.get <| inst [ty,aty] false_tm) |>THEN<|
            REWRITE_TAC[WF_FALSE] |>THEN<| NO_TAC) |>ORELSE<|
      GUESS_WF_THEN
       (REWRITE_TAC[FORALL_PAIR_THM] |>THEN<| ARITH_TAC)
    fun etm ->
      let th = pure_prove_recursive_function_exists etm
      try let wtm = Option.get <| find is_exists (hyp <| Choice.get th)
          let wth = prove(wtm,PRE_GUESS_TAC |>THEN<| GUESS_ORDERING_TAC)
          PROVE_HYP wth th
      with Failure _ -> th in

  instantiate_casewise_recursion,
  pure_prove_recursive_function_exists,
  prove_general_recursive_function_exists

(* ------------------------------------------------------------------------- *)
(* Simple "define" function.                                                 *)
(* ------------------------------------------------------------------------- *)
/// Defines a general recursive function.
let define =
  let close_definition_clauses tm =
    let avs,bod = strip_forall tm
    let cjs = conjuncts bod
    let fs =
      try map (repeat (Choice.get << rator) << Choice.get << lhs << snd << strip_forall) cjs
      with Failure _ -> failwith "close_definition_clauses: non-equation"
    if length (setify fs) <> 1
    then failwith "close_definition_clauses: defining multiple functions" else
    let f = hd fs
    if mem f avs then failwith "close_definition_clauses: fn quantified" else
    let do_clause t =
      let lvs,bod = strip_forall t
      let fvs = subtract (frees(Choice.get <| lhs bod)) (f::lvs)
      SPECL fvs (ASSUME(list_mk_forall(fvs,t)))
    let ths = map do_clause cjs
    let ajs = map (hd << hyp << Choice.get) ths
    let th = ASSUME(list_mk_conj ajs)
    f,itlist GEN avs (itlist PROVE_HYP (CONJUNCTS th) (end_itlist CONJ ths))
  fun tm ->
    let tm' = snd(strip_forall tm)
    try let th,th' = tryfind (fun th -> Some (th,PART_MATCH Choice.succeed th tm')) (!the_definitions)
                     |> Option.getOrFailWith "tryfind"
        if (Choice.isResult << PART_MATCH Choice.succeed th') (concl <| Choice.get th) then
         (warn true "Benign redefinition"; th')
        else failwith ""
    with Failure _ ->
      let f,th = close_definition_clauses tm
      let etm = Choice.get <| mk_exists(f,hd(hyp <| Choice.get th))
      let th1 = prove_general_recursive_function_exists etm
      let th2 = new_specification[fst(Choice.get <| dest_var f)] th1
      let g = Choice.get <| mk_mconst(Choice.get <| dest_var f)
      let th3 = PROVE_HYP th2 (INST [g,f] th)
      the_definitions := th3::(!the_definitions); th3
