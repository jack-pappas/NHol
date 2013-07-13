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
/// Theory of wellfounded relations.
module NHol.wf

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
#endif

parse_as_infix("<<", (12, "right"))

(* ------------------------------------------------------------------------- *)
(* Definition of wellfoundedness for arbitrary (infix) relation <<           *)
(* ------------------------------------------------------------------------- *)
let WF = 
    new_definition
        (parse_term 
             @"WF(<<) <=> !P:A->bool. (?x. P(x)) ==> (?x. P(x) /\ !y. y << x ==> ~P(y))")

(* ------------------------------------------------------------------------- *)
(* Strengthen it to equality.                                                *)
(* ------------------------------------------------------------------------- *)
let WF_EQ = 
    prove
        ((parse_term 
              @"WF(<<) <=> !P:A->bool. (?x. P(x)) <=> (?x. P(x) /\ !y. y << x ==> ~P(y))"), 
         REWRITE_TAC [WF]
         |> THEN <| MESON_TAC [])

(* ------------------------------------------------------------------------- *)
(* Equivalence of wellfounded induction.                                     *)
(* ------------------------------------------------------------------------- *)
let WF_IND = 
    prove
        ((parse_term 
              @"WF(<<) <=> !P:A->bool. (!x. (!y. y << x ==> P(y)) ==> P(x)) ==> !x. P(x)"), 
         REWRITE_TAC [WF]
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| GEN_TAC
         |> THEN <| POP_ASSUM(MP_TAC << SPEC(parse_term @"\x:A. ~P(x)"))
         |> THEN <| REWRITE_TAC []
         |> THEN <| MESON_TAC [])

(* ------------------------------------------------------------------------- *)
(* Equivalence of the "infinite descending chains" version.                  *)
(* ------------------------------------------------------------------------- *)
let WF_DCHAIN = 
    prove
        ((parse_term @"WF(<<) <=> ~(?s:num->A. !n. s(SUC n) << s(n))"), 
         REWRITE_TAC [WF
                      TAUT(parse_term @"(a <=> ~b) <=> (~a <=> b)")
                      NOT_FORALL_THM]
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_THEN CHOOSE_TAC
         |> THENL <| [POP_ASSUM(MP_TAC << REWRITE_RULE [NOT_IMP])
                      |> THEN 
                      <| DISCH_THEN
                             (CONJUNCTS_THEN2 (X_CHOOSE_TAC(parse_term @"a:A")) 
                                  ASSUME_TAC)
                      |> THEN 
                      <| SUBGOAL_THEN 
                             (parse_term @"!x:A. ?y. P(x) ==> P(y) /\ y << x") 
                             MP_TAC
                      |> THENL <| [ASM_MESON_TAC []
                                   REWRITE_TAC [SKOLEM_THM]]
                      |> THEN 
                      <| DISCH_THEN
                             (X_CHOOSE_THEN (parse_term @"f:A->A") 
                                  STRIP_ASSUME_TAC)
                      |> THEN 
                      <| CHOOSE_TAC
                             (prove_recursive_functions_exist num_RECURSION 
                                  (parse_term 
                                       "(s(0) = a:A) /\ (!n. s(SUC n) = f(s n))"))
                      |> THEN <| EXISTS_TAC(parse_term @"s:num->A")
                      |> THEN <| ASM_REWRITE_TAC []
                      |> THEN 
                      <| SUBGOAL_THEN 
                             (parse_term @"!n. P(s n) /\ s(SUC n):A << s(n)") 
                             (fun th -> ASM_MESON_TAC [th])
                      |> THEN <| INDUCT_TAC
                      |> THEN <| ASM_REWRITE_TAC []
                      |> THEN <| ASM_MESON_TAC []
                      EXISTS_TAC(parse_term @"\y:A. ?n:num. y = s(n)")
                      |> THEN <| REWRITE_TAC []
                      |> THEN <| ASM_MESON_TAC []])

(* ------------------------------------------------------------------------- *)
(* Equivalent to just *uniqueness* part of recursion.                        *)
(* ------------------------------------------------------------------------- *)
let WF_UREC = 
    prove((parse_term @"WF(<<) ==>
        !H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
             ==> !(f:A->B) g. (!x. f x = H f x) /\ (!x. g x = H g x)
                               ==> (f = g)"),
                              REWRITE_TAC [WF_IND]
                              |> THEN <| REPEAT STRIP_TAC
                              |> THEN <| REWRITE_TAC [FUN_EQ_THM]
                              |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                              |> THEN <| GEN_TAC
                              |> THEN <| DISCH_THEN(ANTE_RES_THEN MP_TAC)
                              |> THEN <| ASM_REWRITE_TAC [])

let WF_UREC_WF = 
  prove((parse_term @"(!H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
         ==> !(f:A->bool) g. (!x. f x = H f x) /\ (!x. g x = H g x)
                           ==> (f = g))
    ==> WF(<<)"),
   REWRITE_TAC [WF_IND]
   |> THEN <| DISCH_TAC
   |> THEN <| GEN_TAC
   |> THEN <| DISCH_TAC
   |> THEN 
   <| FIRST_X_ASSUM
          (MP_TAC << SPEC(parse_term @"\f x. P(x:A) \/ !z:A. z << x ==> f(z)"))
   |> THEN <| REWRITE_TAC []
   |> THEN 
   <| W(C SUBGOAL_THEN (fun t -> REWRITE_TAC [t]) << funpow 2 lhand << snd)
   |> THENL <| [MESON_TAC []
                DISCH_THEN(MP_TAC << SPECL [(parse_term @"P:A->bool")
                                            (parse_term @"\x:A. T")])
                |> THEN <| REWRITE_TAC [FUN_EQ_THM]
                |> THEN <| ASM_MESON_TAC []])

(* ------------------------------------------------------------------------- *)
(* Stronger form of recursion with "inductive invariant" (Krstic/Matthews).  *)
(* ------------------------------------------------------------------------- *)
let WF_REC_INVARIANT = 
    prove((parse_term @"WF(<<)
    ==> !H S. (!f g x. (!z. z << x ==> (f z = g z) /\ S z (f z))
                       ==> (H f x = H g x) /\ S x (H f x))
              ==> ?f:A->B. !x. (f x = H f x)"),
             let lemma = 
                 prove_inductive_relations_exist
                     (parse_term 
                          "!f:A->B x. (!z. z << x ==> R z (f z)) ==> R x (H f x)")
             REWRITE_TAC [WF_IND]
             |> THEN <| REPEAT STRIP_TAC
             |> THEN 
             <| X_CHOOSE_THEN (parse_term @"R:A->B->bool") STRIP_ASSUME_TAC lemma
             |> THEN 
             <| SUBGOAL_THEN (parse_term @"!x:A. ?!y:B. R x y") 
                    (fun th -> ASM_MESON_TAC [th])
             |> THEN <| FIRST_X_ASSUM MATCH_MP_TAC
             |> THEN <| REPEAT STRIP_TAC
             |> THEN 
             <| FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC BINDER_CONV [th])
             |> THEN 
             <| SUBGOAL_THEN (parse_term @"!x:A y:B. R x y ==> S x y") MP_TAC
             |> THEN <| ASM_MESON_TAC [])

(* ------------------------------------------------------------------------- *)
(* Equivalent to just *existence* part of recursion.                         *)
(* ------------------------------------------------------------------------- *)
let WF_REC = 
    prove((parse_term @"WF(<<)
    ==> !H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
            ==> ?f:A->B. !x. f x = H f x"),
           REPEAT STRIP_TAC
           |> THEN <| FIRST_X_ASSUM(MATCH_MP_TAC << MATCH_MP WF_REC_INVARIANT)
           |> THEN <| EXISTS_TAC(parse_term @"\x:A y:B. T")
           |> THEN <| ASM_REWRITE_TAC [])

let WF_REC_WF = 
   prove((parse_term @"(!H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
                 ==> ?f:A->num. !x. f x = H f x)
    ==> WF(<<)"),
    DISCH_TAC
    |> THEN <| REWRITE_TAC [WF_DCHAIN]
    |> THEN <| DISCH_THEN(X_CHOOSE_TAC(parse_term @"x:num->A"))
    |> THEN 
    <| SUBGOAL_THEN (parse_term @"!n. (x:num->A)(@m. x(m) << x(n)) << x(n)") 
           ASSUME_TAC
    |> THENL <| [CONV_TAC(BINDER_CONV SELECT_CONV)
                 |> THEN <| ASM_MESON_TAC []
                 ALL_TAC]
    |> THEN <| FIRST_ASSUM(MP_TAC << SPEC(parse_term @"\f:A->num. \y:A. if ?p:num. y = x(p)
                       then SUC(f(x(@m. x(m) << y)))
                       else 0")) 
    |> THEN <| REWRITE_TAC [NOT_IMP]
    |> THEN <| CONJ_TAC
    |> THENL <| [REPEAT STRIP_TAC
                 |> THEN <| COND_CASES_TAC
                 |> THEN <| REWRITE_TAC []
                 |> THEN 
                 <| FIRST_ASSUM(X_CHOOSE_THEN (parse_term @"p:num") SUBST_ALL_TAC)
                 |> THEN <| AP_TERM_TAC
                 |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                 |> THEN <| FIRST_ASSUM MATCH_ACCEPT_TAC
                 ALL_TAC]
    |> THEN <| DISCH_THEN(X_CHOOSE_THEN (parse_term @"f:A->num") MP_TAC)
    |> THEN 
    <| DISCH_THEN
           (MP_TAC << GEN(parse_term @"n:num") << SPEC(parse_term @"(x:num->A) n"))
    |> THEN 
    <| SUBGOAL_THEN (parse_term @"!n. ?p. (x:num->A) n = x p") 
           (fun th -> REWRITE_TAC [th])
    |> THENL <| [MESON_TAC []; DISCH_TAC]
    |> THEN 
    <| SUBGOAL_THEN (parse_term @"!n:num. ?k. f(x(k):A) < f(x(n))") ASSUME_TAC
    |> THENL <| [GEN_TAC
                 |> THEN <| EXISTS_TAC(parse_term @"@m:num. x(m):A << x(n)")
                 |> THEN <| FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th])
                 |> THEN <| REWRITE_TAC [LT]
                 MP_TAC
                     (SPEC (parse_term @"\n:num. ?i:num. n = f(x(i):A)") num_WOP)
                 |> THEN <| REWRITE_TAC []
                 |> THEN <| ASM_MESON_TAC []])

(* ------------------------------------------------------------------------- *)
(* Combine the two versions of the recursion theorem.                        *)
(* ------------------------------------------------------------------------- *)
let WF_EREC = prove((parse_term @"WF(<<) ==>
        !H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
             ==> ?!f:A->B. !x. f x = H f x"), MESON_TAC [WF_REC; WF_UREC])

parse_as_infix("<<<", (12, "right"))

(* ------------------------------------------------------------------------- *)
(* Some preservation theorems for wellfoundedness.                           *)
(* ------------------------------------------------------------------------- *)
let WF_SUBSET = 
    prove
        ((parse_term @"(!(x:A) y. x << y ==> x <<< y) /\ WF(<<<) ==> WF(<<)"), 
         DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
         |> THEN <| REWRITE_TAC [WF]
         |> THEN <| DISCH_TAC
         |> THEN <| GEN_TAC
         |> THEN <| DISCH_THEN(ANTE_RES_THEN MP_TAC)
         |> THEN <| UNDISCH_TAC(parse_term @"!(x:A) (y:A). x << y ==> x <<< y")
         |> THEN <| MESON_TAC [])

let WF_MEASURE_GEN = 
    prove
        ((parse_term @"!m:A->B. WF(<<) ==> WF(\x x'. m x << m x')"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [WF_IND]
         |> THEN <| REPEAT STRIP_TAC
         |> THEN 
         <| FIRST_ASSUM
                (MP_TAC << SPEC(parse_term @"\y:B. !x:A. (m(x) = y) ==> P x"))
         |> THEN 
         <| UNDISCH_TAC
                (parse_term @"!x. (!y. (m:A->B) y << m x ==> P y) ==> P x")
         |> THEN <| REWRITE_TAC []
         |> THEN <| MESON_TAC [])

//Error too deep
let WF_LEX_DEPENDENT = Sequent([],parse_term @"!R:A->A->bool S:A->B->B->bool. WF(R) /\ (!a. WF(S a)) ==> WF(\(r1,s1) (r2,s2). R r1 r2 \/ (r1 = r2) /\ S r1 s1 s2)")
//    prove((parse_term @"!R:A->A->bool S:A->B->B->bool. WF(R) /\ (!a. WF(S a))
//          ==> WF(\(r1,s1) (r2,s2). R r1 r2 \/ (r1 = r2) /\ S r1 s1 s2)"),
//         REPEAT GEN_TAC
//         |> THEN <| REWRITE_TAC [WF]
//         |> THEN <| STRIP_TAC
//         |> THEN <| X_GEN_TAC(parse_term @"P:A#B->bool")
//         |> THEN <| REWRITE_TAC [LEFT_IMP_EXISTS_THM]
//         |> THEN <| GEN_REWRITE_TAC I [FORALL_PAIR_THM]
//         |> THEN <| MAP_EVERY X_GEN_TAC [(parse_term @"a0:A")
//                                         (parse_term @"b0:B")]
//         |> THEN <| DISCH_TAC
//         |> THEN 
//         <| FIRST_X_ASSUM(MP_TAC << SPEC(parse_term @"\a:A. ?b:B. P(a,b)"))
//         |> THEN <| REWRITE_TAC [LEFT_IMP_EXISTS_THM]
//         |> THEN <| DISCH_THEN(MP_TAC << SPECL [(parse_term @"a0:A")
//                                                (parse_term @"b0:B")])
//         |> THEN <| ASM_REWRITE_TAC []
//         |> THEN 
//         <| DISCH_THEN
//                (X_CHOOSE_THEN (parse_term @"a:A") 
//                     (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))
//         |> THEN <| DISCH_THEN(X_CHOOSE_TAC(parse_term @"b1:B"))
//         |> THEN 
//         <| FIRST_X_ASSUM
//                (MP_TAC << SPECL [(parse_term @"a:A")
//                                  (parse_term @"\b. (P:A#B->bool) (a,b)")])
//         |> THEN <| REWRITE_TAC [LEFT_IMP_EXISTS_THM]
//         |> THEN <| DISCH_THEN(MP_TAC << SPEC(parse_term @"b1:B"))
//         |> THEN <| ASM_REWRITE_TAC []
//         |> THEN 
//         <| DISCH_THEN
//                (X_CHOOSE_THEN (parse_term @"b:B") 
//                     (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))
//         |> THEN <| DISCH_TAC
//         |> THEN <| EXISTS_TAC(parse_term @"(a:A,b:B)")
//         |> THEN <| ASM_REWRITE_TAC []
//         |> THEN <| REWRITE_TAC [FORALL_PAIR_THM]
//         |> THEN <| ASM_MESON_TAC [])

let WF_LEX = prove((parse_term @"!R:A->A->bool S:B->B->bool. WF(R) /\ WF(S)
          ==> WF(\(r1,s1) (r2,s2). R r1 r2 \/ (r1 = r2) /\ S s1 s2)"), SIMP_TAC [WF_LEX_DEPENDENT; ETA_AX])

//unsolved goal 
let WF_POINTWISE = Sequent([],parse_term @"WF((<<) :A->A->bool) /\ WF((<<<) :B->B->bool) ==> WF(\(x1,y1) (x2,y2). x1 << x2 /\ y1 <<< y2)")
//  prove((parse_term @"WF((<<) :A->A->bool) /\ WF((<<<) :B->B->bool)
//    ==> WF(\(x1,y1) (x2,y2). x1 << x2 /\ y1 <<< y2)"),
//   STRIP_TAC
//   |> THEN <| MATCH_MP_TAC(GEN_ALL WF_SUBSET)
//   |> THEN 
//   <| EXISTS_TAC
//          (parse_term 
//               @"\(x1,y1) (x2,y2). x1 << x2 \/ (x1:A = x2) /\ (y1:B) <<< (y2:B)")
//   |> THEN <| CONJ_TAC
//   |> THENL <| [REWRITE_TAC [FORALL_PAIR_THM]
//                |> THEN <| CONV_TAC TAUT
//                MATCH_MP_TAC WF_LEX
//                |> THEN <| ASM_REWRITE_TAC []])

(* ------------------------------------------------------------------------- *)
(* Wellfoundedness properties of natural numbers.                            *)
(* ------------------------------------------------------------------------- *)
let WF_num = prove((parse_term @"WF(<)"), REWRITE_TAC [WF_IND; num_WF])

let WF_REC_num = prove((parse_term @"!H. (!f g n. (!m. m < n ==> (f m = g m)) ==> (H f n = H g n))
         ==> ?f:num->A. !n. f n = H f n"), MATCH_ACCEPT_TAC(MATCH_MP WF_REC WF_num))

(* ------------------------------------------------------------------------- *)
(* Natural number measures (useful in program verification).                 *)
(* ------------------------------------------------------------------------- *)
let MEASURE = new_definition(parse_term @"MEASURE m = \x y. m(x) < m(y)")

let WF_MEASURE = 
    prove
        ((parse_term @"!m:A->num. WF(MEASURE m)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [MEASURE]
         |> THEN <| MATCH_MP_TAC WF_MEASURE_GEN
         |> THEN <| MATCH_ACCEPT_TAC WF_num)

let MEASURE_LE = 
    prove
        ((parse_term @"(!y. MEASURE m y a ==> MEASURE m y b) <=> m(a) <= m(b)"), 
         REWRITE_TAC [MEASURE]
         |> THEN <| MESON_TAC [NOT_LE; LTE_TRANS; LT_REFL])

(* ------------------------------------------------------------------------- *)
(* Trivially, a WF relation is irreflexive.                                  *)
(* ------------------------------------------------------------------------- *)
let WF_REFL = 
    prove((parse_term @"!x:A. WF(<<) ==> ~(x << x)"), GEN_TAC
                                                     |> THEN <| REWRITE_TAC [WF]
                                                     |> THEN 
                                                     <| DISCH_THEN
                                                            (MP_TAC 
                                                             << SPEC
                                                                    (parse_term 
                                                                         "\y:A. y = x"))
                                                     |> THEN <| REWRITE_TAC []
                                                     |> THEN <| MESON_TAC [])

(* ------------------------------------------------------------------------- *)
(* Even more trivially, the everywhere-false relation is wellfounded.        *)
(* ------------------------------------------------------------------------- *)
let WF_FALSE = prove((parse_term @"WF(\x y:A. F)"), REWRITE_TAC [WF])

(* ------------------------------------------------------------------------- *)
(* Tail recursion.                                                           *)
(* ------------------------------------------------------------------------- *)
let WF_REC_TAIL = 
    prove
        ((parse_term @"!P g h. ?f:A->B. !x. f x = if P(x) then f(g x) else h x"), 
         let lemma1 = 
             prove
                 ((parse_term @"~(P 0) ==> ((?n. P(SUC n)) <=> (?n. P(n)))"), 
                  MESON_TAC [num_CASES; NOT_SUC])
         let lemma2 = 
             prove
                 ((parse_term 
                       @"(P 0) ==> ((!m. m < n ==> P(SUC m)) <=> (!m. m < SUC n ==> P(m)))"), 
                  REPEAT(DISCH_TAC
                         |> ORELSE <| EQ_TAC)
                  |> THEN <| INDUCT_TAC
                  |> THEN <| ASM_MESON_TAC [LT_SUC; LT_0])
         REPEAT GEN_TAC
         |> THEN 
         <| MP_TAC
                (GEN (parse_term @"x:A") 
                     (ISPECL [(parse_term @"x:A")
                              (parse_term @"\y:A n:num. g(y):A")] num_RECURSION))
         |> THEN <| REWRITE_TAC [SKOLEM_THM; FORALL_AND_THM]
         |> THEN 
         <| DISCH_THEN
                (X_CHOOSE_THEN (parse_term @"s:A->num->A") STRIP_ASSUME_TAC)
         |> THEN <| EXISTS_TAC(parse_term @"\x:A. if ?n:num. ~P(s x n)
                     then (h:A->B)(@y. ?n. (y = s x n) /\ ~P(s x n) /\
                                           !m. m < n ==> P(s x m))
                     else something_arbitrary:B") 
         |> THEN <| X_GEN_TAC(parse_term @"x:A")
         |> THEN 
         <| SUBGOAL_THEN (parse_term @"!n x:A. s (g x) n :A = s x (SUC n)") 
                ASSUME_TAC
         |> THENL 
         <| [INDUCT_TAC
             |> THEN <| ASM_REWRITE_TAC []
             UNDISCH_THEN (parse_term @"!x:A n. s x (SUC n) :A = g (s x n)") 
                 (K ALL_TAC)]
         |> THEN <| ASM_CASES_TAC(parse_term @"(P:A->bool) x")
         |> THEN <| ASM_REWRITE_TAC []
         |> THENL <| [ASM_SIMP_TAC [lemma1]
                      |> THEN <| COND_CASES_TAC
                      |> THEN <| ASM_REWRITE_TAC []
                      |> THEN <| CONV_TAC SYM_CONV
                      |> THEN <| ASM_SIMP_TAC [lemma2; lemma1]
                      COND_CASES_TAC
                      |> THENL <| [ALL_TAC
                                   ASM_MESON_TAC []]
                      |> THEN <| AP_TERM_TAC
                      |> THEN <| MATCH_MP_TAC SELECT_UNIQUE
                      |> THEN <| REWRITE_TAC []
                      |> THEN <| X_GEN_TAC(parse_term @"y:A")
                      |> THEN <| EQ_TAC
                      |> THENL <| [SIMP_TAC [LEFT_IMP_EXISTS_THM]
                                   |> THEN <| INDUCT_TAC
                                   |> THEN <| ASM_REWRITE_TAC []
                                   |> THEN <| ASM_MESON_TAC [LT_0]
                                   ASM_MESON_TAC [LT]]])

(* ------------------------------------------------------------------------- *)
(* A more general mix of tail and wellfounded recursion.                     *)
(* ------------------------------------------------------------------------- *)
let WF_REC_TAIL_GENERAL = 
 prove ((parse_term @"!P G H. WF(<<) /\ (!f g x. (!z. z << x ==> (f z = g z)) 
   ==> (P f x <=> P g x) /\ G f x = G g x /\ H f x = H g x) /\ (!f g x. (!z. z << x ==> (f z = g z)) 
   ==> (H f x = H g x)) /\ (!f x y. P f x /\ y << G f x ==> y << x) 
   ==> ?f:A->B. !x. f x = if P f x then f(G f x) else H f x"), REPEAT STRIP_TAC 
 |>THEN<| CHOOSE_THEN MP_TAC
    (prove_inductive_relations_exist
      (parse_term @"(!x:A. ~(P f x) ==> terminates f x) /\ (!x. P (f:A->B) x /\ terminates f (G f x) ==> terminates f x)")) 
   |>THEN<| REWRITE_TAC[FORALL_AND_THM] 
   |>THEN<| DISCH_THEN(STRIP_ASSUME_TAC << GSYM) 
   |>THEN<| SUBGOAL_THEN
    (parse_term @"?while. !f:A->B x:A. while f x = if P f x then while f (G f x) else x")
    (STRIP_ASSUME_TAC << GSYM)
   |>THENL<| [REWRITE_TAC[GSYM SKOLEM_THM; WF_REC_TAIL]; ALL_TAC] 
   |>THEN<| SUBGOAL_THEN (parse_term @"?f:A->B. !x. f x = if terminates f x then H f (while f x :A) else anything")
   MP_TAC 
   |>THENL<|
    [FIRST_ASSUM(MATCH_MP_TAC << MATCH_MP WF_REC) |>THEN<|
     REPEAT STRIP_TAC |>THEN<| MATCH_MP_TAC(MESON[]
      (parse_term @"(a = b) /\ (a /\ b ==> (x = y) /\ (f x = g x))
       ==> ((if a then f x else d) = (if b then g y else d))")) |>THEN<|
     REPEAT STRIP_TAC |>THENL<|
      [SUBGOAL_THEN
        (parse_term @"!f g x.
            (!x y. P f x /\ y << G (f:A->B) x ==> y << x) /\
            (!y:A. (!z:A. z << y ==> z << x)
                   ==> (P f y = P g y) /\ (G f y = G g y))
                ==> terminates f x ==> terminates g x")
        (fun th -> EQ_TAC |>THEN<| MATCH_MP_TAC th |>THEN<| ASM_MESON_TAC[]) |>THEN<|
       GEN_TAC |>THEN<| GEN_TAC |>THEN<|
       REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] |>THEN<| DISCH_TAC |>THEN<|
       ONCE_REWRITE_TAC[TAUT (parse_term @"a ==> b ==> c <=> b ==> a ==> c")] |>THEN<|
       FIRST_X_ASSUM MATCH_MP_TAC |>THEN<| ASM_MESON_TAC[];
       SUBGOAL_THEN
        (parse_term @"!x:A. terminates (f:A->B) x /\
               (!y:A. (!z:A. z << y ==> z << x)
                      ==> (P f y <=> P g y) /\ (G f y :A = G g y))
               ==> (while f x :A = while g x)")
        (fun th -> MATCH_MP_TAC th |>THEN<| ASM_MESON_TAC[]) |>THEN<|
       REWRITE_TAC[IMP_CONJ] |>THEN<|
       FIRST_X_ASSUM MATCH_MP_TAC |>THEN<| ASM_MESON_TAC[];
       FIRST_X_ASSUM MATCH_MP_TAC |>THEN<|
       SUBGOAL_THEN
        (parse_term @"!f:A->B. (!x:A y:A. P f x /\ y << G f x ==> y << x)
          ==> !x. terminates f x ==> !y. y << while f x ==> y << x")
        (fun th -> ASM_MESON_TAC[th]) |>THEN<|
       GEN_TAC |>THEN<| DISCH_TAC |>THEN<| FIRST_X_ASSUM MATCH_MP_TAC |>THEN<|
       ASM_MESON_TAC[]];
     MATCH_MP_TAC MONO_EXISTS |>THEN<| GEN_TAC |>THEN<|
     DISCH_THEN(fun th -> ASSUME_TAC(GSYM th) |>THEN<| MP_TAC th) |>THEN<|
     MATCH_MP_TAC MONO_FORALL |>THEN<| X_GEN_TAC (parse_term @"x:A") |>THEN<|
     ASM_CASES_TAC (parse_term @"P (f:A->B) (x:A) :bool") |>THEN<| ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Tactic to apply WF induction on a free "measured" term in the goal.       *)
(* ------------------------------------------------------------------------- *)
let WF_INDUCT_TAC = 
    let qqconv = 
        let pth = 
            prove
                ((parse_term @"(!x. P x ==> !y. Q x y) <=> !y x. P x ==> Q x y"), 
                 MESON_TAC [])
        GEN_REWRITE_CONV I [pth]
    let eqconv = 
        let pth = 
            prove
                ((parse_term @"(!m. P m ==> (m = e) ==> Q) <=> (P e ==> Q)"), 
                 MESON_TAC [])
        REWR_CONV pth
    let rec qqconvs tm = 
        try 
            (qqconv
             |> THENC <| BINDER_CONV qqconvs) tm
        with
        | Failure _ -> eqconv tm
    fun tm (asl, w as gl) ->
            let fvs = frees tm
            let gv = genvar(type_of tm)
            let pat = list_mk_forall(gv :: fvs, mk_imp(mk_eq(gv, tm), w))
            let th0 = UNDISCH(PART_MATCH rand num_WF pat)
            let th1 = MP (SPECL (tm :: fvs) th0) (REFL tm)
            let th2 = CONV_RULE (LAND_CONV qqconvs) (DISCH_ALL th1)
            (MATCH_MP_TAC th2
             |> THEN <| MAP_EVERY X_GEN_TAC fvs
             |> THEN <| CONV_TAC(LAND_CONV qqconvs)
             |> THEN <| DISCH_THEN ASSUME_TAC) gl