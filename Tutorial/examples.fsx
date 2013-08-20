(*

Copyright 2013 Anh-Dung Phan, Domenico D. D. Masini

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

#load "hol.fsx"

open NHol.lib
open NHol.fusion
open NHol.basics
open NHol.nets
open NHol.printer
open NHol.preterm
open NHol.parser
open NHol.equal
open NHol.bool
open NHol.drule
open NHol.tactics
open NHol.itab
open NHol.simp
open NHol.theorems
open NHol.ind_defs
open NHol.``class``
open NHol.trivia
open NHol.canon
open NHol.meson
open NHol.quot
//open NHol.pair
//open NHol.nums
//open NHol.recursion
//open NHol.arith   
////open NHol.wf: depends on pair module
//open NHol.calc_num
//open NHol.normalizer
//open NHol.grobner

// Modules Evaluation
BETA_RULE;;                 // forces equal module evaluation: maybe not needed
mk_iff;;                    // forces bool module evaluation
MK_CONJ;;                   // forces drule module evaluation
_FALSITY_;;                 // forces tactics module evaluation
ITAUT_TAC;;                 // forces itab module evaluation: maybe not needed
mk_rewrites;;               // forces simp module evaluation
EQ_REFL;;                   // forces theorems module evaluation
EXISTS_EQUATION;;           // forces ind_defs module evaluation
ETA_AX;;                    // forces class module evaluation
o_DEF;;                     // forces trivia module evaluation
CONJ_ACI_RULE;;             // forces canon module evaluation
ASM_MESON_TAC;;             // forces meson module evaluation
lift_function;;             // forces quot module evaluation
////LET_DEF;;                 // forces pair module evaluation: pair module has to be checked
//ONE_ONE;;                   // forces num module evaluation
//PRE;;                       // forces arith module evaluation
//ARITH_ZERO;;                // forces calc_num module evaluation
//SEMIRING_NORMALIZERS_CONV;; // forces normalizer module evaluation
//RING_AND_IDEAL_CONV;;       // forces grobner module evaluation

let noSubgoal gs =
    match gs with
    | Success ((_, [], _) :: _) -> true
    | _ -> false

//let gs1 = g <| parse_term @"!x. (x <=> T) \/ (x <=> F)";;
//let gs2 = e (ACCEPT_TAC BOOL_CASES_AX);;
//
//noSubgoal gs2;;

//let gs0 = g <| parse_term @"HD [T;F] = T";;
//let HD : Protected<thm0> = Choice.result <| Sequent([], parse_term @"!h t. HD(CONS h t) = h");;
//let gs = e (MATCH_ACCEPT_TAC HD);;
//
//noSubgoal gs;;

//// Analysis of ABS_SIMP
//
//g (parse_term "!(t1:A) (t2:B). (\x. t1) t2 = t1");;
////e (REPEAT GEN_TAC |> THEN <| REWRITE_TAC [BETA_THM; REFL_CLAUSE]);;
////e (GEN_TAC);;
//e (REPEAT GEN_TAC);;
//e (REWRITE_TAC [BETA_THM; REFL_CLAUSE]);;

//BETAS_CONV <| parse_term @"(\x y. x /\ y) T F";;

let th : Protected<thm0> = Choice.result <| Sequent([], parse_term @"?!n. n = m");;
let actual = EXISTENCE th;;