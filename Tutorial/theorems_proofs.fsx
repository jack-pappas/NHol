(*

Copyright 2013 Anh-Dung Phan, Domenico Masini

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

#I "./../packages"

#r "FSharp.Compatibility.OCaml.0.1.10/lib/net40/FSharp.Compatibility.OCaml.dll"
#r "FSharp.Compatibility.OCaml.Format.0.1.10/lib/net40/FSharp.Compatibility.OCaml.Format.dll"
#r "FSharp.Compatibility.OCaml.System.0.1.10/lib/net40/FSharp.Compatibility.OCaml.System.dll"
#r "ExtCore.0.8.33/lib/net40/ExtCore.dll"

#I "./../NHol"
#r @"bin/Debug/NHol.dll"

#nowarn "25"
#nowarn "40"
#nowarn "49"
#nowarn "62"

open FSharp.Compatibility.OCaml;;
open FSharp.Compatibility.OCaml.Num;;

open NHol
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

fsi.AddPrinter string_of_type;;
fsi.AddPrinter string_of_term;;
fsi.AddPrinter string_of_thm;;

BETA_RULE;;                 // forces equal module evaluation: maybe not needed
mk_iff;;                    // forces bool module evaluation
MK_CONJ;;                   // forces drule module evaluation

_FALSITY_;;                 // forces tactics module evaluation

// for some reason it seems that it is better to call this after the tactics module evaluation
fsi.AddPrinter string_of_justification;;
fsi.AddPrinter string_of_refinement;;
fsi.AddPrinter string_of_tactic;;
fsi.AddPrinter string_of_thm_tactic;;
fsi.AddPrinter string_of_thm_tactical;;
fsi.AddPrinter string_of_goal;;
fsi.AddPrinter string_of_goalstack;;
fsi.AddPrinter string_of_goalstate;;

ITAUT_TAC;;                 // forces itab module evaluation: maybe not needed
mk_rewrites;;               // forces simp module evaluation
EQ_REFL;;                   // forces theorems module evaluation

(* EQ_REFL: |- !x:A. x = x *)

// Forward proof
let EQ_REFL0 = REFL (parse_term @"x");;                 // |- x = x
let EQ_REFL = GEN (parse_term @"x") EQ_REFL0;;          // |- !x. x = x

// Backward proof
g (parse_term @"!x:A. x = x");;                         // 1 subgoal: !x. x = x
e GEN_TAC;;                                             // 1 subgoal: x = x
e REFL_TAC;;                                            // No subgoals

(* REFL_CLAUSE: |- !x:A. (x = x) <=> T *)

// Forward proof
let REFL_CLAUSE0 = EQ_REFL                              // |- !x. x = x
let REFL_CLAUSE1 = SPEC_ALL REFL_CLAUSE0                // |- x = x
let REFL_CLAUSE2 = EQT_INTRO REFL_CLAUSE1               // |- x = x <=> T
let REFL_CLAUSE = GEN (parse_term @"x") REFL_CLAUSE2    // |- !x. x = x <=> T

// Backward proof
g (parse_term @"!x:A. (x = x) <=> T");;                 // 1 subgoal: !x. x = x <=> T)
e GEN_TAC;;                                             // 1 subgola: x = x <=> T)
e (MATCH_ACCEPT_TAC(EQT_INTRO(SPEC_ALL EQ_REFL)));;     // No subgoals

(* EQ_SYM: |- !(x:A) y. (x = y) ==> (y = x) *)

// Forward proof
let EQ_SYM0 = ASSUME (parse_term @"(x:A = y)")          // x = y |- x = y
let EQ_SYM1 = SYM EQ_SYM0                               // x = y |- y = x
let EQ_SYM2 = DISCH (parse_term @"(x:A = y)") EQ_SYM1   // |- x = y ==> y = x Note that declaring x to be of type A is necessary for this to work
let EQ_SYM3 = GEN (parse_term @"y") EQ_SYM2             // |- !y. x = y ==> y = x
let EQ_SYM = GEN (parse_term @"x") EQ_SYM3              // |- !x y. x = y ==> y = x

// Backward proof
g (parse_term @"!(x:A) y. (x = y) ==> (y = x)");;       // 1 subgoal: !x y. x = y ==> y = x
e (REPEAT GEN_TAC);;                                    // 1 subgoal: x = y ==> y = x
e (DISCH_THEN(ACCEPT_TAC << SYM));;                     // No Subgoal

(* EQ_SYM_EQ: |- !(x:A) y. (x = y) <=> (y = x) *)

// Forward proof
let EQ_SYM_EQ0 = SPEC_ALL EQ_SYM                                                                // |- x = y ==> y = x
let EQ_SYM_EQ1 = 
    INST 
        [(parse_term @"x:A"),(parse_term @"y:A");(parse_term @"y:A"),(parse_term @"x:A")] 
        EQ_SYM_EQ0                                                                              // |- y = x ==> x = y
let EQ_SYM_EQ2 = IMP_ANTISYM_RULE EQ_SYM_EQ0 EQ_SYM_EQ1                                         // |- x = y <=> y = x
let EQ_SYM_EQ3 = GEN (parse_term @"y") EQ_SYM_EQ2                                               // |- !y. x = y <=> y = x
let EQ_SYM_EQ4 = GEN (parse_term @"x") EQ_SYM_EQ3                                               // |- !x y. x = y <=> y = x

// Backward proof
g (parse_term @"!(x:A) y. (x = y) <=> (y = x)");;                                               // 1 subgoal:  !x y. x = y <=> y = x)
e (REPEAT GEN_TAC);;                                                                            // 1 subgoal:  x = y <=> y = x
e EQ_TAC;;                                                                                      // 2 subgoals:
                                                                                                //             x = y ==> y = x
                                                                                                //             y = x ==> x = y
e (MATCH_ACCEPT_TAC EQ_SYM);;                                                                   // 1 subgoal:  y = x ==> x = y 
e (MATCH_ACCEPT_TAC EQ_SYM);;                                                                   // No subgoal         

(* EQ_TRANS: |- !(x:A) y z. (x = y) /\ (y = z) ==> (x = z) *)

// Forward proof
let EQ_TRANS0 = ASSUME (parse_term @"(x:A = y) /\ (y = z)");;                                   // x = y /\ y = z |- x = y /\ y = z
let EQ_TRANS1,EQ_TRANS2 = CONJ_PAIR EQ_TRANS0;;                                                 // x = y /\ y = z |- y = z, x = y /\ y = z |- x = y
let EQ_TRANS3 = TRANS EQ_TRANS1 EQ_TRANS2;;                                                     // x = y /\ y = z |- x = z
let EQ_TRANS4 = DISCH (parse_term @"(x:A = y) /\ (y = z)") EQ_TRANS3;;                          // |- x = y /\ y = z ==> x = z
let EQ_TRANS5 = GEN (parse_term @"y") EQ_TRANS4                                                 // |- !y. x = y /\ y = z ==> x = z
let EQ_TRANS = GEN (parse_term @"x") EQ_TRANS5                                                  // |- !x y. x = y /\ y = z ==> x = z

// Backward proof
g (parse_term @"!(x:A) y z. (x = y) /\ (y = z) ==> (x = z)");;
e STRIP_TAC;; // removes x with GEN_TAC
e STRIP_TAC;; // removes y with GEN_TAC
e STRIP_TAC;; // removes z with GEN_TAC
//e STRIP_TAC;; // this fails: STRIP_TAC tries to apply GEN_TAC, CONJ_TAC and (DISCH_THEN STRIP_ASSUME_TAC) in order: if one fails then tries the next, but at the first fails here it doesn't try the next
e (DISCH_TAC);; // this is what e STRIP_TAC was supposed to do explicitly to remove the outermost implication and put the antecedent as an assumption. Probabily together with CONJ_TAC simultanously which anyway is not needed
e (PURE_ASM_REWRITE_TAC []);;
e REFL_TAC;;

// Backward proof more explicit
g (parse_term @"!(x:A) y z. (x = y) /\ (y = z) ==> (x = z)");;
e GEN_TAC;;
e GEN_TAC;;
e GEN_TAC;;
e (DISCH_TAC);;
e (PURE_ASM_REWRITE_TAC []);;
e REFL_TAC;;

// Analysis of ABS_SIMP

g (parse_term "!(t1:A) (t2:B). (\x. t1) t2 = t1");;
//e (REPEAT GEN_TAC |> THEN <| REWRITE_TAC [BETA_THM; REFL_CLAUSE]);;
e (GEN_TAC);;
//e (REPEAT GEN_TAC);;
e (REWRITE_TAC [BETA_THM; REFL_CLAUSE]);;