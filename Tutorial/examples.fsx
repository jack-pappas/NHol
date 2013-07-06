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

// Modules Evaluation
BETA_RULE;;         // forces equal module evaluation: maybe not needed
mk_iff;;            // forces bool module evaluation
MK_CONJ;;           // forces drule module evaluation
_FALSITY_;;         // forces tactics module evaluation
ITAUT_TAC;;         // forces itab module evaluation: maybe not needd
mk_rewrites;;       // forces simp module evaluation
EQ_REFL;;           // forces theorems module evaluation
EXISTS_EQUATION;;   // forces ind_defs module evaluation
ETA_AX;;            // forces class module evaluation
o_DEF;;             // forces trivia module evaluation
CONJ_ACI_RULE;;     // forces canon module evaluation
ASM_MESON_TAC;;     // forces meson module evaluation
lift_function;;     // forces quot module evaluation

// Exception
parse_term @"~(p /\ q) <=> ~p \/ ~q";;
parse_term @"~(p \/ q) <=> ~p /\ ~q";;
parse_term @"~gate ==> (source <=> drain)";;

TAUT <| parse_term @"(~input_a ==> (internal <=> T)) /\
      (~input_b ==> (output <=> internal)) /\
      (input_a ==> (output <=> F)) /\
      (input_b ==> (output <=> F))
      ==> (output <=> ~(input_a \/ input_b))";;

TAUT <| parse_term @"(i1 /\ i2 <=> a) /\
    (i1 /\ i3 <=> b) /\
    (i2 /\ i3 <=> c) /\
    (i1 /\ c <=> d) /\
    (m /\ r <=> e) /\
    (m /\ w <=> f) /\
    (n /\ w <=> g) /\
    (p /\ w <=> h) /\
    (q /\ w <=> i) /\
    (s /\ x <=> j) /\
    (t /\ x <=> k) /\
    (v /\ x <=> l) /\
    (i1 \/ i2 <=> m) /\
    (i1 \/ i3 <=> n) /\
    (i1 \/ q <=> p) /\
    (i2 \/ i3 <=> q) /\
    (i3 \/ a <=> r) /\
    (a \/ w <=> s) /\
    (b \/ w <=> t) /\
    (d \/ h <=> u) /\
    (c \/ w <=> v) /\
    (~e <=> w) /\
    (~u <=> x) /\
    (i \/ l <=> o1) /\
    (g \/ k <=> o2) /\
    (f \/ j <=> o3)
    ==> (o1 <=> ~i1) /\ (o2 <=> ~i2) /\ (o3 <=> ~i3)";;

(* 4. Propositional logic *)

parse_term @"p \/ ~p";;
ASSUME <| parse_term @"p /\ q";;

// from this point we have to check

//parse_term @"x < 1 ==> p";;
////ARITH_RULE <| parse_term "x < y \/ y <= x";;
//
//get_infix_status "==>";;
//get_infix_status "-";;
//
//parse_as_infix("<>",(12,"right"));;
//parse_as_infix("+",(1,"left"));;
//
//parse_term "x < x + 1";;
//

//parse_as_infix("+",(16,"right"));;