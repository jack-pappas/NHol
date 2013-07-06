(*

Copyright 2013 Anh-Dung Phan

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
//open NHol.wf
//open NHol.calc_num
//open NHol.normalizer
//open NHol.grobner
//open NHol.ind_types
//open NHol.lists
//open NHol.realax
//open NHol.calc_int
//open NHol.realarith
//open NHol.real
//open NHol.int
//open NHol.sets
//open NHol.iterate
//open NHol.cart
//open NHol.define
//open NHol.help
//open NHol.database

//(* ========================================================================= *)
//(* HOL basics                                                                *)
//(* ========================================================================= *)
//
//ARITH_RULE <| parse_term
// "(a * x + b * y + a * y) EXP 3 + (b * x) EXP 3 +
//  (a * x + b * y + b * x) EXP 3 + (a * y) EXP 3 =
//  (a * x + a * y + b * x) EXP 3 + (b * y) EXP 3 +
//  (a * y + b * y + b * x) EXP 3 + (a * x) EXP 3";;

//(* ========================================================================= *)
//(* Propositional logic                                                       *)
//(* ========================================================================= *)
//
//let ex01 =
// TAUT <| parse_term
//    @"(~input_a ==> (internal <=> T)) /\
//      (~input_b ==> (output <=> internal)) /\
//      (input_a ==> (output <=> F)) /\
//      (input_b ==> (output <=> F))
//      ==> (output <=> ~(input_a \/ input_b))";;
//
//let ex02 =
// TAUT <| parse_term
//    @"(i1 /\ i2 <=> a) /\
//     (i1 /\ i3 <=> b) /\
//     (i2 /\ i3 <=> c) /\
//     (i1 /\ c <=> d) /\
//     (m /\ r <=> e) /\
//     (m /\ w <=> f) /\
//     (n /\ w <=> g) /\
//     (p /\ w <=> h) /\
//     (q /\ w <=> i) /\
//     (s /\ x <=> j) /\
//     (t /\ x <=> k) /\
//     (v /\ x <=> l) /\
//     (i1 \/ i2 <=> m) /\
//     (i1 \/ i3 <=> n) /\
//     (i1 \/ q <=> p) /\
//     (i2 \/ i3 <=> q) /\
//     (i3 \/ a <=> r) /\
//     (a \/ w <=> s) /\
//     (b \/ w <=> t) /\
//     (d \/ h <=> u) /\
//     (c \/ w <=> v) /\
//     (~e <=> w) /\
//     (~u <=> x) /\
//     (i \/ l <=> o1) /\
//     (g \/ k <=> o2) /\
//     (f \/ j <=> o3)
//     ==> (o1 <=> ~i1) /\ (o2 <=> ~i2) /\ (o3 <=> ~i3)";;