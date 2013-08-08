(*

Copyright 2013 Jack Pappas, Anh-Dung Phan

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

[<NUnit.Framework.TestFixture>]
module Tests.NHol.Tutorial

open NUnit.Framework
open FsUnit

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
open NHol.pair
open NHol.nums
open NHol.recursion
open NHol.arith   
open NHol.wf
open NHol.calc_num
open NHol.normalizer
open NHol.grobner
open NHol.ind_types
open NHol.lists
open NHol.realax   
open NHol.calc_int 
open NHol.realarith
open NHol.real
open NHol.calc_rat 
open NHol.int
open NHol.sets     
open NHol.iterate
open NHol.cart     
open NHol.define

#if COMPILED
[<TestFixtureSetUp>]
let SetUp () =
    printfn "I'm set up for the fixture"
    BETA_RULE |> ignore                 // forces equal module evaluation: maybe not needed
    mk_iff |> ignore                    // forces bool module evaluation
    MK_CONJ |> ignore                   // forces drule module evaluation
    _FALSITY_ |> ignore                 // forces tactics module evaluation
    ITAUT_TAC |> ignore                 // forces itab module evaluation: maybe not needd
    mk_rewrites |> ignore               // forces simp module evaluation
    EQ_REFL |> ignore                   // forces theorems module evaluation
    EXISTS_EQUATION |> ignore           // forces ind_defs module evaluation
    ETA_AX |> ignore                    // forces class module evaluation
    o_DEF |> ignore                     // forces trivia module evaluation
    CONJ_ACI_RULE |> ignore             // forces canon module evaluation
    ASM_MESON_TAC |> ignore             // forces meson module evaluation
    lift_function |> ignore             // forces quot module evaluation
    LET_DEF |> ignore                   // forces pair module evaluation: pair module has to be checked
    ONE_ONE |> ignore                   // forces num module evaluation
    PRE |> ignore                       // forces arith module evaluation
    WF_EQ |> ignore                     // forces wf module evaluation
    ARITH_ZERO |> ignore                // forces calc_num module evaluation
    SEMIRING_NORMALIZERS_CONV |> ignore // forces normalizer module evaluation
    RING_AND_IDEAL_CONV |> ignore       // forces grobner module evaluation

    INJ_INVERSE2 |> ignore              // ind_types
    LIST_INDUCT_TAC |> ignore           // lists
    dist |> ignore                      // realax
    mk_realintconst |> ignore           // calc_int
    REAL_LTE_TOTAL |> ignore            // realarith
    REAL_OF_NUM_LT |> ignore            // real various

    DECIMAL |> ignore                   // calc_rat
    integer |> ignore                   // int

[<TestFixtureTearDown>]
let TearDown () =
    printfn "Going down for whole fixture..."

[<Test>]
let ``tautology shouldn't fail``() =
    TAUT <| parse_term @"(~input_a ==> (internal <=> T)) /\
      (~input_b ==> (output <=> internal)) /\
      (input_a ==> (output <=> F)) /\
      (input_b ==> (output <=> F))
      ==> (output <=> ~(input_a \/ input_b))"
    |> ignore
#endif
