(*

Copyright 2013 Domenico Masini

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

/// Tests for functions in the NHol.equal module.
module Tests.NHol.bool

open NHol.lib
open NHol.fusion.Hol_kernel
open NHol.bool
open NHol.parser
open NHol.printer

open NUnit.Framework

[<Test>]
let ``{PROVE_HYP} eliminates a provable assumption from a theorem``() =
    
    let given1 = Choice1Of2 (Sequent ([parse_term @"Gamma:bool"], parse_term @"p:bool"))
    let given2 = Choice1Of2 (Sequent ([parse_term @"Delta:bool"; parse_term @"p:bool"], parse_term @"q:bool"))

    let actual = PROVE_HYP given1 given2
    let expected = Sequent ([parse_term @"Delta:bool"; parse_term @"Gamma:bool";], parse_term @"q:bool")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{PROVE_HYP} should return second theorem if conclusion of the first is not in the assuptions of the second``() =
    
    let given1 = Choice1Of2 (Sequent ([parse_term @"Gamma:bool"], parse_term @"p:bool"))
    let given2 = Choice1Of2 (Sequent ([parse_term @"Delta:bool"], parse_term @"q:bool"))

    let actual = PROVE_HYP given1 given2
    let expected = Sequent ([parse_term @"Delta:bool"], parse_term @"q:bool")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{TRUTH} proves truth``() =

    let actual = TRUTH
    let expected = Sequent ([], parse_term @"T")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{EQT_ELIM th} eliminates equality with T``() =

    TRUTH |> ignore
    let given = ASSUME (parse_term @"(p:bool) = T")
    let actual = EQT_ELIM given
    let expected = Sequent ([parse_term @"(p:bool) = T"], parse_term @"p:bool")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{EQT_INTRO th} Introduces equality with T``() =
    let actual = EQT_INTRO (REFL (parse_term @"F"))
    let expected = Sequent ([], parse_term @"F = F <=> T")

    actual
    |> evaluate
    |> assertEqual expected

open NHol.calc_num

//// This tests require calc_num module to be initialized
//
//[<Test>]
//let ``{CONJ thm} Introduces a conjunction``() =
//    let actual = CONJ (NUM_REDUCE_CONV <| parse_term @"2 + 2") (ASSUME <| parse_term @"p:bool")
//    let expected = Sequent ([parse_term @"p:bool"], parse_term @"2 + 2 = 4 /\ p")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

[<Test>]
let ``{CONJUNCT1 thm} Extracts left conjunct of theorem``() =
    let actual = CONJUNCT1(ASSUME <| parse_term @"p /\ q")
    let expected = Sequent ([parse_term @"p /\ q"], parse_term @"p:bool")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{CONJUNCT2 thm} Extracts right conjunct of theorem``() =
    let actual = CONJUNCT2(ASSUME <| parse_term @"p /\ q")
    let expected = Sequent ([parse_term @"p /\ q"], parse_term @"q:bool")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{CONJ_PAIR thm} Extracts both conjuncts of a conjunction``() =
    let actual = CONJ_PAIR(ASSUME <| parse_term @"p /\ q")
    let expected = Choice.result <| Sequent ([parse_term @"p /\ q"], parse_term @"p:bool"),
                   Choice.result <| Sequent ([parse_term @"p /\ q"], parse_term @"q:bool")

    actual
    |> assertEqual expected

[<Test>]
let ``{CONJUNCTS thm} Extracts right conjunct of theorem``() =
    let actual = CONJUNCTS(ASSUME <| parse_term "(x /\ y) /\ z /\ w");
    let expected = 
        [ Sequent ([parse_term @"(x /\ y) /\ z /\ w"], parse_term @"x:bool");
          Sequent ([parse_term @"(x /\ y) /\ z /\ w"], parse_term @"y:bool");
          Sequent ([parse_term @"(x /\ y) /\ z /\ w"], parse_term @"z:bool");
          Sequent ([parse_term @"(x /\ y) /\ z /\ w"], parse_term @"w:bool") ]

    actual
    |> List.map evaluate
    |> assertEqual expected

open NHol.``class``

[<Test>]
let ``{MP thm1 thm2} Implements the Modus Ponens inference rule``() =
    let th1 = TAUT <| parse_term @"p ==> p \/ q"
    let th2 = ASSUME <| parse_term @"p:bool"
    let actual = MP th1 th2
    let expected = Sequent ([parse_term @"p:bool"], parse_term @"p \/ q")

    actual
    |> evaluate
    |> assertEqual expected


[<Test>]
let ``{DISCH term thm} Discharges an assumption``() =
    let tm = parse_term @"p /\ q"
    let actual = DISCH tm (CONJUNCT1(ASSUME tm))
    let expected = Sequent ([], parse_term @"p /\ q ==> p")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{DISCH_ALL thm} Discharges all hypotheses of a theorem``() =
    let ths = end_itlist CONJ (map ASSUME [parse_term @"p:bool"; parse_term @"q:bool"; parse_term @"r:bool"])
    let actual = DISCH_ALL ths
    let expected = Sequent ([], parse_term @"r ==> q ==> p ==> p /\ q /\ r")

    actual
    |> evaluate
    |> assertEqual expected
