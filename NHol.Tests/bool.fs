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

/// Tests for functions in the NHol.bool module.
module Tests.NHol.bool

open NHol.lib
open NHol.fusion
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

[<Test>]
let ``{UNDISCH thm} Undischarges the antecedent of an implicative theorem``() =
    let actual = UNDISCH(TAUT <| parse_term "p /\ q ==> p")
    let expected = Sequent ([parse_term @"p /\ q"], parse_term @"p:bool")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{UNDISCH_ALL thm} Iteratively undischarges antecedents in a chain of implications``() =
    let actual = UNDISCH_ALL(TAUT <| parse_term "p ==> q ==> r ==> p /\ q /\ r")
    let expected = Sequent ([parse_term @"p:bool"; parse_term @"q:bool"; parse_term @"r:bool"], parse_term @"p /\ q /\ r")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{IMP_ANTISYM_RULE thm1 thm2} Deduces equality of boolean terms from forward and backward implications``() =
    let th1 = TAUT <| parse_term @"p /\ q ==> q /\ p"
    let th2 = TAUT <| parse_term @"q /\ p ==> p /\ q"
    let actual = IMP_ANTISYM_RULE th1 th2
    let expected = Sequent ([], parse_term @"p /\ q <=> q /\ p")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{ADD_ASSUM term thm} Adds an assumption to a theorem``() =
    let tm1 = parse_term @"p:bool"
    let tm2 = parse_term @"q:bool"
    let actual = ADD_ASSUM tm2 (ASSUME tm1)
    let expected = Sequent ([tm1; tm2], tm1)

    actual
    |> evaluate
    |> assertEqual expected

open NHol.theorems

[<Test>]
let ``{EQ_IMP_RULE thm} Derives forward and backward implication from equality of boolean terms``() =
    let actual = EQ_IMP_RULE (SPEC_ALL CONJ_SYM)
    let expected = Choice.result <| Sequent ([], parse_term @"t1 /\ t2 ==> t2 /\ t1"),
                   Choice.result <| Sequent ([], parse_term @"t2 /\ t1 ==> t1 /\ t2")

    actual
    |> assertEqual expected

[<Test>]
let ``{IMP_TRANS thm1 thm2} Implements the transitivity of implication``() =
    let th1 = TAUT <| parse_term @"p /\ q /\ r ==> p /\ q"
    let th2 = TAUT <| parse_term @"p /\ q ==> p"
    let actual = IMP_TRANS th1 th2
    let expected = Sequent ([], parse_term @"p /\ q /\ r ==> p")

    actual
    |> evaluate
    |> assertEqual expected

// Test cases for SPEC* functions

//

[<Test>]
let ``{DISJ1 thm term} Introduces a right disjunct into the conclusion of a theorem``() =
    let actual = DISJ1 TRUTH <| parse_term @"F"
    let expected = Sequent ([], parse_term @"T \/ F")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{DISJ2 term thm} Introduces a left disjunct into the conclusion of a theorem``() =
    let actual = DISJ2 (parse_term @"F") TRUTH
    let expected = Sequent ([], parse_term @"F \/ T")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{SIMPLE_DISJ_CASES thm1 thm2} Disjoins hypotheses of two theorems with same conclusion``() =
    let ths = map (UNDISCH << TAUT) [parse_term @"~p ==> p ==> q"; parse_term @"q ==> p ==> q"]
    match ths with
    | [th1; th2] ->
        let actual = SIMPLE_DISJ_CASES th1 th2
        let expected = Sequent ([parse_term @"~p \/ q"], parse_term @"p ==> q")

        actual
        |> evaluate
        |> assertEqual expected
    | _ -> ()

[<Test>]
let ``{NOT_ELIM thm} Transforms |- ~t into |- t ==> F``() =
    let th = UNDISCH(TAUT <| parse_term @"p ==> ~ ~p")
    let actual = NOT_ELIM th
    let expected = Sequent ([parse_term @"p:bool"], parse_term @"~p ==> F")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{NOT_INTRO thm} Transforms |- t ==> F into |- ~t``() =
    let th = TAUT <| parse_term @"F ==> F"
    let actual = NOT_INTRO th
    let expected = Sequent ([], parse_term @"~F")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{EQF_INTRO thm} Converts negation to equality with F``() =
    let th = ASSUME (parse_term @"~p")
    let actual = EQF_INTRO th
    let expected = Sequent ([parse_term @"~p"], parse_term @"p <=> F")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{EQF_ELIM thm} Replaces equality with F by negation``() =
    let th = REFL (parse_term @"F")
    let actual = EQF_ELIM th
    let expected = Sequent ([], parse_term @"~F")

    actual
    |> evaluate
    |> assertEqual expected

//// This test requires nums module to be initialized
//open NHol.simp
//
//[<Test>]
//let ``{CONTR term thm} Implements the intuitionistic contradiction rule``() =
//    let th = REWRITE_RULE [ARITH] (ASSUME <| parse_term @"1 = 0")
//    let actual = CONTR (parse_term @"Russell:Person = Pope") th
//    let expected = Sequent ([parse_term @"1 = 0"], parse_term @"Russell:Person = Pope")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

open NHol.meson

[<Test>]
let ``{EXISTENCE thm} Deduces existence from unique existence``() =
    let th = MESON [] <| parse_term @"?!n. n = m"
    let actual = EXISTENCE th
    let expected = Sequent ([], parse_term @"?n. n = m")

    actual
    |> evaluate
    |> assertEqual expected

