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

#if SKIP_MODULE_INIT
#else
/// Performs setup for this test fixture.
/// Executed once prior to running any tests in this fixture.
[<TestFixtureSetUp>]
let fixtureSetup () : unit =
    // TEMP : Until any "real" code is added here (if ever), just emit a message
    // to the NUnit console/log so we'll know this function has been executed.
    SetupHelpers.emitEmptyTestFixtureSetupMessage "bool"

/// Performs setup for each unit test.
/// Executed once prior to running each unit test in this fixture.
[<SetUp>]
let testSetup () : unit =
    // Emit a message to the NUnit console/log to record when this function is called.
    SetupHelpers.emitTestSetupModuleResetMessage "bool"

    // Reset mutable state for this module and those proceeding it before running each unit test.
    // This helps avoid issues with mutable state which arise because unit tests can run in any order.
    ModuleReset.lib ()
    ModuleReset.fusion ()
    ModuleReset.basics ()
    ModuleReset.nets ()
    ModuleReset.printer ()
    ModuleReset.preterm ()
    ModuleReset.parser ()
    ModuleReset.equal ()
    ModuleReset.bool ()
#endif

(* is_iff  tests *)

(* dest_iff  tests *)

(* mk_iff  tests *)

(* PINST  tests *)

(* PROVE_HYP  tests *)

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

(* T_DEF  tests *)

(* TRUTH  tests *)

[<Test>]
let ``{TRUTH} proves truth``() =

    let actual = TRUTH
    let expected = Sequent ([], parse_term @"T")

    actual
    |> evaluate
    |> assertEqual expected

(* EQT_ELIM  tests *)

[<Test>]
let ``{EQT_ELIM th} eliminates equality with T``() =

    TRUTH |> ignore
    let given = ASSUME (parse_term @"(p:bool) = T")
    let actual = EQT_ELIM given
    let expected = Sequent ([parse_term @"(p:bool) = T"], parse_term @"p:bool")

    actual
    |> evaluate
    |> assertEqual expected

(* EQT_INTRO  tests *)

[<Test>]
let ``{EQT_INTRO th} Introduces equality with T``() =
    let actual = EQT_INTRO (REFL (parse_term @"F"))
    let expected = Sequent ([], parse_term @"F = F <=> T")

    actual
    |> evaluate
    |> assertEqual expected

(* AND_DEF  tests *)

(* mk_conj  tests *)

(* list_mk_conj  tests *)

(* CONJ  tests *)

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
let ``{CONJ thm} Introduces a conjunction``() =

    let given1 = Choice1Of2 (Sequent ([(parse_term "Gamma:bool")], (parse_term "th1:bool")))
    let given2 = Choice1Of2 (Sequent ([(parse_term "Delta:bool")], (parse_term "th2:bool")))

    let actual = CONJ given1 given2
    let expected = Sequent ([parse_term @"Delta:bool"; parse_term @"Gamma:bool"], parse_term @"th1:bool /\ th2:bool")

    actual
    |> evaluate
    |> assertEqual expected

(* CONJUNCT1  tests *)

[<Test>]
let ``{CONJUNCT1 thm} Extracts left conjunct of theorem``() =
    let actual = CONJUNCT1(ASSUME <| parse_term @"p /\ q")
    let expected = Sequent ([parse_term @"p /\ q"], parse_term @"p:bool")

    actual
    |> evaluate
    |> assertEqual expected

(* CONJUNCT2  tests *)

[<Test>]
let ``{CONJUNCT2 thm} Extracts right conjunct of theorem``() =
    let actual = CONJUNCT2(ASSUME <| parse_term @"p /\ q")
    let expected = Sequent ([parse_term @"p /\ q"], parse_term @"q:bool")

    actual
    |> evaluate
    |> assertEqual expected

(* CONJ_PAIR  tests *)

[<Test>]
let ``{CONJ_PAIR thm} Extracts both conjuncts of a conjunction``() =
    let actual = CONJ_PAIR(ASSUME <| parse_term @"p /\ q")
    let expected = Choice.result <| Sequent ([parse_term @"p /\ q"], parse_term @"p:bool"),
                   Choice.result <| Sequent ([parse_term @"p /\ q"], parse_term @"q:bool")

    actual
    |> assertEqual expected

(* CONJUNCTS  tests *)

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

(* IMP_DEF  tests *)

(* mk_imp  tests *)

(* MP  tests *)

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

(* DISCH  tests *)

[<Test>]
let ``{DISCH term thm} Discharges an assumption``() =
    let tm = parse_term @"p /\ q"
    let actual = DISCH tm (CONJUNCT1(ASSUME tm))
    let expected = Sequent ([], parse_term @"p /\ q ==> p")

    actual
    |> evaluate
    |> assertEqual expected

(* DISCH_ALL  tests *)

[<Test>]
let ``{DISCH_ALL thm} Discharges all hypotheses of a theorem``() =
    let ths = end_itlist CONJ (map ASSUME [parse_term @"p:bool"; parse_term @"q:bool"; parse_term @"r:bool"])
    let actual = DISCH_ALL ths
    let expected = Sequent ([], parse_term @"r ==> q ==> p ==> p /\ q /\ r")

    actual
    |> evaluate
    |> assertEqual expected

(* UNDISCH  tests *)

[<Test>]
let ``{UNDISCH thm} Undischarges the antecedent of an implicative theorem``() =
    let actual = UNDISCH(TAUT <| parse_term "p /\ q ==> p")
    let expected = Sequent ([parse_term @"p /\ q"], parse_term @"p:bool")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{UNDISCH a implies b} should return a concludes b``() =

    T_DEF |> ignore

    let given = Choice1Of2 (Sequent ([], (parse_term @"a:bool ==> b:bool")))
    let actual = UNDISCH given
    let expected = Sequent ([parse_term @"a:bool"], parse_term @"b:bool")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{UNDISCH FALSISTY implies F} should return FALSITY concludes F``() =

    T_DEF |> ignore

    let given = Choice1Of2 (Sequent ([], (parse_term @"_FALSITY_:bool ==> F:bool")))
    let actual = UNDISCH given
    let expected = Sequent ([parse_term @"_FALSITY_:bool"], parse_term @"F:bool")

    actual
    |> evaluate
    |> assertEqual expected

(* UNDISCH_ALL  tests *)

[<Test>]
let ``{UNDISCH_ALL thm} Iteratively undischarges antecedents in a chain of implications``() =
    let actual = UNDISCH_ALL(TAUT <| parse_term "p ==> q ==> r ==> p /\ q /\ r")
    let expected = Sequent ([parse_term @"p:bool"; parse_term @"q:bool"; parse_term @"r:bool"], parse_term @"p /\ q /\ r")

    actual
    |> evaluate
    |> assertEqual expected

(* IMP_ANTISYM_RULE  tests *)

[<Test>]
let ``{IMP_ANTISYM_RULE thm1 thm2} Deduces equality of boolean terms from forward and backward implications``() =
    let th1 = TAUT <| parse_term @"p /\ q ==> q /\ p"
    let th2 = TAUT <| parse_term @"q /\ p ==> p /\ q"
    let actual = IMP_ANTISYM_RULE th1 th2
    let expected = Sequent ([], parse_term @"p /\ q <=> q /\ p")

    actual
    |> evaluate
    |> assertEqual expected

(* ADD_ASSUM  tests *)

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

(* EQ_IMP_RULE  tests *)

[<Test>]
let ``{EQ_IMP_RULE thm} Derives forward and backward implication from equality of boolean terms``() =
    let actual = EQ_IMP_RULE (SPEC_ALL CONJ_SYM)
    let expected = Choice.result <| Sequent ([], parse_term @"t1 /\ t2 ==> t2 /\ t1"),
                   Choice.result <| Sequent ([], parse_term @"t2 /\ t1 ==> t1 /\ t2")

    actual
    |> assertEqual expected

[<Test>]
let ``{EQ_IMP_RULE thm} Derives forward and backward implication from equality of boolean terms 2``() =

    mk_iff |> ignore

    let actual = EQ_IMP_RULE (SPEC_ALL CONJ_SYM)
    let expected = Choice.result <| Sequent ([], parse_term @"t1 /\ t2 ==> t2 /\ t1"),
                   Choice.result <| Sequent ([], parse_term @"t2 /\ t1 ==> t1 /\ t2")

    actual
    |> assertEqual expected

(* IMP_TRANS  tests *)

[<Test>]
let ``{IMP_TRANS thm1 thm2} Implements the transitivity of implication``() =
    let th1 = TAUT <| parse_term @"p /\ q /\ r ==> p /\ q"
    let th2 = TAUT <| parse_term @"p /\ q ==> p"
    let actual = IMP_TRANS th1 th2
    let expected = Sequent ([], parse_term @"p /\ q /\ r ==> p")

    actual
    |> evaluate
    |> assertEqual expected

(* FORALL_DEF  tests *)

(* mk_forall  tests *)

(* list_mk_forall  tests *)

(* SPEC  tests *)

(* SPECL  tests *)

(* SPEC_VAR  tests *)

(* SPEC_ALL  tests *)

(* ISPEC  tests *)

(* ISPECL  tests *)

(* GEN  tests *)

(* GENL  tests *)

(* GEN_ALL  tests *)

(* EXISTS_DEF  tests *)

(* mk_exists  tests *)

(* list_mk_exists  tests *)

(* EXISTS  tests *)

(* SIMPLE_EXISTS  tests *)

(* CHOOSE  tests *)

(* SIMPLE_CHOOSE  tests *)

(* OR_DEF  tests *)

(* mk_disj  tests *)

(* list_mk_disj  tests *)

(* DISJ1  tests *)

// Test cases for SPEC* functions

//

[<Test>]
let ``{DISJ1 thm term} Introduces a right disjunct into the conclusion of a theorem``() =
    let actual = DISJ1 TRUTH <| parse_term @"F"
    let expected = Sequent ([], parse_term @"T \/ F")

    actual
    |> evaluate
    |> assertEqual expected

(* DISJ2  tests *)

[<Test>]
let ``{DISJ2 term thm} Introduces a left disjunct into the conclusion of a theorem``() =
    let actual = DISJ2 (parse_term @"F") TRUTH
    let expected = Sequent ([], parse_term @"F \/ T")

    actual
    |> evaluate
    |> assertEqual expected

(* DISJ_CASES  tests *)

(* SIMPLE_DISJ_CASES  tests *)

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

(* F_DEF  tests *)

(* NOT_DEF  tests *)

(* mk_neg  tests *)

(* NOT_ELIM  tests *)

[<Test>]
let ``{NOT_ELIM thm} Transforms |- ~t into |- t ==> F``() =
    let th = UNDISCH(TAUT <| parse_term @"p ==> ~ ~p")
    let actual = NOT_ELIM th
    let expected = Sequent ([parse_term @"p:bool"], parse_term @"~p ==> F")

    actual
    |> evaluate
    |> assertEqual expected

(* NOT_INTRO  tests *)

[<Test>]
let ``{NOT_INTRO thm} Transforms |- t ==> F into |- ~t``() =
    let th = TAUT <| parse_term @"F ==> F"
    let actual = NOT_INTRO th
    let expected = Sequent ([], parse_term @"~F")

    actual
    |> evaluate
    |> assertEqual expected

(* EQF_INTRO  tests *)

[<Test>]
let ``{EQF_INTRO thm} Converts negation to equality with F``() =
    let th = ASSUME (parse_term @"~p")
    let actual = EQF_INTRO th
    let expected = Sequent ([parse_term @"~p"], parse_term @"p <=> F")

    actual
    |> evaluate
    |> assertEqual expected

(* EQF_ELIM  tests *)

[<Test>]
let ``{EQF_ELIM thm} Replaces equality with F by negation``() =
    let th = REFL (parse_term @"F")
    let actual = EQF_ELIM th
    let expected = Sequent ([], parse_term @"~F")

    actual
    |> evaluate
    |> assertEqual expected

(* CONTR  tests *)

//// This test requires calc_num module to be initialized
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

(* EXISTS_UNIQUE_DEF  tests *)

(* mk_uexists  tests *)

(* EXISTENCE  tests *)

[<Test>]
let ``{EXISTENCE thm} Deduces existence from unique existence``() =
    let th = Choice.result <| Sequent([], parse_term @"?!n. n = m")
    let actual = EXISTENCE th
    let expected = Sequent ([], parse_term @"?n. n = m")

    // Compare concrete form since AST form consists of different type vars
    actual
    |> evaluate
    |> string_of_thm
    |> assertEqual (string_of_thm expected)

