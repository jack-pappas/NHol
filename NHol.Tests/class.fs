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

/// Tests for functions in the NHol.``class`` module.
module Tests.NHol.``class``

open NHol.lib
open NHol.fusion
open NHol.parser
open NHol.printer
open NHol.equal
open NHol.bool
open NHol.tactics
open NHol.itab
open NHol.simp
open NHol.theorems
open NHol.``class``

open NUnit.Framework


/// Performs setup for this test fixture.
/// Executed once prior to running any tests in this fixture.
[<TestFixtureSetUp>]
let fixtureSetup () : unit =
    // TEMP : Until any "real" code is added here (if ever), just emit a message
    // to the NUnit console/log so we'll know this function has been executed.
    SetupHelpers.emitEmptyTestFixtureSetupMessage "class"

/// Performs setup for each unit test.
/// Executed once prior to running each unit test in this fixture.
[<SetUp>]
let testSetup () : unit =
    // Emit a message to the NUnit console/log to record when this function is called.
    SetupHelpers.emitTestSetupModuleResetMessage "class"

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
    ModuleReset.drule ()
    ModuleReset.tactics ()
    ModuleReset.itab ()
    ModuleReset.simp ()
    ModuleReset.theorems ()
    ModuleReset.ind_defs ()
    ModuleReset.``class`` ()


[<Test>]
[<Category("Fails")>]
let ``{ETA_CONV} Performs a toplevel eta-conversion``() =
    loadNumsModule()
    let actual = ETA_CONV (parse_term @"\n. 1 + n")
    let expected = Sequent([], parse_term @"(\n. 1 + n) = (+) 1")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
[<Category("Fails")>]
let ``{SELECT_RULE} Introduces an epsilon term in place of an existential quantifier``() =
    let actual = SELECT_RULE NHol.nums.INFINITY_AX
    let expected = Sequent([], parse_term @"ONE_ONE (@(f:ind->ind). ONE_ONE f /\ ~ONTO f) /\ ~ONTO (@(f:ind->ind). ONE_ONE f /\ ~ONTO f)")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
[<Category("Fails")>]
let ``{BOOL_CASES_TAC} Performs boolean case analysis on a (free) term in the goal``() =
    let _ = g <| parse_term @"(b ==> ~b) ==> (b ==> a)"
    let _ = e (BOOL_CASES_TAC <| parse_term @"b:bool")
    let gs = e (REWRITE_TAC[])

    noSubgoal gs
    |> assertEqual true

[<Test>]
[<Category("Fails")>]
let ``{TAUT} Proves a propositional tautology 1``() =
    let actual = TAUT_001 <| parse_term @"a \/ b ==> c <=> (a ==> c) /\ (b ==> c)"
    let expected = Sequent([], parse_term @"a \/ b ==> c <=> (a ==> c) /\ (b ==> c)")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
[<Category("Fails")>]
let ``{TAUT} Proves a propositional tautology 2``() =
    let actual = TAUT_001 <| parse_term @"(p ==> q) \/ (q ==> p)"
    let expected = Sequent([], parse_term @"(p ==> q) \/ (q ==> p)")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
[<Category("Fails")>]
let ``{TAUT} Proves a propositional tautology 3``() =
    loadNumsModule()
    let actual = TAUT_001 <| parse_term @"(x > 2 ==> y > 3) \/ (y < 3 ==> x > 2)"
    let expected = Sequent([], parse_term @"(x > 2 ==> y > 3) \/ (y < 3 ==> x > 2)")

    actual
    |> evaluate
    |> assertEqual expected


