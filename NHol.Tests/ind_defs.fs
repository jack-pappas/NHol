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

/// Tests for functions in the NHol.ind_defs module.
module Tests.NHol.ind_defs

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
open NHol.ind_defs

open NUnit.Framework


/// Performs setup for this test fixture.
/// Executed once prior to running any tests in this fixture.
[<TestFixtureSetUp>]
let fixtureSetup () : unit =
    // TEMP : Until any "real" code is added here (if ever), just emit a message
    // to the NUnit console/log so we'll know this function has been executed.
    SetupHelpers.emitEmptyTestFixtureSetupMessage "ind_defs"

/// Performs setup for each unit test.
/// Executed once prior to running each unit test in this fixture.
[<SetUp>]
let testSetup () : unit =
    // Emit a message to the NUnit console/log to record when this function is called.
    SetupHelpers.emitTestSetupModuleResetMessage "ind_defs"

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


[<Test>]
[<Category("Fails")>]
let ``{RIGHT_BETAS} Apply and beta-reduce equational theorem with abstraction on RHS``() =
    loadNumsModule()
    let th = ASSUME <| parse_term @"f = \a b c. a + b + c + 1"
    let actual = RIGHT_BETAS [parse_term @"x:num"; parse_term @"y:num"] th
    let expected = Sequent([parse_term @"f = \a b c. a + b + c + 1"], parse_term @"f x y = (\c. x + y + c + 1)")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
[<Category("Fails")>]
let ``{EXISTS_EQUATION} Derives existence from explicit equational constraint``() =
    loadNumsModule()
    let th = REFL <| parse_term @"x:num"
    let actual = EXISTS_EQUATION (parse_term @"x = 1") th
    let expected = Sequent([], parse_term @"?x. x = x")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
[<Category("Fails")>]
let ``{MONO_TAC} Attempt to prove monotonicity theorem automatically``() =
    let _ = g <| parse_term @"(!x. P x ==> Q x) ==> (?y. P y /\ ~Q y) ==> (?y. Q y /\ ~P y)"
    let _ = e STRIP_TAC
    let gs = e MONO_TAC

    noSubgoal gs
    |> assertEqual true