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

/// Tests for functions in the NHol.simp module.
module Tests.NHol.simp

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
    SetupHelpers.emitEmptyTestFixtureSetupMessage "simp"

/// Performs setup for each unit test.
/// Executed once prior to running each unit test in this fixture.
[<SetUp>]
let testSetup () : unit =
    // Emit a message to the NUnit console/log to record when this function is called.
    SetupHelpers.emitTestSetupModuleResetMessage "simp"

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


[<Test>]
[<Category("Fails")>]
let ``{REWR_CONV} Uses an instance of a given equation to rewrite a term``() =
    let actual = REWR_CONV EQ_SYM_EQ <| parse_term @"(T : bool) = F"
    let expected = Sequent([], parse_term @"(T : bool) = F <=> F = T")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
[<Category("Fails")>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "term_pmatch")>]
let ``{REWR_CONV} Fails on unmatched terms``() =
    let actual = REWR_CONV EQ_SYM_EQ <| parse_term @"(T : bool) ==> F"

    actual
    |> evaluate
    |> ignore