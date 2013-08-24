(*

Copyright 2013 Jack Pappas, Anh-Dung Phan, Eric Taucher

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

/// Tests for functions in the NHol.nets module.
module Tests.NHol.nets

open NHol.fusion
open NHol.nets

open NUnit.Framework


/// Performs setup for this test fixture.
/// Executed once prior to running any tests in this fixture.
[<TestFixtureSetUp>]
let fixtureSetup () : unit =
    // TEMP : Until any "real" code is added here (if ever), just emit a message
    // to the NUnit console/log so we'll know this function has been executed.
    SetupHelpers.emitEmptyTestFixtureSetupMessage "nets"

/// Performs setup for each unit test.
/// Executed once prior to running each unit test in this fixture.
[<SetUp>]
let testSetup () : unit =
    // Emit a message to the NUnit console/log to record when this function is called.
    SetupHelpers.emitTestSetupModuleResetMessage "nets"

    // Reset mutable state for this module and those proceeding it before running each unit test.
    // This helps avoid issues with mutable state which arise because unit tests can run in any order.
    ModuleReset.lib ()
    ModuleReset.fusion ()
    ModuleReset.basics ()
    ModuleReset.nets ()


(* empty_net  tests *)

(* enter tests *)

[<Test>]
let ``{enter} insert a new element into a net``() =

    let aTerm = Const ("a",Tyvar "bool")
    let bTerm = Const ("b",Tyvar "bool")

    //a = b
    let equalityTerm = 
        Comb
            (Comb
               (Const
                  ("=",
                   Tyapp
                     ("fun",[Tyvar "A"; Tyapp ("fun",[Tyvar "A"; Tyapp ("bool",[])])])), aTerm),bTerm)

    let MY_CONV (x:term) = Sequent([], equalityTerm)

    let expected = Netnode([(Cnet("a", 0), Netnode([], [MY_CONV]))], [])

    let actual = enter [] (aTerm,MY_CONV) empty_net

    actual
    |> evaluate
    |> Unsafe.assertEqual expected

(* lookup tests *)

//[<Test>]
//let ``{lookup} looks up a term in a net and return possible matches``() =
//
//    let aTerm = Const ("a",Tyvar "bool")
//    let bTerm = Const ("b",Tyvar "bool")
//
//    //a = b
//    let equalityTerm = 
//        Comb
//            (Comb
//               (Const
//                  ("=",
//                   Tyapp
//                     ("fun",[Tyvar "A"; Tyapp ("fun",[Tyvar "A"; Tyapp ("bool",[])])])), aTerm),bTerm)
//
//    let MY_CONV (x:term) = Sequent([], equalityTerm)
//
//    let termNet = Netnode([(Cnet("a", 0), Netnode([], [MY_CONV]))], [])
//
//    let actual = lookup bTerm termNet
//
//    actual
//    |> Unsafe.assertEqual bTerm


(* merge_nets  tests *)
