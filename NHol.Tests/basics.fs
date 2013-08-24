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

/// Tests for functions in the NHol.basics module.
module Tests.NHol.basics

open NUnit.Framework
open NHol.lib
open NHol.fusion
open NHol.basics


/// Performs setup for this test fixture.
/// Executed once prior to running any tests in this fixture.
[<TestFixtureSetUp>]
let fixtureSetup () : unit =
    // TEMP : Until any "real" code is added here (if ever), just emit a message
    // to the NUnit console/log so we'll know this function has been executed.
    SetupHelpers.emitEmptyTestFixtureSetupMessage "basics"

/// Performs setup for each unit test.
/// Executed once prior to running each unit test in this fixture.
[<SetUp>]
let testSetup () : unit =
    // Emit a message to the NUnit console/log to record when this function is called.
    SetupHelpers.emitTestSetupModuleResetMessage "basics"

    // Reset mutable state for this module and those proceeding it before running each unit test.
    // This helps avoid issues with mutable state which arise because unit tests can run in any order.
    ModuleReset.lib ()
    ModuleReset.fusion ()
    ModuleReset.basics ()


(* genvar tests *)

(* dest_fun_ty tests *)

(* occurs_in tests *)

(* tysubst tests *)

(* bndvar tests *)

(* body tests *)

(* list_mk_comb tests *)

(* list_mk_abs tests *)

(* strip_comb tests *)

(* strip_abs tests *)

(* is_binary tests *)

(* dest_binary tests *)
[<Test>]
let ``{dest_binary s tm} breaks apart an instance of a binary operator with given name``() =
    let s = "==>"

    let tm = 
        Comb
            (
             Comb(
                  Const("==>", 
                        Tyapp("fun", 
                              [Tyapp("bool", [])
                               Tyapp("fun", 
                                     [Tyapp("bool", [])
                                      Tyvar "?0"])])), Var("a", Tyapp("bool", []))), 
             Var("b", Tyapp("bool", [])))

    let actual = dest_binary s tm
    let expected = (Var ("a", Tyapp ("bool", [])), Var ("b", Tyapp ("bool", [])))

    actual
    |> evaluate
    |> assertEqual expected

(* mk_binary tests *)

(* variants tests *)

(* variables tests *)

(* subst tests *)

(* alpha tests *)

(* mk_mconst tests *)

(* mk_icomb tests *)

(* list_mk_icomb tests *)

(* thm_frees tests *)

(* free_in tests *)

(* find_term tests *)

(* find_terms tests *)

(* is_binder tests *)

(* dest_binder tests *)

(* mk_binder tests *)

(* is_binop tests *)

(* dest_binop tests *)

(* mk_binop tests *)

(* list_mk_binop tests *)

(* binops tests *)

(* is_conj tests *)

(* dest_conj tests *)

(* conjuncts tests *)

(* is_imp tests *)

(* dest_imp tests *)

(* is_forall tests *)

(* dest_forall tests *)

(* strip_forall tests *)

(* is_exists tests *)

(* dest_exists tests *)

(* strip_exists tests *)

(* is_disj tests *)

(* dest_disj tests *)

(* disjuncts tests *)

(* is_neg tests *)

(* dest_neg tests *)

(* is_uexists tests *)

(* dest_uexists tests *)

(* dest_cons tests *)

(* is_cons tests *)

(* dest_list tests *)

(* is_list tests *)

(* dest_fun_tydest_numeral tests *)

(* dest_gabs tests *)

(* is_gabs tests *)

(* dest_fun_ty tests *)

(* list_mk_gabs tests *)

(* strip_gabs tests *)

(* dest_let tests *)

(* is_let tests *)

(* mk_let tests *)

(* make_args tests *)

(* find_path tests *)

(* follow_path tests *)
