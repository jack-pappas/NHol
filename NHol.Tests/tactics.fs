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

/// Tests for functions in the NHol.tactics module.
module Tests.NHol.tactics

open NHol.lib
open NHol.fusion
open NHol.parser
open NHol.printer
open NHol.equal
open NHol.bool
open NHol.tactics
open NHol.simp
open NHol.``class``

open NUnit.Framework


/// Performs setup for this test fixture.
/// Executed once prior to running any tests in this fixture.
[<TestFixtureSetUp>]
let fixtureSetup () : unit =
    // TEMP : Until any "real" code is added here (if ever), just emit a message
    // to the NUnit console/log so we'll know this function has been executed.
    SetupHelpers.emitEmptyTestFixtureSetupMessage "tactics"

/// Performs setup for each unit test.
/// Executed once prior to running each unit test in this fixture.
[<SetUp>]
let testSetup () : unit =
    // Emit a message to the NUnit console/log to record when this function is called.
    SetupHelpers.emitTestSetupModuleResetMessage "tactics"

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


(* null_inst  tests *)

(* null_meta  tests *)

(* equals_goal  tests *)

(* inst_goal  tests *)

(* compose_insts  tests *)

(* _FALSITY_  tests *)

(* mk_fthm  tests *)

[<Test>]
[<Category("Fails")>]
let ``mk_fthm1``() =

    _FALSITY_ |> ignore

    let thm = _FALSITY_                                                // |- _FALSITY_ <==> F  
    let expected = Sequent ([], parse_term @"_FALSITY_ <==> F")

    thm
    |> evaluate
    |> assertEqual expected

[<Test>]
[<Category("Fails")>]
let ``mk_fthm2``() =

    _FALSITY_ |> ignore

    let thm = fst (EQ_IMP_RULE _FALSITY_)                                  // |- _FALSITY_ ==> F  
    let expected = Sequent ([], parse_term @"_FALSITY_ ==> F")

    thm
    |> evaluate
    |> assertEqual expected

[<Test>]
[<Category("Fails")>]
let ``mk_fthm3``() =

    _FALSITY_ |> ignore

    let thm = fst (EQ_IMP_RULE _FALSITY_)                                  // |- _FALSITY_ ==> F
    let pth = UNDISCH thm                                                  // _FALSITY_ |- F    
    let expected = Sequent ([parse_term @"_FALSITY_";], parse_term @"F")

    pth
    |> evaluate
    |> assertEqual expected

(* VALID  tests *)

(* THEN  tests *)

//// This test crashes VS test runner
//
//[<Test>]
//[<Category("Fails")>]
//let ``{THEN} Applies two tactics in sequence``() =
//    let _ = g <| parse_term @"!x y. (x INSERT s) DELETE y =
//             if x = y then s DELETE y else x INSERT (s DELETE y)"
//    let gs = e (REPEAT GEN_TAC |> THEN <| COND_CASES_TAC)
//
//    List.isEmpty gs
//    |> assertEqual true

(* THENL  tests *)

(* ORELSE  tests *)

(* FAIL_TAC  tests *)

(* NO_TAC  tests *)

(* ALL_TAC  tests *)

(* TRY  tests *)

//[<Test>]
//[<Category("Doesn't compile")>]
//let ``{TRY} Applies two tactics in sequence``() =
//    let _ = g <| parse_term @"(x + 1) EXP 2 = x EXP 2 + 2 * x + 1 /\
//       (x EXP 2 = y EXP 2 ==> x = y) /\
//       (x < y ==> 2 * x + 1 < 2 * y)"
//    let gs = e (REPEAT CONJ_TAC |> THEN <| TRY NHol.int.ARITH_TAC)
//
//    List.length gs
//    |> assertEqual 1

(* REPEAT  tests *)

(* EVERY  tests *)

(* FIRST  tests *)

(* MAP_EVERY  tests *)

(* MAP_FIRST  tests *)

(* CHANGED_TAC  tests *)

(* REPLICATE_TAC  tests *)

(* THEN_TCL  tests *)

(* ORELSE_TCL  tests *)

(* REPEAT_TCL  tests *)

(* REPEAT_GTCL  tests *)

(* ALL_THEN  tests *)

(* NO_THEN  tests *)

(* EVERY_TCL  tests *)

(* FIRST_TCL  tests *)

(* LABEL_TAC  tests *)

(* ASSUME_TAC  tests *)

(* FIND_ASSUM  tests *)

//[<Test>]
////[<Category("Doesn't compile")>]
//let ``{FIND_ASSUM} Apply a theorem-tactic to the the first assumption equal to given terms``() =
//    let _ = g <| parse_term @"0 = x /\ y = 0 ==> f(x + f(y)) = f(f(f(x) * x * y))"
//    let _ = e STRIP_TAC
//    let _ = e(FIND_ASSUM SUBST1_TAC (parse_term @"y = 0") |> THEN <|
//                FIND_ASSUM (SUBST1_TAC << SYM) (parse_term @"0 = x"))
//    let gs = e (REWRITE_TAC [NHol.arith.ADD_CLAUSES; NHol.arith.MULT_CLAUSES])
//
//    List.isEmpty gs
//    |> assertEqual true

(* POP_ASSUM  tests *)

(* ASSUM_LIST  tests *)

(* POP_ASSUM_LIST  tests *)

(* EVERY_ASSUM  tests *)

(* FIRST_ASSUM  tests *)

(* RULE_ASSUM_TAC  tests *)

(* USE_THEN  tests *)

(* REMOVE_THEN  tests *)

(* ASM  tests *)

(* HYP  tests *)

(* ACCEPT_TAC  tests *)

[<Test>]
[<Category("Fails")>]
let ``{ACCEPT_TAC} Solves a goal if supplied with the desired theorem (up to alpha-conversion)``() =
    ETA_AX |> ignore
    let _ = g <| parse_term @"!x. (x <=> T) \/ (x <=> F)"
    let gs = e (ACCEPT_TAC BOOL_CASES_AX)
    Printf.printfn "bca: %A" (Choice.map string_of_thm BOOL_CASES_AX)
    Printf.printfn "gs: %A" (Choice.map string_of_goalstack gs)
    noSubgoal gs
    |> assertEqual true

(* CONV_TAC  tests *)

(* REFL_TAC  tests *)

(* ABS_TAC  tests *)

(* MK_COMB_TAC  tests *)

(* AP_TERM_TAC  tests *)

(* AP_THM_TAC  tests *)

(* BINOP_TAC  tests *)

(* SUBST1_TAC  tests *)

[<Test>]
[<Category("Fails")>]
let ``{SUBST1_TAC} Makes a simple term substitution in a goal using a single equational theorem``() =
    let _ = g <| parse_term @"!p x y. 1 = x /\ p(1) ==> p(x)"
    let _ = e (REPEAT STRIP_TAC)
    let _ = e (FIRST_X_ASSUM(SUBST1_TAC << SYM))
    let gs = e (ASM_REWRITE_TAC [])

    noSubgoal gs
    |> assertEqual true

(* SUBST_ALL_TAC  tests *)

(* BETA_TAC  tests *)

(* SUBST_VAR_TAC  tests *)

(* DISCH_TAC  tests *)

(* MP_TAC  tests *)

(* EQ_TAC  tests *)

(* UNDISCH_TAC  tests *)

(* SPEC_TAC  tests *)

(* X_GEN_TAC  tests *)

(* X_CHOOSE_TAC  tests *)

(* EXISTS_TAC  tests *)

//[<Test>]
//[<Category("Doesn't compile")>]
//let ``{EXISTS_TAC} Solves a goal if supplied with the desired theorem (up to alpha-conversion)``() =
//    let _ = g <| parse_term @"?x. 1 < x /\ x < 3"
//    let gs = e (EXISTS_TAC (parse_term @"2") |> THEN <| NHol.int.ARITH_TAC)
//
//    List.isEmpty gs
//    |> assertEqual true

(* GEN_TAC  tests *)

(* CHOOSE_TAC  tests *)

(* CONJ_TAC  tests *)

(* DISJ1_TAC  tests *)

(* DISJ2_TAC  tests *)

(* DISJ_CASES_TAC  tests *)

(* CONTR_TAC  tests *)

(* MATCH_ACCEPT_TAC  tests *)

[<Test>]
[<Category("Fails")>]
let ``{MATCH_ACCEPT_TAC} Solves a goal which is an instance of the supplied theorem``() =
    let _ = g <| parse_term @"HD [T;F] = T"
    let HD = Choice.result <| Sequent([], parse_term @"!h t. HD(CONS h t) = h")
    let gs = e (MATCH_ACCEPT_TAC HD)

    noSubgoal gs
    |> assertEqual true

(* MATCH_MP_TAC  tests *)

(* CONJUNCTS_THEN2  tests *)

(* CONJUNCTS_THEN  tests *)

(* DISJ_CASES_THEN2  tests *)

(* DISJ_CASES_THEN  tests *)

(* DISCH_THEN  tests *)

(* X_CHOOSE_THEN  tests *)

(* CHOOSE_THEN  tests *)

(* STRIP_THM_THEN  tests *)

(* ANTE_RES_THEN  tests *)

(* IMP_RES_THEN  tests *)

(* STRIP_ASSUME_TAC  tests *)

(* STRUCT_CASES_THEN  tests *)

(* STRUCT_CASES_TAC  tests *)

(* STRIP_GOAL_THEN  tests *)

(* STRIP_TAC  tests *)

(* UNDISCH_THEN  tests *)

(* FIRST_X_ASSUM  tests *)

(* SUBGOAL_THEN  tests *)

(* SUBGOAL_TAC  tests *)

(* FREEZE_THEN  tests *)

(* X_META_EXISTS_TAC  tests *)

(* META_EXISTS_TAC  tests *)

(* META_SPEC_TAC  tests *)

(* CHEAT_TAC  tests *)

(* RECALL_ACCEPT_TAC  tests *)

(* ANTS_TAC  tests *)

(* print_goal  tests *)

(* print_goalstack  tests *)

(* by  tests *)

(* rotate  tests *)

(* mk_goalstate  tests *)

(* TAC_PROOF  tests *)

(* prove  tests *)

(* current_goalstack  tests *)

(* refine  tests *)

(* flush_goalstack  tests *)

(* e  tests *)

(* r  tests *)

(* set_goal  tests *)

(* g  tests *)

(* b  tests *)

(* p  tests *)

(* top_realgoal  tests *)

(* top_goal  tests *)

(* top_thm  tests *)
