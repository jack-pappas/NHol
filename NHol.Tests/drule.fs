﻿(*

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

/// Tests for functions in the NHol.drule module.
module Tests.NHol.drule

open NHol.lib
open NHol.fusion
open NHol.basics
open NHol.parser
open NHol.printer
open NHol.equal
open NHol.bool
open NHol.drule
open NHol.``class``

open ExtCore.Control

open NUnit.Framework

#if SKIP_MODULE_INIT
#else
/// Performs setup for this test fixture.
/// Executed once prior to running any tests in this fixture.
[<TestFixtureSetUp>]
let fixtureSetup () : unit =
    // TEMP : Until any "real" code is added here (if ever), just emit a message
    // to the NUnit console/log so we'll know this function has been executed.
    SetupHelpers.emitEmptyTestFixtureSetupMessage "drule"

/// Performs setup for each unit test.
/// Executed once prior to running each unit test in this fixture.
[<SetUp>]
let testSetup () : unit =
    // Emit a message to the NUnit console/log to record when this function is called.
    SetupHelpers.emitTestSetupModuleResetMessage "drule"

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
#endif

(* mk_thm  tests *)

(* MK_CONJ  tests *)

//[<Test>]
//[<Category("Fails")>]
//let ``{MK_CONJ} Conjoin both sides of two equational theorems``() =
//    
//    let given1 = NHol.int.ARITH_RULE <| parse_term @"0 < n <=> ~(n = 0)"
//    let given2 = NHol.int.ARITH_RULE <| parse_term @"1 <= n <=> ~(n = 0)"
//
//    let actual = MK_CONJ given1 given2
//    let expected = Sequent ([], parse_term @"0 < n /\ 1 <= n <=> ~(n = 0) /\ ~(n = 0)")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* MK_DISJ  tests *)

//[<Test>]
//[<Category("Fails")>]
//let ``{MK_DISJ} Disjoin both sides of two equational theorems``() =
//    
//    let given1 = NHol.int.ARITH_RULE <| parse_term @"1 < x <=> 1 <= x - 1"
//    let given2 = NHol.int.ARITH_RULE <| parse_term @"~(1 < x) <=> x = 0 \/ x = 1"
//
//    let actual = MK_DISJ given1 given2
//    let expected = Sequent ([], parse_term @"1 < x \/ ~(1 < x) <=> 1 <= x - 1 \/ x = 0 \/ x = 1")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* MK_FORALL  tests *)

//[<Test>]
//[<Category("Fails")>]
//let ``{MK_FORALL} Universally quantifies both sides of equational theorem``() =
//    
//    let th = NHol.int.ARITH_RULE <| parse_term @"f(x:A) >= 1 <=> ~(f(x) = 0)"
//    let tm = parse_term @"x:A"
//
//    let actual = MK_FORALL tm th
//    let expected = Sequent ([], parse_term @"(!x. f x >= 1) <=> (!x. ~(f x = 0))")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* MK_EXISTS  tests *)

//[<Test>]
//[<Category("Fails")>]
//let ``{MK_EXISTS} Existentially quantifies both sides of equational theorem``() =
//    
//    let th = NHol.int.ARITH_RULE <| parse_term @"f(x:A) >= 1 <=> ~(f(x) = 0)"
//    let tm = parse_term @"x:A"
//
//    let actual = MK_EXISTS tm th
//    let expected = Sequent ([], parse_term @"(?x. f x >= 1) <=> (?x. ~(f x = 0))")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* MP_CONV  tests *)

//open NHol.meson
//open NHol.arith
//open NHol.realarith
//
//[<Test>]
//[<Category("Fails")>]
//let ``{MP_CONV} Removes antecedent of implication theorem by solving it with a conversion``() =
//    
//    let th = MESON [LE_REFL]
//                (parse_term @"(!e. &0 < e / &2 <=> &0 < e) /\
//      (!a x y e. abs(x - a) < e / &2 /\ abs(y - a) < e / &2 ==> abs(x - y) < e)
//      ==> (!e. &0 < e ==> ?n. !m. n <= m ==> abs(x m - a) < e)
//          ==> (!e. &0 < e ==> ?n. !m. n <= m ==> abs(x m - x n) < e)")
//
//    let actual = MP_CONV REAL_ARITH th
//    let expected = Sequent ([], parse_term @"(!e. &0 < e ==> (?n. !m. n <= m ==> abs (x m - a) < e))
//       ==> (!e. &0 < e ==> (?n. !m. n <= m ==> abs (x m - x n) < e))")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* BETAS_CONV  tests *)

(* instantiate  tests *)

(* INSTANTIATE  tests *)

//// This test requires uninitialized module
//[<Test>]
//[<Category("Fails")>]
//let ``{INSTANTIATE} Apply a higher-order instantiation to conclusion of a theorem.``() =
//    let actual = 
//        choice {
//            let! th = SPEC_ALL NOT_FORALL_THM
//            let! t = lhs <| concl th
//            let! i = term_match [] t <| parse_term @"~(!n. prime(n) ==> ODD(n))"
//            return! INSTANTIATE i (Choice.result th)
//        }
//
//    let expected = Sequent ([], parse_term @"~(!x. prime x ==> ODD x) <=> (?x. ~(prime x ==> ODD x))")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

[<Test>]
let ``{INSTANTIATE} Apply a higher-order instantiation to conclusion of a theorem``() =
    let th1:Choice<thm0,exn> = 
        Choice1Of2 (Sequent ([], parse_term @"p /\ q"))

    let instns:instantiation = 
            Choice.get (term_match [] (parse_term @"p:bool") (parse_term @"~a:bool"))

    let newTh = INSTANTIATE instns th1

    newTh
    |> assertEqual (Choice1Of2 (Sequent ([], parse_term @"~a /\ q")))

[<Test>]
let ``{INSTANTIATE} works on manual instantiation``() =
    let betaTh:Choice<thm0,exn> = 
        Choice1Of2 (Sequent ([], parse_term @"(\x:A. (f:A->B) x) (y:A) = (f:A->B) (y:A)"))         // |- (\x. f x) y = f y

    // Trying manual instantiation

    let manualInst:instantiation = 
        (
            [(1, parse_term @"f:E->C")], 
            [(parse_term @"\z:E. t1:C", parse_term @"f:E->C"); (parse_term @"t2:E", parse_term @"y:E")], 
            [(Tyvar "C", Tyvar "B"); (Tyvar "E", Tyvar "A")]
        )

    let newManualTh = INSTANTIATE manualInst betaTh
    let manualTh = Sequent ([], parse_term @"(\x. t1) t2 = t1")

    newManualTh
    |> evaluate
    |> string_of_thm
    |> assertEqual (string_of_thm manualTh)

[<Test>]
let ``{INSTANTIATE} works on a simple instantiation``() =
    let betaTh:Choice<thm0,exn> = 
        Choice1Of2 (Sequent ([], parse_term @"(\x:A. (f:A->B) x) (y:A) = (f:A->B) (y:A)"))         // |- (\x. f x) y = f y
    let inst : instantiation = Choice.get (term_match [] (parse_term @"(\x:A. (f:A->B) x) (y:A)") (parse_term @"(\z:E. t1:C) t2"))

    let newManualTh = INSTANTIATE inst betaTh
    let manualTh = Sequent ([], parse_term @"(\x. t1) t2 = t1")

    newManualTh
    |> evaluate 
    |> string_of_thm
    |> assertEqual (string_of_thm manualTh)

[<Test>]
[<Category("Fails")>]
let ``{BETAS_CONV} Beta conversion over multiple arguments``() =
    let actual = BETAS_CONV <| parse_term @"(\x y. x /\ y) T F"
    let expected = Sequent ([], parse_term @"(\x y. x /\ y) T F = (T /\ F)")

    actual
    |> evaluate
    |> assertEqual expected

(* INSTANTIATE_ALL  tests *)

(* term_match  tests *)

[<Test>]
let ``{term_match} to be defined 1``() =
    let actual = term_match [] (parse_term @"t1:A") (parse_term @"((f:B->A) (x:B))")
    let expected = Choice1Of2 ([], [(parse_term @"((f:B->A) (x:B))", parse_term @"t1:A")], [(aty, aty)])

    actual
    |> assertEqual expected

[<Test>]
let ``{term_match} to be defined 2``() =
    parse_as_binder "\\" |> ignore
    let actual = term_match [] (parse_term @"f:A->B") (parse_term @"\x:A. t1:B")
    let expected = Choice1Of2 ([], [(parse_term @"\x:A. t1:B", parse_term @"f:A->B")], [(aty, aty); (bty, bty)])

    actual
    |> assertEqual expected

(* term_unify  tests *)

(* deep_alpha  tests *)

(* PART_MATCH  tests *)

[<Test>]
[<Category("Fails")>]
let ``{PART_MATCH} Instantiates a theorem by matching part of it to a term``() =
    let th = Choice.result <| Sequent([], parse_term @"!x. x ==> x")
    let actual = PART_MATCH (Choice.map fst << dest_imp) th <| parse_term @"T"
    let expected = Sequent ([], parse_term @"T ==> T")

    actual
    |> evaluate
    |> assertEqual expected

(* GEN_PART_MATCH  tests *)

//[<Test>]
//[<Category("Fails")>]
//let ``{GEN_PART_MATCH} Instantiates a theorem by matching part of it to a term``() =
//    let th = NHol.int.ARITH_RULE <| parse_term @"m = n ==> m + p = n + p"
//    let actual = GEN_PART_MATCH lhand th <| parse_term @"n:num = p"
//    let expected = Sequent ([], parse_term @"n = p ==> n + p' = p + p'")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* MATCH_MP  tests *)

//[<Test>]
//[<Category("Fails")>]
//let ``{MATCH_MP} Modus Ponens inference rule with automatic matching``() =
//    let ith = NHol.int.ARITH_RULE <| parse_term @"!x z:num. x = y ==> (w + z) + x = (w + z) + y"
//    let th = ASSUME <| parse_term @"w:num = z"
//    let actual = MATCH_MP ith th
//    let expected = Sequent ([parse_term @"w = z"], parse_term @"!z'. (w + z') + w = (w + z') + z")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* HIGHER_REWRITE_CONV  tests *)

[<Test>]
[<Category("Fails")>]
let ``{HIGHER_REWRITE_CONV} Rewrite once using more general higher order matching``() =
    loadNumsModule()
    let t = parse_term @"z = if x = 0 then if y = 0 then 0 else x + y else x + y"
    let actual = HIGHER_REWRITE_CONV [COND_ELIM_THM] true t
    let expected = Sequent ([], parse_term @"z = (if x = 0 then if y = 0 then 0 else x + y else x + y) <=>
       (x = 0 ==> z = (if y = 0 then 0 else x + y)) /\ (~(x = 0) ==> z = x + y)")

    actual
    |> evaluate
    |> assertEqual expected

(* new_definition  tests *)
