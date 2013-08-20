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

//// This test crashes VS test runner
//
//[<Test>]
//let ``{THEN} Applies two tactics in sequence``() =
//    let _ = g <| parse_term @"!x y. (x INSERT s) DELETE y =
//             if x = y then s DELETE y else x INSERT (s DELETE y)"
//    let gs = e (REPEAT GEN_TAC |> THEN <| COND_CASES_TAC)
//
//    List.isEmpty gs
//    |> assertEqual true

//[<Test>]
//let ``{TRY} Applies two tactics in sequence``() =
//    let _ = g <| parse_term @"(x + 1) EXP 2 = x EXP 2 + 2 * x + 1 /\
//       (x EXP 2 = y EXP 2 ==> x = y) /\
//       (x < y ==> 2 * x + 1 < 2 * y)"
//    let gs = e (REPEAT CONJ_TAC |> THEN <| TRY NHol.int.ARITH_TAC)
//
//    List.length gs
//    |> assertEqual 1

//[<Test>]
//let ``{FIND_ASSUM} Apply a theorem-tactic to the the first assumption equal to given terms``() =
//    let _ = g <| parse_term @"0 = x /\ y = 0 ==> f(x + f(y)) = f(f(f(x) * x * y))"
//    let _ = e STRIP_TAC
//    let _ = e(FIND_ASSUM SUBST1_TAC (parse_term @"y = 0") |> THEN <|
//                FIND_ASSUM (SUBST1_TAC << SYM) (parse_term @"0 = x"))
//    let gs = e (REWRITE_TAC [NHol.arith.ADD_CLAUSES; NHol.arith.MULT_CLAUSES])
//
//    List.isEmpty gs
//    |> assertEqual true

[<Test>]
let ``{ACCEPT_TAC} Solves a goal if supplied with the desired theorem (up to alpha-conversion)``() =
    ETA_AX |> ignore
    let _ = g <| parse_term @"!x. (x <=> T) \/ (x <=> F)"
    let gs = e (ACCEPT_TAC BOOL_CASES_AX)
    Printf.printfn "bca: %A" (Choice.map string_of_thm BOOL_CASES_AX)
    Printf.printfn "gs: %A" (Choice.map string_of_goalstack gs)
    noSubgoal gs
    |> assertEqual true

[<Test>]
let ``{SUBST1_TAC} Makes a simple term substitution in a goal using a single equational theorem``() =
    let _ = g <| parse_term @"!p x y. 1 = x /\ p(1) ==> p(x)"
    let _ = e (REPEAT STRIP_TAC)
    let _ = e (FIRST_X_ASSUM(SUBST1_TAC << SYM))
    let gs = e (ASM_REWRITE_TAC [])

    noSubgoal gs
    |> assertEqual true

//[<Test>]
//let ``{EXISTS_TAC} Solves a goal if supplied with the desired theorem (up to alpha-conversion)``() =
//    let _ = g <| parse_term @"?x. 1 < x /\ x < 3"
//    let gs = e (EXISTS_TAC (parse_term @"2") |> THEN <| NHol.int.ARITH_TAC)
//
//    List.isEmpty gs
//    |> assertEqual true

[<Test>]
let ``{MATCH_ACCEPT_TAC} Solves a goal which is an instance of the supplied theorem``() =
    let _ = g <| parse_term @"HD [T;F] = T"
    let HD = Choice.result <| Sequent([], parse_term @"!h t. HD(CONS h t) = h")
    let gs = e (MATCH_ACCEPT_TAC HD)

    noSubgoal gs
    |> assertEqual true

