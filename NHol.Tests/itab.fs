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

/// Tests for functions in the NHol.itab module.
module Tests.NHol.itab

open NHol.lib
open NHol.fusion
open NHol.parser
open NHol.printer
open NHol.equal
open NHol.bool
open NHol.tactics
open NHol.itab
open NHol.simp
open NHol.``class``
open NHol.meson

open NUnit.Framework

[<Test>]
let ``{ITAUT_TAC} Simple intuitionistic logic prover``() =
    let _ = g <| parse_term @"!p q. (p ==> q) <=> (~q ==> ~p)"
    let _ = e (REPEAT GEN_TAC |> THEN <| EQ_TAC)
    let _ = e ITAUT_TAC
    let gs = e (MESON_TAC [])

    Choice.map List.isEmpty gs
    |> assertEqual (Choice.result true)

//// This crashes VS test runner
//[<Test>]
//let ``{ITAUT} Attempt to prove term using intuitionistic first-order logic``() =
//    let actual = ITAUT <| parse_term @"~(~(~p)) ==> ~p"
//    let expected = Sequent([], parse_term @"~(~(~p)) ==> ~p")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

