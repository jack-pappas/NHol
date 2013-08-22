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