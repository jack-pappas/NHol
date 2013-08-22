(*

Copyright 2013 Anh-Dung Phan, Domenico Masini, Eric Taucher

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

/// Tests for functions in the NHol.pair module.
module Tests.NHol.pair

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
open NHol.pair

open NUnit.Framework

[<Test>]
let ``{let_CONV} Eliminates a single local variable``() =
    let actual = let_CONV (parse_term @"let x = T in x \/ y")
    let expected = Sequent([], parse_term @"(let x = T in x \/ y) = T \/ y")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{let_CONV} Eliminates a tuple binding``() =
    loadNumsModule()
    let actual = let_CONV (parse_term @"let (x,y) = (1,2) in x+y")
    let expected = Sequent([], parse_term @"(let x,y = 1,2 in x + y) = 1 + 2")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{let_CONV} Eliminates two bindings``() =
    loadNumsModule()
    let actual = let_CONV (parse_term @"let x = 1 and y = 2 in x + y + z")
    let expected = Sequent([], parse_term @"(let x = 1 and y = 2 in x + y + z) = 1 + 2 + z")

    actual
    |> evaluate
    |> assertEqual expected

