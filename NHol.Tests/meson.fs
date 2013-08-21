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

/// Tests for functions in the NHol.meson module.
module Tests.NHol.meson

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
open NHol.meson

open NUnit.Framework

//// This crashes VS test runner
//[<Test>]
//let ``{MESON} doesn't fail on this simple term``() =
//    let actual = MESON [] <| parse_term @"?!n. n = m"
//    let expected = Sequent ([], parse_term @"?!n. n = m")
//
//    actual
//    |> evaluate
//    |> assertEqual expected
