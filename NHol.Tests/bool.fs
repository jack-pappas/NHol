(*

Copyright 2013 Domenico Masini

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

/// Tests for functions in the NHol.equal module.
module Tests.NHol.bool

open NHol.fusion.Hol_kernel
open NHol.bool
open NHol.parser
open NHol.printer

open NUnit.Framework
open FsUnit

[<Test>]
let ``{PROVE_HYP} eliminates a provable assumption from a theorem``() =
    
    let given1 = Choice1Of2 (Sequent ([parse_term @"Gamma:bool"], parse_term @"p:bool"))
    let given2 = Choice1Of2 (Sequent ([parse_term @"Delta:bool"; parse_term @"p:bool"], parse_term @"q:bool"))

    let actual = PROVE_HYP given1 given2
    let expected = Sequent ([parse_term @"Delta:bool"; parse_term @"Gamma:bool";], parse_term @"q:bool")

    actual
    |> evaluate
    |> should equal expected

[<Test>]
let ``{PROVE_HYP} should return second theorem if conclusion of the first is not in the assuptions of the second``() =
    
    let given1 = Choice1Of2 (Sequent ([parse_term @"Gamma:bool"], parse_term @"p:bool"))
    let given2 = Choice1Of2 (Sequent ([parse_term @"Delta:bool"], parse_term @"q:bool"))

    let actual = PROVE_HYP given1 given2
    let expected = Sequent ([parse_term @"Delta:bool"], parse_term @"q:bool")

    actual
    |> evaluate
    |> should equal expected

[<Test>]
let ``{TRUTH} proves truth``() =

    let actual = TRUTH
    let expected = Sequent ([], parse_term @"T")

    actual
    |> evaluate
    |> should equal expected

[<Test>]
let ``{EQT_ELIM th} eliminates equality with T``() =

    TRUTH |> ignore
    let given = ASSUME (parse_term @"(p:bool) = T")
    let actual = EQT_ELIM given
    let expected = Sequent ([parse_term @"(p:bool) = T"], parse_term @"p:bool")

    actual
    |> evaluate
    |> should equal expected