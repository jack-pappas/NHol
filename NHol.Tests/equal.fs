(*

Copyright 2013 Jack Pappas, Anh-Dung Phan

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
module Tests.NHol.equal

open NHol.fusion.Hol_kernel
open NHol.equal
open NHol.parser
open NHol.printer

open NUnit.Framework
open FsUnit

[<Test>]
let ``{mk_primed_var avoid v} returns a variant of v, adding primes, so the new name is not in the avoid list``() =

    mk_primed_var [Var ("x", aty)] (Var ("x", aty))
    |> assertEqual (Choice.result <| Var ("x'", aty))

[<Test>]
let ``{mk_primed_var avoid v} avoids variables of the same name and different types``() =

    mk_primed_var [Var ("x", Tyvar "num")] (Var ("x", aty))
    |> assertEqual (Choice.result <| Var ("x'", aty))

[<Test>]
let ``{mk_primed_var avoid v} avoids constant names``() =

    the_term_constants := [("C", Tyvar "bool")]
    
    let expected = Var ("C'", Tyvar "num")
    let actual = mk_primed_var [] (Var ("C", Tyvar "num"))

    the_term_constants := ["=",Tyapp("fun",[aty;Tyapp("fun",[aty;bool_ty])])]

    actual
    |> assertEqual (Choice.result expected)

(* BETA_CONV tests *)

[<Test>]
let ``{BETA_CONV tm} performs a simple beta conversion``() =

    // (\x. x) v
    let tm = Comb(Abs(Var("x", aty), Var("x", aty)), Var("v", aty))

    // |- (\x. x) v = v
    let expected = 
        Sequent
            ([], 
             Comb
                 (
                  Comb
                      (
                       Const("=", 
                             Tyapp("fun", 
                                   [aty;
                                    Tyapp("fun", 
                                          [aty;
                                           Tyapp("bool", [])])])), 
                       Comb(Abs(Var("x", aty), Var("x", aty)), Var("v", aty))), 
                  Var("v", aty)))

    let actual = BETA_CONV tm

    actual
    |> assertEqual (Choice.result expected)

[<Test>]
let ``{AP_TERM tm th} applies a function to both sides of an equational theorem``() =
    
    // x:bool = y |- x = y
    let th = 
        Sequent
            (
             [Comb
                  (
                   Comb
                       (
                        Const("=", 
                              Tyapp("fun", 
                                    [Tyapp("bool", []);
                                     Tyapp("fun", 
                                           [Tyapp("bool", []);
                                            Tyapp("bool", [])])])), 
                        Var("x", Tyapp("bool", []))), Var("y", Tyapp("bool", [])))], 
             
             Comb
                 (
                  Comb
                      (
                       Const("=", 
                             Tyapp("fun", 
                                   [Tyapp("bool", []);
                                    Tyapp("fun", 
                                          [Tyapp("bool", []);
                                           Tyapp("bool", [])])])), 
                       Var("x", Tyapp("bool", []))), Var("y", Tyapp("bool", []))))

    let expected = 
        Sequent
            (
             [Comb
                  (
                   Comb
                       (
                        Const("=", 
                              Tyapp("fun", 
                                    [Tyapp("bool", []);
                                     Tyapp("fun", 
                                           [Tyapp("bool", []);
                                            Tyapp("bool", [])])])), 
                        Var("x", Tyapp("bool", []))), Var("y", Tyapp("bool", [])))], 
             
             Comb
                 (
                  Comb
                      (
                       Const("=", 
                             Tyapp("fun", 
                                   [Tyapp("bool", []);
                                    Tyapp("fun", 
                                          [Tyapp("bool", []);
                                           Tyapp("bool", [])])])), 
                       
                       Comb
                           (
                            Const("~", 
                                  Tyapp("fun", 
                                        [Tyapp("bool", []);
                                         Tyapp("bool", [])])), 
                            Var("x", Tyapp("bool", [])))), 
                  
                  Comb
                      (
                       Const("~", 
                             Tyapp("fun", 
                                   [Tyapp("bool", []);
                                    Tyapp("bool", [])])), 
                       Var("y", Tyapp("bool", [])))))

    // (~)
    let neg = Const ("~",Tyapp ("fun",[Tyapp ("bool",[]); Tyapp ("bool",[])]))

    let actual = AP_TERM neg (Choice.result th)

    actual
    |> assertEqual (Choice.result expected)

[<Test>]
let ``{AP_THM th tm} proves equality of equal functions applied to a term``() =

    parse_as_infix("=", (12, "right")) |> ignore
    let given = ASSUME (parse_term @"(f:A->B) = (g:A->B)")
    let actual = AP_THM given (parse_term @"(x:A)")
    let expected = Sequent ([parse_term @"(f:A->B) = (g:A->B)"], parse_term @"((f:A->B) x) = ((g:A->B) x)")

    actual
    |> evaluate
    |> should equal expected

[<Test>]
let ``{SYM th} swaps left-hand and right-hand sides of an equation``() =

    parse_as_infix("=", (12, "right")) |> ignore
    let given = ASSUME (parse_term @"t1:A = t2")
    let actual = SYM given
    let expected = Sequent ([parse_term @"t1:A = t2"], parse_term @"t2:A = t1")

    actual
    |> evaluate
    |> should equal expected

[<Test>]
let ``{ALPHA tm1 tm2} Proves equality of alpha-equivalent terms``() =

    parse_as_infix("=", (12, "right")) |> ignore
    parse_as_binder "\\" |> ignore
    let actual = ALPHA (parse_term @"\x:A. x") (parse_term @"\y:A. y")
    let expected = Sequent ([], parse_term @"(\x:A. x) = (\y:A. y)")

    actual
    |> evaluate
    |> should equal expected
