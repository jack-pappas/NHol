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
    |> assertEqual expected

[<Test>]
let ``{SYM th} swaps left-hand and right-hand sides of an equation``() =

    parse_as_infix("=", (12, "right")) |> ignore
    let given = ASSUME (parse_term @"t1:A = t2")
    let actual = SYM given
    let expected = Sequent ([parse_term @"t1:A = t2"], parse_term @"t2:A = t1")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{ALPHA tm1 tm2} Proves equality of alpha-equivalent terms``() =

    parse_as_infix("=", (12, "right")) |> ignore
    parse_as_binder "\\" |> ignore
    let actual = ALPHA (parse_term @"\x:A. x") (parse_term @"\y:A. y")
    let expected = Sequent ([], parse_term @"(\x:A. x) = (\y:A. y)")

    actual
    |> evaluate
    |> assertEqual expected

open NHol.nums
open NHol.calc_num

//// This test requires nums module to be initialized
//
//[<Test>]
//let ``{ALPHA_CONV tm1 tm2} Renames the bound variable of a lambda-abstraction``() =
//    num_tydef |> ignore
//    let actual = ALPHA_CONV (parse_term @"y:num") (parse_term @"\x. x + 1")
//    let expected = Sequent ([], parse_term @"(\x. x + 1) = (\y. y + 1)")
//
//    actual
//    |> evaluate
//    |> assertEqual expected
//

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "alpha: Invalid new variable")>]
let ``{ALPHA_CONV tm1 tm2} Fails on unbounded variables``() =
    let actual = ALPHA_CONV (parse_term @"y:bool") (parse_term @"\x. x /\ y")

    actual
    |> evaluate
    |> ignore

//// This test has wrong inputs
//
//[<Test>]
//let ``{GEN_ALPHA_CONV tm1 tm2} Renames the bound variable of an abstraction or binder``() =
//    let actual = GEN_ALPHA_CONV (parse_term @"y") (parse_term @"\x. x /\ y")
//    let expected = Sequent ([], parse_term @"(\x. x /\ y) = (\y. x /\ x)")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This test requires calc_num module to be initialized
//
//[<Test>]
//let ``{MK_BINOP tm1 (th1, th2)} Compose equational theorems with binary operator``() =
//    let th1 = NUM_REDUCE_CONV (parse_term @"2 * 2")
//    let th2 = NUM_REDUCE_CONV (parse_term @"2 EXP 2")
//    let actual = MK_BINOP (parse_term @"(+):num->num->num") (th1, th2)
//    let expected = Sequent ([], parse_term @"2 * 2 + 2 EXP 2 = 4 + 4")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This test requires calc_num module to be initialized
//
//[<Test>]
//let ``{THENC conv1 conv2} Applies two conversions in sequence``() =
//    let actual = (BETA_CONV |> THENC <| NUM_ADD_CONV) (parse_term @"(\x. x + 1) 3")
//    let expected = Sequent ([], parse_term @"(\x. x + 1) 3 = 4")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This test requires calc_num module to be initialized
//
//[<Test>]
//let ``{ORELSEC conv1 conv2} Applies the first of two conversions that succeeds``() =
//    let actual = (NUM_ADD_CONV |> ORELSEC <| NUM_MULT_CONV) (parse_term @"1 * 1")
//    let expected = Sequent ([], parse_term @"1 * 1 = 1")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This test requires calc_num module to be initialized
//
//[<Test>]
//let ``{FIRST_CONV convl conv} Apply the first of the conversions in a given list that succeeds``() =
//    let actual = FIRST_CONV [NUM_ADD_CONV; NUM_MULT_CONV; NUM_EXP_CONV] (parse_term @"12 * 12")
//    let expected = Sequent ([], parse_term @"12 * 12 = 144")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This test requires calc_num module to be initialized
//
//[<Test>]
//let ``{EVERY_CONV convl conv} Applies in sequence all the conversions in a given list of conversions``() =
//    let actual = EVERY_CONV [BETA_CONV; NUM_ADD_CONV] (parse_term @"(\x. x + 2) 5")
//    let expected = Sequent ([], parse_term @"(\x. x + 2) 5 = 7")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

[<Test>]
let ``{REPEATC conv} Repeatedly apply a conversion (zero or more times) until it fails``() =
    let actual = REPEATC BETA_CONV (parse_term @"(\x. (\y. x /\ y) (x /\ T)) (T : bool)")
    let expected = Sequent ([], parse_term @"(\x. (\y. x /\ y) (x /\ T)) (T : bool) = (T /\ T /\ T)")

    actual
    |> evaluate
    |> assertEqual expected

//// This test requires calc_num module to be initialized
//
//[<Test>]
//let ``{CHANGED_CONV conv} Makes a conversion fail if applying it leaves a term unchanged``() =
//    let actual = REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV num_CONV)) (parse_term @"6")
//    let expected = Sequent ([], parse_term @"6 = SUC (SUC (SUC (SUC (SUC (SUC 0)))))")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

[<Test>]
let ``{TRY_CONV conv} Attempts to apply a conversion; applies identity conversion in case of failure``() =
    let actual = TRY_CONV BETA_CONV (parse_term @"T : bool")
    let expected = Sequent ([], parse_term @"(T : bool) = T")

    actual
    |> evaluate
    |> assertEqual expected
