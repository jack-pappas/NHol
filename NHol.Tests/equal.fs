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

//// This currently fails due to different type vars
//
//[<Test>]
//let ``{RATOR_CONV conv} Applies a conversion to the operator of an application``() =
//    let actual = RATOR_CONV BETA_CONV (parse_term @"(\x y. x /\ y) (T : bool) (F : bool)")
//    let expected = Sequent ([], parse_term @"(\x y. x /\ y) (T : bool) (F : bool) = (\y. T /\ y) F")
//
//    actual
//    |> evaluate
//    |> string_of_thm
//    |> assertEqual (string_of_thm expected)

//// This tests require nums module to be initialized
//
//[<Test>]
//let ``{RAND_CONV conv} Applies a conversion to the operator of an application``() =
//    let actual = RAND_CONV num_CONV (parse_term @"SUCC 2")
//    let expected = Sequent ([], parse_term @"SUC 2 = SUC (SUC 1)")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

// This tests require nums module to be initialized

//[<Test>]
//let ``{LAND_CONV conv} Apply a conversion to left-hand argument of binary operator``() =
//    let actual = LAND_CONV NUM_ADD_CONV (parse_term "(2 + 2) + (2 + 2)")
//    let expected = Sequent ([], parse_term @"(2 + 2) + 2 + 2 = 4 + 2 + 2")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This tests require nums module to be initialized
//
//[<Test>]
//let ``{ABS_CONV conv} Applies a conversion to the body of an abstraction``() =
//    let actual = ABS_CONV SYM_CONV (parse_term @"\x. 1 = x")
//    let expected = Sequent ([], parse_term @"(\x. 1 = x) = (\x. x = 1)")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This tests require nums module to be initialized
//
//[<Test>]
//let ``{BINDER_CONV conv} Applies conversion to the body of a binder``() =
//    let actual = BINDER_CONV SYM_CONV (parse_term "@n. n = m + 1")
//    let expected = Sequent ([], parse_term @"(@n. n = m + 1) = (@n. m + 1 = n)")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This tests require nums module to be initialized
//
//[<Test>]
//let ``{BINOP_CONV conv} Applies a conversion to both arguments of a binary operator``() =
//    let actual = BINOP_CONV NUM_ADD_CONV (parse_term "(1 + 1) * (2 + 2)")
//    let expected = Sequent ([], parse_term @"(1 + 1) * (2 + 2) = 2 * 4")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This tests require nums module to be initialized
//
//[<Test>]
//let ``{ONCE_DEPTH_CONV conv} Applies a conversion to both arguments of a binary operator``() =
//    let actual = ONCE_DEPTH_CONV BETA_CONV (parse_term @"(\x. (\y. y + x) 1) 2")
//    let expected = Sequent ([], parse_term @"(\x. (\y. y + x) 1) 2 = (\y. y + 2) 1")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This tests require nums module to be initialized
//
//[<Test>]
//let ``{DEPTH_CONV conv} Applies a conversion to both arguments of a binary operator``() =
//    let actual = DEPTH_CONV BETA_CONV (parse_term @"(\x. (\y. y + x) 1) 2")
//    let expected = Sequent ([], parse_term @"(\x. (\y. y + x) 1) 2 = 1 + 2")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This tests require nums module to be initialized
//
//[<Test>]
//let ``{REDEPTH_CONV conv} Applies a conversion bottom-up to all subterms, retraversing changed ones``() =
//    let actual = REDEPTH_CONV BETA_CONV (parse_term @"(\f x. (f x) + 1) (\y.y) 2")
//    let expected = Sequent ([], parse_term @"(\f x. f x + 1) (\y. y) 2 = 2 + 1")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This crashes VS test runner
//
//[<Test>]
//let ``{TOP_DEPTH_CONV conv} Applies a conversion top-down to all subterms, retraversing changed ones``() =
//    let actual = TOP_DEPTH_CONV BETA_CONV (parse_term @"(\x. (\y. (\z. z + y) (y + 1)) (x + 2)) 3")
//    let expected = Sequent ([], parse_term @"(\x. (\y. (\z. z + y) (y + 1)) (x + 2)) 3 = ((3 + 2) + 1) + 3 + 2")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This tests require nums module to be initialized
//
//[<Test>]
//let ``{PATH_CONV string conv} Applies a conversion to the subterm indicated by a path string``() =
//    let actual = PATH_CONV "rlr" NUM_ADD_CONV (parse_term @"(1 + 2) + (3 + 4) + (5 + 6)")
//    let expected = Sequent ([], parse_term @"(1 + 2) + (3 + 4) + 5 + 6 = (1 + 2) + 7 + 5 + 6")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This tests require nums module to be initialized
//
//[<Test>]
//let ``{PAT_CONV term conv} Apply a conversion at subterms identified by a ''pattern'' lambda-abstraction``() =
//    let actual = PAT_CONV (parse_term @"\x. x + a + x") NUM_ADD_CONV (parse_term @"(1 + 2) + (3 + 4) + (5 + 6)")
//    let expected = Sequent ([], parse_term @"(1 + 2) + (3 + 4) + 5 + 6 = 3 + (3 + 4) + 11")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

[<Test>]
let ``{SYM_CONV} Interchanges the left and right-hand sides of an equation``() =
    let actual = SYM_CONV (parse_term @"(F : bool) = x") 
    let expected = Sequent ([], parse_term @"(F : bool) = x <=> x = F")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{CONV_RULE conv thm} Makes an inference rule from a conversion``() =
    let tm = parse_term @"(\x. x \/ (F : bool)) (T: bool)"
    let actual = CONV_RULE BETA_CONV (ASSUME tm)
    let expected = Sequent ([tm], parse_term @"(T : bool) \/ (F : bool)")

    actual
    |> evaluate
    |> assertEqual expected

//// This test requires uninitialized modules
//
//open NHol.int
//
//[<Test>]
//let ``{SUBS_CONV thml} Substitution conversion``() =
//    let tm = parse_term @"(\x. x \/ (F : bool)) (T: bool)"
//    let actual = SUBS_CONV [ARITH_RULE (parse_term @"x + 0 = x")] (parse_term @"(x + 0) + (y + 0) + (x + 0) + (0 + 0)")
//    let expected = Sequent ([], parse_term @"(x + 0) + (y + 0) + (x + 0) + 0 + 0 = x + (y + 0) + x + 0 + 0")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This test fails due to different type vars
//
//[<Test>]
//let ``{BETA_RULE thm} Beta-reduces all the beta-redexes in the conclusion of a theorem``() =
//    let tm = parse_term @"f = ((\x y. x + y) y)"
//    let actual = BETA_RULE (ASSUME tm)
//    let expected = Sequent ([tm], parse_term @"f = ((\x y. x + y) y)")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//// This test requires uninitialized modules
//
//open NHol.arith
//
//[<Test>]
//let ``{GSYM thm} everses the first equation(s) encountered in a top-down search``() =
//    let actual = GSYM ADD
//    let expected = Sequent ([], parse_term @"(!n. n = 0 + n) /\ (!m n. SUC (m + n) = SUC m + n)")
//
//    actual
//    |> evaluate
//    |> assertEqual expected