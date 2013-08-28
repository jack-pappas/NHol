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

#if SKIP_MODULE_INIT
#else
/// Performs setup for this test fixture.
/// Executed once prior to running any tests in this fixture.
[<TestFixtureSetUp>]
let fixtureSetup () : unit =
    // TEMP : Until any "real" code is added here (if ever), just emit a message
    // to the NUnit console/log so we'll know this function has been executed.
    SetupHelpers.emitEmptyTestFixtureSetupMessage "equal"

/// Performs setup for each unit test.
/// Executed once prior to running each unit test in this fixture.
[<SetUp>]
let testSetup () : unit =
    // Emit a message to the NUnit console/log to record when this function is called.
    SetupHelpers.emitTestSetupModuleResetMessage "equal"

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
#endif

(* lhand  tests *)

(* lhs  tests *)

(* rhs  tests *)

(* mk_primed_var  tests *)

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

(* AP_TERM  tests *)

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

(* AP_THM  tests *)

[<Test>]
let ``{AP_THM th tm} proves equality of equal functions applied to a term``() =

    parse_as_infix("=", (12, "right")) |> ignore
    let given = ASSUME (parse_term @"(f:A->B) = (g:A->B)")
    let actual = AP_THM given (parse_term @"(x:A)")
    let expected = Sequent ([parse_term @"(f:A->B) = (g:A->B)"], parse_term @"((f:A->B) x) = ((g:A->B) x)")

    actual
    |> evaluate
    |> assertEqual expected

(* SYM  tests *)

[<Test>]
let ``{SYM th} swaps left-hand and right-hand sides of an equation``() =

    parse_as_infix("=", (12, "right")) |> ignore
    let given = ASSUME (parse_term @"t1:A = t2")
    let actual = SYM given
    let expected = Sequent ([parse_term @"t1:A = t2"], parse_term @"t2:A = t1")

    actual
    |> evaluate
    |> assertEqual expected

(* ALPHA  tests *)

[<Test>]
let ``{ALPHA tm1 tm2} Proves equality of alpha-equivalent terms``() =

    parse_as_infix("=", (12, "right")) |> ignore
    parse_as_binder "\\" |> ignore
    let actual = ALPHA (parse_term @"\x:A. x") (parse_term @"\y:A. y")
    let expected = Sequent ([], parse_term @"(\x:A. x) = (\y:A. y)")

    actual
    |> evaluate
    |> assertEqual expected

(* ALPHA_CONV  tests *)

open NHol.nums
open NHol.calc_num

// This test requires nums module to be initialized

[<Test>]
[<Category("Fails")>]
let ``{ALPHA_CONV tm1 tm2} Renames the bound variable of a lambda-abstraction``() =
    loadNumsModule()
    let actual = ALPHA_CONV (parse_term @"y:num") (parse_term @"\x. x + 1")
    let expected = Sequent ([], parse_term @"(\x. x + 1) = (\y. y + 1)")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "alpha: Invalid new variable")>]
let ``{ALPHA_CONV tm1 tm2} Fails on unbounded variables``() =
    let actual = ALPHA_CONV (parse_term @"y:bool") (parse_term @"\x. x /\ y")

    actual
    |> evaluate
    |> ignore

[<Test>]
let ``{ALPHA_CONV tm1 tm2} Renames the bound variable of a lambda-abstraction 2``() =
    parse_as_infix("=", (12, "right")) |> ignore
    parse_as_binder "\\" |> ignore
    let actual = ALPHA_CONV (parse_term @"y:A") (parse_term @"\x:A. ((t:A->B) x)")
    let expected = Sequent ([], parse_term @"(\x:A. ((t:A->B) x)) = (\y:A. ((t:A->B) y))")

    actual
    |> evaluate
    |> assertEqual expected

(* GEN_ALPHA_CONV  tests *)

//// This test has wrong inputs
//
//[<Test>]
//[<Category("Fails")>]
//let ``{GEN_ALPHA_CONV tm1 tm2} Renames the bound variable of an abstraction or binder``() =
//    let actual = GEN_ALPHA_CONV (parse_term @"y") (parse_term @"\x. x /\ y")
//    let expected = Sequent ([], parse_term @"(\x. x /\ y) = (\y. x /\ x)")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* MK_BINOP  tests *)

//// This test requires calc_num module to be initialized
//
//[<Test>]
//[<Category("Fails")>]
//let ``{MK_BINOP tm1 (th1, th2)} Compose equational theorems with binary operator``() =
//    let th1 = NUM_REDUCE_CONV (parse_term @"2 * 2")
//    let th2 = NUM_REDUCE_CONV (parse_term @"2 EXP 2")
//    let actual = MK_BINOP (parse_term @"(+):num->num->num") (th1, th2)
//    let expected = Sequent ([], parse_term @"2 * 2 + 2 EXP 2 = 4 + 4")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* NO_CONV  tests *)

(* ALL_CONV  tests *)

(* THENC  tests *)

//// This test requires calc_num module to be initialized
//
//[<Test>]
//[<Category("Fails")>]
//let ``{THENC conv1 conv2} Applies two conversions in sequence``() =
//    let actual = (BETA_CONV |> THENC <| NUM_ADD_CONV) (parse_term @"(\x. x + 1) 3")
//    let expected = Sequent ([], parse_term @"(\x. x + 1) 3 = 4")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* ORELSEC  tests *)

//// This test requires calc_num module to be initialized
//
//[<Test>]
//[<Category("Fails")>]
//let ``{ORELSEC conv1 conv2} Applies the first of two conversions that succeeds``() =
//    let actual = (NUM_ADD_CONV |> ORELSEC <| NUM_MULT_CONV) (parse_term @"1 * 1")
//    let expected = Sequent ([], parse_term @"1 * 1 = 1")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* FIRST_CONV  tests *)

//// This test requires calc_num module to be initialized
//
//[<Test>]
//[<Category("Fails")>]
//let ``{FIRST_CONV convl conv} Apply the first of the conversions in a given list that succeeds``() =
//    let actual = FIRST_CONV [NUM_ADD_CONV; NUM_MULT_CONV; NUM_EXP_CONV] (parse_term @"12 * 12")
//    let expected = Sequent ([], parse_term @"12 * 12 = 144")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* EVERY_CONV  tests *)

//// This test requires calc_num module to be initialized
//
//[<Test>]
//[<Category("Fails")>]
//let ``{EVERY_CONV convl conv} Applies in sequence all the conversions in a given list of conversions``() =
//    let actual = EVERY_CONV [BETA_CONV; NUM_ADD_CONV] (parse_term @"(\x. x + 2) 5")
//    let expected = Sequent ([], parse_term @"(\x. x + 2) 5 = 7")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* REPEATC  tests *)

[<Test>]
[<Category("Fails")>]
let ``{REPEATC conv} Repeatedly apply a conversion (zero or more times) until it fails``() =
    let actual = REPEATC BETA_CONV (parse_term @"(\x. (\y. x /\ y) (x /\ T)) (T : bool)")
    let expected = Sequent ([], parse_term @"(\x. (\y. x /\ y) (x /\ T)) (T : bool) = (T /\ T /\ T)")

    actual
    |> evaluate
    |> assertEqual expected

(* CHANGED_CONV  tests *)

//// This test requires calc_num module to be initialized
//
//[<Test>]
//[<Category("Fails")>]
//let ``{CHANGED_CONV conv} Makes a conversion fail if applying it leaves a term unchanged``() =
//    let actual = REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV num_CONV)) (parse_term @"6")
//    let expected = Sequent ([], parse_term @"6 = SUC (SUC (SUC (SUC (SUC (SUC 0)))))")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* TRY_CONV  tests *)

[<Test>]
[<Category("Fails")>]
let ``{TRY_CONV conv} Attempts to apply a conversion; applies identity conversion in case of failure``() =
    let actual = TRY_CONV BETA_CONV (parse_term @"T : bool")
    let expected = Sequent ([], parse_term @"(T : bool) = T")

    actual
    |> evaluate
    |> assertEqual expected

(* RATOR_CONV  tests *)

//// This test crashes VS test runner
//
//[<Test>]
//[<Category("Fails")>]
//let ``{RATOR_CONV conv} Applies a conversion to the operator of an application``() =
//    let actual = RATOR_CONV BETA_CONV (parse_term @"(\x y. x /\ y) T F")
//    let expected = Sequent ([], parse_term @"(\x y. x /\ y) T F = (\y. T /\ y) F")
//
//    actual
//    |> evaluate
//    |> string_of_thm
//    |> assertEqual (string_of_thm expected)

(* RAND_CONV  tests *)

//// This tests require calc_num module to be initialized
//
//[<Test>]
//[<Category("Fails")>]
//let ``{RAND_CONV conv} Applies a conversion to the operator of an application``() =
//    let actual = RAND_CONV num_CONV (parse_term @"SUCC 2")
//    let expected = Sequent ([], parse_term @"SUC 2 = SUC (SUC 1)")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* LAND_CONV  tests *)

//// This tests require calc_num module to be initialized
//
//[<Test>]
//[<Category("Fails")>]
//let ``{LAND_CONV conv} Apply a conversion to left-hand argument of binary operator``() =
//    let actual = LAND_CONV NUM_ADD_CONV (parse_term "(2 + 2) + (2 + 2)")
//    let expected = Sequent ([], parse_term @"(2 + 2) + 2 + 2 = 4 + 2 + 2")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

// This tests require nums module to be initialized

(* COMB2_CONV  tests *)

(* COMB_CONV  tests *)

(* ABS_CONV  tests *)

[<Test>]
[<Category("Fails")>]
let ``{ABS_CONV conv} Applies a conversion to the body of an abstraction``() =
    loadNumsModule()
    let actual = ABS_CONV SYM_CONV (parse_term @"\x. 1 = x")
    let expected = Sequent ([], parse_term @"(\x. 1 = x) = (\x. x = 1)")

    actual
    |> evaluate
    |> assertEqual expected

// This tests require nums module to be initialized

(* BINDER_CONV  tests *)

[<Test>]
[<Category("Fails")>]
let ``{BINDER_CONV conv} Applies conversion to the body of a binder``() =
    let actual = BINDER_CONV SYM_CONV (parse_term "@n. n = m + 1")
    let expected = Sequent ([], parse_term @"(@n. n = m + 1) = (@n. m + 1 = n)")

    actual
    |> evaluate
    |> string_of_thm
    |> assertEqual (string_of_thm expected)

(* BINOP_CONV  tests *)

//// This test requires calc_num module to be initialized
//
//[<Test>]
//[<Category("Fails")>]
//let ``{BINOP_CONV conv} Applies a conversion to both arguments of a binary operator``() =
//    let actual = BINOP_CONV NUM_ADD_CONV (parse_term "(1 + 1) * (2 + 2)")
//    let expected = Sequent ([], parse_term @"(1 + 1) * (2 + 2) = 2 * 4")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

// This test requires nums module to be initialized

(* ONCE_DEPTH_CONV  tests *)

[<Test>]
[<Category("Fails")>]
let ``{ONCE_DEPTH_CONV conv} Applies a conversion to both arguments of a binary operator``() =
    let actual = ONCE_DEPTH_CONV BETA_CONV (parse_term @"(\x. (\y. y + x) 1) 2")
    let expected = Sequent ([], parse_term @"(\x. (\y. y + x) 1) 2 = (\y. y + 2) 1")

    actual
    |> evaluate
    |> assertEqual expected

(* DEPTH_CONV  tests *)

// This test requires nums module to be initialized

[<Test>]
[<Category("Fails")>]
let ``{DEPTH_CONV conv} Applies a conversion to both arguments of a binary operator``() =
    let actual = DEPTH_CONV BETA_CONV (parse_term @"(\x. (\y. y + x) 1) 2")
    let expected = Sequent ([], parse_term @"(\x. (\y. y + x) 1) 2 = 1 + 2")

    actual
    |> evaluate
    |> assertEqual expected

(* REDEPTH_CONV  tests *)

// This test requires nums module to be initialized

[<Test>]
[<Category("Fails")>]
let ``{REDEPTH_CONV conv} Applies a conversion bottom-up to all subterms, retraversing changed ones``() =
    let actual = REDEPTH_CONV BETA_CONV (parse_term @"(\f x. (f x) + 1) (\y.y) 2")
    let expected = Sequent ([], parse_term @"(\f x. f x + 1) (\y. y) 2 = 2 + 1")

    actual
    |> evaluate
    |> assertEqual expected

(* TOP_DEPTH_CONV  tests *)

//// This crashes VS test runner
//
//[<Test>]
//[<Category("Fails")>]
//let ``{TOP_DEPTH_CONV conv} Applies a conversion top-down to all subterms, retraversing changed ones``() =
//    let actual = TOP_DEPTH_CONV BETA_CONV (parse_term @"(\x. (\y. (\z. z + y) (y + 1)) (x + 2)) 3")
//    let expected = Sequent ([], parse_term @"(\x. (\y. (\z. z + y) (y + 1)) (x + 2)) 3 = ((3 + 2) + 1) + 3 + 2")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* TOP_SWEEP_CONV  tests *)

(* DEPTH_BINOP_CONV  tests *)

(* PATH_CONV  tests *)

//// This test requires calc_num module to be initialized
//
//[<Test>]
//[<Category("Fails")>]
//let ``{PATH_CONV string conv} Applies a conversion to the subterm indicated by a path string``() =
//    let actual = PATH_CONV "rlr" NUM_ADD_CONV (parse_term @"(1 + 2) + (3 + 4) + (5 + 6)")
//    let expected = Sequent ([], parse_term @"(1 + 2) + (3 + 4) + 5 + 6 = (1 + 2) + 7 + 5 + 6")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* PAT_CONV  tests *)

//// This tests require calc_num module to be initialized
//
//[<Test>]
//[<Category("Fails")>]
//let ``{PAT_CONV term conv} Apply a conversion at subterms identified by a ''pattern'' lambda-abstraction``() =
//    let actual = PAT_CONV (parse_term @"\x. x + a + x") NUM_ADD_CONV (parse_term @"(1 + 2) + (3 + 4) + (5 + 6)")
//    let expected = Sequent ([], parse_term @"(1 + 2) + (3 + 4) + 5 + 6 = 3 + (3 + 4) + 11")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* SYM_CONV  tests *)

[<Test>]
let ``{SYM_CONV} Interchanges the left and right-hand sides of an equation``() =
    let actual = SYM_CONV (parse_term @"(F : bool) = x") 
    let expected = Sequent ([], parse_term @"(F : bool) = x <=> x = F")

    actual
    |> evaluate
    |> assertEqual expected

(* CONV_RULE  tests *)

[<Test>]
[<Category("Fails")>]
let ``{CONV_RULE conv thm} Makes an inference rule from a conversion``() =
    let tm = parse_term @"(\x. x \/ (F : bool)) (T: bool)"
    let actual = CONV_RULE BETA_CONV (ASSUME tm)
    let expected = Sequent ([tm], parse_term @"(T : bool) \/ (F : bool)")

    actual
    |> evaluate
    |> assertEqual expected

(* SUBS_CONV  tests *)

//// This test requires uninitialized modules
//
//open NHol.int
//
//[<Test>]
//[<Category("Fails")>]
//let ``{SUBS_CONV thml} Substitution conversion``() =
//    let tm = parse_term @"(\x. x \/ (F : bool)) (T: bool)"
//    let actual = SUBS_CONV [ARITH_RULE (parse_term @"x + 0 = x")] (parse_term @"(x + 0) + (y + 0) + (x + 0) + (0 + 0)")
//    let expected = Sequent ([], parse_term @"(x + 0) + (y + 0) + (x + 0) + 0 + 0 = x + (y + 0) + x + 0 + 0")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* BETA_RULE  tests *)

[<Test>]
[<Category("Fails")>]
let ``{BETA_RULE thm} Beta-reduces all the beta-redexes in the conclusion of a theorem``() =
    let tm = parse_term @"f = ((\x y. x + y) y')"
    let actual = BETA_RULE (ASSUME tm)
    let expected = Sequent ([tm], parse_term @"f = (\y. y' + y)")

    // Compare concrete form since AST form consists of different type vars
    actual
    |> evaluate
    |> string_of_thm
    |> assertEqual (string_of_thm expected)

(* GSYM  tests *)

//// This test requires uninitialized modules
//
//open NHol.arith
//
//[<Test>]
//[<Category("Fails")>]
//let ``{GSYM thm} everses the first equation(s) encountered in a top-down search``() =
//    let actual = GSYM ADD
//    let expected = Sequent ([], parse_term @"(!n. n = 0 + n) /\ (!m n. SUC (m + n) = SUC m + n)")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

(* SUBS  tests *)

(* CACHE_CONV  tests *)