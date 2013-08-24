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

/// Tests for functions in the NHol.canon module.
module Tests.NHol.canon

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
open NHol.canon

open NUnit.Framework


/// Performs setup for this test fixture.
/// Executed once prior to running any tests in this fixture.
[<TestFixtureSetUp>]
let fixtureSetup () : unit =
    // TEMP : Until any "real" code is added here (if ever), just emit a message
    // to the NUnit console/log so we'll know this function has been executed.
    SetupHelpers.emitEmptyTestFixtureSetupMessage "canon"

/// Performs setup for each unit test.
/// Executed once prior to running each unit test in this fixture.
[<SetUp>]
let testSetup () : unit =
    // Emit a message to the NUnit console/log to record when this function is called.
    SetupHelpers.emitTestSetupModuleResetMessage "canon"

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
    ModuleReset.bool ()
    ModuleReset.drule ()
    ModuleReset.tactics ()
    ModuleReset.itab ()
    ModuleReset.simp ()
    ModuleReset.theorems ()
    ModuleReset.ind_defs ()
    ModuleReset.``class`` ()
    ModuleReset.trivia ()
    ModuleReset.canon ()


[<Test>]
[<Category("Fails")>]
let ``{PRESIMP_CONV} Applies basic propositional simplifications and some miniscoping``() =
    loadNumsModule()
    let actual = PRESIMP_CONV (parse_term @"?x. x = 1 /\ y = 1 \/ F \/ T /\ y = 2")
    let expected = Sequent([], parse_term @"(?x. x = 1 /\ y = 1 \/ F \/ T /\ y = 2) <=>
       (?x. x = 1) /\ y = 1 \/ y = 2")

    actual
    |> evaluate
    |> string_of_thm
    |> assertEqual (string_of_thm expected)

[<Test>]
[<Category("Fails")>]
let ``{CONJ_ACI_RULE} Proves equivalence of two conjunctions containing same set of conjuncts``() =
    let actual = CONJ_ACI_RULE (parse_term @"(a /\ b) /\ (a /\ c) <=> (a /\ (c /\ a)) /\ b")
    let expected = Sequent([], parse_term @"(a /\ b) /\ a /\ c <=> (a /\ c /\ a) /\ b")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
[<Category("Fails")>]
let ``{DISJ_ACI_RULE} Proves equivalence of two disjunctions containing same set of disjuncts``() =
    let actual = DISJ_ACI_RULE (parse_term @"(p \/ q) \/ (q \/ r) <=> r \/ q \/ p")
    let expected = Sequent([], parse_term @"(p \/ q) \/ q \/ r <=> r \/ q \/ p")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
[<Category("Fails")>]
let ``{CONJ_CANON_CONV} Puts an iterated conjunction in canonical form``() =
    let actual = CONJ_CANON_CONV (parse_term @"(a /\ b) /\ ((b /\ d) /\ a) /\ c")
    let expected = Sequent([], parse_term @"(a /\ b) /\ ((b /\ d) /\ a) /\ c <=> a /\ b /\ c /\ d")

    actual
    |> evaluate
    |> string_of_thm
    |> assertEqual (string_of_thm expected)

[<Test>]
[<Category("Fails")>]
let ``{DISJ_CANON_CONV} Puts an iterated disjunction in canonical form``() =
    let actual = DISJ_CANON_CONV (parse_term @"(c \/ a \/ b) \/ (b \/ a \/ d)")
    let expected = Sequent([], parse_term @"(c \/ a \/ b) \/ b \/ a \/ d <=> a \/ b \/ c \/ d")

    actual
    |> evaluate
    |> string_of_thm
    |> assertEqual (string_of_thm expected)

[<Test>]
[<Category("Fails")>]
let ``{NNF_CONV} Convert a term to negation normal form``() =
    let actual = NNF_CONV (parse_term @"(!x. p(x) <=> q(x)) ==> ~ ?y. p(y) /\ ~q(y)")
    let expected = Sequent([], parse_term @"(!x. p x <=> q x) ==> ~(?y. p y /\ ~q y) <=>
       (?x. p x /\ ~q x \/ ~p x /\ q x) \/ (!y. ~p y \/ q y)")
    
    actual
    |> evaluate
    |> string_of_thm 
    |> assertEqual (string_of_thm expected)

[<Test>]
[<Category("Fails")>]
let ``{NNFC_CONV} Convert a term to negation normal form``() =
    let actual = NNFC_CONV (parse_term @"(!x. p(x) <=> q(x)) ==> ~ ?y. p(y) /\ ~q(y)")
    let expected = Sequent([], parse_term @"(!x. p x <=> q x) ==> ~(?y. p y /\ ~q y) <=>
       (?x. (p x \/ q x) /\ (~p x \/ ~q x)) \/ (!y. ~p y \/ q y)")

    actual
    |> evaluate
    |> string_of_thm
    |> assertEqual (string_of_thm expected)

[<Test>]
[<Category("Fails")>]
let ``{SKOLEM_CONV} Completely Skolemize a term already in negation normal form``() =
    let actual = SKOLEM_CONV (parse_term @"(!x. ?y. P x y) \/ (?u. !v. ?z. P (f u v) z)")
    let expected = Sequent([], parse_term @"(!x. ?y. P x y) \/ (?u. !v. ?z. P (f u v) z) <=>
       (?y u z. (!x. P x (y x)) \/ (!v. P (f u v) (z v)))")

    actual
    |> evaluate
    |> string_of_thm
    |> assertEqual (string_of_thm expected)

[<Test>]
[<Category("Fails")>]
let ``{PRENEX_CONV} Puts a term already in NNF into prenex form``() =
    let actual = PRENEX_CONV (parse_term @"(!x. ?y. P x y) \/ (?u. !v. ?w. Q u v w)")
    let expected = Sequent([], parse_term @"(!x. ?y. P x y) \/ (?u. !v. ?w. Q u v w) <=>
       (!x. ?y u. !v. ?w. P x y \/ Q u v w)")

    actual
    |> evaluate
    |> string_of_thm
    |> assertEqual (string_of_thm expected)

[<Test>]
[<Category("Fails")>]
let ``{WEAK_DNF_CONV} Converts a term already in negation normal form into disjunctive normal form``() =
    let actual = WEAK_DNF_CONV (parse_term @"(a \/ b) /\ (a \/ c /\ e)")
    let expected = Sequent([], parse_term @"(a \/ b) /\ (a \/ c /\ e) <=>
       (a /\ a \/ b /\ a) \/ a /\ c /\ e \/ b /\ c /\ e")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
[<Category("Fails")>]
let ``{DNF_CONV} Converts a term already in negation normal form into disjunctive normal form``() =
    let actual = DNF_CONV (parse_term @"(a \/ b) /\ (a \/ c /\ e)")
    let expected = Sequent([], parse_term @"(a \/ b) /\ (a \/ c /\ e)
 <=> a \/ a /\ b \/ a /\ c /\ e \/ b /\ c /\ e")

    actual
    |> evaluate
    |> string_of_thm
    |> assertEqual (string_of_thm expected)

[<Test>]
[<Category("Fails")>]
let ``{WEAK_CNF_CONV} Converts a term already in negation normal form into conjunctive normal form``() =
    let actual = WEAK_CNF_CONV (parse_term @"(a /\ b) \/ (a /\ b /\ c) \/ d")
    let expected = Sequent([], parse_term @"a /\ b \/ a /\ b /\ c \/ d <=>
       ((a \/ a \/ d) /\ (b \/ a \/ d)) /\
       ((a \/ b \/ d) /\ (b \/ b \/ d)) /\
       (a \/ c \/ d) /\
       (b \/ c \/ d)")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
[<Category("Fails")>]
let ``{CNF_CONV} Converts a term already in negation normal form into conjunctive normal form``() =
    let actual = CNF_CONV (parse_term @"(a /\ b) \/ (a /\ b /\ c) \/ d")
    let expected = Sequent([], parse_term @"a /\ b \/ a /\ b /\ c \/ d <=>
       (a \/ d) /\ (a \/ b \/ d) /\ (a \/ c \/ d) /\ (b \/ d) /\ (b \/ c \/ d)")

    actual
    |> evaluate
    |> string_of_thm
    |> assertEqual (string_of_thm expected)

[<Test>]
[<Category("Fails")>]
let ``{ASSOC_CONV} Right-associates a term with respect to an associative binary operator``() =
    let actual = ASSOC_CONV CONJ_ASSOC (parse_term @"((p /\ q) /\ (r /\ s)) /\ t")
    let expected = Sequent([], parse_term @"((p /\ q) /\ r /\ s) /\ t <=> p /\ q /\ r /\ s /\ t")

    actual
    |> evaluate
    |> assertEqual expected

//// This test crashes VS test runner
//[<Test>]
//[<Category("Fails")>]
//let ``{CONDS_ELIM_CONV} Remove all conditional expressions from a Boolean formula``() =
//    let actual = CONDS_ELIM_CONV (parse_term @"!x y. (if x <= y then y else x) <= z ==> x <= z")
//    let expected = Sequent([], parse_term @"(!x y. (if x <= y then y else x) <= z ==> x <= z) <=>
//       (!x y. ~(x <= y) \/ (y <= z ==> x <= z))")
//
//    actual
//    |> evaluate
//    |> assertEqual expected
//
//// This test crashes VS test runner
//[<Test>]
//[<Category("Fails")>]
//let ``{CONDS_CELIM_CONV} Remove all conditional expressions from a Boolean formula``() =
//    let actual = CONDS_CELIM_CONV (parse_term @"y <= z ==> !x. (if x <= y then y else x) <= z")
//    let expected = Sequent([], parse_term @"y <= z ==> (!x. (if x <= y then y else x) <= z) <=>
//       y <= z ==> (!x. (~(x <= y) \/ y <= z) /\ (x <= y \/ x <= z))")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

[<Test>]
[<Category("Fails")>]
let ``{PROP_ATOM_CONV} Applies a conversion to the `atomic subformulas' of a formula``() =
    let actual = PROP_ATOM_CONV(ONCE_DEPTH_CONV SYM_CONV) (parse_term @"(!x. x = y ==> x = z) <=> (y = z <=> 1 + z = z + 1)")
    let expected = Sequent([], parse_term @"((!x. x = y ==> x = z) <=> y = z <=> 1 + z = z + 1) <=>
       (!x. y = x ==> z = x) <=>
       z = y <=>
       z + 1 = 1 + z")

    actual
    |> evaluate
    |> assertEqual expected