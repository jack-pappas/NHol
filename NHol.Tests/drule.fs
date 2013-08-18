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

/// Tests for functions in the NHol.equal module.
module Tests.NHol.drule

open NHol.lib
open NHol.fusion.Hol_kernel
open NHol.basics
open NHol.parser
open NHol.printer
open NHol.equal
open NHol.bool
open NHol.drule
open NHol.``class``

open ExtCore.Control

open NUnit.Framework

//[<Test>]
//let ``{MK_CONJ} Conjoin both sides of two equational theorems``() =
//    
//    let given1 = NHol.int.ARITH_RULE <| parse_term @"0 < n <=> ~(n = 0)"
//    let given2 = NHol.int.ARITH_RULE <| parse_term @"1 <= n <=> ~(n = 0)"
//
//    let actual = MK_CONJ given1 given2
//    let expected = Sequent ([], parse_term @"0 < n /\ 1 <= n <=> ~(n = 0) /\ ~(n = 0)")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//[<Test>]
//let ``{MK_DISJ} Disjoin both sides of two equational theorems``() =
//    
//    let given1 = NHol.int.ARITH_RULE <| parse_term @"1 < x <=> 1 <= x - 1"
//    let given2 = NHol.int.ARITH_RULE <| parse_term @"~(1 < x) <=> x = 0 \/ x = 1"
//
//    let actual = MK_DISJ given1 given2
//    let expected = Sequent ([], parse_term @"1 < x \/ ~(1 < x) <=> 1 <= x - 1 \/ x = 0 \/ x = 1")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//[<Test>]
//let ``{MK_FORALL} Universally quantifies both sides of equational theorem``() =
//    
//    let th = NHol.int.ARITH_RULE <| parse_term @"f(x:A) >= 1 <=> ~(f(x) = 0)"
//    let tm = parse_term @"x:A"
//
//    let actual = MK_FORALL tm th
//    let expected = Sequent ([], parse_term @"(!x. f x >= 1) <=> (!x. ~(f x = 0))")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//[<Test>]
//let ``{MK_EXISTS} Existentially quantifies both sides of equational theorem``() =
//    
//    let th = NHol.int.ARITH_RULE <| parse_term @"f(x:A) >= 1 <=> ~(f(x) = 0)"
//    let tm = parse_term @"x:A"
//
//    let actual = MK_EXISTS tm th
//    let expected = Sequent ([], parse_term @"(?x. f x >= 1) <=> (?x. ~(f x = 0))")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//open NHol.meson
//open NHol.arith
//open NHol.realarith
//
//[<Test>]
//let ``{MP_CONV} Removes antecedent of implication theorem by solving it with a conversion``() =
//    
//    let th = MESON [LE_REFL]
//                (parse_term @"(!e. &0 < e / &2 <=> &0 < e) /\
//      (!a x y e. abs(x - a) < e / &2 /\ abs(y - a) < e / &2 ==> abs(x - y) < e)
//      ==> (!e. &0 < e ==> ?n. !m. n <= m ==> abs(x m - a) < e)
//          ==> (!e. &0 < e ==> ?n. !m. n <= m ==> abs(x m - x n) < e)")
//
//    let actual = MP_CONV REAL_ARITH th
//    let expected = Sequent ([], parse_term @"(!e. &0 < e ==> (?n. !m. n <= m ==> abs (x m - a) < e))
//       ==> (!e. &0 < e ==> (?n. !m. n <= m ==> abs (x m - x n) < e))")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//[<Test>]
//let ``{INSTANTIATE} Apply a higher-order instantiation to conclusion of a theorem.``() =
//    let actual = 
//        choice {
//            let! th = SPEC_ALL NOT_FORALL_THM
//            let! t = lhs <| concl th
//            let! i = term_match [] t <| parse_term @"~(!n. prime(n) ==> ODD(n))"
//            return! INSTANTIATE i (Choice.result th)
//        }
//    let expected = Sequent ([], parse_term @"~(!x. prime x ==> ODD x) <=> (?x. ~(prime x ==> ODD x))")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

[<Test>]
let ``{BETAS_CONV} Beta conversion over multiple arguments``() =
    let actual = BETAS_CONV <| parse_term @"(\x y. x /\ y) T F"
    let expected = Sequent ([], parse_term @"(\x y. x /\ y) T F = T /\ F")

    actual
    |> evaluate
    |> assertEqual expected

[<Test>]
let ``{PART_MATCH} Instantiates a theorem by matching part of it to a term``() =
    let th = Choice.result <| Sequent([], parse_term @"!x. x ==> x")
    let actual = PART_MATCH (Choice.map fst << dest_imp) th <| parse_term @"T"
    let expected = Sequent ([], parse_term @"T ==> T")

    actual
    |> evaluate
    |> assertEqual expected

//[<Test>]
//let ``{GEN_PART_MATCH} Instantiates a theorem by matching part of it to a term``() =
//    let th = NHol.int.ARITH_RULE <| parse_term @"m = n ==> m + p = n + p"
//    let actual = GEN_PART_MATCH lhand th <| parse_term @"n:num = p"
//    let expected = Sequent ([], parse_term @"n = p ==> n + p' = p + p'")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//[<Test>]
//let ``{MATCH_MP} Modus Ponens inference rule with automatic matching``() =
//    let ith = NHol.int.ARITH_RULE <| parse_term @"!x z:num. x = y ==> (w + z) + x = (w + z) + y"
//    let th = ASSUME <| parse_term @"w:num = z"
//    let actual = MATCH_MP ith th
//    let expected = Sequent ([parse_term @"w = z"], parse_term @"!z'. (w + z') + w = (w + z') + z")
//
//    actual
//    |> evaluate
//    |> assertEqual expected

//[<Test>]
//let ``{HIGHER_REWRITE_CONV} Rewrite once using more general higher order matching``() =
//    let t = parse_term @"z = if x = 0 then if y = 0 then 0 else x + y else x + y"
//    let actual = HIGHER_REWRITE_CONV [COND_ELIM_THM] true t
//    let expected = Sequent ([], parse_term @"z = (if x = 0 then if y = 0 then 0 else x + y else x + y) <=>
//       (x = 0 ==> z = (if y = 0 then 0 else x + y)) /\ (~(x = 0) ==> z = x + y)")
//
//    actual
//    |> evaluate
//    |> assertEqual expected