(*

Copyright 1998 University of Cambridge
Copyright 1998-2007 John Harrison
Copyright 2013 Jack Pappas, Eric Taucher

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

#if INTERACTIVE
#else
/// Definition of real numbers.
module NHol.realax

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

open NHol
open lib
open fusion
open fusion.Hol_kernel
open basics
open nets
open printer
open preterm
open parser
open equal
open bool
open drule
open tactics
open itab
open simp
open theorems
open ind_defs
open ``class``
open trivia
open canon
open meson
open quot
open pair
open nums
open recursion
open arith
open wf
open calc_num
open normalizer
open grobner
//open ind_types
//open lists
#endif

parse_as_infix("++", (16, "right"))
parse_as_infix("**", (20, "right"))
parse_as_infix("<<=", (12, "right"))
parse_as_infix("===", (10, "right"))
parse_as_infix("treal_mul", (20, "right"))
parse_as_infix("treal_add", (16, "right"))
parse_as_infix("treal_le", (12, "right"))
parse_as_infix("treal_eq", (10, "right"))
make_overloadable "+" (parse_type @"A->A->A")
make_overloadable "-" (parse_type @"A->A->A")
make_overloadable "*" (parse_type @"A->A->A")
make_overloadable "/" (parse_type @"A->A->A")
make_overloadable "<" (parse_type @"A->A->bool")
make_overloadable "<=" (parse_type @"A->A->bool")
make_overloadable ">" (parse_type @"A->A->bool")
make_overloadable ">=" (parse_type @"A->A->bool")
make_overloadable "--" (parse_type @"A->A")
make_overloadable "pow" (parse_type @"A->num->A")
make_overloadable "inv" (parse_type @"A->A")
make_overloadable "abs" (parse_type @"A->A")
make_overloadable "max" (parse_type @"A->A->A")
make_overloadable "min" (parse_type @"A->A->A")
make_overloadable "&" (parse_type @"num->A")
do_list overload_interface ["+", (parse_term @"(+):num->num->num")
                            "-", (parse_term @"(-):num->num->num")
                            "*", (parse_term @"(*):num->num->num")
                            "<", (parse_term @"(<):num->num->bool")
                            "<=", (parse_term @"(<=):num->num->bool")
                            ">", (parse_term @"(>):num->num->bool")
                            ">=", (parse_term @"(>=):num->num->bool")]

(* ------------------------------------------------------------------------- *)
(* The main infix overloaded operations                                      *)
(* ------------------------------------------------------------------------- *)
/// Give natural number type 'num' priority in operator overloading.
let prioritize_num() = prioritize_overload(mk_type("num", []))

(* ------------------------------------------------------------------------- *)
(* Absolute distance function on the naturals.                               *)
(* ------------------------------------------------------------------------- *)
let dist = new_definition(parse_term @"dist(m,n) = (m - n) + (n - m)")

(* ------------------------------------------------------------------------- *)
(* Some easy theorems.                                                       *)
(* ------------------------------------------------------------------------- *)
let DIST_REFL = 
    prove
        ((parse_term @"!n. dist(n,n) = 0"), 
         REWRITE_TAC [dist; SUB_REFL; ADD_CLAUSES])

let DIST_LZERO = 
    prove
        ((parse_term @"!n. dist(0,n) = n"), 
         REWRITE_TAC [dist; SUB_0; ADD_CLAUSES])
let DIST_RZERO = 
    prove
        ((parse_term @"!n. dist(n,0) = n"), 
         REWRITE_TAC [dist; SUB_0; ADD_CLAUSES])
let DIST_SYM = 
    prove
        ((parse_term @"!m n. dist(m,n) = dist(n,m)"), 
         REWRITE_TAC [dist]
         |> THEN <| MATCH_ACCEPT_TAC ADD_SYM)
let DIST_LADD = 
    prove
        ((parse_term @"!m p n. dist(m + n,m + p) = dist(n,p)"), 
         REWRITE_TAC [dist; SUB_ADD_LCANCEL])
let DIST_RADD = 
    prove
        ((parse_term @"!m p n. dist(m + p,n + p) = dist(m,n)"), 
         REWRITE_TAC [dist; SUB_ADD_RCANCEL])
let DIST_LADD_0 = 
    prove
        ((parse_term @"!m n. dist(m + n,m) = n"), 
         REWRITE_TAC [dist; ADD_SUB2; ADD_SUBR2; ADD_CLAUSES])
let DIST_RADD_0 = 
    prove
        ((parse_term @"!m n. dist(m,m + n) = n"), 
         ONCE_REWRITE_TAC [DIST_SYM]
         |> THEN <| MATCH_ACCEPT_TAC DIST_LADD_0)
let DIST_LMUL = 
    prove
        ((parse_term @"!m n p. m * dist(n,p) = dist(m * n,m * p)"), 
         REWRITE_TAC [dist; LEFT_ADD_DISTRIB; LEFT_SUB_DISTRIB])
let DIST_RMUL = 
    prove
        ((parse_term @"!m n p. dist(m,n) * p = dist(m * p,n * p)"), 
         REWRITE_TAC [dist; RIGHT_ADD_DISTRIB; RIGHT_SUB_DISTRIB])
let DIST_EQ_0 = 
    prove
        ((parse_term @"!m n. (dist(m,n) = 0) <=> (m = n)"), 
         REWRITE_TAC [dist; ADD_EQ_0; SUB_EQ_0; LE_ANTISYM])

(* ------------------------------------------------------------------------- *)
(* Simplifying theorem about the distance operation.                         *)
(* ------------------------------------------------------------------------- *)
let DIST_ELIM_THM = 
    prove
        ((parse_term @"P(dist(x,y)) <=> !d. ((x = y + d) ==> P(d)) /\ ((y = x + d) ==> P(d))"), 
         DISJ_CASES_TAC(SPECL [(parse_term @"x:num")
                               (parse_term @"y:num")] LE_CASES)
         |> THEN 
         <| POP_ASSUM
                (X_CHOOSE_THEN (parse_term @"e:num") SUBST1_TAC 
                 << REWRITE_RULE [LE_EXISTS])
         |> THEN <| REWRITE_TAC [dist; ADD_SUB; ADD_SUB2; ADD_SUBR; ADD_SUBR2]
         |> THEN <| REWRITE_TAC [ADD_CLAUSES; EQ_ADD_LCANCEL]
         |> THEN <| GEN_REWRITE_TAC (RAND_CONV << ONCE_DEPTH_CONV) [EQ_SYM_EQ]
         |> THEN <| REWRITE_TAC [GSYM ADD_ASSOC
                                 EQ_ADD_LCANCEL_0; ADD_EQ_0]
         |> THEN <| ASM_CASES_TAC(parse_term @"e = 0")
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| EQ_TAC
         |> THEN <| REPEAT STRIP_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| FIRST_ASSUM MATCH_MP_TAC
         |> THEN <| ASM_REWRITE_TAC [])

(* ------------------------------------------------------------------------- *)
(* Now some more theorems.                                                   *)
(* ------------------------------------------------------------------------- *)
let DIST_LE_CASES, DIST_ADDBOUND, DIST_TRIANGLE, DIST_ADD2, DIST_ADD2_REV = 
    let rec DIST_ELIM_TAC = 
        let conv = 
            HIGHER_REWRITE_CONV [SUB_ELIM_THM; COND_ELIM_THM; DIST_ELIM_THM] 
                false
        CONV_TAC conv
        |> THEN <| TRY GEN_TAC
        |> THEN <| CONJ_TAC
        |> THEN <| DISCH_THEN(fun th -> 
                           SUBST_ALL_TAC th
                           |> THEN <| (let l, r = dest_eq(concl th)
                                       if is_var l && not(vfree_in l r)
                                       then ALL_TAC
                                       else ASSUME_TAC th))
    let DIST_ELIM_TAC' = 
        REPEAT STRIP_TAC
        |> THEN <| REPEAT DIST_ELIM_TAC
        |> THEN <| REWRITE_TAC [GSYM NOT_LT
                                LT_EXISTS]
        |> THEN <| DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC)
        |> THEN <| POP_ASSUM MP_TAC
        |> THEN <| CONV_TAC(LAND_CONV NUM_CANCEL_CONV)
        |> THEN <| REWRITE_TAC [ADD_CLAUSES; NOT_SUC]
    let DIST_LE_CASES = 
        prove
            ((parse_term @"!m n p. dist(m,n) <= p <=> (m <= n + p) /\ (n <= m + p)"), 
             REPEAT GEN_TAC
             |> THEN <| REPEAT DIST_ELIM_TAC
             |> THEN <| REWRITE_TAC [GSYM ADD_ASSOC
                                     LE_ADD; LE_ADD_LCANCEL])
    let DIST_ADDBOUND = 
        prove
            ((parse_term @"!m n. dist(m,n) <= m + n"), 
             REPEAT GEN_TAC
             |> THEN <| DIST_ELIM_TAC
             |> THENL <| [ONCE_REWRITE_TAC [ADD_SYM]
                          ALL_TAC]
             |> THEN <| REWRITE_TAC [ADD_ASSOC; LE_ADDR])    
    let distFuncs = (CONJUNCTS << prove)((parse_term @"(!m n p. dist(m,p) <= dist(m,n) + dist(n,p)) /\
         (!m n p q. dist(m + n,p + q) <= dist(m,p) + dist(n,q)) /\
         (!m n p q. dist(m,p) <= dist(m + n,p + q) + dist(n,q))"), DIST_ELIM_TAC')
    match distFuncs with
    | [dist_triangle; dist_add2; dist_add2_rev] -> 
        DIST_LE_CASES, DIST_ADDBOUND, dist_triangle, dist_add2, dist_add2_rev
    | _ -> failwith "distFuncs: Unhnadled case."

let DIST_TRIANGLE_LE = 
    prove
        ((parse_term @"!m n p q. dist(m,n) + dist(n,p) <= q ==> dist(m,p) <= q"), 
         REPEAT STRIP_TAC
         |> THEN <| MATCH_MP_TAC LE_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"dist(m,n) + dist(n,p)")
         |> THEN <| ASM_REWRITE_TAC [DIST_TRIANGLE])

let DIST_TRIANGLES_LE = 
    prove((parse_term @"!m n p q r s.
        dist(m,n) <= r /\ dist(p,q) <= s ==> dist(m,p) <= dist(n,q) + r + s"),
       REPEAT STRIP_TAC
       |> THEN <| MATCH_MP_TAC DIST_TRIANGLE_LE
       |> THEN <| EXISTS_TAC(parse_term @"n:num")
       |> THEN <| GEN_REWRITE_TAC RAND_CONV [ADD_SYM]
       |> THEN <| REWRITE_TAC [GSYM ADD_ASSOC]
       |> THEN <| MATCH_MP_TAC LE_ADD2
       |> THEN <| ASM_REWRITE_TAC []
       |> THEN <| MATCH_MP_TAC DIST_TRIANGLE_LE
       |> THEN <| EXISTS_TAC(parse_term @"q:num")
       |> THEN <| GEN_REWRITE_TAC RAND_CONV [ADD_SYM]
       |> THEN <| REWRITE_TAC [LE_ADD_LCANCEL]
       |> THEN <| ONCE_REWRITE_TAC [DIST_SYM]
       |> THEN <| ASM_REWRITE_TAC [])

(* ------------------------------------------------------------------------- *)
(* Useful lemmas about bounds.                                               *)
(* ------------------------------------------------------------------------- *)
let BOUNDS_LINEAR = 
    prove
        ((parse_term @"!A B C. (!n. A * n <= B * n + C) <=> A <= B"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THENL <| [CONV_TAC CONTRAPOS_CONV
                      |> THEN <| REWRITE_TAC [NOT_LE]
                      |> THEN 
                      <| DISCH_THEN
                             (CHOOSE_THEN SUBST1_TAC << REWRITE_RULE [LT_EXISTS])
                      |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB; LE_ADD_LCANCEL]
                      |> THEN <| DISCH_THEN(MP_TAC << SPEC(parse_term @"SUC C"))
                      |> THEN 
                      <| REWRITE_TAC 
                             [NOT_LE; MULT_CLAUSES; ADD_CLAUSES; LT_SUC_LE]
                      |> THEN <| REWRITE_TAC [ADD_ASSOC; LE_ADDR]
                      DISCH_THEN
                          (CHOOSE_THEN SUBST1_TAC << REWRITE_RULE [LE_EXISTS])
                      |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB
                                              GSYM ADD_ASSOC
                                              LE_ADD]])

let BOUNDS_LINEAR_0 = 
    prove
        ((parse_term @"!A B. (!n. A * n <= B) <=> (A = 0)"), 
         REPEAT GEN_TAC
         |> THEN <| MP_TAC(SPECL [(parse_term @"A:num")
                                  (parse_term @"0")
                                  (parse_term @"B:num")] BOUNDS_LINEAR)
         |> THEN <| REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES; LE])

let BOUNDS_DIVIDED = 
    prove((parse_term @"!P. (?B. !n. P(n) <= B) <=>
       (?A B. !n. n * P(n) <= A * n + B)"),
      GEN_TAC
      |> THEN <| EQ_TAC
      |> THEN <| STRIP_TAC
      |> THENL <| [MAP_EVERY EXISTS_TAC [(parse_term @"B:num")
                                         (parse_term @"0")]
                   |> THEN <| GEN_TAC
                   |> THEN <| REWRITE_TAC [ADD_CLAUSES]
                   |> THEN <| GEN_REWRITE_TAC RAND_CONV [MULT_SYM]
                   |> THEN <| ASM_REWRITE_TAC [LE_MULT_LCANCEL]
                   EXISTS_TAC(parse_term @"P(0) + A + B")
                   |> THEN <| GEN_TAC
                   |> THEN 
                   <| MP_TAC
                          (SPECL [(parse_term @"n:num")
                                  (parse_term @"(P:num->num) n")
                                  (parse_term @"P(0) + A + B")] LE_MULT_LCANCEL)
                   |> THEN <| ASM_CASES_TAC(parse_term @"n = 0")
                   |> THEN <| ASM_REWRITE_TAC [LE_ADD]
                   |> THEN <| DISCH_THEN(SUBST1_TAC << SYM)
                   |> THEN <| MATCH_MP_TAC LE_TRANS
                   |> THEN <| EXISTS_TAC(parse_term @"A * n + B")
                   |> THEN <| ASM_REWRITE_TAC []
                   |> THEN <| REWRITE_TAC [LEFT_ADD_DISTRIB]
                   |> THEN <| GEN_REWRITE_TAC RAND_CONV [ADD_SYM]
                   |> THEN 
                   <| GEN_REWRITE_TAC (RAND_CONV << ONCE_DEPTH_CONV) [MULT_SYM]
                   |> THEN <| REWRITE_TAC [GSYM ADD_ASSOC
                                           LE_ADD_LCANCEL]
                   |> THEN <| MATCH_MP_TAC LE_TRANS
                   |> THEN <| EXISTS_TAC(parse_term @"B * n")
                   |> THEN <| REWRITE_TAC [LE_ADD]
                   |> THEN <| UNDISCH_TAC(parse_term @"~(n = 0)")
                   |> THEN 
                   <| SPEC_TAC((parse_term @"n:num"), (parse_term @"n:num"))
                   |> THEN <| INDUCT_TAC
                   |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; LE_ADD]])

let BOUNDS_NOTZERO = 
    prove((parse_term @"!P A B. (P 0 0 = 0) /\ (!m n. P m n <= A * (m + n) + B) ==>
       (?B. !m n. P m n <= B * (m + n))"),
      REPEAT STRIP_TAC
      |> THEN <| EXISTS_TAC(parse_term @"A + B")
      |> THEN <| REPEAT GEN_TAC
      |> THEN <| ASM_CASES_TAC(parse_term @"m + n = 0")
      |> THENL <| [RULE_ASSUM_TAC(REWRITE_RULE [ADD_EQ_0])
                   |> THEN <| ASM_REWRITE_TAC [LE_0]
                   MATCH_MP_TAC LE_TRANS
                   |> THEN <| EXISTS_TAC(parse_term @"A * (m + n) + B")
                   |> THEN <| ASM_REWRITE_TAC []
                   |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB; LE_ADD_LCANCEL]
                   |> THEN <| UNDISCH_TAC(parse_term @"~(m + n = 0)")
                   |> THEN 
                   <| SPEC_TAC((parse_term @"m + n"), (parse_term @"p:num"))
                   |> THEN <| INDUCT_TAC
                   |> THEN <| REWRITE_TAC [MULT_CLAUSES; LE_ADD]])

let BOUNDS_IGNORE = 
    prove
        ((parse_term @"!P Q. (?B. !i. P(i) <= Q(i) + B) <=>
         (?B N. !i. N <= i ==> P(i) <= Q(i) + B)"),
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| STRIP_TAC
         |> THENL 
         <| [EXISTS_TAC(parse_term @"B:num")
             |> THEN <| ASM_REWRITE_TAC []
             POP_ASSUM MP_TAC
             |> THEN <| SPEC_TAC((parse_term @"B:num"), (parse_term @"B:num"))
             |> THEN <| SPEC_TAC((parse_term @"N:num"), (parse_term @"N:num"))
             |> THEN <| INDUCT_TAC
             |> THENL <| [REWRITE_TAC [LE_0]
                          |> THEN <| GEN_TAC
                          |> THEN <| DISCH_TAC
                          |> THEN <| EXISTS_TAC(parse_term @"B:num")
                          |> THEN <| ASM_REWRITE_TAC []
                          GEN_TAC
                          |> THEN <| DISCH_TAC
                          |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                          |> THEN <| EXISTS_TAC(parse_term @"B + P(N:num)")
                          |> THEN <| X_GEN_TAC(parse_term @"i:num")
                          |> THEN <| DISCH_TAC
                          |> THEN <| ASM_CASES_TAC(parse_term @"SUC N <= i")
                          |> THENL <| [MATCH_MP_TAC LE_TRANS
                                       |> THEN 
                                       <| EXISTS_TAC(parse_term @"Q(i:num) + B")
                                       |> THEN 
                                       <| REWRITE_TAC [LE_ADD; ADD_ASSOC]
                                       |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                                       |> THEN <| ASM_REWRITE_TAC []
                                       UNDISCH_TAC(parse_term @"~(SUC N <= i)")
                                       |> THEN <| REWRITE_TAC [NOT_LE; LT]
                                       |> THEN <| ASM_REWRITE_TAC [GSYM NOT_LE]
                                       |> THEN <| DISCH_THEN SUBST1_TAC
                                       |> THEN <| REWRITE_TAC [ADD_ASSOC]
                                       |> THEN <| ONCE_REWRITE_TAC [ADD_SYM]
                                       |> THEN <| REWRITE_TAC [LE_ADD]]]])

(* ------------------------------------------------------------------------- *)
(* Define type of nearly additive functions.                                 *)
(* ------------------------------------------------------------------------- *)
let is_nadd = 
    new_definition
        (parse_term @"is_nadd x <=> (?B. !m n. dist(m * x(n),n * x(m)) <= B * (m + n))")

let is_nadd_0 = 
    prove
        ((parse_term @"is_nadd (\n. 0)"), 
         REWRITE_TAC [is_nadd; MULT_CLAUSES; DIST_REFL; LE_0])
let nadd_abs, nadd_rep = 
    new_basic_type_definition "nadd" ("mk_nadd", "dest_nadd") is_nadd_0

override_interface("fn", (parse_term @"dest_nadd"))
override_interface("afn", (parse_term @"mk_nadd"))

(* ------------------------------------------------------------------------- *)
(* Properties of nearly-additive functions.                                  *)
(* ------------------------------------------------------------------------- *)
let NADD_CAUCHY = 
    prove
        ((parse_term @"!x. ?B. !m n. dist(m * fn x n,n * fn x m) <= B * (m + n)"), 
         REWRITE_TAC [GSYM is_nadd
                      nadd_rep; nadd_abs; ETA_AX])

let NADD_BOUND = 
    prove
        ((parse_term @"!x. ?A B. !n. fn x n <= A * n + B"), 
         GEN_TAC
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"B:num") 
                (SPEC (parse_term @"x:nadd") NADD_CAUCHY)
         |> THEN <| MAP_EVERY EXISTS_TAC [(parse_term @"B + fn x 1")
                                          (parse_term @"B:num")]
         |> THEN <| GEN_TAC
         |> THEN <| POP_ASSUM(MP_TAC << SPECL [(parse_term @"n:num")
                                               (parse_term @"1")])
         |> THEN <| REWRITE_TAC [DIST_LE_CASES; MULT_CLAUSES]
         |> THEN <| DISCH_THEN(MP_TAC << CONJUNCT2)
         |> THEN 
         <| REWRITE_TAC [LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES]
         |> THEN <| REWRITE_TAC [ADD_AC; MULT_AC])

let NADD_MULTIPLICATIVE = 
    prove
        ((parse_term @"!x. ?B. !m n. dist(fn x (m * n),m * fn x n) <= B * m + B"), 
         GEN_TAC
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"B:num") 
                (SPEC (parse_term @"x:nadd") NADD_CAUCHY)
         |> THEN <| EXISTS_TAC(parse_term @"B + fn x 0")
         |> THEN <| REPEAT GEN_TAC
         |> THEN <| ASM_CASES_TAC(parse_term @"n = 0")
         |> THENL <| [MATCH_MP_TAC(LE_IMP DIST_ADDBOUND)
                      |> THEN 
                      <| ASM_REWRITE_TAC 
                             [MULT_CLAUSES; RIGHT_ADD_DISTRIB; MULT_AC]
                      |> THEN <| REWRITE_TAC [LE_EXISTS]
                      |> THEN <| CONV_TAC(ONCE_DEPTH_CONV NUM_CANCEL_CONV)
                      |> THEN <| REWRITE_TAC [GSYM EXISTS_REFL]
                      UNDISCH_TAC(parse_term @"~(n = 0)")]
         |> THEN <| REWRITE_TAC [TAUT(parse_term @"(~a ==> b) <=> a \/ b")
                                 GSYM LE_MULT_LCANCEL
                                 DIST_LMUL]
         |> THEN <| REWRITE_TAC [MULT_ASSOC]
         |> THEN 
         <| GEN_REWRITE_TAC (LAND_CONV << RAND_CONV << RAND_CONV << LAND_CONV) 
                [MULT_SYM]
         |> THEN <| POP_ASSUM(MATCH_MP_TAC << LE_IMP)
         |> THEN 
         <| REWRITE_TAC 
                [LE_EXISTS; RIGHT_ADD_DISTRIB; LEFT_ADD_DISTRIB; MULT_AC]
         |> THEN <| CONV_TAC(ONCE_DEPTH_CONV NUM_CANCEL_CONV)
         |> THEN <| REWRITE_TAC [GSYM EXISTS_REFL])

let NADD_ADDITIVE = 
    prove
        ((parse_term @"!x. ?B. !m n. dist(fn x (m + n),fn x m + fn x n) <= B"), 
         GEN_TAC
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"B:num") 
                (SPEC (parse_term @"x:nadd") NADD_CAUCHY)
         |> THEN <| EXISTS_TAC(parse_term @"3 * B + fn x 0")
         |> THEN <| REPEAT GEN_TAC
         |> THEN <| ASM_CASES_TAC(parse_term @"m + n = 0")
         |> THENL <| [RULE_ASSUM_TAC(REWRITE_RULE [ADD_EQ_0])
                      |> THEN <| ONCE_REWRITE_TAC [DIST_SYM]
                      |> THEN 
                      <| ASM_REWRITE_TAC [ADD_CLAUSES; DIST_LADD_0; LE_ADDR]
                      MATCH_MP_TAC LE_TRANS
                      |> THEN <| EXISTS_TAC(parse_term @"3 * B")
                      |> THEN <| REWRITE_TAC [LE_ADD]
                      |> THEN <| UNDISCH_TAC(parse_term @"~(m + n = 0)")]
         |> THEN <| REWRITE_TAC [TAUT(parse_term @"(~a ==> b) <=> a \/ b")
                                 GSYM LE_MULT_LCANCEL]
         |> THEN <| REWRITE_TAC [DIST_LMUL; LEFT_ADD_DISTRIB]
         |> THEN 
         <| GEN_REWRITE_TAC (LAND_CONV << RAND_CONV << LAND_CONV) 
                [RIGHT_ADD_DISTRIB]
         |> THEN <| MATCH_MP_TAC(LE_IMP DIST_ADD2)
         |> THEN 
         <| SUBGOAL_THEN 
                (parse_term @"(m + n) * 3 * B = B * (m + m + n) + B * (n + m + n)") 
                SUBST1_TAC
         |> THENL <| [REWRITE_TAC 
                          [SYM(REWRITE_CONV [ARITH] (parse_term @"1 + 1 + 1"))]
                      |> THEN 
                      <| REWRITE_TAC 
                             [RIGHT_ADD_DISTRIB; LEFT_ADD_DISTRIB; MULT_CLAUSES]
                      |> THEN <| REWRITE_TAC [MULT_AC]
                      |> THEN <| CONV_TAC NUM_CANCEL_CONV
                      |> THEN <| REFL_TAC
                      MATCH_MP_TAC LE_ADD2
                      |> THEN <| ASM_REWRITE_TAC []])

let NADD_SUC = 
    prove
        ((parse_term @"!x. ?B. !n. dist(fn x (SUC n),fn x n) <= B"), 
         GEN_TAC
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"B:num") 
                (SPEC (parse_term @"x:nadd") NADD_ADDITIVE)
         |> THEN <| EXISTS_TAC(parse_term @"B + fn x 1")
         |> THEN <| GEN_TAC
         |> THEN <| MATCH_MP_TAC(LE_IMP DIST_TRIANGLE)
         |> THEN <| EXISTS_TAC(parse_term @"fn x n + fn x 1")
         |> THEN <| ASM_REWRITE_TAC [ADD1]
         |> THEN <| MATCH_MP_TAC LE_ADD2
         |> THEN <| ASM_REWRITE_TAC [DIST_LADD_0; LE_REFL])

let NADD_DIST_LEMMA = 
    prove
        ((parse_term @"!x. ?B. !m n. dist(fn x (m + n),fn x m) <= B * n"), 
         GEN_TAC
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"B:num") 
                (SPEC (parse_term @"x:nadd") NADD_SUC)
         |> THEN <| EXISTS_TAC(parse_term @"B:num")
         |> THEN <| GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [ADD_CLAUSES; DIST_REFL; LE_0]
         |> THEN <| MATCH_MP_TAC(LE_IMP DIST_TRIANGLE)
         |> THEN <| EXISTS_TAC(parse_term @"fn x (m + n)")
         |> THEN <| REWRITE_TAC [ADD1; LEFT_ADD_DISTRIB]
         |> THEN <| GEN_REWRITE_TAC RAND_CONV [ADD_SYM]
         |> THEN <| MATCH_MP_TAC LE_ADD2
         |> THEN <| ASM_REWRITE_TAC [GSYM ADD1
                                     MULT_CLAUSES])

let NADD_DIST = 
    prove
        ((parse_term @"!x. ?B. !m n. dist(fn x m,fn x n) <= B * dist(m,n)"), 
         GEN_TAC
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"B:num") 
                (SPEC (parse_term @"x:nadd") NADD_DIST_LEMMA)
         |> THEN <| EXISTS_TAC(parse_term @"B:num")
         |> THEN <| REPEAT GEN_TAC
         |> THEN 
         <| DISJ_CASES_THEN MP_TAC (SPECL [(parse_term @"m:num")
                                           (parse_term @"n:num")] LE_CASES)
         |> THEN 
         <| DISCH_THEN(CHOOSE_THEN SUBST1_TAC << ONCE_REWRITE_RULE [LE_EXISTS])
         |> THENL <| [ONCE_REWRITE_TAC [DIST_SYM]
                      ALL_TAC]
         |> THEN <| ASM_REWRITE_TAC [DIST_LADD_0])

let NADD_ALTMUL = 
    prove
        ((parse_term @"!x y. ?A B. !n. dist(n * fn x (fn y n),fn x n * fn y n) <= A * n + B"), 
         REPEAT GEN_TAC
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"B:num") 
                (SPEC (parse_term @"x:nadd") NADD_CAUCHY)
         |> THEN <| MP_TAC(SPEC (parse_term @"y:nadd") NADD_BOUND)
         |> THEN 
         <| DISCH_THEN
                (X_CHOOSE_THEN (parse_term @"M:num") 
                     (X_CHOOSE_TAC(parse_term @"L:num")))
         |> THEN <| MAP_EVERY EXISTS_TAC [(parse_term @"B * (1 + M)")
                                          (parse_term @"B * L")]
         |> THEN <| GEN_TAC
         |> THEN 
         <| GEN_REWRITE_TAC (LAND_CONV << RAND_CONV << RAND_CONV) [MULT_SYM]
         |> THEN <| MATCH_MP_TAC LE_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"B * (n + fn y n)")
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| REWRITE_TAC [LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB]
         |> THEN <| REWRITE_TAC [MULT_CLAUSES
                                 GSYM ADD_ASSOC
                                 LE_ADD_LCANCEL]
         |> THEN <| ASM_REWRITE_TAC [GSYM LEFT_ADD_DISTRIB
                                     GSYM MULT_ASSOC
                                     LE_MULT_LCANCEL])

override_interface("===", (parse_term @"(nadd_eq):nadd->nadd->bool"))

(* ------------------------------------------------------------------------- *)
(* Definition of the equivalence relation and proof that it *is* one.        *)
(* ------------------------------------------------------------------------- *)
let nadd_eq = 
    new_definition(parse_term @"x === y <=> ?B. !n. dist(fn x n,fn y n) <= B")

let NADD_EQ_REFL = 
    prove
        ((parse_term @"!x. x === x"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_eq; DIST_REFL; LE_0])

let NADD_EQ_SYM = 
    prove((parse_term @"!x y. x === y <=> y === x"), REPEAT GEN_TAC
                                                    |> THEN 
                                                    <| REWRITE_TAC [nadd_eq]
                                                    |> THEN 
                                                    <| GEN_REWRITE_TAC 
                                                           (RAND_CONV 
                                                            << ONCE_DEPTH_CONV) 
                                                           [DIST_SYM]
                                                    |> THEN <| REFL_TAC)

let NADD_EQ_TRANS = 
    prove
        ((parse_term @"!x y z. x === y /\ y === z ==> x === z"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_eq]
         |> THEN 
         <| DISCH_THEN
                (CONJUNCTS_THEN2 (X_CHOOSE_TAC(parse_term @"B1:num")) 
                     (X_CHOOSE_TAC(parse_term @"B2:num")))
         |> THEN <| EXISTS_TAC(parse_term @"B1 + B2")
         |> THEN <| X_GEN_TAC(parse_term @"n:num")
         |> THEN <| MATCH_MP_TAC(LE_IMP DIST_TRIANGLE)
         |> THEN <| EXISTS_TAC(parse_term @"fn y n")
         |> THEN <| MATCH_MP_TAC LE_ADD2
         |> THEN <| ASM_REWRITE_TAC [])

override_interface("&", (parse_term @"nadd_of_num:num->nadd"))

(* ------------------------------------------------------------------------- *)
(* Injection of the natural numbers.                                         *)
(* ------------------------------------------------------------------------- *)
let nadd_of_num = new_definition(parse_term @"&k = afn(\n. k * n)")

let NADD_OF_NUM = 
    prove
        ((parse_term @"!k. fn(&k) = \n. k * n"), 
         REWRITE_TAC [nadd_of_num
                      GSYM nadd_rep
                      is_nadd]
         |> THEN <| REWRITE_TAC [DIST_REFL; LE_0; MULT_AC])

let NADD_OF_NUM_WELLDEF = 
    prove
        ((parse_term @"!m n. (m = n) ==> &m === &n"), 
         REPEAT GEN_TAC
         |> THEN <| DISCH_THEN SUBST1_TAC
         |> THEN <| MATCH_ACCEPT_TAC NADD_EQ_REFL)

let NADD_OF_NUM_EQ = 
    prove
        ((parse_term @"!m n. (&m === &n) <=> (m = n)"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| REWRITE_TAC [NADD_OF_NUM_WELLDEF]
         |> THEN <| REWRITE_TAC [nadd_eq; NADD_OF_NUM]
         |> THEN <| REWRITE_TAC [GSYM DIST_RMUL
                                 BOUNDS_LINEAR_0; DIST_EQ_0])

override_interface("<<=", (parse_term @"nadd_le:nadd->nadd->bool"))

(* ------------------------------------------------------------------------- *)
(* Definition of (reflexive) ordering and the only special property needed.  *)
(* ------------------------------------------------------------------------- *)
let nadd_le = 
    new_definition(parse_term @"x <<= y <=> ?B. !n. fn x n <= fn y n + B")

let NADD_LE_WELLDEF_LEMMA = 
    prove
        ((parse_term @"!x x' y y'. x === x' /\ y === y' /\ x <<= y ==> x' <<= y'"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_eq; nadd_le]
         |> THEN <| REWRITE_TAC [DIST_LE_CASES; FORALL_AND_THM]
         |> THEN 
         <| DISCH_THEN
                (CONJUNCTS_THEN2 (X_CHOOSE_TAC(parse_term @"B1:num")) MP_TAC)
         |> THEN 
         <| DISCH_THEN
                (CONJUNCTS_THEN2 (X_CHOOSE_TAC(parse_term @"B2:num")) MP_TAC)
         |> THEN <| DISCH_THEN(X_CHOOSE_TAC(parse_term @"B:num"))
         |> THEN <| EXISTS_TAC(parse_term @"(B2 + B) + B1")
         |> THEN <| X_GEN_TAC(parse_term @"n:num")
         |> THEN <| FIRST_ASSUM(MATCH_MP_TAC << LE_IMP << CONJUNCT2)
         |> THEN <| REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL]
         |> THEN <| FIRST_ASSUM(MATCH_MP_TAC << LE_IMP)
         |> THEN <| ASM_REWRITE_TAC [LE_ADD_RCANCEL])

let NADD_LE_WELLDEF = 
    prove
        ((parse_term @"!x x' y y'. x === x' /\ y === y' ==> (x <<= y <=> x' <<= y')"), 
         REPEAT STRIP_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| MATCH_MP_TAC NADD_LE_WELLDEF_LEMMA
         |> THEN <| ASM_REWRITE_TAC []
         |> THENL <| [MAP_EVERY EXISTS_TAC [(parse_term @"x:nadd")
                                            (parse_term @"y:nadd")]
                      MAP_EVERY EXISTS_TAC [(parse_term @"x':nadd")
                                            (parse_term @"y':nadd")]
                      |> THEN <| ONCE_REWRITE_TAC [NADD_EQ_SYM]]
         |> THEN <| ASM_REWRITE_TAC [])

let NADD_LE_REFL = 
    prove((parse_term @"!x. x <<= x"), REWRITE_TAC [nadd_le; LE_ADD])

let NADD_LE_TRANS = 
    prove
        ((parse_term @"!x y z. x <<= y /\ y <<= z ==> x <<= z"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_le]
         |> THEN 
         <| DISCH_THEN
                (CONJUNCTS_THEN2 (X_CHOOSE_TAC(parse_term @"B1:num")) MP_TAC)
         |> THEN <| DISCH_THEN(X_CHOOSE_TAC(parse_term @"B2:num"))
         |> THEN <| EXISTS_TAC(parse_term @"B2 + B1")
         |> THEN <| GEN_TAC
         |> THEN <| FIRST_ASSUM(MATCH_MP_TAC << LE_IMP)
         |> THEN <| ASM_REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL])

let NADD_LE_ANTISYM = 
    prove
        ((parse_term @"!x y. x <<= y /\ y <<= x <=> (x === y)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_le; nadd_eq; DIST_LE_CASES]
         |> THEN <| EQ_TAC
         |> THENL <| [DISCH_THEN
                          (CONJUNCTS_THEN2 (X_CHOOSE_TAC(parse_term @"B1:num")) 
                               (X_CHOOSE_TAC(parse_term @"B2:num")))
                      |> THEN <| EXISTS_TAC(parse_term @"B1 + B2")
                      |> THEN <| GEN_TAC
                      |> THEN <| CONJ_TAC
                      |> THEN <| FIRST_ASSUM(MATCH_MP_TAC << LE_IMP)
                      |> THEN 
                      <| ASM_REWRITE_TAC 
                             [ADD_ASSOC; LE_ADD_RCANCEL; LE_ADD; LE_ADDR]
                      DISCH_THEN(X_CHOOSE_TAC(parse_term @"B:num"))
                      |> THEN <| CONJ_TAC
                      |> THEN <| EXISTS_TAC(parse_term @"B:num")
                      |> THEN <| ASM_REWRITE_TAC []])

let NADD_LE_TOTAL_LEMMA = 
    prove
        ((parse_term @"!x y. ~(x <<= y) ==> !B. ?n. ~(n = 0) /\ fn y n + B < fn x n"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_le; NOT_FORALL_THM; NOT_EXISTS_THM]
         |> THEN <| REWRITE_TAC [NOT_LE]
         |> THEN <| DISCH_TAC
         |> THEN <| GEN_TAC
         |> THEN 
         <| POP_ASSUM
                (X_CHOOSE_TAC(parse_term @"n:num") 
                 << SPEC(parse_term @"B + fn x 0"))
         |> THEN <| EXISTS_TAC(parse_term @"n:num")
         |> THEN <| POP_ASSUM MP_TAC
         |> THEN <| ASM_CASES_TAC(parse_term @"n = 0")
         |> THEN <| ASM_REWRITE_TAC [NOT_LT; ADD_ASSOC; LE_ADDR]
         |> THEN <| CONV_TAC CONTRAPOS_CONV
         |> THEN <| REWRITE_TAC [NOT_LT]
         |> THEN <| DISCH_THEN(MATCH_MP_TAC << LE_IMP)
         |> THEN <| REWRITE_TAC [ADD_ASSOC; LE_ADD])

let NADD_LE_TOTAL = 
    prove
        ((parse_term @"!x y. x <<= y \/ y <<= x"), REPEAT GEN_TAC
                                                  |> THEN 
                                                  <| GEN_REWRITE_TAC I 
                                                         [TAUT
                                                              (parse_term @"a <=> ~ ~ a")]
                                                  |> THEN 
                                                  <| X_CHOOSE_TAC 
                                                         (parse_term @"B1:num") 
                                                         (SPEC 
                                                              (parse_term @"x:nadd") 
                                                              NADD_CAUCHY)
                                                  |> THEN 
                                                  <| X_CHOOSE_TAC 
                                                         (parse_term @"B2:num") 
                                                         (SPEC 
                                                              (parse_term @"y:nadd") 
                                                              NADD_CAUCHY)
                                                  |> THEN 
                                                  <| PURE_ONCE_REWRITE_TAC 
                                                         [DE_MORGAN_THM]
                                                  |> THEN 
                                                  <| DISCH_THEN
                                                         (MP_TAC 
                                                          << end_itlist CONJ 
                                                          << map
                                                                 (MATCH_MP 
                                                                      NADD_LE_TOTAL_LEMMA) 
                                                          << CONJUNCTS)
                                                  |> THEN 
                                                  <| REWRITE_TAC 
                                                         [AND_FORALL_THM]
                                                  |> THEN 
                                                  <| DISCH_THEN
                                                         (MP_TAC 
                                                          << SPEC
                                                                 (parse_term @"B1 + B2"))
                                                  |> THEN 
                                                  <| REWRITE_TAC 
                                                         [RIGHT_AND_EXISTS_THM]
                                                  |> THEN 
                                                  <| REWRITE_TAC 
                                                         [LEFT_AND_EXISTS_THM]
                                                  |> THEN 
                                                  <| DISCH_THEN
                                                         (X_CHOOSE_THEN 
                                                              (parse_term @"m:num") 
                                                              (X_CHOOSE_THEN 
                                                                   (parse_term @"n:num") 
                                                                   MP_TAC))
                                                  |> THEN 
                                                  <| DISCH_THEN
                                                         (MP_TAC 
                                                          << MATCH_MP
                                                                 (ITAUT
                                                                      (parse_term @"(~a /\ b) /\ (~c /\ d) ==> ~(c \/ ~b) /\ ~(a \/ ~d)")))
                                                  |> THEN 
                                                  <| REWRITE_TAC 
                                                         [NOT_LT
                                                          GSYM LE_MULT_LCANCEL]
                                                  |> THEN 
                                                  <| REWRITE_TAC [NOT_LE]
                                                  |> THEN 
                                                  <| DISCH_THEN
                                                         (MP_TAC 
                                                          << MATCH_MP LT_ADD2)
                                                  |> THEN 
                                                  <| REWRITE_TAC [NOT_LT]
                                                  |> THEN 
                                                  <| REWRITE_TAC 
                                                         [LEFT_ADD_DISTRIB]
                                                  |> THEN 
                                                  <| ONCE_REWRITE_TAC 
                                                         [AC ADD_AC 
                                                              (parse_term @"(a + b + c) + (d + e + f) = (d + b + e) + (a + c + f)")]
                                                  |> THEN 
                                                  <| MATCH_MP_TAC LE_ADD2
                                                  |> THEN 
                                                  <| REWRITE_TAC 
                                                         [GSYM RIGHT_ADD_DISTRIB]
                                                  |> THEN <| CONJ_TAC
                                                  |> THEN 
                                                  <| GEN_REWRITE_TAC 
                                                         (RAND_CONV << RAND_CONV) 
                                                         [MULT_SYM]
                                                  |> THEN 
                                                  <| RULE_ASSUM_TAC
                                                         (REWRITE_RULE 
                                                              [DIST_LE_CASES])
                                                  |> THEN <| ASM_REWRITE_TAC [])

let NADD_ARCH = 
    prove
        ((parse_term @"!x. ?n. x <<= &n"), 
         REWRITE_TAC [nadd_le; NADD_OF_NUM; NADD_BOUND])

let NADD_OF_NUM_LE = 
    prove
        ((parse_term @"!m n. (&m <<= &n) <=> m <= n"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_le; NADD_OF_NUM]
         |> THEN <| REWRITE_TAC [BOUNDS_LINEAR])

override_interface("++", (parse_term @"nadd_add:nadd->nadd->nadd"))

(* ------------------------------------------------------------------------- *)
(* Addition.                                                                 *)
(* ------------------------------------------------------------------------- *)
let nadd_add = new_definition(parse_term @"x ++ y = afn(\n. fn x n + fn y n)")

let NADD_ADD = 
    prove
        ((parse_term @"!x y. fn(x ++ y) = \n. fn x n + fn y n"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_add
                                 GSYM nadd_rep
                                 is_nadd]
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"B1:num") 
                (SPEC (parse_term @"x:nadd") NADD_CAUCHY)
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"B2:num") 
                (SPEC (parse_term @"y:nadd") NADD_CAUCHY)
         |> THEN <| EXISTS_TAC(parse_term @"B1 + B2")
         |> THEN <| MAP_EVERY X_GEN_TAC [(parse_term @"m:num")
                                         (parse_term @"n:num")]
         |> THEN 
         <| GEN_REWRITE_TAC (LAND_CONV << ONCE_DEPTH_CONV) [LEFT_ADD_DISTRIB]
         |> THEN <| MATCH_MP_TAC(LE_IMP DIST_ADD2)
         |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB]
         |> THEN <| MATCH_MP_TAC LE_ADD2
         |> THEN <| ASM_REWRITE_TAC [])

let NADD_ADD_WELLDEF = 
    prove
        ((parse_term @"!x x' y y'. x === x' /\ y === y' ==> (x ++ y === x' ++ y')"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_eq; NADD_ADD]
         |> THEN 
         <| DISCH_THEN
                (CONJUNCTS_THEN2 (X_CHOOSE_TAC(parse_term @"B1:num")) 
                     (X_CHOOSE_TAC(parse_term @"B2:num")))
         |> THEN <| EXISTS_TAC(parse_term @"B1 + B2")
         |> THEN <| X_GEN_TAC(parse_term @"n:num")
         |> THEN <| MATCH_MP_TAC(LE_IMP DIST_ADD2)
         |> THEN <| MATCH_MP_TAC LE_ADD2
         |> THEN <| ASM_REWRITE_TAC [])

(* ------------------------------------------------------------------------- *)
(* Basic properties of addition.                                             *)
(* ------------------------------------------------------------------------- *)
let NADD_ADD_SYM = 
    prove
        ((parse_term @"!x y. (x ++ y) === (y ++ x)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_add]
         |> THEN <| GEN_REWRITE_TAC (RAND_CONV << ONCE_DEPTH_CONV) [ADD_SYM]
         |> THEN <| REWRITE_TAC [NADD_EQ_REFL])

let NADD_ADD_ASSOC = 
    prove
        ((parse_term @"!x y z. (x ++ (y ++ z)) === ((x ++ y) ++ z)"), 
         REPEAT GEN_TAC
         |> THEN <| ONCE_REWRITE_TAC [nadd_add]
         |> THEN <| REWRITE_TAC [NADD_ADD; ADD_ASSOC; NADD_EQ_REFL])

let NADD_ADD_LID = 
    prove
        ((parse_term @"!x. (&0 ++ x) === x"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_eq; NADD_ADD; NADD_OF_NUM]
         |> THEN <| REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES; DIST_REFL; LE_0])

let NADD_ADD_LCANCEL = 
    prove
        ((parse_term @"!x y z. (x ++ y) === (x ++ z) ==> y === z"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_eq; NADD_ADD; DIST_LADD])

let NADD_LE_ADD = 
    prove
        ((parse_term @"!x y. x <<= (x ++ y)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_le; NADD_ADD]
         |> THEN <| EXISTS_TAC(parse_term @"0")
         |> THEN <| REWRITE_TAC [ADD_CLAUSES; LE_ADD])

let NADD_LE_EXISTS = 
    prove
        ((parse_term @"!x y. x <<= y ==> ?d. y === x ++ d"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_le]
         |> THEN <| DISCH_THEN(X_CHOOSE_THEN (parse_term @"B:num") MP_TAC)
         |> THEN <| REWRITE_TAC [LE_EXISTS; SKOLEM_THM]
         |> THEN 
         <| DISCH_THEN
                (X_CHOOSE_THEN (parse_term @"d:num->num") (ASSUME_TAC << GSYM))
         |> THEN <| EXISTS_TAC(parse_term @"afn d")
         |> THEN <| REWRITE_TAC [nadd_eq; NADD_ADD]
         |> THEN <| EXISTS_TAC(parse_term @"B:num")
         |> THEN <| X_GEN_TAC(parse_term @"n:num")
         |> THEN <| SUBGOAL_THEN (parse_term @"fn(afn d) = d") SUBST1_TAC
         |> THENL <| [REWRITE_TAC [GSYM nadd_rep
                                   is_nadd]
                      |> THEN 
                      <| X_CHOOSE_TAC (parse_term @"B1:num") 
                             (SPEC (parse_term @"x:nadd") NADD_CAUCHY)
                      |> THEN 
                      <| X_CHOOSE_TAC (parse_term @"B2:num") 
                             (SPEC (parse_term @"y:nadd") NADD_CAUCHY)
                      |> THEN <| EXISTS_TAC(parse_term @"B1 + (B2 + B)")
                      |> THEN <| REPEAT GEN_TAC
                      |> THEN <| MATCH_MP_TAC(LE_IMP DIST_ADD2_REV)
                      |> THEN 
                      <| MAP_EVERY EXISTS_TAC [(parse_term @"m * fn x n")
                                               (parse_term @"n * fn x m")]
                      |> THEN <| ONCE_REWRITE_TAC [RIGHT_ADD_DISTRIB]
                      |> THEN <| GEN_REWRITE_TAC RAND_CONV [ADD_SYM]
                      |> THEN <| MATCH_MP_TAC LE_ADD2
                      |> THEN <| ASM_REWRITE_TAC []
                      |> THEN <| ONCE_REWRITE_TAC [ADD_SYM]
                      |> THEN <| ASM_REWRITE_TAC [GSYM LEFT_ADD_DISTRIB]
                      |> THEN 
                      <| GEN_REWRITE_TAC (LAND_CONV << ONCE_DEPTH_CONV) 
                             [LEFT_ADD_DISTRIB]
                      |> THEN <| MATCH_MP_TAC(LE_IMP DIST_ADD2)
                      |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB]
                      |> THEN <| GEN_REWRITE_TAC RAND_CONV [ADD_SYM]
                      |> THEN <| MATCH_MP_TAC LE_ADD2
                      |> THEN <| ONCE_REWRITE_TAC [ADD_SYM]
                      |> THEN <| ASM_REWRITE_TAC []
                      |> THEN 
                      <| GEN_REWRITE_TAC (LAND_CONV << ONCE_DEPTH_CONV) 
                             [MULT_SYM]
                      |> THEN <| REWRITE_TAC [GSYM DIST_LMUL
                                              DIST_ADDBOUND; LE_MULT_LCANCEL]
                      ASM_REWRITE_TAC [DIST_RADD_0; LE_REFL]])

let NADD_OF_NUM_ADD = 
    prove
        ((parse_term @"!m n. &m ++ &n === &(m + n)"), 
         REWRITE_TAC [nadd_eq; NADD_OF_NUM; NADD_ADD]
         |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB; DIST_REFL; LE_0])

override_interface("**", (parse_term @"nadd_mul:nadd->nadd->nadd"))

(* ------------------------------------------------------------------------- *)
(* Multiplication.                                                           *)
(* ------------------------------------------------------------------------- *)
let nadd_mul = new_definition(parse_term @"x ** y = afn(\n. fn x (fn y n))")

let NADD_MUL = 
    prove
        ((parse_term @"!x y. fn(x ** y) = \n. fn x (fn y n)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_mul
                                 GSYM nadd_rep
                                 is_nadd]
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"B:num") 
                (SPEC (parse_term @"y:nadd") NADD_CAUCHY)
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"C:num") 
                (SPEC (parse_term @"x:nadd") NADD_DIST)
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"D:num") 
                (SPEC (parse_term @"x:nadd") NADD_MULTIPLICATIVE)
         |> THEN <| MATCH_MP_TAC BOUNDS_NOTZERO
         |> THEN <| REWRITE_TAC [MULT_CLAUSES; DIST_REFL]
         |> THEN <| MAP_EVERY EXISTS_TAC [(parse_term @"D + C * B")
                                          (parse_term @"D + D")]
         |> THEN <| REPEAT GEN_TAC
         |> THEN <| MATCH_MP_TAC LE_TRANS
         |> THEN 
         <| EXISTS_TAC(parse_term @"(D * m + D) + (D * n + D) + C * B * (m + n)")
         |> THEN <| CONJ_TAC
         |> THENL 
         <| [MATCH_MP_TAC(LE_IMP DIST_TRIANGLE)
             |> THEN <| EXISTS_TAC(parse_term @"fn x (m * fn y n)")
             |> THEN <| MATCH_MP_TAC LE_ADD2
             |> THEN <| ONCE_REWRITE_TAC [DIST_SYM]
             |> THEN <| ASM_REWRITE_TAC []
             |> THEN <| MATCH_MP_TAC(LE_IMP DIST_TRIANGLE)
             |> THEN <| EXISTS_TAC(parse_term @"fn x (n * fn y m)")
             |> THEN <| MATCH_MP_TAC LE_ADD2
             |> THEN <| ONCE_REWRITE_TAC [DIST_SYM]
             |> THEN <| ASM_REWRITE_TAC []
             |> THEN <| MATCH_MP_TAC LE_TRANS
             |> THEN <| EXISTS_TAC(parse_term @"C * dist(m * fn y n,n * fn y m)")
             |> THEN <| ASM_REWRITE_TAC [LE_MULT_LCANCEL]
             MATCH_MP_TAC EQ_IMP_LE
             |> THEN 
             <| REWRITE_TAC 
                    [LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_ASSOC; ADD_AC]])

(* ------------------------------------------------------------------------- *)
(* Properties of multiplication.                                             *)
(* ------------------------------------------------------------------------- *)
let NADD_MUL_SYM = 
    prove
        ((parse_term @"!x y. (x ** y) === (y ** x)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_eq; NADD_MUL]
         |> THEN 
         <| X_CHOOSE_THEN (parse_term @"A1:num") MP_TAC 
                (SPECL [(parse_term @"x:nadd")
                        (parse_term @"y:nadd")] NADD_ALTMUL)
         |> THEN <| DISCH_THEN(X_CHOOSE_TAC(parse_term @"B1:num"))
         |> THEN 
         <| X_CHOOSE_THEN (parse_term @"A2:num") MP_TAC 
                (SPECL [(parse_term @"y:nadd")
                        (parse_term @"x:nadd")] NADD_ALTMUL)
         |> THEN <| DISCH_THEN(X_CHOOSE_TAC(parse_term @"B2:num"))
         |> THEN <| REWRITE_TAC [BOUNDS_DIVIDED]
         |> THEN <| REWRITE_TAC [DIST_LMUL]
         |> THEN <| MAP_EVERY EXISTS_TAC [(parse_term @"A1 + A2")
                                          (parse_term @"B1 + B2")]
         |> THEN <| GEN_TAC
         |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB]
         |> THEN 
         <| ONCE_REWRITE_TAC 
                [AC ADD_AC (parse_term @"(a + b) + (c + d) = (a + c) + (b + d)")]
         |> THEN <| MATCH_MP_TAC(LE_IMP DIST_TRIANGLE)
         |> THEN <| EXISTS_TAC(parse_term @"fn x n * fn y n")
         |> THEN <| MATCH_MP_TAC LE_ADD2
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| ONCE_REWRITE_TAC [DIST_SYM]
         |> THEN <| GEN_REWRITE_TAC (LAND_CONV << funpow 2 RAND_CONV) [MULT_SYM]
         |> THEN <| ASM_REWRITE_TAC [])

let NADD_MUL_ASSOC = 
    prove
        ((parse_term @"!x y z. (x ** (y ** z)) === ((x ** y) ** z)"), 
         REPEAT GEN_TAC
         |> THEN <| ONCE_REWRITE_TAC [nadd_mul]
         |> THEN <| REWRITE_TAC [NADD_MUL; NADD_EQ_REFL])

let NADD_MUL_LID = 
    prove
        ((parse_term @"!x. (&1 ** x) === x"), 
         REWRITE_TAC [NADD_OF_NUM; nadd_mul; MULT_CLAUSES]
         |> THEN <| REWRITE_TAC [nadd_abs; NADD_EQ_REFL; ETA_AX])

let NADD_LDISTRIB = 
    prove
        ((parse_term @"!x y z. x ** (y ++ z) === (x ** y) ++ (x ** z)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_eq]
         |> THEN <| REWRITE_TAC [NADD_ADD; NADD_MUL]
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"B:num") 
                (SPEC (parse_term @"x:nadd") NADD_ADDITIVE)
         |> THEN <| EXISTS_TAC(parse_term @"B:num")
         |> THEN <| ASM_REWRITE_TAC [])

let NADD_MUL_WELLDEF_LEMMA = 
    prove
        ((parse_term @"!x y y'. y === y' ==> (x ** y) === (x ** y')"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_eq; NADD_MUL]
         |> THEN <| DISCH_THEN(X_CHOOSE_TAC(parse_term @"B1:num"))
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"B2:num") 
                (SPEC (parse_term @"x:nadd") NADD_DIST)
         |> THEN <| EXISTS_TAC(parse_term @"B2 * B1")
         |> THEN <| X_GEN_TAC(parse_term @"n:num")
         |> THEN <| MATCH_MP_TAC LE_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"B2 * dist(fn y n,fn y' n)")
         |> THEN <| ASM_REWRITE_TAC [LE_MULT_LCANCEL])

let NADD_MUL_WELLDEF = 
    prove((parse_term @"!x x' y y'. x === x' /\ y === y'
               ==> (x ** y) === (x' ** y')"),
              REPEAT GEN_TAC
              |> THEN <| STRIP_TAC
              |> THEN <| MATCH_MP_TAC NADD_EQ_TRANS
              |> THEN <| EXISTS_TAC(parse_term @"x' ** y")
              |> THEN <| CONJ_TAC
              |> THENL <| [MATCH_MP_TAC NADD_EQ_TRANS
                           |> THEN <| EXISTS_TAC(parse_term @"y ** x'")
                           |> THEN <| REWRITE_TAC [NADD_MUL_SYM]
                           |> THEN <| MATCH_MP_TAC NADD_EQ_TRANS
                           |> THEN <| EXISTS_TAC(parse_term @"y ** x")
                           |> THEN <| REWRITE_TAC [NADD_MUL_SYM]
                           ALL_TAC]
              |> THEN <| MATCH_MP_TAC NADD_MUL_WELLDEF_LEMMA
              |> THEN <| ASM_REWRITE_TAC [])

let NADD_OF_NUM_MUL = 
    prove
        ((parse_term @"!m n. &m ** &n === &(m * n)"), 
         REWRITE_TAC [nadd_eq; NADD_OF_NUM; NADD_MUL]
         |> THEN <| REWRITE_TAC [MULT_ASSOC; DIST_REFL; LE_0])

(* ------------------------------------------------------------------------- *)
(* A few handy lemmas.                                                       *)
(* ------------------------------------------------------------------------- *)
let NADD_LE_0 = 
    prove
        ((parse_term @"!x. &0 <<= x"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_le; NADD_OF_NUM; MULT_CLAUSES; LE_0])

let NADD_EQ_IMP_LE = 
    prove
        ((parse_term @"!x y. x === y ==> x <<= y"), REPEAT GEN_TAC
                                                   |> THEN 
                                                   <| REWRITE_TAC 
                                                          [nadd_eq; nadd_le; 
                                                           DIST_LE_CASES]
                                                   |> THEN 
                                                   <| DISCH_THEN
                                                          (X_CHOOSE_TAC
                                                               (parse_term @"B:num"))
                                                   |> THEN 
                                                   <| EXISTS_TAC
                                                          (parse_term @"B:num")
                                                   |> THEN <| ASM_REWRITE_TAC [])

let NADD_LE_LMUL = 
    prove
        ((parse_term @"!x y z. y <<= z ==> (x ** y) <<= (x ** z)"), 
         REPEAT GEN_TAC
         |> THEN 
         <| DISCH_THEN
                (X_CHOOSE_TAC(parse_term @"d:nadd") << MATCH_MP NADD_LE_EXISTS)
         |> THEN <| MATCH_MP_TAC NADD_LE_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"x ** y ++ x ** d")
         |> THEN <| REWRITE_TAC [NADD_LE_ADD]
         |> THEN <| MATCH_MP_TAC NADD_EQ_IMP_LE
         |> THEN <| MATCH_MP_TAC NADD_EQ_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"x ** (y ++ d)")
         |> THEN <| ONCE_REWRITE_TAC [NADD_EQ_SYM]
         |> THEN <| REWRITE_TAC [NADD_LDISTRIB]
         |> THEN <| MATCH_MP_TAC NADD_MUL_WELLDEF
         |> THEN <| ASM_REWRITE_TAC [NADD_EQ_REFL])

let NADD_LE_RMUL = 
    prove
        ((parse_term @"!x y z. x <<= y ==> (x ** z) <<= (y ** z)"), 
         MESON_TAC [NADD_LE_LMUL; NADD_LE_WELLDEF; NADD_MUL_SYM])

let NADD_LE_RADD = 
    prove
        ((parse_term @"!x y z. x ++ z <<= y ++ z <=> x <<= y"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_le; NADD_ADD]
         |> THEN 
         <| GEN_REWRITE_TAC (LAND_CONV << funpow 2 BINDER_CONV << RAND_CONV) 
                [ADD_SYM]
         |> THEN <| REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL]
         |> THEN 
         <| GEN_REWRITE_TAC (LAND_CONV << funpow 2 BINDER_CONV << RAND_CONV) 
                [ADD_SYM]
         |> THEN <| REFL_TAC)

let NADD_LE_LADD = 
    prove
        ((parse_term @"!x y z. x ++ y <<= x ++ z <=> y <<= z"), 
         MESON_TAC [NADD_LE_RADD; NADD_ADD_SYM; NADD_LE_WELLDEF])
let NADD_RDISTRIB = 
    prove
        ((parse_term @"!x y z. (x ++ y) ** z === x ** z ++ y ** z"), 
         MESON_TAC 
             [NADD_LDISTRIB; NADD_MUL_SYM; NADD_ADD_WELLDEF; NADD_EQ_TRANS; 
              NADD_EQ_REFL; NADD_EQ_SYM])

(* ------------------------------------------------------------------------- *)
(* The Archimedean property in a more useful form.                           *)
(* ------------------------------------------------------------------------- *)
let NADD_ARCH_MULT = 
    prove
        ((parse_term @"!x k. ~(x === &0) ==> ?N. &k <<= &N ** x"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_eq; nadd_le; NOT_EXISTS_THM]
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"B:num") 
                (SPEC (parse_term @"x:nadd") NADD_CAUCHY)
         |> THEN <| DISCH_THEN(MP_TAC << SPEC(parse_term @"B + k"))
         |> THEN <| REWRITE_TAC [NOT_FORALL_THM; NADD_OF_NUM]
         |> THEN <| REWRITE_TAC [MULT_CLAUSES; DIST_RZERO; NOT_LE]
         |> THEN <| DISCH_THEN(X_CHOOSE_TAC(parse_term @"N:num"))
         |> THEN <| MAP_EVERY EXISTS_TAC [(parse_term @"N:num")
                                          (parse_term @"B * N")]
         |> THEN <| X_GEN_TAC(parse_term @"i:num")
         |> THEN <| REWRITE_TAC [NADD_MUL; NADD_OF_NUM]
         |> THEN 
         <| MATCH_MP_TAC(GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_ADD_RCANCEL))))
         |> THEN <| EXISTS_TAC(parse_term @"B * i")
         |> THEN <| REWRITE_TAC [GSYM ADD_ASSOC
                                 GSYM LEFT_ADD_DISTRIB]
         |> THEN <| MATCH_MP_TAC LE_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"i * fn x N")
         |> THEN <| RULE_ASSUM_TAC(REWRITE_RULE [DIST_LE_CASES])
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| REWRITE_TAC [GSYM RIGHT_ADD_DISTRIB]
         |> THEN <| GEN_REWRITE_TAC RAND_CONV [MULT_SYM]
         |> THEN <| REWRITE_TAC [LE_MULT_RCANCEL]
         |> THEN <| DISJ1_TAC
         |> THEN <| MATCH_MP_TAC LT_IMP_LE
         |> THEN <| ONCE_REWRITE_TAC [ADD_SYM]
         |> THEN <| FIRST_ASSUM ACCEPT_TAC)

let NADD_ARCH_ZERO = 
    prove
        ((parse_term @"!x k. (!n. &n ** x <<= k) ==> (x === &0)"), 
         REPEAT GEN_TAC
         |> THEN <| CONV_TAC CONTRAPOS_CONV
         |> THEN <| DISCH_TAC
         |> THEN <| REWRITE_TAC [NOT_FORALL_THM]
         |> THEN 
         <| X_CHOOSE_TAC (parse_term @"p:num") 
                (SPEC (parse_term @"k:nadd") NADD_ARCH)
         |> THEN <| FIRST_ASSUM(MP_TAC << MATCH_MP NADD_ARCH_MULT)
         |> THEN 
         <| DISCH_THEN
                (X_CHOOSE_TAC(parse_term @"N:num") << SPEC(parse_term @"p:num"))
         |> THEN <| EXISTS_TAC(parse_term @"N + 1")
         |> THEN <| DISCH_TAC
         |> THEN <| UNDISCH_TAC(parse_term @"~(x === &0)")
         |> THEN <| REWRITE_TAC [GSYM NADD_LE_ANTISYM
                                 NADD_LE_0]
         |> THEN 
         <| MATCH_MP_TAC(GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL NADD_LE_RADD))))
         |> THEN <| EXISTS_TAC(parse_term @"&N ** x")
         |> THEN <| MATCH_MP_TAC NADD_LE_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"k:nadd")
         |> THEN <| CONJ_TAC
         |> THENL 
         <| [SUBGOAL_THEN (parse_term @"&(N + 1) ** x === x ++ &N ** x") MP_TAC
             |> THENL <| [ONCE_REWRITE_TAC [ADD_SYM]
                          |> THEN <| MATCH_MP_TAC NADD_EQ_TRANS
                          |> THEN <| EXISTS_TAC(parse_term @"&1 ** x ++ &N ** x")
                          |> THEN <| CONJ_TAC
                          |> THENL 
                          <| [MATCH_MP_TAC NADD_EQ_TRANS
                              |> THEN 
                              <| EXISTS_TAC(parse_term @"(&1 ++ &N) ** x")
                              |> THEN <| CONJ_TAC
                              |> THENL 
                              <| [MESON_TAC 
                                      [NADD_OF_NUM_ADD; NADD_MUL_WELLDEF; 
                                       NADD_EQ_REFL; NADD_EQ_SYM]
                                  MESON_TAC 
                                      [NADD_RDISTRIB; NADD_MUL_SYM; NADD_EQ_SYM; 
                                       NADD_EQ_TRANS]]
                              MESON_TAC 
                                  [NADD_ADD_WELLDEF; NADD_EQ_REFL; NADD_MUL_LID]]
                          ASM_MESON_TAC [NADD_LE_WELLDEF; NADD_EQ_REFL]]
             ASM_MESON_TAC 
                 [NADD_LE_TRANS; NADD_LE_WELLDEF; NADD_EQ_REFL; NADD_ADD_LID]])

let NADD_ARCH_LEMMA = 
    prove
        ((parse_term @"!x y z. (!n. &n ** x <<= &n ** y ++ z) ==> x <<= y"), 
         REPEAT STRIP_TAC
         |> THEN <| DISJ_CASES_TAC(SPECL [(parse_term @"x:nadd")
                                          (parse_term @"y:nadd")] NADD_LE_TOTAL)
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN 
         <| FIRST_ASSUM
                (X_CHOOSE_TAC(parse_term @"d:nadd") << MATCH_MP NADD_LE_EXISTS)
         |> THEN <| MATCH_MP_TAC NADD_EQ_IMP_LE
         |> THEN <| MATCH_MP_TAC NADD_EQ_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"y ++ d")
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| MATCH_MP_TAC NADD_EQ_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"y ++ &0")
         |> THEN <| CONJ_TAC
         |> THENL 
         <| [MATCH_MP_TAC NADD_ADD_WELLDEF
             |> THEN <| REWRITE_TAC [NADD_EQ_REFL]
             |> THEN <| MATCH_MP_TAC NADD_ARCH_ZERO
             |> THEN <| EXISTS_TAC(parse_term @"z:nadd")
             |> THEN 
             <| ASM_MESON_TAC 
                    [NADD_MUL_WELLDEF; NADD_LE_WELLDEF; NADD_LDISTRIB; 
                     NADD_LE_LADD; NADD_EQ_REFL]
             ASM_MESON_TAC 
                 [NADD_ADD_LID; NADD_ADD_WELLDEF; NADD_EQ_TRANS; NADD_ADD_SYM]])

(* ------------------------------------------------------------------------- *)
(* Completeness.                                                             *)
(* ------------------------------------------------------------------------- *)
let NADD_COMPLETE = 
    prove
        ((parse_term @"!P. (?x. P x) /\ (?M. !x. P x ==> x <<= M) ==>
       ?M. (!x. P x ==> x <<= M) /\
           !M'. (!x. P x ==> x <<= M') ==> M <<= M'"), 
         GEN_TAC
         |> THEN 
         <| DISCH_THEN
                (CONJUNCTS_THEN2 (X_CHOOSE_TAC(parse_term @"a:nadd")) 
                     (X_CHOOSE_TAC(parse_term @"m:nadd")))
         |> THEN <| SUBGOAL_THEN (parse_term @"!n. ?r. (?x. P x /\ &r <<= &n ** x) /\
             !r'. (?x. P x /\ &r' <<= &n ** x) ==> r' <= r") MP_TAC
         |> THENL <| [GEN_TAC
                      |> THEN <| REWRITE_TAC [GSYM num_MAX]
                      |> THEN <| CONJ_TAC
                      |> THENL 
                      <| [MAP_EVERY EXISTS_TAC [(parse_term @"0")
                                                (parse_term @"a:nadd")]
                          |> THEN <| ASM_REWRITE_TAC [NADD_LE_0]
                          X_CHOOSE_TAC (parse_term @"N:num") 
                              (SPEC (parse_term @"m:nadd") NADD_ARCH)
                          |> THEN <| EXISTS_TAC(parse_term @"n * N")
                          |> THEN <| X_GEN_TAC(parse_term @"p:num")
                          |> THEN 
                          <| DISCH_THEN
                                 (X_CHOOSE_THEN (parse_term @"w:nadd") 
                                      STRIP_ASSUME_TAC)
                          |> THEN <| ONCE_REWRITE_TAC [GSYM NADD_OF_NUM_LE]
                          |> THEN <| MATCH_MP_TAC NADD_LE_TRANS
                          |> THEN <| EXISTS_TAC(parse_term @"&n ** w")
                          |> THEN <| ASM_REWRITE_TAC []
                          |> THEN <| MATCH_MP_TAC NADD_LE_TRANS
                          |> THEN <| EXISTS_TAC(parse_term @"&n ** &N")
                          |> THEN <| CONJ_TAC
                          |> THENL 
                          <| [MATCH_MP_TAC NADD_LE_LMUL
                              |> THEN <| MATCH_MP_TAC NADD_LE_TRANS
                              |> THEN <| EXISTS_TAC(parse_term @"m:nadd")
                              |> THEN <| ASM_REWRITE_TAC []
                              |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                              |> THEN <| ASM_REWRITE_TAC []
                              MATCH_MP_TAC NADD_EQ_IMP_LE
                              |> THEN <| MATCH_ACCEPT_TAC NADD_OF_NUM_MUL]]
                      ONCE_REWRITE_TAC [SKOLEM_THM]
                      |> THEN 
                      <| DISCH_THEN
                             (X_CHOOSE_THEN (parse_term @"r:num->num") 
                                  (fun th -> 
                                      let th1, th2 = 
                                          CONJ_PAIR
                                              (SPEC (parse_term @"n:num") th)
                                      MAP_EVERY 
                                          (MP_TAC << GEN(parse_term @"n:num")) 
                                          [th1; th2]))
                      |> THEN 
                      <| DISCH_THEN
                             (MP_TAC << GEN(parse_term @"n:num") 
                              << SPECL [(parse_term @"n:num")
                                        (parse_term @"SUC(r(n:num))")])
                      |> THEN 
                      <| REWRITE_TAC [LE_SUC_LT; LT_REFL; NOT_EXISTS_THM]
                      |> THEN 
                      <| DISCH_THEN
                             (ASSUME_TAC << GENL [(parse_term @"n:num")
                                                  (parse_term @"x:nadd")] 
                              << MATCH_MP
                                     (ITAUT
                                          (parse_term @"(a \/ b) /\ ~(c /\ b) ==> c ==> a")) 
                              << CONJ
                                     (SPECL [(parse_term @"&n ** x")
                                             (parse_term @"&(SUC(r(n:num)))")] 
                                          NADD_LE_TOTAL) << SPEC_ALL)
                      |> THEN <| DISCH_TAC]
         |> THEN 
         <| SUBGOAL_THEN (parse_term @"!n i. i * r(n) <= n * r(i) + n") 
                ASSUME_TAC
         |> THENL <| [REPEAT GEN_TAC
                      |> THEN 
                      <| FIRST_ASSUM
                             (X_CHOOSE_THEN (parse_term @"x:nadd") 
                                  STRIP_ASSUME_TAC << SPEC(parse_term @"n:num"))
                      |> THEN <| ONCE_REWRITE_TAC [GSYM NADD_OF_NUM_LE]
                      |> THEN <| MATCH_MP_TAC NADD_LE_TRANS
                      |> THEN <| EXISTS_TAC(parse_term @"&i ** &n ** x")
                      |> THEN <| CONJ_TAC
                      |> THENL 
                      <| [MATCH_MP_TAC NADD_LE_TRANS
                          |> THEN <| EXISTS_TAC(parse_term @"&i ** &(r(n:num))")
                          |> THEN <| CONJ_TAC
                          |> THENL <| [MATCH_MP_TAC NADD_EQ_IMP_LE
                                       |> THEN <| ONCE_REWRITE_TAC [NADD_EQ_SYM]
                                       |> THEN 
                                       <| MATCH_ACCEPT_TAC NADD_OF_NUM_MUL
                                       MATCH_MP_TAC NADD_LE_LMUL
                                       |> THEN <| ASM_REWRITE_TAC []]
                          MATCH_MP_TAC NADD_LE_TRANS
                          |> THEN 
                          <| EXISTS_TAC(parse_term @"&n ** &(SUC(r(i:num)))")
                          |> THEN <| CONJ_TAC
                          |> THENL <| [MATCH_MP_TAC NADD_LE_TRANS
                                       |> THEN 
                                       <| EXISTS_TAC(parse_term @"&n ** &i ** x")
                                       |> THEN <| CONJ_TAC
                                       |> THENL 
                                       <| [MATCH_MP_TAC NADD_EQ_IMP_LE
                                           |> THEN <| MATCH_MP_TAC NADD_EQ_TRANS
                                           |> THEN 
                                           <| EXISTS_TAC
                                                  (parse_term @"(&i ** &n) ** x")
                                           |> THEN 
                                           <| REWRITE_TAC [NADD_MUL_ASSOC]
                                           |> THEN <| MATCH_MP_TAC NADD_EQ_TRANS
                                           |> THEN 
                                           <| EXISTS_TAC
                                                  (parse_term @"(&n ** &i) ** x")
                                           |> THEN 
                                           <| REWRITE_TAC 
                                                  [ONCE_REWRITE_RULE 
                                                       [NADD_EQ_SYM] 
                                                       NADD_MUL_ASSOC]
                                           |> THEN 
                                           <| MATCH_MP_TAC NADD_MUL_WELLDEF
                                           |> THEN 
                                           <| REWRITE_TAC 
                                                  [NADD_MUL_SYM; NADD_EQ_REFL]
                                           MATCH_MP_TAC NADD_LE_LMUL
                                           |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                                           |> THEN <| ASM_REWRITE_TAC []]
                                       ONCE_REWRITE_TAC [ADD_SYM]
                                       |> THEN <| REWRITE_TAC [GSYM MULT_SUC]
                                       |> THEN <| MATCH_MP_TAC NADD_EQ_IMP_LE
                                       |> THEN <| REWRITE_TAC [NADD_OF_NUM_MUL]]]
                      ALL_TAC]
         |> THEN <| EXISTS_TAC(parse_term @"afn r")
         |> THEN <| SUBGOAL_THEN (parse_term @"fn(afn r) = r") ASSUME_TAC
         |> THENL <| [REWRITE_TAC [GSYM nadd_rep]
                      |> THEN <| REWRITE_TAC [is_nadd; DIST_LE_CASES]
                      |> THEN <| EXISTS_TAC(parse_term @"1")
                      |> THEN <| REWRITE_TAC [MULT_CLAUSES]
                      |> THEN <| REWRITE_TAC [FORALL_AND_THM]
                      |> THEN <| GEN_REWRITE_TAC RAND_CONV [SWAP_FORALL_THM]
                      |> THEN 
                      <| GEN_REWRITE_TAC 
                             (LAND_CONV << funpow 2 BINDER_CONV 
                              << funpow 2 RAND_CONV) [ADD_SYM]
                      |> THEN <| REWRITE_TAC []
                      |> THEN <| MAP_EVERY X_GEN_TAC [(parse_term @"i:num")
                                                      (parse_term @"n:num")]
                      |> THEN <| MATCH_MP_TAC LE_TRANS
                      |> THEN <| EXISTS_TAC(parse_term @"n * r(i:num) + n")
                      |> THEN <| ASM_REWRITE_TAC [ADD_ASSOC; LE_ADD]
                      ALL_TAC]
         |> THEN <| CONJ_TAC
         |> THENL <| [X_GEN_TAC(parse_term @"x:nadd")
                      |> THEN <| DISCH_TAC
                      |> THEN <| MATCH_MP_TAC NADD_ARCH_LEMMA
                      |> THEN <| EXISTS_TAC(parse_term @"&2")
                      |> THEN <| X_GEN_TAC(parse_term @"n:num")
                      |> THEN <| MATCH_MP_TAC NADD_LE_TRANS
                      |> THEN <| EXISTS_TAC(parse_term @"&(SUC(r(n:num)))")
                      |> THEN <| CONJ_TAC
                      |> THENL 
                      <| [FIRST_ASSUM MATCH_MP_TAC
                          |> THEN <| ASM_REWRITE_TAC []
                          ASM_REWRITE_TAC 
                              [nadd_le; NADD_ADD; NADD_MUL; NADD_OF_NUM]
                          |> THEN <| ONCE_REWRITE_TAC [ADD_SYM]
                          |> THEN <| REWRITE_TAC [ADD1; RIGHT_ADD_DISTRIB]
                          |> THEN 
                          <| REWRITE_TAC 
                                 [MULT_2; MULT_CLAUSES; ADD_ASSOC; 
                                  LE_ADD_RCANCEL]
                          |> THEN <| REWRITE_TAC [GSYM ADD_ASSOC]
                          |> THEN <| ONCE_REWRITE_TAC [ADD_SYM]
                          |> THEN <| ONCE_REWRITE_TAC [BOUNDS_IGNORE]
                          |> THEN <| MAP_EVERY EXISTS_TAC [(parse_term @"0")
                                                           (parse_term @"n:num")]
                          |> THEN <| X_GEN_TAC(parse_term @"i:num")
                          |> THEN <| DISCH_TAC
                          |> THEN <| GEN_REWRITE_TAC LAND_CONV [MULT_SYM]
                          |> THEN <| MATCH_MP_TAC LE_TRANS
                          |> THEN <| EXISTS_TAC(parse_term @"n * r(i:num) + n")
                          |> THEN 
                          <| ASM_REWRITE_TAC [LE_ADD_LCANCEL; ADD_CLAUSES]]
                      X_GEN_TAC(parse_term @"z:nadd")
                      |> THEN <| DISCH_TAC
                      |> THEN <| MATCH_MP_TAC NADD_ARCH_LEMMA
                      |> THEN <| EXISTS_TAC(parse_term @"&1")
                      |> THEN <| X_GEN_TAC(parse_term @"n:num")
                      |> THEN <| MATCH_MP_TAC NADD_LE_TRANS
                      |> THEN <| EXISTS_TAC(parse_term @"&(r(n:num)) ++ &1")
                      |> THEN <| CONJ_TAC
                      |> THENL <| [ASM_REWRITE_TAC 
                                       [nadd_le; NADD_ADD; NADD_MUL; NADD_OF_NUM]
                                   |> THEN <| EXISTS_TAC(parse_term @"0")
                                   |> THEN 
                                   <| REWRITE_TAC [ADD_CLAUSES; MULT_CLAUSES]
                                   |> THEN <| GEN_TAC
                                   |> THEN 
                                   <| GEN_REWRITE_TAC (RAND_CONV << LAND_CONV) 
                                          [MULT_SYM]
                                   |> THEN <| ASM_REWRITE_TAC []
                                   REWRITE_TAC [NADD_LE_RADD]
                                   |> THEN 
                                   <| FIRST_ASSUM
                                          (X_CHOOSE_THEN (parse_term @"x:nadd") 
                                               MP_TAC 
                                           << SPEC(parse_term @"n:num"))
                                   |> THEN <| DISCH_THEN STRIP_ASSUME_TAC
                                   |> THEN <| MATCH_MP_TAC NADD_LE_TRANS
                                   |> THEN <| EXISTS_TAC(parse_term @"&n ** x")
                                   |> THEN <| ASM_REWRITE_TAC []
                                   |> THEN <| MATCH_MP_TAC NADD_LE_LMUL
                                   |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                                   |> THEN <| ASM_REWRITE_TAC []]])

(* ------------------------------------------------------------------------- *)
(* A bit more on nearly-multiplicative functions.                            *)
(* ------------------------------------------------------------------------- *)
let NADD_UBOUND = 
    prove
        ((parse_term @"!x. ?B N. !n. N <= n ==> fn x n <= B * n"), 
         GEN_TAC
         |> THEN 
         <| X_CHOOSE_THEN (parse_term @"A1:num") 
                (X_CHOOSE_TAC(parse_term @"A2:num")) 
                (SPEC (parse_term @"x:nadd") NADD_BOUND)
         |> THEN <| EXISTS_TAC(parse_term @"A1 + A2")
         |> THEN <| EXISTS_TAC(parse_term @"1")
         |> THEN <| REPEAT STRIP_TAC
         |> THEN <| MATCH_MP_TAC LE_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"A1 * n + A2")
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB; LE_ADD_LCANCEL]
         |> THEN 
         <| GEN_REWRITE_TAC LAND_CONV [GSYM(el 3 (CONJUNCTS MULT_CLAUSES))]
         |> THEN <| ASM_REWRITE_TAC [LE_MULT_LCANCEL])

let NADD_NONZERO = 
    prove
        ((parse_term @"!x. ~(x === &0) ==> ?N. !n. N <= n ==> ~(fn x n = 0)"), 
         GEN_TAC
         |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP NADD_ARCH_MULT)
         |> THEN <| DISCH_THEN(MP_TAC << SPEC(parse_term @"1"))
         |> THEN <| REWRITE_TAC [nadd_le; NADD_MUL; NADD_OF_NUM; MULT_CLAUSES]
         |> THEN 
         <| DISCH_THEN
                (X_CHOOSE_THEN (parse_term @"A1:num") 
                     (X_CHOOSE_TAC(parse_term @"A2:num")))
         |> THEN <| EXISTS_TAC(parse_term @"A2 + 1")
         |> THEN <| X_GEN_TAC(parse_term @"n:num")
         |> THEN <| REPEAT DISCH_TAC
         |> THEN <| FIRST_ASSUM(UNDISCH_TAC << check is_forall << concl)
         |> THEN <| REWRITE_TAC [NOT_FORALL_THM
                                 NOT_LE
                                 GSYM LE_SUC_LT
                                 ADD1]
         |> THEN <| EXISTS_TAC(parse_term @"n:num")
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES])

let NADD_LBOUND = 
    prove
        ((parse_term @"!x. ~(x === &0) ==> ?A N. !n. N <= n ==> n <= A * fn x n"), 
         GEN_TAC
         |> THEN <| DISCH_TAC
         |> THEN 
         <| FIRST_ASSUM
                (X_CHOOSE_TAC(parse_term @"N:num") << MATCH_MP NADD_NONZERO)
         |> THEN <| FIRST_ASSUM(MP_TAC << MATCH_MP NADD_ARCH_MULT)
         |> THEN <| DISCH_THEN(MP_TAC << SPEC(parse_term @"1"))
         |> THEN <| REWRITE_TAC [nadd_le; NADD_MUL; NADD_OF_NUM; MULT_CLAUSES]
         |> THEN 
         <| DISCH_THEN
                (X_CHOOSE_THEN (parse_term @"A1:num") 
                     (X_CHOOSE_TAC(parse_term @"A2:num")))
         |> THEN <| EXISTS_TAC(parse_term @"A1 + A2")
         |> THEN <| EXISTS_TAC(parse_term @"N:num")
         |> THEN <| GEN_TAC
         |> THEN <| DISCH_THEN(ANTE_RES_THEN ASSUME_TAC)
         |> THEN <| MATCH_MP_TAC LE_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"A1 * fn x n + A2")
         |> THEN <| ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB; LE_ADD_LCANCEL]
         |> THEN 
         <| GEN_REWRITE_TAC LAND_CONV [GSYM(el 3 (CONJUNCTS MULT_CLAUSES))]
         |> THEN <| REWRITE_TAC [LE_MULT_LCANCEL]
         |> THEN <| DISJ2_TAC
         |> THEN 
         <| REWRITE_TAC [GSYM(REWRITE_CONV [ARITH_SUC] (parse_term @"SUC 0"))]
         |> THEN <| ASM_REWRITE_TAC [GSYM NOT_LT
                                     LT])

(* ------------------------------------------------------------------------- *)
(* Auxiliary function for the multiplicative inverse.                        *)
(* ------------------------------------------------------------------------- *)
let nadd_rinv = 
    new_definition(parse_term @"nadd_rinv(x) = \n. (n * n) DIV (fn x n)")

let NADD_MUL_LINV_LEMMA0 = 
    prove
        ((parse_term @"!x. ~(x === &0) ==> ?A B. !n. nadd_rinv x n <= A * n + B"), 
         GEN_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ONCE_REWRITE_TAC [BOUNDS_IGNORE]
         |> THEN <| FIRST_ASSUM(MP_TAC << MATCH_MP NADD_LBOUND)
         |> THEN 
         <| DISCH_THEN
                (X_CHOOSE_THEN (parse_term @"A:num") 
                     (X_CHOOSE_TAC(parse_term @"N:num")))
         |> THEN <| MAP_EVERY EXISTS_TAC [(parse_term @"A:num")
                                          (parse_term @"0")
                                          (parse_term @"SUC N")]
         |> THEN <| GEN_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| REWRITE_TAC [ADD_CLAUSES]
         |> THEN <| MP_TAC(SPECL [(parse_term @"nadd_rinv x n")
                                  (parse_term @"A * n")
                                  (parse_term @"n:num")] LE_MULT_RCANCEL)
         |> THEN <| UNDISCH_TAC(parse_term @"SUC N <= n")
         |> THEN <| ASM_CASES_TAC(parse_term @"n = 0")
         |> THEN <| ASM_REWRITE_TAC [LE; NOT_SUC]
         |> THEN <| DISCH_TAC
         |> THEN <| DISCH_THEN(SUBST1_TAC << SYM)
         |> THEN <| MATCH_MP_TAC LE_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"nadd_rinv x n * A * fn x n")
         |> THEN <| ASM_REWRITE_TAC [LE_MULT_LCANCEL]
         |> THEN <| CONJ_TAC
         |> THENL <| [DISJ2_TAC
                      |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                      |> THEN <| MATCH_MP_TAC LE_TRANS
                      |> THEN <| EXISTS_TAC(parse_term @"SUC N")
                      |> THEN <| ASM_REWRITE_TAC [LE; LE_REFL]
                      GEN_REWRITE_TAC LAND_CONV [MULT_SYM]
                      |> THEN <| REWRITE_TAC [GSYM MULT_ASSOC
                                              LE_MULT_LCANCEL]
                      |> THEN <| DISJ2_TAC
                      |> THEN <| ASM_CASES_TAC(parse_term @"fn x n = 0")
                      |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; LE_0; nadd_rinv]
                      |> THEN <| FIRST_ASSUM(MP_TAC << MATCH_MP DIVISION)
                      |> THEN 
                      <| DISCH_THEN
                             (fun t -> 
                                 GEN_REWRITE_TAC RAND_CONV 
                                     [CONJUNCT1(SPEC_ALL t)])
                      |> THEN <| GEN_REWRITE_TAC LAND_CONV [MULT_SYM]
                      |> THEN <| REWRITE_TAC [LE_ADD]])

let NADD_MUL_LINV_LEMMA1 = 
    prove
        ((parse_term @"!x n. ~(fn x n = 0) ==> dist(fn x n * nadd_rinv(x) n, n * n) <= fn x n"), 
         REPEAT GEN_TAC
         |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP DIVISION)
         |> THEN 
         <| DISCH_THEN
                (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC 
                 << SPEC(parse_term @"n * n"))
         |> THEN <| REWRITE_TAC [nadd_rinv]
         |> THEN 
         <| GEN_REWRITE_TAC (LAND_CONV << RAND_CONV << LAND_CONV) [MULT_SYM]
         |> THEN <| REWRITE_TAC [DIST_RADD_0]
         |> THEN <| MATCH_MP_TAC LT_IMP_LE
         |> THEN <| FIRST_ASSUM MATCH_ACCEPT_TAC)

let NADD_MUL_LINV_LEMMA2 = 
    prove((parse_term @"!x. ~(x === &0) ==> ?N. !n. N <= n ==>
         dist(fn x n * nadd_rinv(x) n, n * n) <= fn x n"),
        GEN_TAC
        |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP NADD_NONZERO)
        |> THEN <| DISCH_THEN(X_CHOOSE_TAC(parse_term @"N:num"))
        |> THEN <| EXISTS_TAC(parse_term @"N:num")
        |> THEN <| REPEAT STRIP_TAC
        |> THEN <| MATCH_MP_TAC NADD_MUL_LINV_LEMMA1
        |> THEN <| FIRST_ASSUM MATCH_MP_TAC
        |> THEN <| ASM_REWRITE_TAC [])

let NADD_MUL_LINV_LEMMA3 = 
    prove((parse_term @"!x. ~(x === &0) ==> ?N. !m n. N <= n ==>
        dist(m * fn x m * fn x n * nadd_rinv(x) n,
             m * fn x m * n * n) <= m * fn x m * fn x n"),
            GEN_TAC
            |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP NADD_MUL_LINV_LEMMA2)
            |> THEN <| DISCH_THEN(X_CHOOSE_TAC(parse_term @"N:num"))
            |> THEN <| EXISTS_TAC(parse_term @"N:num")
            |> THEN <| REPEAT STRIP_TAC
            |> THEN <| REWRITE_TAC [GSYM DIST_LMUL
                                    MULT_ASSOC]
            |> THEN <| REWRITE_TAC [LE_MULT_LCANCEL]
            |> THEN <| DISJ2_TAC
            |> THEN <| FIRST_ASSUM MATCH_MP_TAC
            |> THEN <| ASM_REWRITE_TAC [])

let NADD_MUL_LINV_LEMMA4 = 
    prove((parse_term @"!x. ~(x === &0) ==> ?N. !m n. N <= m /\ N <= n ==>
        (fn x m * fn x n) * dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <=
          (m * n) * dist(m * fn x n,n * fn x m) + (fn x m * fn x n) * (m + n)"),
         GEN_TAC
         |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP NADD_MUL_LINV_LEMMA3)
         |> THEN <| DISCH_THEN(X_CHOOSE_TAC(parse_term @"N:num"))
         |> THEN <| EXISTS_TAC(parse_term @"N:num")
         |> THEN <| REPEAT STRIP_TAC
         |> THEN <| REWRITE_TAC [DIST_LMUL; LEFT_ADD_DISTRIB]
         |> THEN <| GEN_REWRITE_TAC (RAND_CONV << LAND_CONV) [DIST_SYM]
         |> THEN <| MATCH_MP_TAC DIST_TRIANGLES_LE
         |> THEN <| CONJ_TAC
         |> THENL 
         <| [ANTE_RES_THEN (MP_TAC << SPEC(parse_term @"m:num")) 
                 (ASSUME(parse_term @"N <= n"))
             ANTE_RES_THEN (MP_TAC << SPEC(parse_term @"n:num")) 
                 (ASSUME(parse_term @"N <= m"))]
         |> THEN <| MATCH_MP_TAC EQ_IMP
         |> THEN <| REWRITE_TAC [MULT_AC])

let NADD_MUL_LINV_LEMMA5 = 
    prove((parse_term @"!x. ~(x === &0) ==> ?B N. !m n. N <= m /\ N <= n ==>
        (fn x m * fn x n) * dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <=
        B * (m * n) * (m + n)"),
       GEN_TAC
       |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP NADD_MUL_LINV_LEMMA4)
       |> THEN <| DISCH_THEN(X_CHOOSE_TAC(parse_term @"N1:num"))
       |> THEN 
       <| X_CHOOSE_TAC (parse_term @"B1:num") 
              (SPEC (parse_term @"x:nadd") NADD_CAUCHY)
       |> THEN 
       <| X_CHOOSE_THEN (parse_term @"B2:num") 
              (X_CHOOSE_TAC(parse_term @"N2:num")) 
              (SPEC (parse_term @"x:nadd") NADD_UBOUND)
       |> THEN <| EXISTS_TAC(parse_term @"B1 + B2 * B2")
       |> THEN <| EXISTS_TAC(parse_term @"N1 + N2")
       |> THEN <| REPEAT STRIP_TAC
       |> THEN <| MATCH_MP_TAC LE_TRANS
       |> THEN <| EXISTS_TAC(parse_term @"(m * n) * dist(m * fn x n,n * fn x m) +
              (fn x m * fn x n) * (m + n)") 
       |> THEN <| CONJ_TAC
       |> THENL <| [FIRST_ASSUM MATCH_MP_TAC
                    |> THEN <| CONJ_TAC
                    |> THEN <| MATCH_MP_TAC LE_TRANS
                    |> THEN <| EXISTS_TAC(parse_term @"N1 + N2")
                    |> THEN <| ASM_REWRITE_TAC [LE_ADD; LE_ADDR]
                    REWRITE_TAC [RIGHT_ADD_DISTRIB]
                    |> THEN <| MATCH_MP_TAC LE_ADD2]
       |> THEN <| CONJ_TAC
       |> THENL <| [GEN_REWRITE_TAC RAND_CONV [MULT_SYM]
                    |> THEN <| GEN_REWRITE_TAC RAND_CONV [GSYM MULT_ASSOC]
                    |> THEN <| GEN_REWRITE_TAC (funpow 2 RAND_CONV) [MULT_SYM]
                    |> THEN <| ASM_REWRITE_TAC [LE_MULT_LCANCEL]
                    ONCE_REWRITE_TAC 
                        [AC MULT_AC 
                             (parse_term @"(a * b) * (c * d) * e = ((a * c) * (b * d)) * e")]
                    |> THEN <| REWRITE_TAC [LE_MULT_RCANCEL]
                    |> THEN <| DISJ1_TAC
                    |> THEN <| MATCH_MP_TAC LE_MULT2
                    |> THEN <| CONJ_TAC
                    |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                    |> THEN <| MATCH_MP_TAC LE_TRANS
                    |> THEN <| EXISTS_TAC(parse_term @"N1 + N2")
                    |> THEN <| ASM_REWRITE_TAC [LE_ADD; LE_ADDR]])

let NADD_MUL_LINV_LEMMA6 = 
    prove((parse_term @"!x. ~(x === &0) ==> ?B N. !m n. N <= m /\ N <= n ==>
        (m * n) * dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <=
        B * (m * n) * (m + n)"),
       GEN_TAC
       |> THEN <| DISCH_TAC
       |> THEN <| FIRST_ASSUM(MP_TAC << MATCH_MP NADD_MUL_LINV_LEMMA5)
       |> THEN 
       <| DISCH_THEN
              (X_CHOOSE_THEN (parse_term @"B1:num") 
                   (X_CHOOSE_TAC(parse_term @"N1:num")))
       |> THEN <| FIRST_ASSUM(MP_TAC << MATCH_MP NADD_LBOUND)
       |> THEN 
       <| DISCH_THEN
              (X_CHOOSE_THEN (parse_term @"B2:num") 
                   (X_CHOOSE_TAC(parse_term @"N2:num")))
       |> THEN <| EXISTS_TAC(parse_term @"B1 * B2 * B2")
       |> THEN <| EXISTS_TAC(parse_term @"N1 + N2")
       |> THEN <| REPEAT STRIP_TAC
       |> THEN <| MATCH_MP_TAC LE_TRANS
       |> THEN <| EXISTS_TAC(parse_term @"(B2 * B2) * (fn x m * fn x n) *
              dist (m * nadd_rinv x n,n * nadd_rinv x m)")
       |> THEN <| CONJ_TAC
       |> THENL <| [REWRITE_TAC [MULT_ASSOC; LE_MULT_RCANCEL]
                    |> THEN <| DISJ1_TAC
                    |> THEN 
                    <| ONCE_REWRITE_TAC 
                           [AC MULT_AC 
                                (parse_term @"((a * b) * c) * d = (a * c) * (b * d)")]
                    |> THEN <| MATCH_MP_TAC LE_MULT2
                    |> THEN <| CONJ_TAC
                    |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                    ONCE_REWRITE_TAC 
                        [AC MULT_AC 
                             (parse_term @"(a * b * c) * (d * e) * f = (b * c) * (a * (d * e) * f)")]
                    |> THEN <| REWRITE_TAC [LE_MULT_LCANCEL]
                    |> THEN <| DISJ2_TAC
                    |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                    |> THEN <| CONJ_TAC]
       |> THEN <| MATCH_MP_TAC LE_TRANS
       |> THEN <| EXISTS_TAC(parse_term @"N1 + N2")
       |> THEN <| ASM_REWRITE_TAC [LE_ADD; LE_ADDR])

let NADD_MUL_LINV_LEMMA7 = 
    prove((parse_term @"!x. ~(x === &0) ==> ?B N. !m n. N <= m /\ N <= n ==>
        dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <= B * (m + n)"),
       GEN_TAC
       |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP NADD_MUL_LINV_LEMMA6)
       |> THEN 
       <| DISCH_THEN
              (X_CHOOSE_THEN (parse_term @"B:num") 
                   (X_CHOOSE_TAC(parse_term @"N:num")))
       |> THEN <| MAP_EVERY EXISTS_TAC [(parse_term @"B:num")
                                        (parse_term @"N + 1")]
       |> THEN <| MAP_EVERY X_GEN_TAC [(parse_term @"m:num")
                                       (parse_term @"n:num")]
       |> THEN <| STRIP_TAC
       |> THEN <| SUBGOAL_THEN (parse_term @"N <= m /\ N <= n") MP_TAC
       |> THENL <| [CONJ_TAC
                    |> THEN <| MATCH_MP_TAC LE_TRANS
                    |> THEN <| EXISTS_TAC(parse_term @"N + 1")
                    |> THEN <| ASM_REWRITE_TAC [LE_ADD]
                    DISCH_THEN(ANTE_RES_THEN MP_TAC)
                    |> THEN 
                    <| ONCE_REWRITE_TAC 
                           [AC MULT_AC (parse_term @"a * b * c = b * a * c")]
                    |> THEN <| REWRITE_TAC [LE_MULT_LCANCEL]
                    |> THEN <| DISCH_THEN(DISJ_CASES_THEN2 MP_TAC ACCEPT_TAC)
                    |> THEN <| CONV_TAC CONTRAPOS_CONV
                    |> THEN <| DISCH_THEN(K ALL_TAC)
                    |> THEN <| ONCE_REWRITE_TAC [GSYM(CONJUNCT1 LE)]
                    |> THEN <| REWRITE_TAC [NOT_LE
                                            GSYM LE_SUC_LT]
                    |> THEN 
                    <| REWRITE_TAC 
                           [EQT_ELIM
                                (REWRITE_CONV [ARITH] 
                                     (parse_term @"SUC 0 = 1 * 1"))]
                    |> THEN <| MATCH_MP_TAC LE_MULT2
                    |> THEN <| CONJ_TAC
                    |> THEN <| MATCH_MP_TAC LE_TRANS
                    |> THEN <| EXISTS_TAC(parse_term @"N + 1")
                    |> THEN <| ASM_REWRITE_TAC [LE_ADDR]])

let NADD_MUL_LINV_LEMMA7a = 
    prove
        ((parse_term @"!x. ~(x === &0) ==> !N. ?A B. !m n. m <= N ==>
        dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <= A * n + B"),
       GEN_TAC
       |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP NADD_MUL_LINV_LEMMA0)
       |> THEN 
       <| DISCH_THEN
              (X_CHOOSE_THEN (parse_term @"A0:num") 
                   (X_CHOOSE_TAC(parse_term @"B0:num")))
       |> THEN <| INDUCT_TAC
       |> THENL <| [MAP_EVERY EXISTS_TAC [(parse_term @"nadd_rinv x 0")
                                          (parse_term @"0")]
                    |> THEN <| REPEAT GEN_TAC
                    |> THEN <| REWRITE_TAC [LE]
                    |> THEN <| DISCH_THEN SUBST1_TAC
                    |> THEN 
                    <| REWRITE_TAC [MULT_CLAUSES; DIST_LZERO; ADD_CLAUSES]
                    |> THEN <| GEN_REWRITE_TAC RAND_CONV [MULT_SYM]
                    |> THEN <| MATCH_ACCEPT_TAC LE_REFL
                    FIRST_ASSUM
                        (X_CHOOSE_THEN (parse_term @"A:num") 
                             (X_CHOOSE_TAC(parse_term @"B:num")))
                    |> THEN 
                    <| EXISTS_TAC
                           (parse_term @"A + (nadd_rinv(x)(SUC N) + SUC N * A0)")
                    |> THEN <| EXISTS_TAC(parse_term @"SUC N * B0 + B")
                    |> THEN <| REPEAT GEN_TAC
                    |> THEN <| REWRITE_TAC [LE]
                    |> THEN 
                    <| DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC)
                    |> THENL <| [MATCH_MP_TAC LE_TRANS
                                 |> THEN 
                                 <| EXISTS_TAC
                                        (parse_term @"SUC N * nadd_rinv x n + n * nadd_rinv x (SUC N)")
                                 |> THEN <| REWRITE_TAC [DIST_ADDBOUND]
                                 |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB]
                                 |> THEN 
                                 <| ONCE_REWRITE_TAC 
                                        [AC ADD_AC 
                                             (parse_term @"(a + b + c) + d + e = (c + d) + (b + a + e)")]
                                 |> THEN <| MATCH_MP_TAC LE_ADD2
                                 |> THEN <| CONJ_TAC
                                 |> THENL 
                                 <| [REWRITE_TAC [GSYM MULT_ASSOC
                                                  GSYM LEFT_ADD_DISTRIB]
                                     |> THEN 
                                     <| ASM_REWRITE_TAC [LE_MULT_LCANCEL]
                                     GEN_REWRITE_TAC LAND_CONV [MULT_SYM]
                                     |> THEN <| MATCH_ACCEPT_TAC LE_ADD]
                                 MATCH_MP_TAC LE_TRANS
                                 |> THEN <| EXISTS_TAC(parse_term @"A * n + B")
                                 |> THEN <| CONJ_TAC
                                 |> THENL <| [FIRST_ASSUM MATCH_MP_TAC
                                              |> THEN <| ASM_REWRITE_TAC []
                                              REWRITE_TAC 
                                                  [ADD_ASSOC; LE_ADD_RCANCEL]
                                              |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB
                                                                      GSYM 
                                                                          ADD_ASSOC
                                                                      LE_ADD]]]])

let NADD_MUL_LINV_LEMMA8 = 
    prove((parse_term @"!x. ~(x === &0) ==>
        ?B. !m n. dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <= B * (m + n)"),
       GEN_TAC
       |> THEN <| DISCH_TAC
       |> THEN <| FIRST_ASSUM(MP_TAC << MATCH_MP NADD_MUL_LINV_LEMMA7)
       |> THEN 
       <| DISCH_THEN
              (X_CHOOSE_THEN (parse_term @"B0:num") 
                   (X_CHOOSE_TAC(parse_term @"N:num")))
       |> THEN 
       <| FIRST_ASSUM
              (MP_TAC << SPEC(parse_term @"N:num") 
               << MATCH_MP NADD_MUL_LINV_LEMMA7a)
       |> THEN 
       <| DISCH_THEN
              (X_CHOOSE_THEN (parse_term @"A:num") 
                   (X_CHOOSE_TAC(parse_term @"B:num")))
       |> THEN <| MATCH_MP_TAC BOUNDS_NOTZERO
       |> THEN <| REWRITE_TAC [DIST_REFL]
       |> THEN <| EXISTS_TAC(parse_term @"A + B0")
       |> THEN <| EXISTS_TAC(parse_term @"B:num")
       |> THEN <| REPEAT GEN_TAC
       |> THEN 
       <| DISJ_CASES_THEN2 ASSUME_TAC MP_TAC 
              (SPECL [(parse_term @"N:num")
                      (parse_term @"m:num")] LE_CASES)
       |> THENL <| [DISJ_CASES_THEN2 ASSUME_TAC MP_TAC 
                        (SPECL [(parse_term @"N:num")
                                (parse_term @"n:num")] LE_CASES)
                    |> THENL <| [MATCH_MP_TAC LE_TRANS
                                 |> THEN 
                                 <| EXISTS_TAC(parse_term @"B0 * (m + n)")
                                 |> THEN <| CONJ_TAC
                                 |> THENL <| [FIRST_ASSUM MATCH_MP_TAC
                                              |> THEN <| ASM_REWRITE_TAC []
                                              GEN_REWRITE_TAC 
                                                  (RAND_CONV 
                                                   << funpow 2 LAND_CONV) 
                                                  [ADD_SYM]
                                              |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB
                                                                      GSYM 
                                                                          ADD_ASSOC
                                                                      LE_ADD]]
                                 DISCH_THEN(ANTE_RES_THEN ASSUME_TAC)
                                 |> THEN <| MATCH_MP_TAC LE_TRANS
                                 |> THEN <| EXISTS_TAC(parse_term @"A * m + B")
                                 |> THEN <| ONCE_REWRITE_TAC [DIST_SYM]
                                 |> THEN <| ASM_REWRITE_TAC [LE_ADD_RCANCEL]
                                 |> THEN <| REWRITE_TAC [LEFT_ADD_DISTRIB
                                                         RIGHT_ADD_DISTRIB
                                                         GSYM ADD_ASSOC
                                                         LE_ADD]]
                    DISCH_THEN(ANTE_RES_THEN ASSUME_TAC)
                    |> THEN <| MATCH_MP_TAC LE_TRANS
                    |> THEN <| EXISTS_TAC(parse_term @"A * n + B")
                    |> THEN <| ASM_REWRITE_TAC [LE_ADD_RCANCEL]
                    |> THEN 
                    <| GEN_REWRITE_TAC (RAND_CONV << RAND_CONV) [ADD_SYM]
                    |> THEN <| REWRITE_TAC [LEFT_ADD_DISTRIB
                                            RIGHT_ADD_DISTRIB
                                            GSYM ADD_ASSOC
                                            LE_ADD]])

(* ------------------------------------------------------------------------- *)
(* Now the multiplicative inverse proper.                                    *)
(* ------------------------------------------------------------------------- *)
let nadd_inv = 
    new_definition
        (parse_term @"nadd_inv(x) = if x === &0 then &0 else afn(nadd_rinv x)")

override_interface("inv", (parse_term @"nadd_inv:nadd->nadd"))

let NADD_INV = 
    prove
        ((parse_term @"!x. fn(nadd_inv x) = if x === &0 then (\n. 0) else nadd_rinv x"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [nadd_inv]
         |> THEN <| ASM_CASES_TAC(parse_term @"x === &0")
         |> THEN <| ASM_REWRITE_TAC [NADD_OF_NUM; MULT_CLAUSES]
         |> THEN <| REWRITE_TAC [GSYM nadd_rep
                                 is_nadd]
         |> THEN <| MATCH_MP_TAC NADD_MUL_LINV_LEMMA8
         |> THEN <| POP_ASSUM ACCEPT_TAC)

let NADD_MUL_LINV = 
    prove
        ((parse_term @"!x. ~(x === &0) ==> inv(x) ** x === &1"), 
         GEN_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| REWRITE_TAC [nadd_eq; NADD_MUL]
         |> THEN <| ONCE_REWRITE_TAC [BOUNDS_DIVIDED]
         |> THEN 
         <| X_CHOOSE_THEN (parse_term @"A1:num") 
                (X_CHOOSE_TAC(parse_term @"B1:num")) 
                (SPECL [(parse_term @"inv(x)")
                        (parse_term @"x:nadd")] NADD_ALTMUL)
         |> THEN <| REWRITE_TAC [DIST_LMUL; NADD_OF_NUM; MULT_CLAUSES]
         |> THEN 
         <| FIRST_ASSUM
                (X_CHOOSE_TAC(parse_term @"N:num") 
                 << MATCH_MP NADD_MUL_LINV_LEMMA2)
         |> THEN 
         <| X_CHOOSE_THEN (parse_term @"A':num") 
                (X_CHOOSE_TAC(parse_term @"B':num")) 
                (SPEC (parse_term @"x:nadd") NADD_BOUND)
         |> THEN 
         <| SUBGOAL_THEN 
                (parse_term @"?A2 B2. !n. dist(fn x n * nadd_rinv x n,n * n) <= A2 * n + B2") 
                STRIP_ASSUME_TAC
         |> THENL <| [EXISTS_TAC(parse_term @"A':num")
                      |> THEN <| ONCE_REWRITE_TAC [BOUNDS_IGNORE]
                      |> THEN <| MAP_EVERY EXISTS_TAC [(parse_term @"B':num")
                                                       (parse_term @"N:num")]
                      |> THEN <| REPEAT STRIP_TAC
                      |> THEN <| MATCH_MP_TAC LE_TRANS
                      |> THEN <| EXISTS_TAC(parse_term @"fn x n")
                      |> THEN <| ASM_REWRITE_TAC []
                      |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                      |> THEN <| ASM_REWRITE_TAC []
                      MAP_EVERY EXISTS_TAC [(parse_term @"A1 + A2")
                                            (parse_term @"B1 + B2")]
                      |> THEN <| GEN_TAC
                      |> THEN <| MATCH_MP_TAC DIST_TRIANGLE_LE
                      |> THEN <| EXISTS_TAC(parse_term @"fn (inv x) n * fn x n")
                      |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB]
                      |> THEN 
                      <| ONCE_REWRITE_TAC 
                             [AC ADD_AC 
                                  (parse_term @"(a + b) + c + d = (a + c) + (b + d)")]
                      |> THEN <| MATCH_MP_TAC LE_ADD2
                      |> THEN <| ASM_REWRITE_TAC []
                      |> THEN 
                      <| GEN_REWRITE_TAC (LAND_CONV << RAND_CONV << LAND_CONV) 
                             [MULT_SYM]
                      |> THEN <| ASM_REWRITE_TAC [NADD_INV]])

let NADD_INV_0 = 
    prove((parse_term @"inv(&0) === &0"), REWRITE_TAC [nadd_inv; NADD_EQ_REFL])

(* ------------------------------------------------------------------------- *)
(* Welldefinedness follows from already established principles because if    *)
(* x = y then y' = y' 1 = y' (x' x) = y' (x' y) = (y' y) x' = 1 x' = x'      *)
(* ------------------------------------------------------------------------- *)
let NADD_INV_WELLDEF = 
    prove
        ((parse_term @"!x y. x === y ==> inv(x) === inv(y)"), 
         let TAC tm ths = 
             MATCH_MP_TAC NADD_EQ_TRANS
             |> THEN <| EXISTS_TAC tm
             |> THEN <| CONJ_TAC
             |> THENL <| [ALL_TAC
                          ASM_MESON_TAC ths]
         REPEAT STRIP_TAC
         |> THEN <| ASM_CASES_TAC(parse_term @"x === &0")
         |> THENL <| [SUBGOAL_THEN (parse_term @"y === &0") ASSUME_TAC
                      |> THENL <| [ASM_MESON_TAC [NADD_EQ_TRANS; NADD_EQ_SYM]
                                   ASM_REWRITE_TAC [nadd_inv; NADD_EQ_REFL]]
                      SUBGOAL_THEN (parse_term @"~(y === &0)") ASSUME_TAC
                      |> THENL <| [ASM_MESON_TAC [NADD_EQ_TRANS; NADD_EQ_SYM]
                                   ALL_TAC]]
         |> THEN 
         <| TAC (parse_term @"inv(y) ** &1") 
                [NADD_MUL_SYM; NADD_MUL_LID; NADD_EQ_TRANS]
         |> THEN 
         <| TAC (parse_term @"inv(y) ** (inv(x) ** x)") 
                [NADD_MUL_LINV; NADD_MUL_WELLDEF; NADD_EQ_REFL]
         |> THEN 
         <| TAC (parse_term @"inv(y) ** (inv(x) ** y)") 
                [NADD_MUL_WELLDEF; NADD_EQ_REFL; NADD_EQ_SYM]
         |> THEN 
         <| TAC (parse_term @"(inv(y) ** y) ** inv(x)") 
                [NADD_MUL_ASSOC; NADD_MUL_SYM; NADD_EQ_TRANS; NADD_MUL_WELLDEF; 
                 NADD_EQ_REFL]
         |> THEN 
         <| ASM_MESON_TAC 
                [NADD_MUL_LINV; NADD_MUL_WELLDEF; NADD_EQ_REFL; NADD_MUL_LID; 
                 NADD_EQ_TRANS; NADD_EQ_SYM])

(* ------------------------------------------------------------------------- *)
(* Definition of the new type.                                               *)
(* ------------------------------------------------------------------------- *)
let hreal_tybij = 
    define_quotient_type "hreal" ("mk_hreal", "dest_hreal") (parse_term @"(===)")

do_list overload_interface ["+", (parse_term @"hreal_add:hreal->hreal->hreal")
                            "*", (parse_term @"hreal_mul:hreal->hreal->hreal")
                            "<=", (parse_term @"hreal_le:hreal->hreal->bool")]
do_list override_interface ["&", (parse_term @"hreal_of_num:num->hreal")
                            "inv", (parse_term @"hreal_inv:hreal->hreal")]

let hreal_of_num, hreal_of_num_th = 
    lift_function (snd hreal_tybij) (NADD_EQ_REFL, NADD_EQ_TRANS) "hreal_of_num" 
        NADD_OF_NUM_WELLDEF
let hreal_add, hreal_add_th = 
    lift_function (snd hreal_tybij) (NADD_EQ_REFL, NADD_EQ_TRANS) "hreal_add" 
        NADD_ADD_WELLDEF
let hreal_mul, hreal_mul_th = 
    lift_function (snd hreal_tybij) (NADD_EQ_REFL, NADD_EQ_TRANS) "hreal_mul" 
        NADD_MUL_WELLDEF
let hreal_le, hreal_le_th = 
    lift_function (snd hreal_tybij) (NADD_EQ_REFL, NADD_EQ_TRANS) "hreal_le" 
        NADD_LE_WELLDEF
let hreal_inv, hreal_inv_th = 
    lift_function (snd hreal_tybij) (NADD_EQ_REFL, NADD_EQ_TRANS) "hreal_inv" 
        NADD_INV_WELLDEF

let HREAL_COMPLETE = 
    let th1 = ASSUME(parse_term @"(P:nadd->bool) = (\x. Q(mk_hreal((===) x)))")
    let th2 = BETA_RULE(AP_THM th1 (parse_term @"x:nadd"))
    let th3 = 
        lift_theorem hreal_tybij (NADD_EQ_REFL, NADD_EQ_SYM, NADD_EQ_TRANS) 
            [hreal_of_num_th; hreal_add_th; hreal_mul_th; hreal_le_th; th2] 
            (SPEC_ALL NADD_COMPLETE)
    let th4 = 
        MATCH_MP (DISCH_ALL th3) 
            (REFL(parse_term @"\x. Q(mk_hreal((===) x)):bool"))
    CONV_RULE (GEN_ALPHA_CONV(parse_term @"P:hreal->bool")) (GEN_ALL th4)

let HREAL_OF_NUM_EQ, HREAL_OF_NUM_LE, HREAL_OF_NUM_ADD, HREAL_OF_NUM_MUL, HREAL_LE_REFL, HREAL_LE_TRANS, HREAL_LE_ANTISYM, HREAL_LE_TOTAL, HREAL_LE_ADD, HREAL_LE_EXISTS, HREAL_ARCH, HREAL_ADD_SYM, HREAL_ADD_ASSOC, HREAL_ADD_LID, HREAL_ADD_LCANCEL, HREAL_MUL_SYM, HREAL_MUL_ASSOC, HREAL_MUL_LID, HREAL_ADD_LDISTRIB, HREAL_MUL_LINV, HREAL_INV_0 = 
    let naddFuncs =
        map (lift_theorem hreal_tybij (NADD_EQ_REFL, NADD_EQ_SYM, NADD_EQ_TRANS) 
         [hreal_of_num_th; hreal_add_th; hreal_mul_th; hreal_le_th; hreal_inv_th])
         [NADD_OF_NUM_EQ; NADD_OF_NUM_LE; NADD_OF_NUM_ADD; NADD_OF_NUM_MUL; 
          NADD_LE_REFL; NADD_LE_TRANS; NADD_LE_ANTISYM; NADD_LE_TOTAL; NADD_LE_ADD; 
          NADD_LE_EXISTS; NADD_ARCH; NADD_ADD_SYM; NADD_ADD_ASSOC; NADD_ADD_LID; 
          NADD_ADD_LCANCEL; NADD_MUL_SYM; NADD_MUL_ASSOC; NADD_MUL_LID; NADD_LDISTRIB; 
          NADD_MUL_LINV; NADD_INV_0]
    match naddFuncs with
    | [hreal_of_num_eq; hreal_of_num_le; hreal_of_num_add; hreal_of_num_mul; 
       hreal_le_refl; hreal_le_trans; hreal_le_antisym; hreal_le_total; 
       hreal_le_add; hreal_le_exists; hreal_arch; hreal_add_sym; hreal_add_assoc; 
       hreal_add_lid; hreal_add_lcancel; hreal_mul_sym; hreal_mul_assoc; 
       hreal_mul_lid; hreal_add_ldistrib; hreal_mul_linv; hreal_inv_0] -> 
          hreal_of_num_eq, hreal_of_num_le, hreal_of_num_add, hreal_of_num_mul, 
          hreal_le_refl, hreal_le_trans, hreal_le_antisym, hreal_le_total, 
          hreal_le_add, hreal_le_exists, hreal_arch, hreal_add_sym, hreal_add_assoc, 
          hreal_add_lid, hreal_add_lcancel, hreal_mul_sym, hreal_mul_assoc, 
          hreal_mul_lid, hreal_add_ldistrib, hreal_mul_linv, hreal_inv_0
    | _ -> failwith "naddFuncs: Unhandled case."

(* ------------------------------------------------------------------------- *)
(* Consequential theorems needed later.                                      *)
(* ------------------------------------------------------------------------- *)
let HREAL_LE_EXISTS_DEF = 
    prove
        ((parse_term @"!m n. m <= n <=> ?d. n = m + d"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| REWRITE_TAC [HREAL_LE_EXISTS]
         |> THEN <| DISCH_THEN(CHOOSE_THEN SUBST1_TAC)
         |> THEN <| REWRITE_TAC [HREAL_LE_ADD])

let HREAL_EQ_ADD_LCANCEL = 
    prove
        ((parse_term @"!m n p. (m + n = m + p) <=> (n = p)"), REPEAT GEN_TAC
                                                             |> THEN <| EQ_TAC
                                                             |> THEN 
                                                             <| REWRITE_TAC 
                                                                    [HREAL_ADD_LCANCEL]
                                                             |> THEN 
                                                             <| DISCH_THEN 
                                                                    SUBST1_TAC
                                                             |> THEN <| REFL_TAC)

let HREAL_EQ_ADD_RCANCEL = 
    prove
        ((parse_term @"!m n p. (m + p = n + p) <=> (m = n)"), 
         ONCE_REWRITE_TAC [HREAL_ADD_SYM]
         |> THEN <| REWRITE_TAC [HREAL_EQ_ADD_LCANCEL])

let HREAL_LE_ADD_LCANCEL = 
    prove
        ((parse_term @"!m n p. (m + n <= m + p) <=> (n <= p)"), 
         REWRITE_TAC [HREAL_LE_EXISTS_DEF
                      GSYM HREAL_ADD_ASSOC
                      HREAL_EQ_ADD_LCANCEL])

let HREAL_LE_ADD_RCANCEL = 
    prove
        ((parse_term @"!m n p. (m + p <= n + p) <=> (m <= n)"), 
         ONCE_REWRITE_TAC [HREAL_ADD_SYM]
         |> THEN <| MATCH_ACCEPT_TAC HREAL_LE_ADD_LCANCEL)
let HREAL_ADD_RID = 
    prove
        ((parse_term @"!n. n + &0 = n"), 
         ONCE_REWRITE_TAC [HREAL_ADD_SYM]
         |> THEN <| MATCH_ACCEPT_TAC HREAL_ADD_LID)
let HREAL_ADD_RDISTRIB = 
    prove
        ((parse_term @"!m n p. (m + n) * p = m * p + n * p"), 
         ONCE_REWRITE_TAC [HREAL_MUL_SYM]
         |> THEN <| MATCH_ACCEPT_TAC HREAL_ADD_LDISTRIB)

let HREAL_MUL_LZERO = 
    prove
        ((parse_term @"!m. &0 * m = &0"), 
         GEN_TAC
         |> THEN <| MP_TAC(SPECL [(parse_term @"&0")
                                  (parse_term @"&1")
                                  (parse_term @"m:hreal")] HREAL_ADD_RDISTRIB)
         |> THEN <| REWRITE_TAC [HREAL_ADD_LID]
         |> THEN <| GEN_REWRITE_TAC (funpow 2 LAND_CONV) [GSYM HREAL_ADD_LID]
         |> THEN <| REWRITE_TAC [HREAL_EQ_ADD_RCANCEL]
         |> THEN <| DISCH_THEN(ACCEPT_TAC << SYM))

let HREAL_MUL_RZERO = 
    prove
        ((parse_term @"!m. m * &0 = &0"), 
         ONCE_REWRITE_TAC [HREAL_MUL_SYM]
         |> THEN <| MATCH_ACCEPT_TAC HREAL_MUL_LZERO)

let HREAL_ADD_AC = 
    prove((parse_term @"(m + n = n + m) /\
   ((m + n) + p = m + (n + p)) /\
   (m + (n + p) = n + (m + p))"), REWRITE_TAC 
                                      [HREAL_ADD_ASSOC
                                       EQT_INTRO(SPEC_ALL HREAL_ADD_SYM)]
                                  |> THEN <| AP_THM_TAC
                                  |> THEN <| AP_TERM_TAC
                                  |> THEN <| MATCH_ACCEPT_TAC HREAL_ADD_SYM)

let HREAL_LE_ADD2 = 
    prove
        ((parse_term @"!a b c d. a <= b /\ c <= d ==> a + c <= b + d"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [HREAL_LE_EXISTS_DEF]
         |> THEN 
         <| DISCH_THEN
                (CONJUNCTS_THEN2 (X_CHOOSE_TAC(parse_term @"d1:hreal")) 
                     (X_CHOOSE_TAC(parse_term @"d2:hreal")))
         |> THEN <| EXISTS_TAC(parse_term @"d1 + d2")
         |> THEN <| ASM_REWRITE_TAC [HREAL_ADD_AC])

let HREAL_LE_MUL_RCANCEL_IMP = 
    prove
        ((parse_term @"!a b c. a <= b ==> a * c <= b * c"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [HREAL_LE_EXISTS_DEF]
         |> THEN <| DISCH_THEN(X_CHOOSE_THEN (parse_term @"d:hreal") SUBST1_TAC)
         |> THEN <| EXISTS_TAC(parse_term @"d * c")
         |> THEN <| REWRITE_TAC [HREAL_ADD_RDISTRIB])

(* ------------------------------------------------------------------------- *)
(* Define operations on representatives of signed reals.                     *)
(* ------------------------------------------------------------------------- *)
let treal_of_num = new_definition(parse_term @"treal_of_num n = (&n, &0)")

let treal_neg = 
    new_definition(parse_term @"treal_neg ((x:hreal),(y:hreal)) = (y,x)")
let treal_add = 
    new_definition(parse_term @"(x1,y1) treal_add (x2,y2) = (x1 + x2, y1 + y2)")
let treal_mul = 
    new_definition
        (parse_term @"(x1,y1) treal_mul (x2,y2) = ((x1 * x2) + (y1 * y2),(x1 * y2) + (y1 * x2))")
let treal_le = 
    new_definition(parse_term @"(x1,y1) treal_le (x2,y2) <=> x1 + y2 <= x2 + y1")
let treal_inv = new_definition(parse_term @"treal_inv(x,y) = if x = y then (&0, &0)
                    else if y <= x then (inv(@d. x = y + d), &0)
                    else (&0, inv(@d. y = x + d))");;


(* ------------------------------------------------------------------------- *)
(* Define the equivalence relation and prove it *is* one.                    *)
(* ------------------------------------------------------------------------- *)
let treal_eq = 
    new_definition
        (parse_term @"(x1,y1) treal_eq (x2,y2) <=> (x1 + y2 = x2 + y1)")

let TREAL_EQ_REFL = 
    prove
        ((parse_term @"!x. x treal_eq x"), 
         REWRITE_TAC [FORALL_PAIR_THM; treal_eq])
let TREAL_EQ_SYM = 
    prove
        ((parse_term @"!x y. x treal_eq y <=> y treal_eq x"), 
         REWRITE_TAC [FORALL_PAIR_THM; treal_eq; EQ_SYM_EQ])

let TREAL_EQ_TRANS = 
    prove
        ((parse_term @"!x y z. x treal_eq y /\ y treal_eq z ==> x treal_eq z"), 
         REWRITE_TAC [FORALL_PAIR_THM; treal_eq]
         |> THEN <| REPEAT GEN_TAC
         |> THEN 
         <| DISCH_THEN
                (MP_TAC << MK_COMB << (AP_TERM(parse_term @"(+)") ||>> I) 
                 << CONJ_PAIR)
         |> THEN <| GEN_REWRITE_TAC (LAND_CONV << LAND_CONV) [HREAL_ADD_SYM]
         |> THEN <| REWRITE_TAC [GSYM HREAL_ADD_ASSOC
                                 HREAL_EQ_ADD_LCANCEL]
         |> THEN <| REWRITE_TAC [HREAL_ADD_ASSOC; HREAL_EQ_ADD_RCANCEL]
         |> THEN 
         <| DISCH_THEN(MATCH_ACCEPT_TAC << ONCE_REWRITE_RULE [HREAL_ADD_SYM]))

(* ------------------------------------------------------------------------- *)
(* Useful to avoid unnecessary use of the equivalence relation.              *)
(* ------------------------------------------------------------------------- *)
let TREAL_EQ_AP = 
    prove
        ((parse_term @"!x y. (x = y) ==> x treal_eq y"), SIMP_TAC [TREAL_EQ_REFL])

(* ------------------------------------------------------------------------- *)
(* Commutativity properties for injector.                                    *)
(* ------------------------------------------------------------------------- *)
let TREAL_OF_NUM_EQ = 
    prove
        ((parse_term @"!m n. (treal_of_num m treal_eq treal_of_num n) <=> (m = n)"), 
         REWRITE_TAC [treal_of_num; treal_eq; HREAL_OF_NUM_EQ; HREAL_ADD_RID])

let TREAL_OF_NUM_LE = 
    prove
        ((parse_term @"!m n. (treal_of_num m treal_le treal_of_num n) <=> m <= n"), 
         REWRITE_TAC [treal_of_num; treal_le; HREAL_OF_NUM_LE; HREAL_ADD_RID])
let TREAL_OF_NUM_ADD = 
    prove
        ((parse_term @"!m n. (treal_of_num m treal_add treal_of_num n) treal_eq
         (treal_of_num(m + n))"),
         REWRITE_TAC 
             [treal_of_num; treal_eq; treal_add; HREAL_OF_NUM_ADD; HREAL_ADD_RID; 
              ADD_CLAUSES])
let TREAL_OF_NUM_MUL = 
    prove
        ((parse_term @"!m n. (treal_of_num m treal_mul treal_of_num n) treal_eq
         (treal_of_num(m * n))"),
         REWRITE_TAC 
             [treal_of_num; treal_eq; treal_mul; HREAL_OF_NUM_MUL; 
              HREAL_MUL_RZERO; HREAL_MUL_LZERO; HREAL_ADD_RID; HREAL_ADD_LID; 
              HREAL_ADD_RID; MULT_CLAUSES])

(* ------------------------------------------------------------------------- *)
(* Strong forms of equality are useful to simplify welldefinedness proofs.   *)
(* ------------------------------------------------------------------------- *)
let TREAL_ADD_SYM_EQ = 
    prove
        ((parse_term @"!x y. x treal_add y = y treal_add x"), 
         REWRITE_TAC [FORALL_PAIR_THM; treal_add; PAIR_EQ; HREAL_ADD_SYM])

let TREAL_MUL_SYM_EQ = 
    prove
        ((parse_term @"!x y. x treal_mul y = y treal_mul x"), 
         REWRITE_TAC [FORALL_PAIR_THM; treal_mul; HREAL_MUL_SYM; HREAL_ADD_SYM])

(* ------------------------------------------------------------------------- *)
(* Prove the properties of operations on representatives.                    *)
(* ------------------------------------------------------------------------- *)
let TREAL_ADD_SYM = 
    prove
        ((parse_term @"!x y. (x treal_add y) treal_eq (y treal_add x)"), 
         REPEAT GEN_TAC
         |> THEN <| MATCH_MP_TAC TREAL_EQ_AP
         |> THEN <| MATCH_ACCEPT_TAC TREAL_ADD_SYM_EQ)

let TREAL_ADD_ASSOC = 
    prove((parse_term @"!x y z. (x treal_add (y treal_add z)) treal_eq
           ((x treal_add y) treal_add z)"),
        SIMP_TAC [FORALL_PAIR_THM; TREAL_EQ_AP; treal_add; HREAL_ADD_ASSOC])
let TREAL_ADD_LID = 
    prove
        ((parse_term @"!x. ((treal_of_num 0) treal_add x) treal_eq x"), 
         REWRITE_TAC 
             [FORALL_PAIR_THM; treal_of_num; treal_add; treal_eq; HREAL_ADD_LID])
let TREAL_ADD_LINV = 
    prove
        ((parse_term @"!x. ((treal_neg x) treal_add x) treal_eq (treal_of_num 0)"), 
         REWRITE_TAC 
             [FORALL_PAIR_THM; treal_neg; treal_add; treal_eq; treal_of_num; 
              HREAL_ADD_LID; HREAL_ADD_RID; HREAL_ADD_SYM])
let TREAL_MUL_SYM = 
    prove
        ((parse_term @"!x y. (x treal_mul y) treal_eq (y treal_mul x)"), 
         SIMP_TAC [TREAL_EQ_AP; TREAL_MUL_SYM_EQ])

let TREAL_MUL_ASSOC = 
    prove((parse_term @"!x y z. (x treal_mul (y treal_mul z)) treal_eq
           ((x treal_mul y) treal_mul z)"),
          SIMP_TAC [FORALL_PAIR_THM
                    TREAL_EQ_AP
                    treal_mul
                    HREAL_ADD_LDISTRIB
                    HREAL_ADD_RDISTRIB
                    GSYM HREAL_MUL_ASSOC
                    HREAL_ADD_AC])

let TREAL_MUL_LID = 
    prove
        ((parse_term @"!x. ((treal_of_num 1) treal_mul x) treal_eq x"), 
         SIMP_TAC [FORALL_PAIR_THM; treal_of_num; treal_mul; treal_eq]
         |> THEN 
         <| REWRITE_TAC 
                [HREAL_MUL_LZERO; HREAL_MUL_LID; HREAL_ADD_LID; HREAL_ADD_RID])
let TREAL_ADD_LDISTRIB = 
    prove
        ((parse_term @"!x y z. (x treal_mul (y treal_add z)) treal_eq
           ((x treal_mul y) treal_add (x treal_mul z))"),
         SIMP_TAC 
             [FORALL_PAIR_THM; TREAL_EQ_AP; treal_mul; treal_add; 
              HREAL_ADD_LDISTRIB; PAIR_EQ; HREAL_ADD_AC])
let TREAL_LE_REFL = 
    prove
        ((parse_term @"!x. x treal_le x"), 
         REWRITE_TAC [FORALL_PAIR_THM; treal_le; HREAL_LE_REFL])
let TREAL_LE_ANTISYM = 
    prove
        ((parse_term @"!x y. x treal_le y /\ y treal_le x <=> (x treal_eq y)"), 
         REWRITE_TAC [FORALL_PAIR_THM; treal_le; treal_eq; HREAL_LE_ANTISYM])

let TREAL_LE_TRANS = 
    prove
        ((parse_term @"!x y z. x treal_le y /\ y treal_le z ==> x treal_le z"), 
         REWRITE_TAC [FORALL_PAIR_THM; treal_le]
         |> THEN <| REPEAT GEN_TAC
         |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP HREAL_LE_ADD2)
         |> THEN <| GEN_REWRITE_TAC (LAND_CONV << LAND_CONV) [HREAL_ADD_SYM]
         |> THEN <| REWRITE_TAC [GSYM HREAL_ADD_ASSOC
                                 HREAL_LE_ADD_LCANCEL]
         |> THEN <| REWRITE_TAC [HREAL_ADD_ASSOC; HREAL_LE_ADD_RCANCEL]
         |> THEN 
         <| DISCH_THEN(MATCH_ACCEPT_TAC << ONCE_REWRITE_RULE [HREAL_ADD_SYM]))

let TREAL_LE_TOTAL = 
    prove
        ((parse_term @"!x y. x treal_le y \/ y treal_le x"), 
         REWRITE_TAC [FORALL_PAIR_THM; treal_le; HREAL_LE_TOTAL])

let TREAL_LE_LADD_IMP = 
    prove
        ((parse_term @"!x y z. (y treal_le z) ==> (x treal_add y) treal_le (x treal_add z)"), 
         REWRITE_TAC [FORALL_PAIR_THM; treal_le; treal_add]
         |> THEN <| REWRITE_TAC [GSYM HREAL_ADD_ASSOC
                                 HREAL_LE_ADD_LCANCEL]
         |> THEN <| ONCE_REWRITE_TAC [HREAL_ADD_SYM]
         |> THEN <| REWRITE_TAC [GSYM HREAL_ADD_ASSOC
                                 HREAL_LE_ADD_LCANCEL])

let TREAL_LE_MUL = 
    prove((parse_term @"!x y. (treal_of_num 0) treal_le x /\ (treal_of_num 0) treal_le y
         ==> (treal_of_num 0) treal_le (x treal_mul y)"),
        REWRITE_TAC [FORALL_PAIR_THM; treal_of_num; treal_le; treal_mul]
        |> THEN <| REPEAT GEN_TAC
        |> THEN <| REWRITE_TAC [HREAL_ADD_LID; HREAL_ADD_RID]
        |> THEN <| DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
        |> THEN 
        <| DISCH_THEN(CHOOSE_THEN SUBST1_TAC << MATCH_MP HREAL_LE_EXISTS)
        |> THEN <| REWRITE_TAC [HREAL_ADD_LDISTRIB
                                HREAL_LE_ADD_LCANCEL
                                GSYM HREAL_ADD_ASSOC]
        |> THEN <| GEN_REWRITE_TAC RAND_CONV [HREAL_ADD_SYM]
        |> THEN <| ASM_REWRITE_TAC [HREAL_LE_ADD_LCANCEL]
        |> THEN <| MATCH_MP_TAC HREAL_LE_MUL_RCANCEL_IMP
        |> THEN <| ASM_REWRITE_TAC [])

let TREAL_INV_0 = 
    prove
        ((parse_term @"treal_inv (treal_of_num 0) treal_eq (treal_of_num 0)"), 
         REWRITE_TAC [treal_inv; treal_eq; treal_of_num])

let TREAL_MUL_LINV = 
    prove((parse_term @"!x. ~(x treal_eq treal_of_num 0) ==>
        (treal_inv(x) treal_mul x) treal_eq (treal_of_num 1)"),
       REWRITE_TAC [FORALL_PAIR_THM]
       |> THEN <| MAP_EVERY X_GEN_TAC [(parse_term @"x:hreal")
                                       (parse_term @"y:hreal")]
       |> THEN 
       <| PURE_REWRITE_TAC [treal_eq; treal_of_num; treal_mul; treal_inv]
       |> THEN <| PURE_REWRITE_TAC [HREAL_ADD_LID; HREAL_ADD_RID]
       |> THEN <| DISCH_TAC
       |> THEN <| PURE_ASM_REWRITE_TAC [COND_CLAUSES]
       |> THEN <| COND_CASES_TAC
       |> THEN <| PURE_REWRITE_TAC [treal_mul; treal_eq]
       |> THEN 
       <| REWRITE_TAC 
              [HREAL_ADD_LID; HREAL_ADD_RID; HREAL_MUL_LZERO; HREAL_MUL_RZERO]
       |> THENL <| [ALL_TAC
                    DISJ_CASES_THEN MP_TAC 
                        (SPECL [(parse_term @"x:hreal")
                                (parse_term @"y:hreal")] HREAL_LE_TOTAL)
                    |> THEN <| ASM_REWRITE_TAC []
                    |> THEN <| DISCH_TAC]
       |> THEN <| FIRST_ASSUM(MP_TAC << MATCH_MP HREAL_LE_EXISTS)
       |> THEN <| DISCH_THEN(MP_TAC << SELECT_RULE)
       |> THEN 
       <| DISCH_THEN
              (fun th -> 
                  ASSUME_TAC(SYM th)
                  |> THEN <| GEN_REWRITE_TAC (LAND_CONV << RAND_CONV) [th])
       |> THEN <| REWRITE_TAC [HREAL_ADD_LDISTRIB]
       |> THEN <| GEN_REWRITE_TAC RAND_CONV [HREAL_ADD_SYM]
       |> THEN <| AP_TERM_TAC
       |> THEN <| MATCH_MP_TAC HREAL_MUL_LINV
       |> THEN <| DISCH_THEN SUBST_ALL_TAC
       |> THEN <| FIRST_ASSUM(UNDISCH_TAC << check is_eq << concl)
       |> THEN <| ASM_REWRITE_TAC [HREAL_ADD_RID]
       |> THEN <| PURE_ONCE_REWRITE_TAC [EQ_SYM_EQ]
       |> THEN <| ASM_REWRITE_TAC [])

(* ------------------------------------------------------------------------- *)
(* Show that the operations respect the equivalence relation.                *)
(* ------------------------------------------------------------------------- *)
let TREAL_OF_NUM_WELLDEF = 
    prove
        ((parse_term @"!m n. (m = n) ==> (treal_of_num m) treal_eq (treal_of_num n)"), 
         REPEAT GEN_TAC
         |> THEN <| DISCH_THEN SUBST1_TAC
         |> THEN <| MATCH_ACCEPT_TAC TREAL_EQ_REFL)

let TREAL_NEG_WELLDEF = 
    prove
        ((parse_term @"!x1 x2. x1 treal_eq x2 ==> (treal_neg x1) treal_eq (treal_neg x2)"), 
         REWRITE_TAC [FORALL_PAIR_THM; treal_neg; treal_eq]
         |> THEN <| REPEAT STRIP_TAC
         |> THEN <| ONCE_REWRITE_TAC [HREAL_ADD_SYM]
         |> THEN <| ASM_REWRITE_TAC [])

let TREAL_ADD_WELLDEFR = 
    prove
        ((parse_term @"!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_add y) treal_eq (x2 treal_add y)"), 
         REWRITE_TAC [FORALL_PAIR_THM; treal_add; treal_eq]
         |> THEN <| REWRITE_TAC [HREAL_EQ_ADD_RCANCEL; HREAL_ADD_ASSOC]
         |> THEN <| ONCE_REWRITE_TAC [HREAL_ADD_SYM]
         |> THEN <| REWRITE_TAC [HREAL_EQ_ADD_RCANCEL; HREAL_ADD_ASSOC])

let TREAL_ADD_WELLDEF = 
    prove((parse_term @"!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
       (x1 treal_add y1) treal_eq (x2 treal_add y2)"),
      REPEAT GEN_TAC
      |> THEN <| DISCH_TAC
      |> THEN <| MATCH_MP_TAC TREAL_EQ_TRANS
      |> THEN <| EXISTS_TAC(parse_term @"x1 treal_add y2")
      |> THEN <| CONJ_TAC
      |> THENL <| [ONCE_REWRITE_TAC [TREAL_ADD_SYM_EQ]
                   ALL_TAC]
      |> THEN <| MATCH_MP_TAC TREAL_ADD_WELLDEFR
      |> THEN <| ASM_REWRITE_TAC [])

let TREAL_MUL_WELLDEFR = 
    prove
        ((parse_term @"!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_mul y) treal_eq (x2 treal_mul y)"), 
         REWRITE_TAC [FORALL_PAIR_THM; treal_mul; treal_eq]
         |> THEN <| REPEAT GEN_TAC
         |> THEN 
         <| ONCE_REWRITE_TAC 
                [AC HREAL_ADD_AC 
                     (parse_term @"(a + b) + (c + d) = (a + d) + (b + c)")]
         |> THEN <| REWRITE_TAC [GSYM HREAL_ADD_RDISTRIB]
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| AP_TERM_TAC
         |> THEN <| ONCE_REWRITE_TAC [HREAL_ADD_SYM]
         |> THEN <| POP_ASSUM SUBST1_TAC
         |> THEN <| REFL_TAC)

let TREAL_MUL_WELLDEF = 
  prove((parse_term @"!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_mul y1) treal_eq (x2 treal_mul y2)"),
    REPEAT GEN_TAC
    |> THEN <| DISCH_TAC
    |> THEN <| MATCH_MP_TAC TREAL_EQ_TRANS
    |> THEN <| EXISTS_TAC(parse_term @"x1 treal_mul y2")
    |> THEN <| CONJ_TAC
    |> THENL <| [ONCE_REWRITE_TAC [TREAL_MUL_SYM_EQ]
                 ALL_TAC]
    |> THEN <| MATCH_MP_TAC TREAL_MUL_WELLDEFR
    |> THEN <| ASM_REWRITE_TAC [])

let TREAL_EQ_IMP_LE = 
    prove
        ((parse_term @"!x y. x treal_eq y ==> x treal_le y"), 
         SIMP_TAC [FORALL_PAIR_THM; treal_eq; treal_le; HREAL_LE_REFL])

let TREAL_LE_WELLDEF = 
  prove((parse_term @"!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_le y1 <=> x2 treal_le y2)"),
    REPEAT(STRIP_TAC
           |> ORELSE <| EQ_TAC)
    |> THENL <| [MATCH_MP_TAC TREAL_LE_TRANS
                 |> THEN <| EXISTS_TAC(parse_term @"y1:hreal#hreal")
                 |> THEN <| CONJ_TAC
                 |> THENL <| [MATCH_MP_TAC TREAL_LE_TRANS
                              |> THEN <| EXISTS_TAC(parse_term @"x1:hreal#hreal")
                              |> THEN <| ASM_REWRITE_TAC []
                              |> THEN <| MATCH_MP_TAC TREAL_EQ_IMP_LE
                              |> THEN <| ONCE_REWRITE_TAC [TREAL_EQ_SYM]
                              MATCH_MP_TAC TREAL_EQ_IMP_LE]
                 MATCH_MP_TAC TREAL_LE_TRANS
                 |> THEN <| EXISTS_TAC(parse_term @"y2:hreal#hreal")
                 |> THEN <| CONJ_TAC
                 |> THENL <| [MATCH_MP_TAC TREAL_LE_TRANS
                              |> THEN <| EXISTS_TAC(parse_term @"x2:hreal#hreal")
                              |> THEN <| ASM_REWRITE_TAC []
                              |> THEN <| MATCH_MP_TAC TREAL_EQ_IMP_LE
                              MATCH_MP_TAC TREAL_EQ_IMP_LE
                              |> THEN <| ONCE_REWRITE_TAC [TREAL_EQ_SYM]]]
    |> THEN <| ASM_REWRITE_TAC [])

let TREAL_INV_WELLDEF = 
    prove
        ((parse_term @"!x y. x treal_eq y ==> (treal_inv x) treal_eq (treal_inv y)"), 
         let lemma = 
             prove
                 ((parse_term @"(@d. x = x + d) = &0"), 
                  MATCH_MP_TAC SELECT_UNIQUE
                  |> THEN <| BETA_TAC
                  |> THEN <| GEN_TAC
                  |> THEN 
                  <| GEN_REWRITE_TAC (funpow 2 LAND_CONV) [GSYM HREAL_ADD_RID]
                  |> THEN <| REWRITE_TAC [HREAL_EQ_ADD_LCANCEL]
                  |> THEN <| MATCH_ACCEPT_TAC EQ_SYM_EQ)
         REWRITE_TAC [FORALL_PAIR_THM]
         |> THEN <| MAP_EVERY X_GEN_TAC [(parse_term @"x1:hreal")
                                         (parse_term @"x2:hreal")
                                         (parse_term @"y1:hreal")
                                         (parse_term @"y2:hreal")]
         |> THEN <| PURE_REWRITE_TAC [treal_eq; treal_inv]
         |> THEN <| ASM_CASES_TAC(parse_term @"x1 :hreal = x2")
         |> THEN <| ASM_CASES_TAC(parse_term @"y1 :hreal = y2")
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| REWRITE_TAC [TREAL_EQ_REFL]
         |> THEN 
         <| DISCH_THEN(MP_TAC << GEN_REWRITE_RULE RAND_CONV [HREAL_ADD_SYM])
         |> THEN <| REWRITE_TAC [HREAL_EQ_ADD_LCANCEL; HREAL_EQ_ADD_RCANCEL]
         |> THEN <| DISCH_TAC
         |> THEN 
         <| ASM_REWRITE_TAC [HREAL_LE_REFL; lemma; HREAL_INV_0; TREAL_EQ_REFL]
         |> THEN <| ASM_CASES_TAC(parse_term @"x2 <= x1")
         |> THEN <| ASM_REWRITE_TAC []
         |> THENL 
         <| [FIRST_ASSUM
                 (ASSUME_TAC << SYM << SELECT_RULE << MATCH_MP HREAL_LE_EXISTS)
             |> THEN <| UNDISCH_TAC(parse_term @"x1 + y2 = x2 + y1")
             |> THEN <| FIRST_ASSUM(SUBST1_TAC << SYM)
             |> THEN <| REWRITE_TAC [HREAL_EQ_ADD_LCANCEL
                                     GSYM HREAL_ADD_ASSOC]
             |> THEN <| DISCH_THEN(SUBST1_TAC << SYM)
             |> THEN 
             <| REWRITE_TAC [ONCE_REWRITE_RULE [HREAL_ADD_SYM] HREAL_LE_ADD]
             |> THEN 
             <| GEN_REWRITE_TAC 
                    (RAND_CONV << LAND_CONV << RAND_CONV << BINDER_CONV 
                     << LAND_CONV) [HREAL_ADD_SYM]
             |> THEN <| REWRITE_TAC [HREAL_EQ_ADD_LCANCEL; TREAL_EQ_REFL]
             DISJ_CASES_THEN MP_TAC 
                 (SPECL [(parse_term @"x1:hreal")
                         (parse_term @"x2:hreal")] HREAL_LE_TOTAL)
             |> THEN <| ASM_REWRITE_TAC []
             |> THEN <| DISCH_TAC
             |> THEN 
             <| FIRST_ASSUM
                    (ASSUME_TAC << SYM << SELECT_RULE 
                     << MATCH_MP HREAL_LE_EXISTS)
             |> THEN <| UNDISCH_TAC(parse_term @"x1 + y2 = x2 + y1")
             |> THEN <| FIRST_ASSUM(SUBST1_TAC << SYM)
             |> THEN <| REWRITE_TAC [HREAL_EQ_ADD_LCANCEL
                                     GSYM HREAL_ADD_ASSOC]
             |> THEN <| DISCH_THEN SUBST1_TAC
             |> THEN 
             <| REWRITE_TAC [ONCE_REWRITE_RULE [HREAL_ADD_SYM] HREAL_LE_ADD]
             |> THEN <| COND_CASES_TAC
             |> THENL 
             <| [UNDISCH_TAC(parse_term @"(@d. x2 = x1 + d) + y1 <= y1:hreal")
                 |> THEN 
                 <| GEN_REWRITE_TAC (LAND_CONV << RAND_CONV) 
                        [GSYM HREAL_ADD_LID]
                 |> THEN 
                 <| REWRITE_TAC 
                        [ONCE_REWRITE_RULE [HREAL_ADD_SYM] HREAL_LE_ADD_LCANCEL]
                 |> THEN <| DISCH_TAC
                 |> THEN 
                 <| SUBGOAL_THEN (parse_term @"(@d. x2 = x1 + d) = &0") MP_TAC
                 |> THENL <| [ASM_REWRITE_TAC [GSYM HREAL_LE_ANTISYM]
                              |> THEN 
                              <| GEN_REWRITE_TAC RAND_CONV [GSYM HREAL_ADD_LID]
                              |> THEN <| REWRITE_TAC [HREAL_LE_ADD]
                              DISCH_THEN SUBST_ALL_TAC
                              |> THEN <| UNDISCH_TAC(parse_term @"x1 + & 0 = x2")
                              |> THEN <| ASM_REWRITE_TAC [HREAL_ADD_RID]]
                 GEN_REWRITE_TAC 
                     (funpow 3 RAND_CONV << BINDER_CONV << LAND_CONV) 
                     [HREAL_ADD_SYM]
                 |> THEN <| REWRITE_TAC [HREAL_EQ_ADD_LCANCEL; TREAL_EQ_REFL]]])

(* ------------------------------------------------------------------------- *)
(* Now define the quotient type -- the reals at last!                        *)
(* ------------------------------------------------------------------------- *)
let real_tybij = 
    define_quotient_type "real" ("mk_real", "dest_real") 
        (parse_term @"(treal_eq)")

let real_of_num, real_of_num_th = 
    lift_function (snd real_tybij) (TREAL_EQ_REFL, TREAL_EQ_TRANS) "real_of_num" 
        TREAL_OF_NUM_WELLDEF
let real_neg, real_neg_th = 
    lift_function (snd real_tybij) (TREAL_EQ_REFL, TREAL_EQ_TRANS) "real_neg" 
        TREAL_NEG_WELLDEF
let real_add, real_add_th = 
    lift_function (snd real_tybij) (TREAL_EQ_REFL, TREAL_EQ_TRANS) "real_add" 
        TREAL_ADD_WELLDEF
let real_mul, real_mul_th = 
    lift_function (snd real_tybij) (TREAL_EQ_REFL, TREAL_EQ_TRANS) "real_mul" 
        TREAL_MUL_WELLDEF
let real_le, real_le_th = 
    lift_function (snd real_tybij) (TREAL_EQ_REFL, TREAL_EQ_TRANS) "real_le" 
        TREAL_LE_WELLDEF
let real_inv, real_inv_th = 
    lift_function (snd real_tybij) (TREAL_EQ_REFL, TREAL_EQ_TRANS) "real_inv" 
        TREAL_INV_WELLDEF

let REAL_ADD_SYM, REAL_ADD_ASSOC, REAL_ADD_LID, REAL_ADD_LINV, REAL_MUL_SYM, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_ADD_LDISTRIB, REAL_LE_REFL, REAL_LE_ANTISYM, REAL_LE_TRANS, REAL_LE_TOTAL, REAL_LE_LADD_IMP, REAL_LE_MUL, REAL_INV_0, REAL_MUL_LINV, REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_ADD, REAL_OF_NUM_MUL =
    let realFuncs =
        map (lift_theorem real_tybij (TREAL_EQ_REFL, TREAL_EQ_SYM, TREAL_EQ_TRANS) 
                    [real_of_num_th; real_neg_th; real_add_th; real_mul_th; real_le_th; 
                    real_inv_th]) 
            [TREAL_ADD_SYM; TREAL_ADD_ASSOC; TREAL_ADD_LID; TREAL_ADD_LINV; 
                TREAL_MUL_SYM; TREAL_MUL_ASSOC; TREAL_MUL_LID; TREAL_ADD_LDISTRIB; 
                TREAL_LE_REFL; TREAL_LE_ANTISYM; TREAL_LE_TRANS; TREAL_LE_TOTAL; 
                TREAL_LE_LADD_IMP; TREAL_LE_MUL; TREAL_INV_0; TREAL_MUL_LINV; 
                TREAL_OF_NUM_EQ; TREAL_OF_NUM_LE; TREAL_OF_NUM_ADD; TREAL_OF_NUM_MUL]
    match realFuncs with
    | [real_add_sym; real_add_assoc; real_add_lid; real_add_linv; real_mul_sym; 
            real_mul_assoc; real_mul_lid; real_add_ldistrib; real_le_refl; 
            real_le_antisym; real_le_trans; real_le_total; real_le_ladd_imp; 
            real_le_mul; real_inv_0; real_mul_linv; real_of_num_eq; real_of_num_le; 
            real_of_num_add; real_of_num_mul] -> 
            real_add_sym, real_add_assoc, real_add_lid, real_add_linv, real_mul_sym, 
            real_mul_assoc, real_mul_lid, real_add_ldistrib, real_le_refl, 
            real_le_antisym, real_le_trans, real_le_total, real_le_ladd_imp, 
            real_le_mul, real_inv_0, real_mul_linv, real_of_num_eq, real_of_num_le, 
            real_of_num_add, real_of_num_mul
    | _ -> failwith "realFuncs: Unhandled case."

parse_as_prefix "--"
parse_as_infix("/", (22, "left"))
parse_as_infix("pow", (24, "left"))
do_list overload_interface ["+", (parse_term @"real_add:real->real->real")
                            "-", (parse_term @"real_sub:real->real->real")
                            "*", (parse_term @"real_mul:real->real->real")
                            "/", (parse_term @"real_div:real->real->real")
                            "<", (parse_term @"real_lt:real->real->bool")
                            "<=", (parse_term @"real_le:real->real->bool")
                            ">", (parse_term @"real_gt:real->real->bool")
                            ">=", (parse_term @"real_ge:real->real->bool")
                            "--", (parse_term @"real_neg:real->real")
                            "pow", (parse_term @"real_pow:real->num->real")
                            "inv", (parse_term @"real_inv:real->real")
                            "abs", (parse_term @"real_abs:real->real")
                            "max", (parse_term @"real_max:real->real->real")
                            "min", (parse_term @"real_min:real->real->real")
                            "&", (parse_term @"real_of_num:num->real")]

(* ------------------------------------------------------------------------- *)
(* Set up a friendly interface.                                              *)
(* ------------------------------------------------------------------------- *)
/// Give real number type 'real' priority in operator overloading.
let prioritize_real() = prioritize_overload(mk_type("real", []))

(* ------------------------------------------------------------------------- *)
(* Additional definitions.                                                   *)
(* ------------------------------------------------------------------------- *)
let real_sub = new_definition(parse_term @"x - y = x + --y")

let real_lt = new_definition(parse_term @"x < y <=> ~(y <= x)")
let real_ge = new_definition(parse_term @"x >= y <=> y <= x")
let real_gt = new_definition(parse_term @"x > y <=> y < x")
let real_abs = new_definition(parse_term @"abs(x) = if &0 <= x then x else --x")
let real_pow = new_recursive_definition num_RECURSION (parse_term @"(x pow 0 = &1) /\
   (!n. x pow (SUC n) = x * (x pow n))")
let real_div = new_definition(parse_term @"x / y = x * inv(y)")
let real_max = 
    new_definition(parse_term @"real_max m n = if m <= n then n else m")
let real_min = 
    new_definition(parse_term @"real_min m n = if m <= n then m else n")

(*----------------------------------------------------------------------------*)
(* Derive the supremum property for an arbitrary bounded nonempty set         *)
(*----------------------------------------------------------------------------*)
let REAL_HREAL_LEMMA1 = 
    prove
        ((parse_term @"?r:hreal->real.
       (!x. &0 <= x <=> ?y. x = r y) /\
       (!y z. y <= z <=> r y <= r z)"), 
         EXISTS_TAC(parse_term @"\y. mk_real((treal_eq)(y,hreal_of_num 0))")
         |> THEN <| REWRITE_TAC [GSYM real_le_th]
         |> THEN <| REWRITE_TAC [treal_le; HREAL_ADD_LID; HREAL_ADD_RID]
         |> THEN <| GEN_TAC
         |> THEN <| EQ_TAC
         |> THENL <| [MP_TAC
                          (INST 
                               [(parse_term @"dest_real x"), 
                                (parse_term @"r:hreal#hreal->bool")] 
                               (snd real_tybij))
                      |> THEN <| REWRITE_TAC [fst real_tybij]
                      |> THEN 
                      <| DISCH_THEN
                             (X_CHOOSE_THEN (parse_term @"p:hreal#hreal") MP_TAC)
                      |> THEN 
                      <| DISCH_THEN(MP_TAC << AP_TERM(parse_term @"mk_real"))
                      |> THEN <| REWRITE_TAC [fst real_tybij]
                      |> THEN <| DISCH_THEN SUBST1_TAC
                      |> THEN <| REWRITE_TAC [GSYM real_of_num_th
                                              GSYM real_le_th]
                      |> THEN 
                      <| SUBST1_TAC
                             (GSYM(ISPEC (parse_term @"p:hreal#hreal") PAIR))
                      |> THEN <| PURE_REWRITE_TAC [treal_of_num; treal_le]
                      |> THEN <| PURE_REWRITE_TAC [HREAL_ADD_LID; HREAL_ADD_RID]
                      |> THEN 
                      <| DISCH_THEN
                             (X_CHOOSE_THEN (parse_term @"d:hreal") SUBST1_TAC 
                              << MATCH_MP HREAL_LE_EXISTS)
                      |> THEN <| EXISTS_TAC(parse_term @"d:hreal")
                      |> THEN <| AP_TERM_TAC
                      |> THEN <| ONCE_REWRITE_TAC [FUN_EQ_THM]
                      |> THEN <| X_GEN_TAC(parse_term @"q:hreal#hreal")
                      |> THEN 
                      <| SUBST1_TAC
                             (GSYM(ISPEC (parse_term @"q:hreal#hreal") PAIR))
                      |> THEN <| PURE_REWRITE_TAC [treal_eq]
                      |> THEN 
                      <| GEN_REWRITE_TAC (LAND_CONV << RAND_CONV) 
                             [HREAL_ADD_SYM]
                      |> THEN <| REWRITE_TAC [GSYM HREAL_ADD_ASSOC
                                              HREAL_EQ_ADD_LCANCEL]
                      |> THEN <| REWRITE_TAC [HREAL_ADD_RID]
                      DISCH_THEN(CHOOSE_THEN SUBST1_TAC)
                      |> THEN <| REWRITE_TAC [GSYM real_of_num_th
                                              GSYM real_le_th]
                      |> THEN <| REWRITE_TAC [treal_of_num; treal_le]
                      |> THEN <| REWRITE_TAC [HREAL_ADD_LID; HREAL_ADD_RID]
                      |> THEN <| GEN_REWRITE_TAC RAND_CONV [GSYM HREAL_ADD_LID]
                      |> THEN <| REWRITE_TAC [HREAL_LE_ADD]])

let REAL_HREAL_LEMMA2 = 
    prove
        ((parse_term @"?h r. (!x:hreal. h(r x) = x) /\
         (!x. &0 <= x ==> (r(h x) = x)) /\
         (!x:hreal. &0 <= r x) /\
         (!x y. x <= y <=> r x <= r y)"), 
         STRIP_ASSUME_TAC REAL_HREAL_LEMMA1
         |> THEN <| EXISTS_TAC(parse_term @"\x:real. @y:hreal. x = r y")
         |> THEN <| EXISTS_TAC(parse_term @"r:hreal->real")
         |> THEN <| ASM_REWRITE_TAC [BETA_THM]
         |> THEN 
         <| SUBGOAL_THEN 
                (parse_term @"!y z. ((r:hreal->real) y = r z) <=> (y = z)") 
                ASSUME_TAC
         |> THENL <| [ASM_REWRITE_TAC [GSYM REAL_LE_ANTISYM
                                       GSYM HREAL_LE_ANTISYM]
                      ALL_TAC]
         |> THEN <| ASM_REWRITE_TAC [GEN_REWRITE_RULE (LAND_CONV << BINDER_CONV) 
                                         [EQ_SYM_EQ] (SPEC_ALL SELECT_REFL)
                                     GSYM EXISTS_REFL]
         |> THEN <| GEN_TAC
         |> THEN <| DISCH_THEN(ACCEPT_TAC << SYM << SELECT_RULE))

let REAL_COMPLETE_SOMEPOS = 
    prove
        ((parse_term @"!P. (?x. P x /\ &0 <= x) /\
       (?M. !x. P x ==> x <= M)
       ==> ?M. (!x. P x ==> x <= M) /\
               !M'. (!x. P x ==> x <= M') ==> M <= M'"), 
         REPEAT STRIP_TAC
         |> THEN <| STRIP_ASSUME_TAC REAL_HREAL_LEMMA2
         |> THEN 
         <| MP_TAC
                (SPEC (parse_term @"\y:hreal. (P:real->bool)(r y)") 
                     HREAL_COMPLETE)
         |> THEN <| BETA_TAC
         |> THEN 
         <| W(C SUBGOAL_THEN MP_TAC << funpow 2 (fst << dest_imp) << snd)
         |> THENL 
         <| [CONJ_TAC
             |> THENL <| [EXISTS_TAC(parse_term @"(h:real->hreal) x")
                          |> THEN <| UNDISCH_TAC(parse_term @"(P:real->bool) x")
                          |> THEN 
                          <| MATCH_MP_TAC
                                 (TAUT(parse_term @"(b <=> a) ==> a ==> b"))
                          |> THEN <| AP_TERM_TAC
                          |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                          |> THEN <| ASM_REWRITE_TAC []
                          EXISTS_TAC(parse_term @"(h:real->hreal) M")
                          |> THEN <| X_GEN_TAC(parse_term @"y:hreal")
                          |> THEN <| DISCH_THEN(ANTE_RES_THEN MP_TAC)
                          |> THEN <| ASM_REWRITE_TAC []
                          |> THEN 
                          <| MATCH_MP_TAC
                                 (TAUT(parse_term @"(b <=> a) ==> a ==> b"))
                          |> THEN <| AP_TERM_TAC
                          |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                          |> THEN <| MATCH_MP_TAC REAL_LE_TRANS
                          |> THEN <| EXISTS_TAC(parse_term @"x:real")
                          |> THEN <| ASM_REWRITE_TAC []
                          |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                          |> THEN <| ASM_REWRITE_TAC []]
             MATCH_MP_TAC
                 (TAUT(parse_term @"(b ==> c) ==> a ==> (a ==> b) ==> c"))
             |> THEN 
             <| DISCH_THEN
                    (X_CHOOSE_THEN (parse_term @"B:hreal") STRIP_ASSUME_TAC)]
         |> THEN <| EXISTS_TAC(parse_term @"(r:hreal->real) B")
         |> THEN <| CONJ_TAC
         |> THENL <| [X_GEN_TAC(parse_term @"z:real")
                      |> THEN <| DISCH_TAC
                      |> THEN 
                      <| DISJ_CASES_TAC
                             (SPECL [(parse_term @"&0")
                                     (parse_term @"z:real")] REAL_LE_TOTAL)
                      |> THENL <| [ANTE_RES_THEN (SUBST1_TAC << SYM) 
                                       (ASSUME(parse_term @"&0 <= z"))
                                   |> THEN 
                                   <| FIRST_ASSUM
                                          (fun th -> GEN_REWRITE_TAC I [GSYM th])
                                   |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                                   |> THEN 
                                   <| UNDISCH_TAC(parse_term @"(P:real->bool) z")
                                   |> THEN 
                                   <| MATCH_MP_TAC
                                          (TAUT
                                               (parse_term @"(b <=> a) ==> a ==> b"))
                                   |> THEN <| AP_TERM_TAC
                                   |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                                   |> THEN <| ASM_REWRITE_TAC []
                                   MATCH_MP_TAC REAL_LE_TRANS
                                   |> THEN <| EXISTS_TAC(parse_term @"&0")
                                   |> THEN <| ASM_REWRITE_TAC []]
                      X_GEN_TAC(parse_term @"C:real")
                      |> THEN <| DISCH_TAC
                      |> THEN 
                      <| SUBGOAL_THEN (parse_term @"B:hreal <= (h(C:real))") 
                             MP_TAC
                      |> THENL <| [FIRST_ASSUM MATCH_MP_TAC
                                   |> THEN <| ASM_REWRITE_TAC []
                                   |> THEN 
                                   <| SUBGOAL_THEN 
                                          (parse_term @"(r:hreal->real)(h C) = C") 
                                          (fun th -> ASM_REWRITE_TAC [th])
                                   ASM_REWRITE_TAC []
                                   |> THEN <| MATCH_MP_TAC EQ_IMP
                                   |> THEN <| AP_TERM_TAC]
                      |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                      |> THEN <| MATCH_MP_TAC REAL_LE_TRANS
                      |> THEN <| EXISTS_TAC(parse_term @"x:real")
                      |> THEN <| ASM_REWRITE_TAC []
                      |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                      |> THEN <| ASM_REWRITE_TAC []])

let REAL_COMPLETE = 
    prove
        ((parse_term @"!P. (?x. P x) /\
       (?M. !x. P x ==> x <= M)
       ==> ?M. (!x. P x ==> x <= M) /\
               !M'. (!x. P x ==> x <= M') ==> M <= M'"), 
         let lemma = 
             prove
                 ((parse_term @"y = (y - x) + x"), 
                  REWRITE_TAC [real_sub
                               GSYM REAL_ADD_ASSOC
                               REAL_ADD_LINV]
                  |> THEN <| ONCE_REWRITE_TAC [REAL_ADD_SYM]
                  |> THEN <| REWRITE_TAC [REAL_ADD_LID])
         REPEAT STRIP_TAC
         |> THEN <| DISJ_CASES_TAC(SPECL [(parse_term @"&0")
                                          (parse_term @"x:real")] REAL_LE_TOTAL)
         |> THENL 
         <| [MATCH_MP_TAC REAL_COMPLETE_SOMEPOS
             |> THEN <| CONJ_TAC
             |> THENL <| [EXISTS_TAC(parse_term @"x:real")
                          EXISTS_TAC(parse_term @"M:real")]
             |> THEN <| ASM_REWRITE_TAC []
             FIRST_ASSUM(MP_TAC << MATCH_MP REAL_LE_LADD_IMP)
             |> THEN <| DISCH_THEN(MP_TAC << SPEC(parse_term @"--x"))
             |> THEN <| REWRITE_TAC [REAL_ADD_LINV]
             |> THEN <| ONCE_REWRITE_TAC [REAL_ADD_SYM]
             |> THEN <| REWRITE_TAC [REAL_ADD_LID]
             |> THEN <| DISCH_TAC
             |> THEN 
             <| MP_TAC
                    (SPEC (parse_term @"\y. P(y + x) :bool") 
                         REAL_COMPLETE_SOMEPOS)
             |> THEN <| BETA_TAC
             |> THEN 
             <| W(C SUBGOAL_THEN MP_TAC << funpow 2 (fst << dest_imp) << snd)
             |> THENL 
             <| [CONJ_TAC
                 |> THENL 
                 <| [EXISTS_TAC(parse_term @"&0")
                     |> THEN <| ASM_REWRITE_TAC [REAL_LE_REFL; REAL_ADD_LID]
                     EXISTS_TAC(parse_term @"M + --x")
                     |> THEN <| GEN_TAC
                     |> THEN <| DISCH_THEN(ANTE_RES_THEN MP_TAC)
                     |> THEN 
                     <| DISCH_THEN
                            (MP_TAC << SPEC(parse_term @"--x") 
                             << MATCH_MP REAL_LE_LADD_IMP)
                     |> THEN 
                     <| DISCH_THEN(MP_TAC << ONCE_REWRITE_RULE [REAL_ADD_SYM])
                     |> THEN <| REWRITE_TAC [GSYM REAL_ADD_ASSOC]
                     |> THEN 
                     <| REWRITE_TAC 
                            [ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LINV]
                     |> THEN 
                     <| REWRITE_TAC 
                            [ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LID]]
                 MATCH_MP_TAC
                     (TAUT(parse_term @"(b ==> c) ==> a ==> (a ==> b) ==> c"))
                 |> THEN 
                 <| DISCH_THEN
                        (X_CHOOSE_THEN (parse_term @"B:real") STRIP_ASSUME_TAC)]
             |> THEN <| EXISTS_TAC(parse_term @"B + x")
             |> THEN <| CONJ_TAC
             |> THENL 
             <| [GEN_TAC
                 |> THEN <| GEN_REWRITE_TAC (LAND_CONV << RAND_CONV) [lemma]
                 |> THEN 
                 <| DISCH_THEN
                        (ANTE_RES_THEN
                             (MP_TAC << SPEC(parse_term @"x:real") 
                              << MATCH_MP REAL_LE_LADD_IMP))
                 |> THEN <| ONCE_REWRITE_TAC [REAL_ADD_SYM]
                 |> THEN <| REWRITE_TAC [real_sub
                                         GSYM REAL_ADD_ASSOC
                                         REAL_ADD_LINV]
                 |> THEN 
                 <| REWRITE_TAC [ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LID]
                 |> THEN <| REPEAT STRIP_TAC
                 |> THEN <| ONCE_REWRITE_TAC [REAL_ADD_SYM]
                 |> THEN <| ASM_REWRITE_TAC []
                 REPEAT STRIP_TAC
                 |> THEN <| SUBGOAL_THEN (parse_term @"B <= M' - x") MP_TAC
                 |> THENL 
                 <| [FIRST_ASSUM MATCH_MP_TAC
                     |> THEN <| X_GEN_TAC(parse_term @"z:real")
                     |> THEN <| DISCH_TAC
                     |> THEN <| SUBGOAL_THEN (parse_term @"z + x <= M'") MP_TAC
                     |> THENL 
                     <| [FIRST_ASSUM MATCH_MP_TAC
                         |> THEN <| ASM_REWRITE_TAC []
                         DISCH_THEN
                             (MP_TAC << SPEC(parse_term @"--x") 
                              << MATCH_MP REAL_LE_LADD_IMP)
                         |> THEN <| ONCE_REWRITE_TAC [REAL_ADD_SYM]
                         |> THEN <| REWRITE_TAC [real_sub]
                         |> THEN <| MATCH_MP_TAC EQ_IMP
                         |> THEN <| AP_THM_TAC
                         |> THEN <| AP_TERM_TAC
                         |> THEN <| REWRITE_TAC [GSYM REAL_ADD_ASSOC]
                         |> THEN 
                         <| REWRITE_TAC 
                                [ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LINV]
                         |> THEN 
                         <| REWRITE_TAC 
                                [ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LID]]
                     DISCH_THEN
                         (MP_TAC << SPEC(parse_term @"x:real") 
                          << MATCH_MP REAL_LE_LADD_IMP)
                     |> THEN <| MATCH_MP_TAC EQ_IMP
                     |> THEN <| BINOP_TAC
                     |> THENL 
                     <| [MATCH_ACCEPT_TAC REAL_ADD_SYM
                         ONCE_REWRITE_TAC [REAL_ADD_SYM]
                         |> THEN <| REWRITE_TAC [real_sub]
                         |> THEN <| REWRITE_TAC [GSYM REAL_ADD_ASSOC
                                                 REAL_ADD_LINV]
                         |> THEN 
                         <| REWRITE_TAC 
                                [ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LID]]]]])

do_list reduce_interface ["+", (parse_term @"hreal_add:hreal->hreal->hreal")
                          "*", (parse_term @"hreal_mul:hreal->hreal->hreal")
                          "<=", (parse_term @"hreal_le:hreal->hreal->bool")
                          "inv", (parse_term @"hreal_inv:hreal->hreal")]
do_list remove_interface ["**"
                          "++"
                          "<<="
                          "==="
                          "fn"
                          "afn"]
