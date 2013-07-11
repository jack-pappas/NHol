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
/// Natural number arithmetic.
module NHol.arith

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
#endif

parse_as_infix("<", (12, "right"))
parse_as_infix("<=", (12, "right"))
parse_as_infix(">", (12, "right"))
parse_as_infix(">=", (12, "right"))
parse_as_infix("+", (16, "right"))
parse_as_infix("-", (18, "left"))
parse_as_infix("*", (20, "right"))
parse_as_infix("EXP", (24, "left"))
parse_as_infix("DIV", (22, "left"))
parse_as_infix("MOD", (22, "left"))

(* ------------------------------------------------------------------------- *)
(* Note: all the following proofs are intuitionistic and intensional, except *)
(* for the least number principle num_WOP.                                   *)
(* (And except the arith rewrites at the end; these could be done that way   *)
(* but they use the conditional anyway.) In fact, one could very easily      *)
(* write a "decider" returning P \/ ~P for quantifier-free P.                *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* The predecessor function.                                                 *)
(* ------------------------------------------------------------------------- *)
let PRE = new_recursive_definition num_RECURSION (parse_term @"(PRE 0 = 0) /\
   (!n. PRE (SUC n) = n)")

(* ------------------------------------------------------------------------- *)
(* Addition.                                                                 *)
(* ------------------------------------------------------------------------- *)
let ADD = new_recursive_definition num_RECURSION (parse_term @"(!n. 0 + n = n) /\
   (!m n. (SUC m) + n = SUC(m + n))")

let ADD_0 = 
    prove((parse_term @"!m. m + 0 = m"), INDUCT_TAC
                                        |> THEN <| ASM_REWRITE_TAC [ADD])
let ADD_SUC = 
    prove
        ((parse_term @"!m n. m + (SUC n) = SUC(m + n)"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [ADD])
let ADD_CLAUSES = prove((parse_term @"(!n. 0 + n = n) /\
    (!m. m + 0 = m) /\
    (!m n. (SUC m) + n = SUC(m + n)) /\
    (!m n. m + (SUC n) = SUC(m + n))"), REWRITE_TAC [ADD; ADD_0; ADD_SUC])
let ADD_SYM = 
    prove
        ((parse_term @"!m n. m + n = n + m"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [ADD_CLAUSES])
let ADD_ASSOC = 
    prove
        ((parse_term @"!m n p. m + (n + p) = (m + n) + p"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [ADD_CLAUSES])
let ADD_AC = prove((parse_term @"(m + n = n + m) /\
    ((m + n) + p = m + (n + p)) /\
    (m + (n + p) = n + (m + p))"), MESON_TAC [ADD_ASSOC; ADD_SYM])
let ADD_EQ_0 = 
    prove
        ((parse_term @"!m n. (m + n = 0) <=> (m = 0) /\ (n = 0)"), 
         REPEAT INDUCT_TAC
         |> THEN <| REWRITE_TAC [ADD_CLAUSES; NOT_SUC])
let EQ_ADD_LCANCEL = 
    prove
        ((parse_term @"!m n p. (m + n = m + p) <=> (n = p)"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [ADD_CLAUSES; SUC_INJ])
let EQ_ADD_RCANCEL = 
    prove
        ((parse_term @"!m n p. (m + p = n + p) <=> (m = n)"), 
         ONCE_REWRITE_TAC [ADD_SYM]
         |> THEN <| MATCH_ACCEPT_TAC EQ_ADD_LCANCEL)
let EQ_ADD_LCANCEL_0 = 
    prove
        ((parse_term @"!m n. (m + n = m) <=> (n = 0)"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [ADD_CLAUSES; SUC_INJ])
let EQ_ADD_RCANCEL_0 = 
    prove
        ((parse_term @"!m n. (m + n = n) <=> (m = 0)"), 
         ONCE_REWRITE_TAC [ADD_SYM]
         |> THEN <| MATCH_ACCEPT_TAC EQ_ADD_LCANCEL_0)

(* ------------------------------------------------------------------------- *)
(* Now define "bitwise" binary representation of numerals.                   *)
(* ------------------------------------------------------------------------- *)
let BIT0 = 
    prove
        ((parse_term @"!n. BIT0 n = n + n"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [BIT0_DEF; ADD_CLAUSES])

let BIT1 = 
    prove((parse_term @"!n. BIT1 n = SUC(n + n)"), REWRITE_TAC [BIT1_DEF; BIT0])
let BIT0_THM = 
    prove
        ((parse_term @"!n. NUMERAL (BIT0 n) = NUMERAL n + NUMERAL n"), 
         REWRITE_TAC [NUMERAL; BIT0])
let BIT1_THM = 
    prove
        ((parse_term @"!n. NUMERAL (BIT1 n) = SUC(NUMERAL n + NUMERAL n)"), 
         REWRITE_TAC [NUMERAL; BIT1])

(* ------------------------------------------------------------------------- *)
(* Following is handy before num_CONV arrives.                               *)
(* ------------------------------------------------------------------------- *)
let ONE = 
    prove((parse_term @"1 = SUC 0"), REWRITE_TAC[BIT1
                                                 REWRITE_RULE [NUMERAL] 
                                                     ADD_CLAUSES
                                                 NUMERAL])

let TWO = 
    prove((parse_term @"2 = SUC 1"), REWRITE_TAC[BIT0
                                                 BIT1
                                                 REWRITE_RULE [NUMERAL] 
                                                     ADD_CLAUSES
                                                 NUMERAL])

(* ------------------------------------------------------------------------- *)
(* One immediate consequence.                                                *)
(* ------------------------------------------------------------------------- *)
let ADD1 = 
    prove((parse_term @"!m. SUC m = m + 1"), REWRITE_TAC [BIT1_THM; ADD_CLAUSES])

(* ------------------------------------------------------------------------- *)
(* Multiplication.                                                           *)
(* ------------------------------------------------------------------------- *)
let MULT = new_recursive_definition num_RECURSION (parse_term @"(!n. 0 * n = 0) /\
   (!m n. (SUC m) * n = (m * n) + n)")

let MULT_0 = 
    prove
        ((parse_term @"!m. m * 0 = 0"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [MULT; ADD_CLAUSES])
let MULT_SUC = 
    prove
        ((parse_term @"!m n. m * (SUC n) = m + (m * n)"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [MULT; ADD_CLAUSES; ADD_ASSOC])
let MULT_CLAUSES = 
    prove
        ((parse_term @"(!n. 0 * n = 0) /\
    (!m. m * 0 = 0) /\
    (!n. 1 * n = n) /\
    (!m. m * 1 = m) /\
    (!m n. (SUC m) * n = (m * n) + n) /\
    (!m n. m * (SUC n) = m + (m * n))"), 
         REWRITE_TAC [BIT1_THM; MULT; MULT_0; MULT_SUC; ADD_CLAUSES])

let MULT_SYM = 
    prove
        ((parse_term @"!m n. m * n = n * m"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES
                                     EQT_INTRO(SPEC_ALL ADD_SYM)])

let LEFT_ADD_DISTRIB = 
    prove
        ((parse_term @"!m n p. m * (n + p) = (m * n) + (m * p)"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [ADD; MULT_CLAUSES; ADD_ASSOC])

let RIGHT_ADD_DISTRIB = 
    prove
        ((parse_term @"!m n p. (m + n) * p = (m * p) + (n * p)"), 
         ONCE_REWRITE_TAC [MULT_SYM]
         |> THEN <| MATCH_ACCEPT_TAC LEFT_ADD_DISTRIB)
let MULT_ASSOC = 
    prove
        ((parse_term @"!m n p. m * (n * p) = (m * n) * p"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; RIGHT_ADD_DISTRIB])
let MULT_AC = prove((parse_term @"(m * n = n * m) /\
    ((m * n) * p = m * (n * p)) /\
    (m * (n * p) = n * (m * p))"), MESON_TAC [MULT_ASSOC; MULT_SYM])
let MULT_EQ_0 = 
    prove
        ((parse_term @"!m n. (m * n = 0) <=> (m = 0) \/ (n = 0)"), 
         REPEAT INDUCT_TAC
         |> THEN <| REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES; NOT_SUC])

let EQ_MULT_LCANCEL = 
    prove
        ((parse_term @"!m n p. (m * n = m * p) <=> (m = 0) \/ (n = p)"), 
         INDUCT_TAC
         |> THEN <| REWRITE_TAC [MULT_CLAUSES; NOT_SUC]
         |> THEN <| REPEAT INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES
                                     ADD_CLAUSES
                                     GSYM NOT_SUC
                                     NOT_SUC]
         |> THEN <| ASM_REWRITE_TAC [SUC_INJ
                                     GSYM ADD_ASSOC
                                     EQ_ADD_LCANCEL])

let EQ_MULT_RCANCEL = 
    prove
        ((parse_term @"!m n p. (m * p = n * p) <=> (m = n) \/ (p = 0)"), 
         ONCE_REWRITE_TAC [MULT_SYM; DISJ_SYM]
         |> THEN <| MATCH_ACCEPT_TAC EQ_MULT_LCANCEL)
let MULT_2 = 
    prove
        ((parse_term @"!n. 2 * n = n + n"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [BIT0_THM; MULT_CLAUSES; RIGHT_ADD_DISTRIB])

let MULT_EQ_1 = 
    prove
        ((parse_term @"!m n. (m * n = 1) <=> (m = 1) /\ (n = 1)"), 
         INDUCT_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [MULT_CLAUSES
                                 ADD_CLAUSES
                                 BIT0_THM
                                 BIT1_THM
                                 GSYM NOT_SUC]
         |> THEN <| REWRITE_TAC [SUC_INJ; ADD_EQ_0; MULT_EQ_0]
         |> THEN <| CONV_TAC TAUT)

(* ------------------------------------------------------------------------- *)
(* Exponentiation.                                                           *)
(* ------------------------------------------------------------------------- *)
let EXP = new_recursive_definition num_RECURSION (parse_term @"(!m. m EXP 0 = 1) /\
   (!m n. m EXP (SUC n) = m * (m EXP n))")

let EXP_EQ_0 = 
    prove
        ((parse_term @"!m n. (m EXP n = 0) <=> (m = 0) /\ ~(n = 0)"), 
         REPEAT INDUCT_TAC
         |> THEN 
         <| ASM_REWRITE_TAC 
                [BIT1_THM; NOT_SUC; NOT_SUC; EXP; MULT_CLAUSES; ADD_CLAUSES; 
                 ADD_EQ_0])

let EXP_EQ_1 = 
    prove
        ((parse_term @"!x n. x EXP n = 1 <=> x = 1 \/ n = 0"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [EXP; MULT_EQ_1; NOT_SUC]
         |> THEN <| CONV_TAC TAUT)

let EXP_ZERO = 
    prove
        ((parse_term @"!n. 0 EXP n = if n = 0 |>THEN<| 1 else 0"), 
         GEN_TAC
         |> THEN <| COND_CASES_TAC
         |> THEN <| ASM_REWRITE_TAC [EXP_EQ_0; EXP_EQ_1])

let EXP_ADD = 
    prove
        ((parse_term @"!m n p. m EXP (n + p) = (m EXP n) * (m EXP p)"), 
         GEN_TAC
         |> THEN <| GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [EXP; ADD_CLAUSES; MULT_CLAUSES; MULT_AC])

let EXP_ONE = 
    prove
        ((parse_term @"!n. 1 EXP n = 1"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [EXP; MULT_CLAUSES])
let EXP_1 = 
    prove
        ((parse_term @"!n. n EXP 1 = n"), 
         REWRITE_TAC [ONE; EXP; MULT_CLAUSES; ADD_CLAUSES])
let EXP_2 = 
    prove
        ((parse_term @"!n. n EXP 2 = n * n"), 
         REWRITE_TAC 
             [BIT0_THM; BIT1_THM; EXP; EXP_ADD; MULT_CLAUSES; ADD_CLAUSES])
let MULT_EXP = 
    prove
        ((parse_term @"!p m n. (m * n) EXP p = m EXP p * n EXP p"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [EXP; MULT_CLAUSES; MULT_AC])

let EXP_MULT = 
    prove
        ((parse_term @"!m n p. m EXP (n * p) = (m EXP n) EXP p"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [EXP_ADD; EXP; MULT_CLAUSES]
         |> THENL <| [CONV_TAC(ONCE_DEPTH_CONV SYM_CONV)
                      |> THEN <| INDUCT_TAC
                      |> THEN <| ASM_REWRITE_TAC [EXP; MULT_CLAUSES]
                      REWRITE_TAC [MULT_EXP]
                      |> THEN <| MATCH_ACCEPT_TAC MULT_SYM])

(* ------------------------------------------------------------------------- *)
(* Define the orderings recursively too.                                     *)
(* ------------------------------------------------------------------------- *)
let LE = new_recursive_definition num_RECURSION (parse_term @"(!m. (m <= 0) <=> (m = 0)) /\
   (!m n. (m <= SUC n) <=> (m = SUC n) \/ (m <= n))")

let LT = new_recursive_definition num_RECURSION (parse_term @"(!m. (m < 0) <=> F) /\
   (!m n. (m < SUC n) <=> (m = n) \/ (m < n))")
let GE = new_definition(parse_term @"m >= n <=> n <= m")
let GT = new_definition(parse_term @"m > n <=> n < m")

(* ------------------------------------------------------------------------- *)
(* Maximum and minimum of natural numbers.                                   *)
(* ------------------------------------------------------------------------- *)
let MAX = 
    new_definition(parse_term @"!m n. MAX m n = if m <= n |>THEN<| n else m")

let MIN = 
    new_definition(parse_term @"!m n. MIN m n = if m <= n |>THEN<| m else n")

(* ------------------------------------------------------------------------- *)
(* Step cases.                                                               *)
(* ------------------------------------------------------------------------- *)
let LE_SUC_LT = 
    prove
        ((parse_term @"!m n. (SUC m <= n) <=> (m < n)"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [LE; LT; NOT_SUC; SUC_INJ])

let LT_SUC_LE = 
    prove
        ((parse_term @"!m n. (m < SUC n) <=> (m <= n)"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ONCE_REWRITE_TAC [LT; LE]
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| REWRITE_TAC [LT])

let LE_SUC = 
    prove
        ((parse_term @"!m n. (SUC m <= SUC n) <=> (m <= n)"), 
         REWRITE_TAC [LE_SUC_LT; LT_SUC_LE])
let LT_SUC = 
    prove
        ((parse_term @"!m n. (SUC m < SUC n) <=> (m < n)"), 
         REWRITE_TAC [LT_SUC_LE; LE_SUC_LT])

(* ------------------------------------------------------------------------- *)
(* Base cases.                                                               *)
(* ------------------------------------------------------------------------- *)
let LE_0 = prove((parse_term @"!n. 0 <= n"), INDUCT_TAC
                                            |> THEN <| ASM_REWRITE_TAC [LE])

let LT_0 = prove((parse_term @"!n. 0 < SUC n"), REWRITE_TAC [LT_SUC_LE; LE_0])

(* ------------------------------------------------------------------------- *)
(* Reflexivity.                                                              *)
(* ------------------------------------------------------------------------- *)
let LE_REFL = prove((parse_term @"!n. n <= n"), INDUCT_TAC
                                               |> THEN <| REWRITE_TAC [LE])

let LT_REFL = 
    prove((parse_term @"!n. ~(n < n)"), INDUCT_TAC
                                       |> THEN <| ASM_REWRITE_TAC [LT_SUC]
                                       |> THEN <| REWRITE_TAC [LT])

(* ------------------------------------------------------------------------- *)
(* Antisymmetry.                                                             *)
(* ------------------------------------------------------------------------- *)
let LE_ANTISYM = 
    prove
        ((parse_term @"!m n. (m <= n /\ n <= m) <=> (m = n)"), 
         REPEAT INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [LE_SUC; SUC_INJ]
         |> THEN <| REWRITE_TAC [LE
                                 NOT_SUC
                                 GSYM NOT_SUC])

let LT_ANTISYM = 
    prove((parse_term @"!m n. ~(m < n /\ n < m)"), REPEAT INDUCT_TAC
                                                  |> THEN 
                                                  <| ASM_REWRITE_TAC [LT_SUC]
                                                  |> THEN <| REWRITE_TAC [LT])

let LET_ANTISYM = 
    prove
        ((parse_term @"!m n. ~(m <= n /\ n < m)"), 
         REPEAT INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [LE_SUC; LT_SUC]
         |> THEN <| REWRITE_TAC [LE; LT; NOT_SUC])

let LTE_ANTISYM = 
    prove
        ((parse_term @"!m n. ~(m < n /\ n <= m)"), 
         ONCE_REWRITE_TAC [CONJ_SYM]
         |> THEN <| REWRITE_TAC [LET_ANTISYM])

(* ------------------------------------------------------------------------- *)
(* Transitivity.                                                             *)
(* ------------------------------------------------------------------------- *)
let LE_TRANS = 
    prove
        ((parse_term @"!m n p. m <= n /\ n <= p ==> m <= p"), 
         REPEAT INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [LE_SUC; LE_0]
         |> THEN <| REWRITE_TAC [LE; NOT_SUC])

let LT_TRANS = 
    prove
        ((parse_term @"!m n p. m < n /\ n < p ==> m < p"), 
         REPEAT INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [LT_SUC; LT_0]
         |> THEN <| REWRITE_TAC [LT; NOT_SUC])

let LET_TRANS = 
    prove
        ((parse_term @"!m n p. m <= n /\ n < p ==> m < p"), 
         REPEAT INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [LE_SUC; LT_SUC; LT_0]
         |> THEN <| REWRITE_TAC [LT; LE; NOT_SUC])

let LTE_TRANS = 
    prove
        ((parse_term @"!m n p. m < n /\ n <= p ==> m < p"), 
         REPEAT INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [LE_SUC; LT_SUC; LT_0]
         |> THEN <| REWRITE_TAC [LT; LE; NOT_SUC])

(* ------------------------------------------------------------------------- *)
(* Totality.                                                                 *)
(* ------------------------------------------------------------------------- *)
let LE_CASES = 
    prove
        ((parse_term @"!m n. m <= n \/ n <= m"), 
         REPEAT INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [LE_0; LE_SUC])

let LT_CASES = 
    prove
        ((parse_term @"!m n. (m < n) \/ (n < m) \/ (m = n)"), 
         REPEAT INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [LT_SUC; SUC_INJ]
         |> THEN <| REWRITE_TAC [LT
                                 NOT_SUC
                                 GSYM NOT_SUC]
         |> THEN <| W(W(curry SPEC_TAC) << hd << frees << snd)
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [LT_0])

let LET_CASES = 
    prove
        ((parse_term @"!m n. m <= n \/ n < m"), 
         REPEAT INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [LE_SUC_LT; LT_SUC_LE; LE_0])
let LTE_CASES = 
    prove
        ((parse_term @"!m n. m < n \/ n <= m"), 
         ONCE_REWRITE_TAC [DISJ_SYM]
         |> THEN <| MATCH_ACCEPT_TAC LET_CASES)

(* ------------------------------------------------------------------------- *)
(* Relationship between orderings.                                           *)
(* ------------------------------------------------------------------------- *)
let LE_LT = 
    prove
        ((parse_term @"!m n. (m <= n) <=> (m < n) \/ (m = n)"), 
         REPEAT INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [LE_SUC; LT_SUC; SUC_INJ; LE_0; LT_0]
         |> THEN <| REWRITE_TAC [LE; LT])

let LT_LE = 
    prove
        ((parse_term @"!m n. (m < n) <=> (m <= n) /\ ~(m = n)"), 
         REWRITE_TAC [LE_LT]
         |> THEN <| REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THENL <| [DISCH_TAC
                      |> THEN <| ASM_REWRITE_TAC []
                      |> THEN <| DISCH_THEN SUBST_ALL_TAC
                      |> THEN <| POP_ASSUM MP_TAC
                      |> THEN <| REWRITE_TAC [LT_REFL]
                      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)
                      |> THEN <| ASM_REWRITE_TAC []])

let NOT_LE = 
    prove
        ((parse_term @"!m n. ~(m <= n) <=> (n < m)"), 
         REPEAT INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [LE_SUC; LT_SUC]
         |> THEN <| REWRITE_TAC [LE
                                 LT
                                 NOT_SUC
                                 GSYM NOT_SUC
                                 LE_0]
         |> THEN <| W(W(curry SPEC_TAC) << hd << frees << snd)
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [LT_0])

let NOT_LT = 
    prove
        ((parse_term @"!m n. ~(m < n) <=> n <= m"), REPEAT INDUCT_TAC
                                                   |> THEN 
                                                   <| ASM_REWRITE_TAC 
                                                          [LE_SUC; LT_SUC]
                                                   |> THEN <| REWRITE_TAC [LE
                                                                           LT
                                                                           NOT_SUC
                                                                           GSYM 
                                                                               NOT_SUC
                                                                           LE_0]
                                                   |> THEN 
                                                   <| W
                                                          (W(curry SPEC_TAC) 
                                                           << hd << frees << snd)
                                                   |> THEN <| INDUCT_TAC
                                                   |> THEN <| REWRITE_TAC [LT_0])

let LT_IMP_LE = 
    prove((parse_term @"!m n. m < n ==> m <= n"), REWRITE_TAC [LT_LE]
                                                 |> THEN <| REPEAT STRIP_TAC
                                                 |> THEN <| ASM_REWRITE_TAC [])

let EQ_IMP_LE = 
    prove
        ((parse_term @"!m n. (m = n) ==> m <= n"), 
         REPEAT STRIP_TAC
         |> THEN <| ASM_REWRITE_TAC [LE_REFL])

(* ------------------------------------------------------------------------- *)
(* Often useful to shuffle between different versions of "0 < n".            *)
(* ------------------------------------------------------------------------- *)
let LT_NZ = 
    prove((parse_term @"!n. 0 < n <=> ~(n = 0)"), INDUCT_TAC
                                                 |> THEN 
                                                 <| ASM_REWRITE_TAC 
                                                        [NOT_SUC; LT; EQ_SYM_EQ]
                                                 |> THEN <| CONV_TAC TAUT)

let LE_1 = 
    prove((parse_term @"(!n. ~(n = 0) ==> 0 < n) /\
    (!n. ~(n = 0) ==> 1 <= n) /\
    (!n. 0 < n ==> ~(n = 0)) /\
    (!n. 0 < n ==> 1 <= n) /\
    (!n. 1 <= n ==> 0 < n) /\
    (!n. 1 <= n ==> ~(n = 0))"),
     REWRITE_TAC[LT_NZ; GSYM NOT_LT; ONE; LT])

(* ------------------------------------------------------------------------- *)
(* Relate the orderings to arithmetic operations.                            *)
(* ------------------------------------------------------------------------- *)
let LE_EXISTS = 
    prove
        ((parse_term @"!m n. (m <= n) <=> (?d. n = m + d)"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [LE]
         |> THENL <| [REWRITE_TAC 
                          [CONV_RULE (LAND_CONV SYM_CONV) (SPEC_ALL ADD_EQ_0)]
                      |> THEN <| REWRITE_TAC [RIGHT_EXISTS_AND_THM; EXISTS_REFL]
                      EQ_TAC
                      |> THENL <| [DISCH_THEN
                                       (DISJ_CASES_THEN2 SUBST1_TAC MP_TAC)
                                   |> THENL 
                                   <| [EXISTS_TAC(parse_term @"0")
                                       |> THEN <| REWRITE_TAC [ADD_CLAUSES]
                                       DISCH_THEN
                                           (X_CHOOSE_THEN (parse_term @"d:num") 
                                                SUBST1_TAC)
                                       |> THEN <| EXISTS_TAC(parse_term @"SUC d")
                                       |> THEN <| REWRITE_TAC [ADD_CLAUSES]]
                                   ONCE_REWRITE_TAC [LEFT_IMP_EXISTS_THM]
                                   |> THEN <| INDUCT_TAC
                                   |> THEN <| REWRITE_TAC [ADD_CLAUSES; SUC_INJ]
                                   |> THEN <| DISCH_THEN SUBST1_TAC
                                   |> THEN <| REWRITE_TAC []
                                   |> THEN <| DISJ2_TAC
                                   |> THEN <| REWRITE_TAC [EQ_ADD_LCANCEL
                                                           GSYM EXISTS_REFL]]])

let LT_EXISTS = 
    prove
        ((parse_term @"!m n. (m < n) <=> (?d. n = m + SUC d)"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [LT
                                 ADD_CLAUSES
                                 GSYM NOT_SUC]
         |> THEN <| ASM_REWRITE_TAC [SUC_INJ]
         |> THEN <| EQ_TAC
         |> THENL <| [DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC)
                      |> THENL <| [EXISTS_TAC(parse_term @"0")
                                   |> THEN <| REWRITE_TAC [ADD_CLAUSES]
                                   DISCH_THEN
                                       (X_CHOOSE_THEN (parse_term @"d:num") 
                                            SUBST1_TAC)
                                   |> THEN <| EXISTS_TAC(parse_term @"SUC d")
                                   |> THEN <| REWRITE_TAC [ADD_CLAUSES]]
                      ONCE_REWRITE_TAC [LEFT_IMP_EXISTS_THM]
                      |> THEN <| INDUCT_TAC
                      |> THEN <| REWRITE_TAC [ADD_CLAUSES; SUC_INJ]
                      |> THEN <| DISCH_THEN SUBST1_TAC
                      |> THEN <| REWRITE_TAC []
                      |> THEN <| DISJ2_TAC
                      |> THEN <| REWRITE_TAC [SUC_INJ
                                              EQ_ADD_LCANCEL
                                              GSYM EXISTS_REFL]])

(* ------------------------------------------------------------------------- *)
(* Interaction with addition.                                                *)
(* ------------------------------------------------------------------------- *)
let LE_ADD = 
    prove
        ((parse_term @"!m n. m <= m + n"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [LE; ADD_CLAUSES; LE_REFL])

let LE_ADDR = 
    prove((parse_term @"!m n. n <= m + n"), ONCE_REWRITE_TAC [ADD_SYM]
                                           |> THEN <| MATCH_ACCEPT_TAC LE_ADD)
let LT_ADD = 
    prove
        ((parse_term @"!m n. (m < m + n) <=> (0 < n)"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [ADD_CLAUSES; LT_SUC])
let LT_ADDR = 
    prove
        ((parse_term @"!m n. (n < m + n) <=> (0 < m)"), 
         ONCE_REWRITE_TAC [ADD_SYM]
         |> THEN <| MATCH_ACCEPT_TAC LT_ADD)

let LE_ADD_LCANCEL = 
    prove
        ((parse_term @"!m n p. (m + n) <= (m + p) <=> n <= p"), 
         REWRITE_TAC [LE_EXISTS
                      GSYM ADD_ASSOC
                      EQ_ADD_LCANCEL])

let LE_ADD_RCANCEL = 
    prove
        ((parse_term @"!m n p. (m + p) <= (n + p) <=> (m <= n)"), 
         ONCE_REWRITE_TAC [ADD_SYM]
         |> THEN <| MATCH_ACCEPT_TAC LE_ADD_LCANCEL)

let LT_ADD_LCANCEL = 
    prove
        ((parse_term @"!m n p. (m + n) < (m + p) <=> n < p"), 
         REWRITE_TAC [LT_EXISTS
                      GSYM ADD_ASSOC
                      EQ_ADD_LCANCEL; SUC_INJ])

let LT_ADD_RCANCEL = 
    prove
        ((parse_term @"!m n p. (m + p) < (n + p) <=> (m < n)"), 
         ONCE_REWRITE_TAC [ADD_SYM]
         |> THEN <| MATCH_ACCEPT_TAC LT_ADD_LCANCEL)

let LE_ADD2 = 
    prove
        ((parse_term @"!m n p q. m <= p /\ n <= q ==> m + n <= p + q"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [LE_EXISTS]
         |> THEN 
         <| DISCH_THEN
                (CONJUNCTS_THEN2 (X_CHOOSE_TAC(parse_term @"a:num")) 
                     (X_CHOOSE_TAC(parse_term @"b:num")))
         |> THEN <| EXISTS_TAC(parse_term @"a + b")
         |> THEN <| ASM_REWRITE_TAC [ADD_AC])

let LET_ADD2 = 
    prove
        ((parse_term @"!m n p q. m <= p /\ n < q ==> m + n < p + q"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [LE_EXISTS; LT_EXISTS]
         |> THEN 
         <| DISCH_THEN
                (CONJUNCTS_THEN2 (X_CHOOSE_TAC(parse_term @"a:num")) 
                     (X_CHOOSE_TAC(parse_term @"b:num")))
         |> THEN <| EXISTS_TAC(parse_term @"a + b")
         |> THEN <| ASM_REWRITE_TAC [SUC_INJ; ADD_CLAUSES; ADD_AC])

let LTE_ADD2 = 
    prove
        ((parse_term @"!m n p q. m < p /\ n <= q ==> m + n < p + q"), 
         ONCE_REWRITE_TAC [ADD_SYM; CONJ_SYM]
         |> THEN <| MATCH_ACCEPT_TAC LET_ADD2)

let LT_ADD2 = 
    prove
        ((parse_term @"!m n p q. m < p /\ n < q ==> m + n < p + q"), 
         REPEAT STRIP_TAC
         |> THEN <| MATCH_MP_TAC LTE_ADD2
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| MATCH_MP_TAC LT_IMP_LE
         |> THEN <| ASM_REWRITE_TAC [])

(* ------------------------------------------------------------------------- *)
(* And multiplication.                                                       *)
(* ------------------------------------------------------------------------- *)
let LT_MULT = 
    prove
        ((parse_term @"!m n. (0 < m * n) <=> (0 < m) /\ (0 < n)"), 
         REPEAT INDUCT_TAC
         |> THEN <| REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES; LT_0])

let LE_MULT2 = 
    prove
        ((parse_term @"!m n p q. m <= n /\ p <= q ==> m * p <= n * q"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [LE_EXISTS]
         |> THEN 
         <| DISCH_THEN
                (CONJUNCTS_THEN2 (X_CHOOSE_TAC(parse_term @"a:num")) 
                     (X_CHOOSE_TAC(parse_term @"b:num")))
         |> THEN <| EXISTS_TAC(parse_term @"a * p + m * b + a * b")
         |> THEN <| ASM_REWRITE_TAC [LEFT_ADD_DISTRIB]
         |> THEN <| REWRITE_TAC [LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; ADD_ASSOC])

let LT_LMULT = 
    prove
        ((parse_term @"!m n p. ~(m = 0) /\ n < p ==> m * n < m * p"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [LT_LE]
         |> THEN <| STRIP_TAC
         |> THEN <| CONJ_TAC
         |> THENL <| [MATCH_MP_TAC LE_MULT2
                      |> THEN <| ASM_REWRITE_TAC [LE_REFL]
                      ASM_REWRITE_TAC [EQ_MULT_LCANCEL]])

let LE_MULT_LCANCEL = 
    prove
        ((parse_term @"!m n p. (m * n) <= (m * p) <=> (m = 0) \/ n <= p"), 
         REPEAT INDUCT_TAC
         |> THEN 
         <| ASM_REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES; LE_REFL; LE_0; NOT_SUC]
         |> THEN <| REWRITE_TAC [LE_SUC]
         |> THEN <| REWRITE_TAC [LE
                                 LE_ADD_LCANCEL
                                 GSYM ADD_ASSOC]
         |> THEN <| ASM_REWRITE_TAC [GSYM(el 4 (CONJUNCTS MULT_CLAUSES))
                                     NOT_SUC])

let LE_MULT_RCANCEL = 
    prove
        ((parse_term @"!m n p. (m * p) <= (n * p) <=> (m <= n) \/ (p = 0)"), 
         ONCE_REWRITE_TAC [MULT_SYM; DISJ_SYM]
         |> THEN <| MATCH_ACCEPT_TAC LE_MULT_LCANCEL)

let LT_MULT_LCANCEL = 
    prove
        ((parse_term @"!m n p. (m * n) < (m * p) <=> ~(m = 0) /\ n < p"), 
         REPEAT INDUCT_TAC
         |> THEN 
         <| ASM_REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES; LT_REFL; LT_0; NOT_SUC]
         |> THEN <| REWRITE_TAC [LT_SUC]
         |> THEN <| REWRITE_TAC [LT
                                 LT_ADD_LCANCEL
                                 GSYM ADD_ASSOC]
         |> THEN <| ASM_REWRITE_TAC [GSYM(el 4 (CONJUNCTS MULT_CLAUSES))
                                     NOT_SUC])

let LT_MULT_RCANCEL = 
    prove
        ((parse_term @"!m n p. (m * p) < (n * p) <=> (m < n) /\ ~(p = 0)"), 
         ONCE_REWRITE_TAC [MULT_SYM; CONJ_SYM]
         |> THEN <| MATCH_ACCEPT_TAC LT_MULT_LCANCEL)

let LT_MULT2 = 
    prove
        ((parse_term @"!m n p q. m < n /\ p < q ==> m * p < n * q"), 
         REPEAT STRIP_TAC
         |> THEN <| MATCH_MP_TAC LET_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"n * p")
         |> THEN <| ASM_SIMP_TAC [LE_MULT_RCANCEL; LT_IMP_LE; LT_MULT_LCANCEL]
         |> THEN <| UNDISCH_TAC(parse_term @"m < n")
         |> THEN <| CONV_TAC CONTRAPOS_CONV
         |> THEN <| SIMP_TAC [LT])

let LE_SQUARE_REFL = 
    prove
        ((parse_term @"!n. n <= n * n"), 
         INDUCT_TAC
         |> THEN <| REWRITE_TAC [MULT_CLAUSES; LE_0; LE_ADDR])

(* ------------------------------------------------------------------------- *)
(* Useful "without loss of generality" lemmas.                               *)
(* ------------------------------------------------------------------------- *)
let WLOG_LE = 
    prove
        ((parse_term 
              "(!m n. P m n <=> P n m) /\ (!m n. m <= n ==> P m n) ==> !m n. P m n"), 
         MESON_TAC [LE_CASES])

let WLOG_LT = 
 prove
  ((parse_term @"(!m. P m m) /\ (!m n. P m n <=> P n m) /\ (!m n. m < n ==> P m n)
    ==> !m y. P m y"),
   MESON_TAC[LT_CASES])

(* ------------------------------------------------------------------------- *)
(* Existence of least and greatest elements of (finite) set.                 *)
(* ------------------------------------------------------------------------- *)
let num_WF = 
    prove
        ((parse_term @"!P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n"), 
         GEN_TAC
         |> THEN 
         <| MP_TAC(SPEC (parse_term @"\n. !m. m < n ==> P m") num_INDUCTION)
         |> THEN <| REWRITE_TAC [LT; BETA_THM]
         |> THEN <| MESON_TAC [LT])

let num_WOP = 
    prove
        ((parse_term @"!P. (?n. P n) <=> (?n. P(n) /\ !m. m < n ==> ~P(m))"), 
         GEN_TAC
         |> THEN <| EQ_TAC
         |> THENL <| [ALL_TAC
                      MESON_TAC []]
         |> THEN <| CONV_TAC CONTRAPOS_CONV
         |> THEN <| REWRITE_TAC [NOT_EXISTS_THM]
         |> THEN <| DISCH_TAC
         |> THEN <| MATCH_MP_TAC num_WF
         |> THEN <| ASM_MESON_TAC [])

let num_MAX = 
  prove((parse_term @"!P. (?x. P x) /\ (?M. !x. P x ==> x <= M) <=>
        ?m. P m /\ (!x. P x ==> x <= m)"),
    GEN_TAC
       |> THEN <| EQ_TAC
       |> THENL <| [DISCH_THEN
                        (CONJUNCTS_THEN2 (X_CHOOSE_TAC(parse_term @"a:num")) 
                             MP_TAC)
                    |> THEN 
                    <| DISCH_THEN
                           (X_CHOOSE_THEN (parse_term @"m:num") MP_TAC 
                            << ONCE_REWRITE_RULE [num_WOP])
                    |> THEN <| DISCH_THEN(fun th -> EXISTS_TAC
                                                        (parse_term @"m:num")
                                                    |> THEN <| MP_TAC th)
                    |> THEN <| REWRITE_TAC 
                           [TAUT (parse_term @"(a /\ b ==> c /\ a) <=> (a /\ b ==> c)")]
                    |> THEN <| SPEC_TAC((parse_term @"m:num"), (parse_term @"m:num"))
                    |> THEN <| INDUCT_TAC
                    |> THENL <| [REWRITE_TAC [LE; LT]
                                 |> THEN 
                                 <| DISCH_THEN(IMP_RES_THEN SUBST_ALL_TAC)
                                 |> THEN <| POP_ASSUM ACCEPT_TAC
                                 DISCH_THEN
                                     (CONJUNCTS_THEN2 ASSUME_TAC 
                                          (MP_TAC << SPEC(parse_term @"m:num")))
                                 |> THEN <| REWRITE_TAC [LT]
                                 |> THEN <| CONV_TAC CONTRAPOS_CONV
                                 |> THEN <| DISCH_TAC
                                 |> THEN <| REWRITE_TAC []
                                 |> THEN <| X_GEN_TAC(parse_term @"p:num")
                                 |> THEN <| FIRST_ASSUM (MP_TAC << SPEC(parse_term @"p:num"))
                                 |> THEN <| REWRITE_TAC [LE]
                                 |> THEN <| ASM_CASES_TAC(parse_term @"p = SUC m")
                                 |> THEN <| ASM_REWRITE_TAC []]
                    REPEAT STRIP_TAC
                    |> THEN <| EXISTS_TAC(parse_term @"m:num")
                    |> THEN <| ASM_REWRITE_TAC []])

(* ------------------------------------------------------------------------- *)
(* Oddness and evenness (recursively rather than inductively!)               *)
(* ------------------------------------------------------------------------- *)
let EVEN = new_recursive_definition num_RECURSION (parse_term @"(EVEN 0 <=> T) /\
    (!n. EVEN (SUC n) <=> ~(EVEN n))")

let ODD = new_recursive_definition num_RECURSION (parse_term @"(ODD 0 <=> F) /\
    (!n. ODD (SUC n) <=> ~(ODD n))")
let NOT_EVEN = 
    prove
        ((parse_term @"!n. ~(EVEN n) <=> ODD n"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [EVEN; ODD])
let NOT_ODD = 
    prove
        ((parse_term @"!n. ~(ODD n) <=> EVEN n"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [EVEN; ODD])

let EVEN_OR_ODD = 
    prove((parse_term @"!n. EVEN n \/ ODD n"), INDUCT_TAC
                                              |> THEN 
                                              <| REWRITE_TAC 
                                                     [EVEN; ODD; NOT_EVEN; 
                                                      NOT_ODD]
                                              |> THEN 
                                              <| ONCE_REWRITE_TAC [DISJ_SYM]
                                              |> THEN <| ASM_REWRITE_TAC [])

let EVEN_AND_ODD = 
    prove
        ((parse_term @"!n. ~(EVEN n /\ ODD n)"), 
         REWRITE_TAC [GSYM NOT_EVEN
                      ITAUT(parse_term @"~(p /\ ~p)")])

let EVEN_ADD = 
    prove
        ((parse_term @"!m n. EVEN(m + n) <=> (EVEN m <=> EVEN n)"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [EVEN; ADD_CLAUSES]
         |> THEN <| X_GEN_TAC(parse_term @"p:num")
         |> THEN 
         <| DISJ_CASES_THEN MP_TAC (SPEC (parse_term @"n:num") EVEN_OR_ODD)
         |> THEN 
         <| DISJ_CASES_THEN MP_TAC (SPEC (parse_term @"p:num") EVEN_OR_ODD)
         |> THEN <| REWRITE_TAC [GSYM NOT_EVEN]
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC [])

let EVEN_MULT = 
    prove
        ((parse_term @"!m n. EVEN(m * n) <=> EVEN(m) \/ EVEN(n)"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; EVEN_ADD; EVEN]
         |> THEN <| X_GEN_TAC(parse_term @"p:num")
         |> THEN 
         <| DISJ_CASES_THEN MP_TAC (SPEC (parse_term @"n:num") EVEN_OR_ODD)
         |> THEN 
         <| DISJ_CASES_THEN MP_TAC (SPEC (parse_term @"p:num") EVEN_OR_ODD)
         |> THEN <| REWRITE_TAC [GSYM NOT_EVEN]
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC [])

let EVEN_EXP = 
    prove
        ((parse_term @"!m n. EVEN(m EXP n) <=> EVEN(m) /\ ~(n = 0)"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [EVEN; EXP; ONE; EVEN_MULT; NOT_SUC]
         |> THEN <| CONV_TAC ITAUT)

let ODD_ADD = 
    prove
        ((parse_term @"!m n. ODD(m + n) <=> ~(ODD m <=> ODD n)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [GSYM NOT_EVEN
                                 EVEN_ADD]
         |> THEN <| CONV_TAC ITAUT)

let ODD_MULT = 
    prove
        ((parse_term @"!m n. ODD(m * n) <=> ODD(m) /\ ODD(n)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [GSYM NOT_EVEN
                                 EVEN_MULT]
         |> THEN <| CONV_TAC ITAUT)

let ODD_EXP = 
    prove
        ((parse_term @"!m n. ODD(m EXP n) <=> ODD(m) \/ (n = 0)"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [ODD; EXP; ONE; ODD_MULT; NOT_SUC]
         |> THEN <| CONV_TAC ITAUT)

let EVEN_DOUBLE = 
    prove
        ((parse_term @"!n. EVEN(2 * n)"), GEN_TAC
                                         |> THEN <| REWRITE_TAC [EVEN_MULT]
                                         |> THEN <| DISJ1_TAC
                                         |> THEN 
                                         <| PURE_REWRITE_TAC 
                                                [BIT0_THM; BIT1_THM]
                                         |> THEN <| REWRITE_TAC [EVEN; EVEN_ADD])

let ODD_DOUBLE = 
    prove
        ((parse_term @"!n. ODD(SUC(2 * n))"), 
         REWRITE_TAC [ODD]
         |> THEN <| REWRITE_TAC [NOT_ODD; EVEN_DOUBLE])

let EVEN_EXISTS_LEMMA = 
    prove
        ((parse_term @"!n. (EVEN n ==> ?m. n = 2 * m) /\
        (~EVEN n ==> ?m. n = SUC(2 * m))"), 
         INDUCT_TAC
         |> THEN <| REWRITE_TAC [EVEN]
         |> THENL <| [EXISTS_TAC(parse_term @"0")
                      |> THEN <| REWRITE_TAC [MULT_CLAUSES]
                      POP_ASSUM STRIP_ASSUME_TAC
                      |> THEN <| CONJ_TAC
                      |> THEN 
                      <| DISCH_THEN
                             (ANTE_RES_THEN(X_CHOOSE_TAC(parse_term @"m:num")))
                      |> THENL <| [EXISTS_TAC(parse_term @"SUC m")
                                   |> THEN <| ASM_REWRITE_TAC []
                                   |> THEN <| REWRITE_TAC [MULT_2]
                                   |> THEN <| REWRITE_TAC [ADD_CLAUSES]
                                   EXISTS_TAC(parse_term @"m:num")
                                   |> THEN <| ASM_REWRITE_TAC []]])

let EVEN_EXISTS = 
    prove
        ((parse_term @"!n. EVEN n <=> ?m. n = 2 * m"), 
         GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THENL <| [MATCH_MP_TAC(CONJUNCT1(SPEC_ALL EVEN_EXISTS_LEMMA))
                      |> THEN <| ASM_REWRITE_TAC []
                      POP_ASSUM(CHOOSE_THEN SUBST1_TAC)
                      |> THEN <| REWRITE_TAC [EVEN_DOUBLE]])

let ODD_EXISTS = 
    prove
        ((parse_term @"!n. ODD n <=> ?m. n = SUC(2 * m)"), 
         GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THENL <| [MATCH_MP_TAC(CONJUNCT2(SPEC_ALL EVEN_EXISTS_LEMMA))
                      |> THEN <| ASM_REWRITE_TAC [NOT_EVEN]
                      POP_ASSUM(CHOOSE_THEN SUBST1_TAC)
                      |> THEN <| REWRITE_TAC [ODD_DOUBLE]])

let EVEN_ODD_DECOMPOSITION = 
    prove
        ((parse_term @"!n. (?k m. ODD m /\ (n = 2 EXP k * m)) <=> ~(n = 0)"), 
         MATCH_MP_TAC num_WF
         |> THEN <| X_GEN_TAC(parse_term @"n:num")
         |> THEN <| DISCH_TAC
         |> THEN <| DISJ_CASES_TAC(SPEC (parse_term @"n:num") EVEN_OR_ODD)
         |> THENL <| [ALL_TAC
                      ASM_MESON_TAC [ODD; EXP; MULT_CLAUSES]]
         |> THEN <| FIRST_X_ASSUM(MP_TAC << GEN_REWRITE_RULE I [EVEN_EXISTS])
         |> THEN <| DISCH_THEN(X_CHOOSE_THEN (parse_term @"m:num") SUBST_ALL_TAC)
         |> THEN <| FIRST_X_ASSUM(MP_TAC << SPEC(parse_term @"m:num"))
         |> THEN <| ASM_CASES_TAC(parse_term @"m = 0")
         |> THEN <| ASM_REWRITE_TAC [MULT_EQ_0]
         |> THENL <| [REWRITE_TAC [MULT_CLAUSES; LT]
                      |> THEN <| CONV_TAC(ONCE_DEPTH_CONV SYM_CONV)
                      |> THEN <| REWRITE_TAC [EXP_EQ_0; MULT_EQ_0; TWO; NOT_SUC]
                      |> THEN <| MESON_TAC [ODD]
                      ALL_TAC]
         |> THEN <| ANTS_TAC
         |> THENL <| [GEN_REWRITE_TAC LAND_CONV 
                          [GSYM(el 2 (CONJUNCTS MULT_CLAUSES))]
                      |> THEN <| ASM_REWRITE_TAC [LT_MULT_RCANCEL; TWO; LT]
                      ALL_TAC]
         |> THEN <| REWRITE_TAC [TWO; NOT_SUC]
         |> THEN <| REWRITE_TAC [GSYM TWO]
         |> THEN <| ONCE_REWRITE_TAC [SWAP_EXISTS_THM]
         |> THEN <| MATCH_MP_TAC MONO_EXISTS
         |> THEN <| X_GEN_TAC(parse_term @"p:num")
         |> THEN 
         <| DISCH_THEN(X_CHOOSE_THEN (parse_term @"k:num") STRIP_ASSUME_TAC)
         |> THEN <| EXISTS_TAC(parse_term @"SUC k")
         |> THEN <| ASM_REWRITE_TAC [EXP; MULT_ASSOC])

(* ------------------------------------------------------------------------- *)
(* Cutoff subtraction, also defined recursively. (Not the HOL88 defn.)       *)
(* ------------------------------------------------------------------------- *)
let SUB = new_recursive_definition num_RECURSION (parse_term @"(!m. m - 0 = m) /\
   (!m n. m - (SUC n) = PRE(m - n))")

let SUB_0 = 
    prove
        ((parse_term @"!m. (0 - m = 0) /\ (m - 0 = m)"), 
         REWRITE_TAC [SUB]
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [SUB; PRE])

let SUB_PRESUC = 
    prove
        ((parse_term @"!m n. PRE(SUC m - n) = m - n"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [SUB; PRE])

let SUB_SUC = 
    prove
        ((parse_term @"!m n. SUC m - SUC n = m - n"), 
         REPEAT INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [SUB; PRE; SUB_PRESUC])
let SUB_REFL = 
    prove
        ((parse_term @"!n. n - n = 0"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [SUB_SUC; SUB_0])

let ADD_SUB = 
    prove
        ((parse_term @"!m n. (m + n) - n = m"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [ADD_CLAUSES; SUB_SUC; SUB_0])

let ADD_SUB2 = 
    prove
        ((parse_term @"!m n. (m + n) - m = n"), 
         ONCE_REWRITE_TAC [ADD_SYM]
         |> THEN <| MATCH_ACCEPT_TAC ADD_SUB)

let SUB_EQ_0 = 
    prove
        ((parse_term @"!m n. (m - n = 0) <=> m <= n"), 
         REPEAT INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [SUB_SUC; LE_SUC; SUB_0]
         |> THEN <| REWRITE_TAC [LE; LE_0])

let ADD_SUBR2 = 
    prove((parse_term @"!m n. m - (m + n) = 0"), REWRITE_TAC [SUB_EQ_0; LE_ADD])
let ADD_SUBR = 
    prove
        ((parse_term @"!m n. n - (m + n) = 0"), 
         ONCE_REWRITE_TAC [ADD_SYM]
         |> THEN <| MATCH_ACCEPT_TAC ADD_SUBR2)

let SUB_ADD = 
    prove
        ((parse_term @"!m n. n <= m ==> ((m - n) + n = m)"), 
         REWRITE_TAC [LE_EXISTS]
         |> THEN <| REPEAT STRIP_TAC
         |> THEN <| ASM_REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] ADD_SUB]
         |> THEN <| MATCH_ACCEPT_TAC ADD_SYM)

let SUB_ADD_LCANCEL = 
    prove
        ((parse_term @"!m n p. (m + n) - (m + p) = n - p"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [ADD_CLAUSES; SUB_0; SUB_SUC])
let SUB_ADD_RCANCEL = 
    prove
        ((parse_term @"!m n p. (m + p) - (n + p) = m - n"), 
         ONCE_REWRITE_TAC [ADD_SYM]
         |> THEN <| MATCH_ACCEPT_TAC SUB_ADD_LCANCEL)

let LEFT_SUB_DISTRIB = 
    prove
        ((parse_term @"!m n p. m * (n - p) = m * n - m * p"), 
         REPEAT GEN_TAC
         |> THEN <| CONV_TAC SYM_CONV
         |> THEN <| DISJ_CASES_TAC(SPECL [(parse_term @"n:num")
                                          (parse_term @"p:num")] LE_CASES)
         |> THENL 
         <| [FIRST_ASSUM
                 (fun th -> REWRITE_TAC [REWRITE_RULE [GSYM SUB_EQ_0] th])
             |> THEN 
             <| ASM_REWRITE_TAC [MULT_CLAUSES; SUB_EQ_0; LE_MULT_LCANCEL]
             POP_ASSUM(CHOOSE_THEN SUBST1_TAC << REWRITE_RULE [LE_EXISTS])
             |> THEN <| REWRITE_TAC [LEFT_ADD_DISTRIB]
             |> THEN <| REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] ADD_SUB]])

let RIGHT_SUB_DISTRIB = 
    prove
        ((parse_term @"!m n p. (m - n) * p = m * p - n * p"), 
         ONCE_REWRITE_TAC [MULT_SYM]
         |> THEN <| MATCH_ACCEPT_TAC LEFT_SUB_DISTRIB)
let SUC_SUB1 = 
    prove((parse_term @"!n. SUC n - 1 = n"), REWRITE_TAC [ONE; SUB_SUC; SUB_0])

let EVEN_SUB = 
    prove
        ((parse_term @"!m n. EVEN(m - n) <=> m <= n \/ (EVEN(m) <=> EVEN(n))"), 
         REPEAT GEN_TAC
         |> THEN <| ASM_CASES_TAC(parse_term @"m <= n:num")
         |> THENL <| [ASM_MESON_TAC [SUB_EQ_0; EVEN]
                      ALL_TAC]
         |> THEN <| DISJ_CASES_TAC(SPECL [(parse_term @"m:num")
                                          (parse_term @"n:num")] LE_CASES)
         |> THEN <| ASM_SIMP_TAC []
         |> THEN 
         <| FIRST_ASSUM
                (MP_TAC << AP_TERM(parse_term @"EVEN") << MATCH_MP SUB_ADD)
         |> THEN <| ASM_MESON_TAC [EVEN_ADD])

let ODD_SUB = 
    prove
        ((parse_term @"!m n. ODD(m - n) <=> n < m /\ ~(ODD m <=> ODD n)"), 
         REWRITE_TAC [GSYM NOT_EVEN
                      EVEN_SUB; DE_MORGAN_THM; NOT_LE]
         |> THEN <| CONV_TAC TAUT)

(* ------------------------------------------------------------------------- *)
(* The factorial function.                                                   *)
(* ------------------------------------------------------------------------- *)
let FACT = new_recursive_definition num_RECURSION (parse_term @"(FACT 0 = 1) /\
    (!n. FACT (SUC n) = (SUC n) * FACT(n))")

let FACT_LT = 
    prove((parse_term @"!n. 0 < FACT n"), INDUCT_TAC
                                         |> THEN 
                                         <| ASM_REWRITE_TAC [FACT; LT_MULT]
                                         |> THEN <| REWRITE_TAC [ONE; LT_0])

let FACT_LE = 
    prove((parse_term @"!n. 1 <= FACT n"), REWRITE_TAC [ONE; LE_SUC_LT; FACT_LT])

let FACT_NZ = 
    prove((parse_term @"!n. ~(FACT n = 0)"), REWRITE_TAC [GSYM LT_NZ
                                                          FACT_LT])

let FACT_MONO = 
    prove
        ((parse_term @"!m n. m <= n ==> FACT m <= FACT n"), 
         REPEAT GEN_TAC
         |> THEN 
         <| DISCH_THEN
                (X_CHOOSE_THEN (parse_term @"d:num") SUBST1_TAC 
                 << REWRITE_RULE [LE_EXISTS])
         |> THEN <| SPEC_TAC((parse_term @"d:num"), (parse_term @"d:num"))
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [ADD_CLAUSES; LE_REFL]
         |> THEN <| REWRITE_TAC [FACT]
         |> THEN <| MATCH_MP_TAC LE_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"FACT(m + d)")
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN 
         <| GEN_REWRITE_TAC LAND_CONV [GSYM(el 2 (CONJUNCTS MULT_CLAUSES))]
         |> THEN <| REWRITE_TAC [LE_MULT_RCANCEL]
         |> THEN <| REWRITE_TAC [ONE; LE_SUC; LE_0])

(* ------------------------------------------------------------------------- *)
(* More complicated theorems about exponential.                              *)
(* ------------------------------------------------------------------------- *)
let EXP_LT_0 = 
    prove
        ((parse_term @"!n x. 0 < x EXP n <=> ~(x = 0) \/ (n = 0)"), 
         REWRITE_TAC [GSYM NOT_LE
                      LE; EXP_EQ_0; DE_MORGAN_THM])

let LT_EXP = 
    prove((parse_term @"!x m n. x EXP m < x EXP n <=> 2 <= x /\ m < n \/
                                  (x = 0) /\ ~(m = 0) /\ (n = 0)"),
     REPEAT GEN_TAC |>THEN<|
     REPEAT GEN_TAC
     |> THEN <| ASM_CASES_TAC(parse_term @"x = 0")
     |> THEN <| ASM_REWRITE_TAC []
     |> THENL <| [REWRITE_TAC [GSYM NOT_LT
                               TWO; ONE; LT]
                  |> THEN 
                  <| SPEC_TAC((parse_term @"n:num"), (parse_term @"n:num"))
                  |> THEN <| INDUCT_TAC
                  |> THEN <| REWRITE_TAC [EXP; NOT_SUC; MULT_CLAUSES; LT]
                  |> THEN 
                  <| SPEC_TAC((parse_term @"m:num"), (parse_term @"m:num"))
                  |> THEN <| INDUCT_TAC
                  |> THEN 
                  <| REWRITE_TAC [EXP; MULT_CLAUSES; NOT_SUC; LT_REFL; LT]
                  |> THEN <| REWRITE_TAC [ONE; LT_0]
                  ALL_TAC]
     |> THEN <| EQ_TAC
     |> THENL <| [CONV_TAC CONTRAPOS_CONV
                  |> THEN <| REWRITE_TAC [NOT_LT; DE_MORGAN_THM; NOT_LE]
                  |> THEN <| REWRITE_TAC [TWO; ONE; LT]
                  |> THEN <| ASM_REWRITE_TAC [SYM ONE]
                  |> THEN <| STRIP_TAC
                  |> THEN <| ASM_REWRITE_TAC [EXP_ONE; LE_REFL]
                  |> THEN 
                  <| FIRST_ASSUM
                         (X_CHOOSE_THEN (parse_term @"d:num") SUBST1_TAC 
                          << REWRITE_RULE [LE_EXISTS])
                  |> THEN 
                  <| SPEC_TAC((parse_term @"d:num"), (parse_term @"d:num"))
                  |> THEN <| INDUCT_TAC
                  |> THEN <| REWRITE_TAC [ADD_CLAUSES; EXP; LE_REFL]
                  |> THEN <| MATCH_MP_TAC LE_TRANS
                  |> THEN <| EXISTS_TAC(parse_term @"1 * x EXP (n + d)")
                  |> THEN <| CONJ_TAC
                  |> THENL <| [ASM_REWRITE_TAC [MULT_CLAUSES]
                               REWRITE_TAC [LE_MULT_RCANCEL]
                               |> THEN <| DISJ1_TAC
                               |> THEN <| UNDISCH_TAC(parse_term @"~(x = 0)")
                               |> THEN <| CONV_TAC CONTRAPOS_CONV
                               |> THEN <| REWRITE_TAC [NOT_LE]
                               |> THEN <| REWRITE_TAC [ONE; LT]]
                  STRIP_TAC
                  |> THEN 
                  <| FIRST_ASSUM
                         (X_CHOOSE_THEN (parse_term @"d:num") SUBST1_TAC 
                          << REWRITE_RULE [LT_EXISTS])
                  |> THEN 
                  <| SPEC_TAC((parse_term @"d:num"), (parse_term @"d:num"))
                  |> THEN <| INDUCT_TAC
                  |> THEN <| REWRITE_TAC [ADD_CLAUSES; EXP]
                  |> THENL <| [MATCH_MP_TAC LTE_TRANS
                               |> THEN <| EXISTS_TAC(parse_term @"2 * x EXP m")
                               |> THEN <| CONJ_TAC
                               |> THENL <| [ASM_REWRITE_TAC 
                                                [MULT_2; LT_ADD; EXP_LT_0]
                                            ASM_REWRITE_TAC [LE_MULT_RCANCEL]]
                               MATCH_MP_TAC LTE_TRANS
                               |> THEN 
                               <| EXISTS_TAC(parse_term @"x EXP (m + SUC d)")
                               |> THEN <| ASM_REWRITE_TAC []
                               |> THEN 
                               <| REWRITE_TAC 
                                      [ADD_CLAUSES; EXP; MULT_ASSOC; 
                                       LE_MULT_RCANCEL]
                               |> THEN <| DISJ1_TAC
                               |> THEN <| MATCH_MP_TAC LE_TRANS
                               |> THEN <| EXISTS_TAC(parse_term @"x * 1")
                               |> THEN <| CONJ_TAC
                               |> THENL <| [REWRITE_TAC [MULT_CLAUSES; LE_REFL]
                                            REWRITE_TAC [LE_MULT_LCANCEL]
                                            |> THEN <| DISJ2_TAC
                                            |> THEN 
                                            <| UNDISCH_TAC
                                                   (parse_term @"~(x = 0)")
                                            |> THEN <| CONV_TAC CONTRAPOS_CONV
                                            |> THEN <| REWRITE_TAC [NOT_LE]
                                            |> THEN <| REWRITE_TAC [ONE; LT]]]])

let LE_EXP = 
    prove((parse_term @"!x m n. x EXP m <= x EXP n <=>
            if x = 0 |>THEN<| (m = 0) ==> (n = 0)
            else (x = 1) \/ m <= n"),
     REPEAT GEN_TAC
           |> THEN <| REWRITE_TAC [GSYM NOT_LT
                                   LT_EXP; DE_MORGAN_THM]
           |> THEN <| COND_CASES_TAC
           |> THEN <| ASM_REWRITE_TAC [TWO; LT; ONE]
           |> THEN <| CONV_TAC(EQT_INTRO << TAUT))

let EQ_EXP = 
    prove((parse_term @"!x m n. x EXP m = x EXP n <=>
            if x = 0 |>THEN<| (m = 0 <=> n = 0)
            else (x = 1) \/ m = n"),
     REPEAT GEN_TAC
           |> THEN <| GEN_REWRITE_TAC LAND_CONV [GSYM LE_ANTISYM
                                                 LE_EXP]
           |> THEN <| COND_CASES_TAC
           |> THEN <| ASM_REWRITE_TAC [LE_EXP]
           |> THEN <| REWRITE_TAC [GSYM LE_ANTISYM]
           |> THEN <| CONV_TAC TAUT)

let EXP_MONO_LE_IMP = 
    prove
        ((parse_term @"!x y n. x <= y ==> x EXP n <= y EXP n"), 
         REWRITE_TAC [RIGHT_FORALL_IMP_THM]
         |> THEN <| REPEAT GEN_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_SIMP_TAC [LE_MULT2; EXP; LE_REFL])

let EXP_MONO_LT_IMP = 
    prove
        ((parse_term @"!x y n. x < y /\ ~(n = 0) ==> x EXP n < y EXP n"), 
         GEN_TAC
         |> THEN <| GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [NOT_SUC; EXP]
         |> THEN <| DISCH_TAC
         |> THEN <| MATCH_MP_TAC LET_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"x * y EXP n")
         |> THEN 
         <| ASM_SIMP_TAC 
                [LT_IMP_LE; LE_MULT_LCANCEL; LT_MULT_RCANCEL; EXP_MONO_LE_IMP; 
                 EXP_EQ_0]
         |> THEN <| ASM_MESON_TAC [CONJUNCT1 LT])

let EXP_MONO_LE = 
    prove
        ((parse_term @"!x y n. x EXP n <= y EXP n <=> x <= y \/ n = 0"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| STRIP_TAC
         |> THEN <| ASM_SIMP_TAC [EXP; LE_REFL; EXP_MONO_LE_IMP]
         |> THEN <| ASM_MESON_TAC [NOT_LE; EXP_MONO_LT_IMP])

let EXP_MONO_LT = 
    prove
        ((parse_term @"!x y n. x EXP n < y EXP n <=> x < y /\ ~(n = 0)"), 
         REWRITE_TAC [GSYM NOT_LE
                      EXP_MONO_LE; DE_MORGAN_THM])

let EXP_MONO_EQ = 
    prove
        ((parse_term @"!x y n. x EXP n = y EXP n <=> x = y \/ n = 0"), 
         REWRITE_TAC [GSYM LE_ANTISYM
                      EXP_MONO_LE]
         |> THEN <| CONV_TAC TAUT)

(* ------------------------------------------------------------------------- *)
(* Division and modulus, via existence proof of their basic property.        *)
(* ------------------------------------------------------------------------- *)
let DIVMOD_EXIST = 
    prove
        ((parse_term @"!m n. ~(n = 0) ==> ?q r. (m = q * n + r) /\ r < n"), 
         REPEAT STRIP_TAC
         |> THEN <| MP_TAC(SPEC (parse_term @"\r. ?q. m = q * n + r") num_WOP)
         |> THEN <| BETA_TAC
         |> THEN <| DISCH_THEN(MP_TAC << fst << EQ_IMP_RULE)
         |> THEN <| REWRITE_TAC [LEFT_IMP_EXISTS_THM]
         |> THEN <| DISCH_THEN(MP_TAC << SPECL [(parse_term @"m:num")
                                                (parse_term @"0")])
         |> THEN <| REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES]
         |> THEN <| DISCH_THEN(X_CHOOSE_THEN (parse_term @"r:num") MP_TAC)
         |> THEN 
         <| DISCH_THEN
                (CONJUNCTS_THEN2 (X_CHOOSE_TAC(parse_term @"q:num")) MP_TAC)
         |> THEN <| DISCH_THEN(fun th -> 
                            MAP_EVERY EXISTS_TAC [(parse_term @"q:num")
                                                  (parse_term @"r:num")]
                            |> THEN <| MP_TAC th)
         |> THEN <| CONV_TAC CONTRAPOS_CONV
         |> THEN <| ASM_REWRITE_TAC [NOT_LT]
         |> THEN 
         <| DISCH_THEN
                (X_CHOOSE_THEN (parse_term @"d:num") SUBST_ALL_TAC 
                 << REWRITE_RULE [LE_EXISTS])
         |> THEN <| REWRITE_TAC [NOT_FORALL_THM]
         |> THEN <| EXISTS_TAC(parse_term @"d:num")
         |> THEN <| REWRITE_TAC [NOT_IMP; RIGHT_AND_EXISTS_THM]
         |> THEN <| EXISTS_TAC(parse_term @"q + 1")
         |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB]
         |> THEN <| REWRITE_TAC [MULT_CLAUSES; ADD_ASSOC; LT_ADDR]
         |> THEN <| ASM_REWRITE_TAC [GSYM NOT_LE
                                     LE])

let DIVMOD_EXIST_0 = 
    prove
        ((parse_term @"!m n. ?q r. if n = 0 |>THEN<| q = 0 /\ r = m
                else m = q * n + r /\ r < n"),
         REPEAT GEN_TAC
         |> THEN <| ASM_CASES_TAC(parse_term @"n = 0")
         |> THEN 
         <| ASM_SIMP_TAC [DIVMOD_EXIST; RIGHT_EXISTS_AND_THM; EXISTS_REFL])

let DIVISION_0 = 
    new_specification ["DIV"
                       "MOD"] (REWRITE_RULE [SKOLEM_THM] DIVMOD_EXIST_0)

let DIVISION = 
    prove
        ((parse_term 
              "!m n. ~(n = 0) ==> (m = m DIV n * n + m MOD n) /\ m MOD n < n"), 
         MESON_TAC [DIVISION_0])
let DIVISION_SIMP = 
    prove
        ((parse_term @"(!m n. ~(n = 0) ==> m DIV n * n + m MOD n = m) /\
    (!m n. ~(n = 0) ==> n * m DIV n + m MOD n = m)"), 
         MESON_TAC [DIVISION; MULT_SYM])

let DIVMOD_UNIQ_LEMMA = 
    prove((parse_term @"!m n q1 r1 q2 r2. ((m = q1 * n + r1) /\ r1 < n) /\
                      ((m = q2 * n + r2) /\ r2 < n)
                      ==> (q1 = q2) /\ (r1 = r2)"),
                     REPEAT GEN_TAC
                     |> THEN <| STRIP_TAC
                     |> THEN <| SUBGOAL_THEN (parse_term @"r1:num = r2") MP_TAC
                     |> THENL <| [UNDISCH_TAC(parse_term @"m = q2 * n + r2")
                                  |> THEN <| ASM_REWRITE_TAC []
                                  |> THEN 
                                  <| DISJ_CASES_THEN MP_TAC 
                                         (SPECL [(parse_term @"q1:num")
                                                 (parse_term @"q2:num")] LE_CASES)
                                  |> THEN 
                                  <| DISCH_THEN
                                         (X_CHOOSE_THEN (parse_term @"d:num") 
                                              SUBST1_TAC 
                                          << REWRITE_RULE [LE_EXISTS])
                                  |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB
                                                          GSYM ADD_ASSOC
                                                          EQ_ADD_LCANCEL]
                                  |> THENL 
                                  <| [DISCH_TAC
                                      |> THEN 
                                      <| UNDISCH_TAC(parse_term @"r1 < n")
                                      DISCH_THEN(ASSUME_TAC << SYM)
                                      |> THEN 
                                      <| UNDISCH_TAC(parse_term @"r2 < n")]
                                  |> THEN <| ASM_REWRITE_TAC []
                                  |> THEN <| ONCE_REWRITE_TAC [MULT_SYM]
                                  |> THEN 
                                  <| SPEC_TAC
                                         ((parse_term @"d:num"), 
                                          (parse_term @"d:num"))
                                  |> THEN <| INDUCT_TAC
                                  |> THEN <| REWRITE_TAC [ADD_CLAUSES
                                                          MULT_CLAUSES
                                                          GSYM NOT_LE
                                                          LE_ADD
                                                          GSYM ADD_ASSOC]
                                  DISCH_THEN SUBST_ALL_TAC
                                  |> THEN <| REWRITE_TAC []
                                  |> THEN <| CONV_TAC SYM_CONV
                                  |> THEN 
                                  <| UNDISCH_TAC(parse_term @"m = q1 * n + r2")
                                  |> THEN 
                                  <| ASM_REWRITE_TAC 
                                         [EQ_ADD_RCANCEL; EQ_MULT_RCANCEL]
                                  |> THEN 
                                  <| REPEAT(UNDISCH_TAC(parse_term @"r2 < n"))
                                  |> THEN <| ASM_CASES_TAC(parse_term @"n = 0")
                                  |> THEN <| ASM_REWRITE_TAC [GSYM NOT_LE
                                                              LE_0]])

let DIVMOD_UNIQ = 
    prove
        ((parse_term 
              "!m n q r. (m = q * n + r) /\ r < n ==> (m DIV n = q) /\ (m MOD n = r)"), 
         REPEAT GEN_TAC
         |> THEN <| DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC << GSYM)
         |> THEN <| MATCH_MP_TAC DIVMOD_UNIQ_LEMMA
         |> THEN <| MAP_EVERY EXISTS_TAC [(parse_term @"m:num")
                                          (parse_term @"n:num")]
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| MATCH_MP_TAC DIVISION
         |> THEN <| DISCH_TAC
         |> THEN <| UNDISCH_TAC(parse_term @"r < n")
         |> THEN <| ASM_REWRITE_TAC [GSYM NOT_LE
                                     LE_0])

let MOD_UNIQ = 
    prove
        ((parse_term @"!m n q r. (m = q * n + r) /\ r < n ==> (m MOD n = r)"), 
         REPEAT GEN_TAC
         |> THEN <| DISCH_THEN(fun th -> REWRITE_TAC [MATCH_MP DIVMOD_UNIQ th]))
let DIV_UNIQ = 
    prove
        ((parse_term @"!m n q r. (m = q * n + r) /\ r < n ==> (m DIV n = q)"), 
         REPEAT GEN_TAC
         |> THEN <| DISCH_THEN(fun th -> REWRITE_TAC [MATCH_MP DIVMOD_UNIQ th]))

let DIV_MULT, MOD_MULT = 
    (CONJ_PAIR << prove)
        ((parse_term @"(!m n. ~(m = 0) ==> (m * n) DIV m = n) /\
    (!m n. ~(m = 0) ==> (m * n) MOD m = 0)"), 
         SIMP_TAC [AND_FORALL_THM
                   TAUT(parse_term @"(a ==> b) /\ (a ==> c) <=> a ==> b /\ c")]
         |> THEN <| REPEAT GEN_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| MATCH_MP_TAC DIVMOD_UNIQ
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES; MULT_AC; LT_NZ])

let MOD_LT = 
    prove
        ((parse_term @"!m n. m < n ==> (m MOD n = m)"), 
         REPEAT STRIP_TAC
         |> THEN <| MATCH_MP_TAC MOD_UNIQ
         |> THEN <| EXISTS_TAC(parse_term @"0")
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES])

let MOD_EQ = 
    prove
        ((parse_term @"!m n p q. (m = n + q * p) ==> (m MOD p = n MOD p)"), 
         REPEAT GEN_TAC
         |> THEN <| ASM_CASES_TAC(parse_term @"p = 0")
         |> THENL <| [ASM_REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES]
                      |> THEN <| DISCH_THEN SUBST1_TAC
                      |> THEN <| REFL_TAC
                      DISCH_THEN SUBST1_TAC
                      |> THEN <| MATCH_MP_TAC MOD_UNIQ
                      |> THEN <| EXISTS_TAC(parse_term @"q + n DIV p")
                      |> THEN <| POP_ASSUM(MP_TAC << MATCH_MP DIVISION)
                      |> THEN 
                      <| DISCH_THEN
                             (STRIP_ASSUME_TAC << GSYM 
                              << SPEC(parse_term @"n:num"))
                      |> THEN <| ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB
                                                  GSYM ADD_ASSOC]
                      |> THEN <| MATCH_ACCEPT_TAC ADD_SYM])

let DIV_LE = 
    prove
        ((parse_term @"!m n. ~(n = 0) ==> m DIV n <= m"), 
         REPEAT STRIP_TAC
         |> THEN 
         <| FIRST_ASSUM
                (fun th -> GEN_REWRITE_TAC RAND_CONV [MATCH_MP DIVISION th])
         |> THEN <| UNDISCH_TAC(parse_term @"~(n = 0)")
         |> THEN <| SPEC_TAC((parse_term @"n:num"), (parse_term @"n:num"))
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [MULT_CLAUSES
                                 GSYM ADD_ASSOC
                                 LE_ADD])

let DIV_MUL_LE = 
    prove
        ((parse_term @"!m n. n * (m DIV n) <= m"), 
         REPEAT GEN_TAC
         |> THEN <| ASM_CASES_TAC(parse_term @"n = 0")
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; LE_0]
         |> THEN 
         <| POP_ASSUM(MP_TAC << SPEC(parse_term @"m:num") << MATCH_MP DIVISION)
         |> THEN 
         <| DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [CONJUNCT1 th])
         |> THEN <| REWRITE_TAC [LE_ADD; MULT_AC])

let DIV_0, MOD_0 = 
    (CONJ_PAIR << prove)
        ((parse_term @"(!n. ~(n = 0) ==> 0 DIV n = 0) /\
    (!n. ~(n = 0) ==> 0 MOD n = 0)"), 
         SIMP_TAC [AND_FORALL_THM
                   TAUT(parse_term @"(a ==> b) /\ (a ==> c) <=> a ==> b /\ c")]
         |> THEN <| GEN_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| MATCH_MP_TAC DIVMOD_UNIQ
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES; LT_NZ])

let DIV_1, MOD_1 = 
    (CONJ_PAIR << prove)
        ((parse_term @"(!n. n DIV 1 = n) /\ (!n. n MOD 1 = 0)"), 
         SIMP_TAC [AND_FORALL_THM]
         |> THEN <| GEN_TAC
         |> THEN <| MATCH_MP_TAC DIVMOD_UNIQ
         |> THEN <| REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES]
         |> THEN <| REWRITE_TAC [ONE; LT])

let DIV_LT = 
    prove
        ((parse_term @"!m n. m < n ==> (m DIV n = 0)"), 
         REPEAT STRIP_TAC
         |> THEN <| MATCH_MP_TAC DIV_UNIQ
         |> THEN <| EXISTS_TAC(parse_term @"m:num")
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES])

let MOD_MOD = 
    prove
        ((parse_term 
              "!m n p. ~(n * p = 0) ==> ((m MOD (n * p)) MOD n = m MOD n)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [MULT_EQ_0; DE_MORGAN_THM]
         |> THEN <| STRIP_TAC
         |> THEN <| CONV_TAC SYM_CONV
         |> THEN <| MATCH_MP_TAC MOD_EQ
         |> THEN <| EXISTS_TAC(parse_term @"m DIV (n * p) * p")
         |> THEN <| MP_TAC(SPECL [(parse_term @"m:num")
                                  (parse_term @"n * p:num")] DIVISION)
         |> THEN <| ASM_REWRITE_TAC [MULT_EQ_0; MULT_AC; ADD_AC]
         |> THEN <| DISCH_THEN(fun th -> REWRITE_TAC [GSYM th]))

let MOD_MOD_REFL = 
    prove
        ((parse_term @"!m n. ~(n = 0) ==> ((m MOD n) MOD n = m MOD n)"), 
         REPEAT GEN_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| MP_TAC(SPECL [(parse_term @"m:num")
                                  (parse_term @"n:num")
                                  (parse_term @"1")] MOD_MOD)
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; MULT_EQ_0]
         |> THEN <| REWRITE_TAC [ONE; NOT_SUC])

let DIV_MULT2 = 
    prove
        ((parse_term @"!m n p. ~(m * p = 0) ==> ((m * n) DIV (m * p) = n DIV p)"), 
         REWRITE_TAC [MULT_EQ_0; DE_MORGAN_THM]
         |> THEN <| REPEAT STRIP_TAC
         |> THEN <| MATCH_MP_TAC DIV_UNIQ
         |> THEN <| EXISTS_TAC(parse_term @"m * (n MOD p)")
         |> THEN <| ASM_SIMP_TAC [LT_MULT_LCANCEL; DIVISION]
         |> THEN 
         <| ONCE_REWRITE_TAC 
                [AC MULT_AC (parse_term @"a * b * c:num = b * a * c")]
         |> THEN <| REWRITE_TAC [GSYM LEFT_ADD_DISTRIB
                                 EQ_MULT_LCANCEL]
         |> THEN <| ASM_SIMP_TAC [GSYM DIVISION])

let MOD_MULT2 = 
    prove
        ((parse_term 
              "!m n p. ~(m * p = 0) ==> ((m * n) MOD (m * p) = m * n MOD p)"), 
         REWRITE_TAC [MULT_EQ_0; DE_MORGAN_THM]
         |> THEN <| REPEAT STRIP_TAC
         |> THEN <| MATCH_MP_TAC MOD_UNIQ
         |> THEN <| EXISTS_TAC(parse_term @"n DIV p")
         |> THEN <| ASM_SIMP_TAC [LT_MULT_LCANCEL; DIVISION]
         |> THEN 
         <| ONCE_REWRITE_TAC 
                [AC MULT_AC (parse_term @"a * b * c:num = b * a * c")]
         |> THEN <| REWRITE_TAC [GSYM LEFT_ADD_DISTRIB
                                 EQ_MULT_LCANCEL]
         |> THEN <| ASM_SIMP_TAC [GSYM DIVISION])

let MOD_EXISTS = 
    prove
        ((parse_term 
              "!m n. (?q. m = n * q) <=> if n = 0 |>THEN<| (m = 0) else (m MOD n = 0)"), 
         REPEAT GEN_TAC
         |> THEN <| COND_CASES_TAC
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES]
         |> THEN <| EQ_TAC
         |> THEN <| STRIP_TAC
         |> THEN <| ASM_SIMP_TAC [MOD_MULT]
         |> THEN <| EXISTS_TAC(parse_term @"m DIV n")
         |> THEN 
         <| SUBGOAL_THEN (parse_term @"m = (m DIV n) * n + m MOD n") 
                (fun th -> GEN_REWRITE_TAC LAND_CONV [th])
         |> THENL <| [ASM_MESON_TAC [DIVISION]
                      ASM_REWRITE_TAC [ADD_CLAUSES; MULT_AC]])

let LE_RDIV_EQ = 
    prove
        ((parse_term @"!a b n. ~(a = 0) ==> (n <= b DIV a <=> a * n <= b)"), 
         REPEAT STRIP_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THENL <| [MATCH_MP_TAC LE_TRANS
                      |> THEN <| EXISTS_TAC(parse_term @"a * (b DIV a)")
                      |> THEN <| ASM_REWRITE_TAC [DIV_MUL_LE; LE_MULT_LCANCEL]
                      SUBGOAL_THEN (parse_term @"a * n < a * (b DIV a + 1)") 
                          MP_TAC
                      |> THENL <| [MATCH_MP_TAC LET_TRANS
                                   |> THEN 
                                   <| EXISTS_TAC
                                          (parse_term @"(b DIV a) * a + b MOD a")
                                   |> THEN <| CONJ_TAC
                                   |> THENL <| [ASM_MESON_TAC [DIVISION]
                                                ALL_TAC]
                                   |> THEN 
                                   <| SIMP_TAC 
                                          [LEFT_ADD_DISTRIB; MULT_SYM; 
                                           MULT_CLAUSES; LT_ADD_LCANCEL]
                                   |> THEN <| ASM_MESON_TAC [DIVISION]
                                   ASM_REWRITE_TAC [LT_MULT_LCANCEL
                                                    GSYM ADD1
                                                    LT_SUC_LE]]])

let LE_LDIV_EQ = 
    prove
        ((parse_term @"!a b n. ~(a = 0) ==> (b DIV a <= n <=> b < a * (n + 1))"), 
         REPEAT STRIP_TAC
         |> THEN <| ONCE_REWRITE_TAC [GSYM NOT_LT]
         |> THEN <| GEN_REWRITE_TAC (LAND_CONV << RAND_CONV) [GSYM LE_SUC_LT]
         |> THEN <| ASM_SIMP_TAC [LE_RDIV_EQ]
         |> THEN <| REWRITE_TAC [NOT_LT; NOT_LE; ADD1])

let LE_LDIV = 
    prove
        ((parse_term @"!a b n. ~(a = 0) /\ b <= a * n ==> b DIV a <= n"), 
         SIMP_TAC [LE_LDIV_EQ; LEFT_ADD_DISTRIB; MULT_CLAUSES]
         |> THEN <| MESON_TAC [LT_ADD; LT_NZ; LET_TRANS])

let DIV_MONO = 
    prove
        ((parse_term @"!m n p. ~(p = 0) /\ m <= n ==> m DIV p <= n DIV p"), 
         REPEAT STRIP_TAC
         |> THEN 
         <| MATCH_MP_TAC
                (MESON [LE_REFL] 
                     (parse_term @"(!k:num. k <= a ==> k <= b) ==> a <= b"))
         |> THEN <| ASM_SIMP_TAC [LE_RDIV_EQ]
         |> THEN <| ASM_MESON_TAC [LE_TRANS])

let DIV_MONO_LT = 
    prove
        ((parse_term @"!m n p. ~(p = 0) /\ m + p <= n ==> m DIV p < n DIV p"), 
         REPEAT STRIP_TAC
         |> THEN 
         <| MATCH_MP_TAC
                (MESON [ADD1; LE_SUC_LT; LE_REFL] 
                     (parse_term @"(!k:num. k <= a ==> k + 1 <= b) ==> a < b"))
         |> THEN <| ASM_SIMP_TAC [LE_RDIV_EQ; LEFT_ADD_DISTRIB; MULT_CLAUSES]
         |> THEN <| ASM_MESON_TAC [LE_REFL; LE_TRANS; LE_ADD2; ADD_SYM])

let DIV_EQ_0 = 
    prove
        ((parse_term @"!m n. ~(n = 0) ==> ((m DIV n = 0) <=> m < n)"), 
         REPEAT(STRIP_TAC
                |> ORELSE <| EQ_TAC)
         |> THENL <| [FIRST_ASSUM
                          (SUBST1_TAC << CONJUNCT1 << SPEC(parse_term @"m:num") 
                           << MATCH_MP DIVISION)
                      |> THEN 
                      <| ASM_SIMP_TAC [MULT_CLAUSES; ADD_CLAUSES; DIVISION]
                      MATCH_MP_TAC DIV_UNIQ
                      |> THEN <| EXISTS_TAC(parse_term @"m:num")
                      |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES]])

let MOD_EQ_0 = 
    prove
        ((parse_term @"!m n. ~(n = 0) ==> ((m MOD n = 0) <=> (?q. m = q * n))"), 
         REPEAT(STRIP_TAC
                |> ORELSE <| EQ_TAC)
         |> THENL <| [FIRST_ASSUM
                          (SUBST1_TAC << CONJUNCT1 << SPEC(parse_term @"m:num") 
                           << MATCH_MP DIVISION)
                      |> THEN 
                      <| ASM_SIMP_TAC [MULT_CLAUSES; ADD_CLAUSES; DIVISION]
                      |> THEN <| MESON_TAC []
                      MATCH_MP_TAC MOD_UNIQ
                      |> THEN <| ASM_SIMP_TAC [ADD_CLAUSES; MULT_AC]
                      |> THEN <| ASM_MESON_TAC [NOT_LE
                                                CONJUNCT1 LE]])

let EVEN_MOD = 
    prove
        ((parse_term @"!n. EVEN(n) <=> (n MOD 2 = 0)"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [EVEN_EXISTS]
         |> THEN <| ONCE_REWRITE_TAC [MULT_SYM]
         |> THEN <| MATCH_MP_TAC(GSYM MOD_EQ_0)
         |> THEN <| REWRITE_TAC [TWO; NOT_SUC])

let ODD_MOD = 
    prove
        ((parse_term @"!n. ODD(n) <=> (n MOD 2 = 1)"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [GSYM NOT_EVEN
                                 EVEN_MOD]
         |> THEN <| SUBGOAL_THEN (parse_term @"n MOD 2 < 2") MP_TAC
         |> THENL <| [SIMP_TAC [DIVISION; TWO; NOT_SUC]
                      ALL_TAC]
         |> THEN <| SPEC_TAC((parse_term @"n MOD 2"), (parse_term @"n:num"))
         |> THEN <| REWRITE_TAC [TWO; ONE; LT]
         |> THEN <| MESON_TAC [NOT_SUC])

let MOD_MULT_RMOD = 
    prove
        ((parse_term 
              "!m n p. ~(n = 0) ==> ((m * (p MOD n)) MOD n = (m * p) MOD n)"), 
         REPEAT STRIP_TAC
         |> THEN <| CONV_TAC SYM_CONV
         |> THEN <| MATCH_MP_TAC MOD_EQ
         |> THEN <| EXISTS_TAC(parse_term @"m * p DIV n")
         |> THEN <| REWRITE_TAC [GSYM MULT_ASSOC
                                 GSYM LEFT_ADD_DISTRIB]
         |> THEN <| REWRITE_TAC [EQ_MULT_LCANCEL]
         |> THEN <| DISJ2_TAC
         |> THEN <| ONCE_REWRITE_TAC [ADD_SYM]
         |> THEN <| ASM_SIMP_TAC [DIVISION])

let MOD_MULT_LMOD = 
    prove
        ((parse_term 
              "!m n p. ~(n = 0) ==> (((m MOD n) * p) MOD n = (m * p) MOD n)"), 
         ONCE_REWRITE_TAC [MULT_SYM]
         |> THEN <| SIMP_TAC [MOD_MULT_RMOD])
let MOD_MULT_MOD2 = 
    prove
        ((parse_term 
              "!m n p. ~(n = 0) ==> (((m MOD n) * (p MOD n)) MOD n = (m * p) MOD n)"), 
         SIMP_TAC [MOD_MULT_RMOD; MOD_MULT_LMOD])

let MOD_EXP_MOD = 
    prove
        ((parse_term 
              "!m n p. ~(n = 0) ==> (((m MOD n) EXP p) MOD n = (m EXP p) MOD n)"), 
         REPEAT STRIP_TAC
         |> THEN <| SPEC_TAC((parse_term @"p:num"), (parse_term @"p:num"))
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [EXP]
         |> THEN <| ASM_SIMP_TAC [MOD_MULT_LMOD]
         |> THEN <| MATCH_MP_TAC EQ_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"(m * ((m MOD n) EXP p) MOD n) MOD n")
         |> THEN <| CONJ_TAC
         |> THENL <| [ALL_TAC
                      ASM_REWRITE_TAC []]
         |> THEN <| ASM_SIMP_TAC [MOD_MULT_RMOD])

let MOD_MULT_ADD = 
    prove
        ((parse_term @"!m n p. (m * n + p) MOD n = p MOD n"), 
         REPEAT STRIP_TAC
         |> THEN <| ASM_CASES_TAC(parse_term @"n = 0")
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES]
         |> THEN <| MATCH_MP_TAC MOD_UNIQ
         |> THEN <| EXISTS_TAC(parse_term @"m + p DIV n")
         |> THEN <| ASM_SIMP_TAC [RIGHT_ADD_DISTRIB
                                  GSYM ADD_ASSOC
                                  EQ_ADD_LCANCEL; DIVISION])

let DIV_MULT_ADD = 
    prove
        ((parse_term @"!a b n. ~(n = 0) ==> (a * n + b) DIV n = a + b DIV n"), 
         REPEAT STRIP_TAC
         |> THEN <| MATCH_MP_TAC DIV_UNIQ
         |> THEN <| EXISTS_TAC(parse_term @"b MOD n")
         |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB
                                 GSYM ADD_ASSOC]
         |> THEN <| ASM_MESON_TAC [DIVISION])

let MOD_ADD_MOD = 
    prove
        ((parse_term 
              "!a b n. ~(n = 0) ==> ((a MOD n + b MOD n) MOD n = (a + b) MOD n)"), 
         REPEAT STRIP_TAC
         |> THEN <| CONV_TAC SYM_CONV
         |> THEN <| MATCH_MP_TAC MOD_EQ
         |> THEN <| EXISTS_TAC(parse_term @"a DIV n + b DIV n")
         |> THEN <| REWRITE_TAC [RIGHT_ADD_DISTRIB]
         |> THEN 
         <| ONCE_REWRITE_TAC 
                [AC ADD_AC (parse_term @"(a + b) + (c + d) = (c + a) + (d + b)")]
         |> THEN <| BINOP_TAC
         |> THEN <| ASM_SIMP_TAC [DIVISION])

let DIV_ADD_MOD = 
    prove((parse_term @"!a b n. ~(n = 0)
            ==> (((a + b) MOD n = a MOD n + b MOD n) <=>
                 ((a + b) DIV n = a DIV n + b DIV n))"),
     REPEAT STRIP_TAC
                |> THEN <| FIRST_ASSUM(MP_TAC << MATCH_MP DIVISION)
                |> THEN 
                <| DISCH_THEN
                       (fun th -> 
                           MAP_EVERY (MP_TAC << CONJUNCT1 << C SPEC th) 
                               [(parse_term @"a + b:num")
                                (parse_term @"a:num")
                                (parse_term @"b:num")])
                |> THEN 
                <| DISCH_THEN
                       (fun th1 -> 
                           DISCH_THEN
                               (fun th2 -> 
                                   MP_TAC
                                       (MK_COMB
                                            (AP_TERM (parse_term @"(+)") th2, th1))))
                |> THEN 
                <| DISCH_THEN
                       (fun th -> GEN_REWRITE_TAC (funpow 2 LAND_CONV) [th])
                |> THEN 
                <| ONCE_REWRITE_TAC 
                       [AC ADD_AC 
                            (parse_term @"(a + b) + c + d = (a + c) + (b + d)")]
                |> THEN <| REWRITE_TAC [GSYM RIGHT_ADD_DISTRIB]
                |> THEN <| DISCH_THEN(fun th -> 
                                   EQ_TAC
                                   |> THEN <| DISCH_TAC
                                   |> THEN <| MP_TAC th)
                |> THEN 
                <| ASM_REWRITE_TAC 
                       [EQ_ADD_RCANCEL; EQ_ADD_LCANCEL; EQ_MULT_RCANCEL]
                |> THEN <| REWRITE_TAC [EQ_SYM_EQ])

let DIV_REFL = 
    prove
        ((parse_term @"!n. ~(n = 0) ==> (n DIV n = 1)"), 
         REPEAT STRIP_TAC
         |> THEN <| MATCH_MP_TAC DIV_UNIQ
         |> THEN <| EXISTS_TAC(parse_term @"0")
         |> THEN <| REWRITE_TAC [ADD_CLAUSES; MULT_CLAUSES]
         |> THEN <| POP_ASSUM MP_TAC
         |> THEN <| SPEC_TAC((parse_term @"n:num"), (parse_term @"n:num"))
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [LT_0])

let MOD_LE = 
    prove
        ((parse_term @"!m n. ~(n = 0) ==> m MOD n <= m"), 
         REPEAT GEN_TAC
         |> THEN 
         <| DISCH_THEN
                (fun th -> GEN_REWRITE_TAC RAND_CONV [MATCH_MP DIVISION th])
         |> THEN <| ONCE_REWRITE_TAC [ADD_SYM]
         |> THEN <| REWRITE_TAC [LE_ADD])

let DIV_MONO2 = 
    prove
        ((parse_term @"!m n p. ~(p = 0) /\ p <= m ==> n DIV m <= n DIV p"), 
         REPEAT STRIP_TAC
         |> THEN <| ASM_SIMP_TAC [LE_RDIV_EQ]
         |> THEN <| MATCH_MP_TAC LE_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"m * n DIV m")
         |> THEN <| ASM_REWRITE_TAC [LE_MULT_RCANCEL]
         |> THEN <| ONCE_REWRITE_TAC [MULT_SYM]
         |> THEN <| MP_TAC(SPECL [(parse_term @"n:num")
                                  (parse_term @"m:num")] DIVISION)
         |> THEN <| ASM_MESON_TAC [LE_ADD; LE])

let DIV_LE_EXCLUSION = 
    prove
        ((parse_term 
              "!a b c d. ~(b = 0) /\ b * c < (a + 1) * d ==> c DIV d <= a DIV b"), 
         REPEAT GEN_TAC
         |> THEN <| ASM_CASES_TAC(parse_term @"d = 0")
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; LT]
         |> THEN <| STRIP_TAC
         |> THEN 
         <| MATCH_MP_TAC
                (MESON [LE_REFL] 
                     (parse_term @"(!k:num. k <= a ==> k <= b) ==> a <= b"))
         |> THEN <| X_GEN_TAC(parse_term @"k:num")
         |> THEN 
         <| SUBGOAL_THEN 
                (parse_term @"b * d * k <= b * c ==> (b * k) * d < (a + 1) * d") 
                MP_TAC
         |> THENL <| [ASM_MESON_TAC [LET_TRANS; MULT_AC]
                      ALL_TAC]
         |> THEN <| MATCH_MP_TAC MONO_IMP
         |> THEN <| ASM_SIMP_TAC [LE_MULT_LCANCEL; LT_MULT_RCANCEL; LE_RDIV_EQ]
         |> THEN <| REWRITE_TAC [GSYM ADD1
                                 LT_SUC_LE])

let DIV_EQ_EXCLUSION = 
    prove
        ((parse_term 
              "b * c < (a + 1) * d /\ a * d < (c + 1) * b ==> (a DIV b = c DIV d)"), 
         REPEAT GEN_TAC
         |> THEN <| ASM_CASES_TAC(parse_term @"b = 0")
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; LT]
         |> THEN <| ASM_CASES_TAC(parse_term @"d = 0")
         |> THEN <| ASM_REWRITE_TAC [MULT_CLAUSES; LT]
         |> THEN <| ASM_MESON_TAC [MULT_SYM; LE_ANTISYM; DIV_LE_EXCLUSION])

let MULT_DIV_LE = 
    prove
        ((parse_term @"!m n p. ~(p = 0) ==> m * (n DIV p) <= (m * n) DIV p"), 
         REPEAT GEN_TAC
         |> THEN <| SIMP_TAC [LE_RDIV_EQ]
         |> THEN 
         <| DISCH_THEN(MP_TAC << SPEC(parse_term @"n:num") << MATCH_MP DIVISION)
         |> THEN 
         <| DISCH_THEN
                (fun th -> 
                    GEN_REWRITE_TAC (RAND_CONV << RAND_CONV) [CONJUNCT1 th])
         |> THEN <| REWRITE_TAC [LEFT_ADD_DISTRIB]
         |> THEN <| REWRITE_TAC [MULT_AC; LE_ADD])

let DIV_DIV = 
    prove
        ((parse_term 
              "!m n p. ~(n * p = 0) ==> ((m DIV n) DIV p = m DIV (n * p))"), 
         REWRITE_TAC [MULT_EQ_0; DE_MORGAN_THM]
         |> THEN <| REPEAT STRIP_TAC
         |> THEN 
         <| MATCH_MP_TAC
                (MESON [LE_ANTISYM] 
                     (parse_term @"(!k. k <= m <=> k <= n) ==> m = n"))
         |> THEN <| ASM_SIMP_TAC [LE_RDIV_EQ; MULT_EQ_0; MULT_ASSOC])

let DIV_MOD = 
    prove
        ((parse_term 
              "!m n p. ~(n * p = 0) ==> ((m DIV n) MOD p = (m MOD (n * p)) DIV n)"), 
         REWRITE_TAC [MULT_EQ_0; DE_MORGAN_THM]
         |> THEN <| REPEAT STRIP_TAC
         |> THEN 
         <| MATCH_MP_TAC
                (MESON [LE_ANTISYM] 
                     (parse_term @"(!k. k <= m <=> k <= n) ==> m = n"))
         |> THEN <| X_GEN_TAC(parse_term @"k:num")
         |> THEN <| MATCH_MP_TAC EQ_TRANS
         |> THEN 
         <| EXISTS_TAC(parse_term @"k + p * ((m DIV n) DIV p) <= (m DIV n)")
         |> THEN <| CONJ_TAC
         |> THENL 
         <| [MP_TAC(SPECL [(parse_term @"m DIV n")
                           (parse_term @"p:num")] DIVISION)
             |> THEN <| ASM_REWRITE_TAC []
             MP_TAC(SPECL [(parse_term @"m:num")
                           (parse_term @"n * p:num")] DIVISION)
             |> THEN 
             <| ASM_SIMP_TAC [LE_RDIV_EQ; MULT_EQ_0; DIV_DIV; LEFT_ADD_DISTRIB]]
         |> THEN <| REWRITE_TAC [MULT_AC]
         |> THEN <| MESON_TAC [ADD_SYM; MULT_SYM; LE_ADD_RCANCEL])

let MOD_MOD_EXP_MIN = 
    prove
        ((parse_term @"!x p m n. ~(p = 0)
              ==> x MOD (p EXP m) MOD (p EXP n) = x MOD (p EXP (MIN m n))"),
         REPEAT STRIP_TAC
         |> THEN <| REWRITE_TAC [MIN]
         |> THEN <| ASM_CASES_TAC(parse_term @"m:num <= n")
         |> THEN <| ASM_REWRITE_TAC []
         |> THENL 
         <| [FIRST_X_ASSUM
                 (CHOOSE_THEN SUBST1_TAC << GEN_REWRITE_RULE I [LE_EXISTS])
             |> THEN <| MATCH_MP_TAC MOD_LT
             |> THEN <| MATCH_MP_TAC LTE_TRANS
             |> THEN <| EXISTS_TAC(parse_term @"p EXP m")
             |> THEN <| ASM_SIMP_TAC [DIVISION; EXP_EQ_0; LE_EXP; LE_ADD]
             SUBGOAL_THEN (parse_term @"?d. m = n + d") (CHOOSE_THEN SUBST1_TAC)
             |> THENL <| [ASM_MESON_TAC [LE_CASES; LE_EXISTS]
                          ASM_SIMP_TAC [EXP_ADD; MOD_MOD; MULT_EQ_0; EXP_EQ_0]]])

(* ------------------------------------------------------------------------- *)
(* Theorems for eliminating cutoff subtraction, predecessor, DIV and MOD.    *)
(* We have versions that introduce universal or existential quantifiers.     *)
(* ------------------------------------------------------------------------- *)
let PRE_ELIM_THM = 
    prove
        ((parse_term 
              "P(PRE n) <=> !m. n = SUC m \/ m = 0 /\ n = 0 ==> P m(parse_term @"), 
         SPEC_TAC((parse_term @"n:num"), (parse_term @"n:num"))
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [NOT_SUC; SUC_INJ; PRE]
         |> THEN <| MESON_TAC [])

let PRE_ELIM_THM' = 
    prove
        ((parse_term @"P(PRE n) <=> ?m. (n = SUC m \/ m = 0 /\ n = 0) /\ P m"), 
         MP_TAC
             (INST [(parse_term @"\x:num. ~P x"), (parse_term @"P:num->bool")] 
                  PRE_ELIM_THM)
         |> THEN <| MESON_TAC [])

let SUB_ELIM_THM = 
    prove
        ((parse_term @"P(a - b) <=> !d. a = b + d \/ a < b /\ d = 0 ==> P d"), 
         DISJ_CASES_TAC(SPECL [(parse_term @"a:num")
                               (parse_term @"b:num")] LTE_CASES)
         |> THENL <| [ASM_MESON_TAC [NOT_LT; SUB_EQ_0; LT_IMP_LE; LE_ADD]
                      ALL_TAC]
         |> THEN 
         <| FIRST_ASSUM
                (X_CHOOSE_THEN (parse_term @"e:num") SUBST1_TAC 
                 << REWRITE_RULE [LE_EXISTS])
         |> THEN <| SIMP_TAC [ADD_SUB2
                              GSYM NOT_LE
                              LE_ADD; EQ_ADD_LCANCEL]
         |> THEN <| MESON_TAC [])

let SUB_ELIM_THM' = 
    prove
        ((parse_term @"P(a - b) <=> ?d. (a = b + d \/ a < b /\ d = 0) /\ P d"), 
         MP_TAC
             (INST [(parse_term @"\x:num. ~P x"), (parse_term @"P:num->bool")] 
                  SUB_ELIM_THM)
         |> THEN <| MESON_TAC [])

let DIVMOD_ELIM_THM = 
    prove((parse_term @"P (m DIV n) (m MOD n) <=>
         !q r. n = 0 /\ q = 0 /\ r = m \/ m = q * n + r /\ r < n ==> P q r"),
     ASM_CASES_TAC(parse_term @"n = 0")
        |> THEN <| ASM_REWRITE_TAC []
        |> THENL <| [ASM_MESON_TAC [DIVISION_0; LT]
                     FIRST_ASSUM(MP_TAC << MATCH_MP DIVISION)
                     |> THEN <| MESON_TAC [DIVMOD_UNIQ]])

let DIVMOD_ELIM_THM' = 
  prove((parse_term @"P (m DIV n) (m MOD n) <=>
         ?q r. (n = 0 /\ q = 0 /\ r = m \/ m = q * n + r /\ r < n) /\ P q r"),
    MP_TAC
            (INST 
                 [(parse_term @"\x:num y:num. ~P x y"), 
                  (parse_term @"P:num->num->bool")] DIVMOD_ELIM_THM)
        |> THEN <| MESON_TAC [])

(* ------------------------------------------------------------------------- *)
(* Crude but useful conversion for cancelling down equations.                *)
(* ------------------------------------------------------------------------- *)
let NUM_CANCEL_CONV = 
    let rec minter i l1' l2' l1 l2 = 
        if l1 = []
        then (i, l1', l2' @ l2)
        elif l2 = []
        then (i, l1 @ l1', l2')
        else 
            let h1 = hd l1
            let h2 = hd l2
            if h1 = h2
            then minter (h1 :: i) l1' l2' (tl l1) (tl l2)
            elif h1 < h2
            then minter i (h1 :: l1') l2' (tl l1) l2
            else minter i l1' (h2 :: l2') l1 (tl l2)
    let add_tm = (parse_term @"(+)")
    let eq_tm = (parse_term @"(=) :num->num->bool")
    let EQ_ADD_LCANCEL_0' = 
        GEN_REWRITE_RULE (funpow 2 BINDER_CONV << LAND_CONV) [EQ_SYM_EQ] 
            EQ_ADD_LCANCEL_0
    let AC_RULE = AC ADD_AC
    fun tm -> 
        let l, r = dest_eq tm
        let lats = sort (<=) (binops (parse_term @"(+)") l)
        let rats = sort (<=) (binops (parse_term @"(+)") r)
        let i, lats', rats' = minter [] [] [] lats rats
        let l' = list_mk_binop add_tm (i @ lats')
        let r' = list_mk_binop add_tm (i @ rats')
        let lth = AC_RULE(mk_eq(l, l'))
        let rth = AC_RULE(mk_eq(r, r'))
        let eth = MK_COMB(AP_TERM eq_tm lth, rth)
        GEN_REWRITE_RULE (RAND_CONV << REPEATC) 
            [EQ_ADD_LCANCEL; EQ_ADD_LCANCEL_0; EQ_ADD_LCANCEL_0'] eth

(* ------------------------------------------------------------------------- *)
(* This is handy for easing MATCH_MP on inequalities.                        *)
(* ------------------------------------------------------------------------- *)
let LE_IMP = 
    let pth = PURE_ONCE_REWRITE_RULE [IMP_CONJ] LE_TRANS
    fun th -> GEN_ALL(MATCH_MP pth (SPEC_ALL th))

parse_as_binder "minimal"

(* ------------------------------------------------------------------------- *)
(* Binder for "the minimal n such that".                                     *)
(* ------------------------------------------------------------------------- *)
let minimal = 
    new_definition
        (parse_term @"(minimal) (P:num->bool) = @n. P n /\ !m. m < n ==> ~(P m)")

let MINIMAL = 
    prove
        ((parse_term 
              "!P. (?n. P n) <=> P((minimal) P) /\ (!m. m < (minimal) P ==> ~(P m))"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [minimal]
         |> THEN <| CONV_TAC(RAND_CONV SELECT_CONV)
         |> THEN <| REWRITE_TAC [GSYM num_WOP])

(* ------------------------------------------------------------------------- *)
(* A common lemma for transitive relations.                                  *)
(* ------------------------------------------------------------------------- *)
let TRANSITIVE_STEPWISE_LT_EQ = 
    prove((parse_term @"!R. (!x y z. R x y /\ R y z ==> R x z)
          ==> ((!m n. m < n ==> R m n) <=> (!n. R n (SUC n)))"),
         REPEAT STRIP_TAC
         |> THEN <| EQ_TAC
         |> THEN <| ASM_SIMP_TAC [LT]
         |> THEN <| DISCH_TAC
         |> THEN <| SIMP_TAC [LT_EXISTS; LEFT_IMP_EXISTS_THM]
         |> THEN <| GEN_TAC
         |> THEN <| ONCE_REWRITE_TAC [SWAP_FORALL_THM]
         |> THEN <| REWRITE_TAC [LEFT_FORALL_IMP_THM; EXISTS_REFL; ADD_CLAUSES]
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [ADD_CLAUSES]
         |> THEN <| ASM_MESON_TAC [])

let TRANSITIVE_STEPWISE_LT = 
    prove((parse_term @"!R. (!x y z. R x y /\ R y z ==> R x z) /\ (!n. R n (SUC n))
        ==> !m n. m < n ==> R m n"),
       REPEAT GEN_TAC
       |> THEN 
       <| MATCH_MP_TAC(TAUT(parse_term @"(a ==> (c <=> b)) ==> a /\ b ==> c"))
       |> THEN <| MATCH_ACCEPT_TAC TRANSITIVE_STEPWISE_LT_EQ)

let TRANSITIVE_STEPWISE_LE_EQ = 
    prove((parse_term @"!R. (!x. R x x) /\ (!x y z. R x y /\ R y z ==> R x z)
        ==> ((!m n. m <= n ==> R m n) <=> (!n. R n (SUC n)))"),
       REPEAT STRIP_TAC
       |> THEN <| EQ_TAC
       |> THEN <| ASM_SIMP_TAC [LE; LE_REFL]
       |> THEN <| DISCH_TAC
       |> THEN <| SIMP_TAC [LE_EXISTS; LEFT_IMP_EXISTS_THM]
       |> THEN <| GEN_TAC
       |> THEN <| ONCE_REWRITE_TAC [SWAP_FORALL_THM]
       |> THEN <| REWRITE_TAC [LEFT_FORALL_IMP_THM; EXISTS_REFL; ADD_CLAUSES]
       |> THEN <| INDUCT_TAC
       |> THEN <| REWRITE_TAC [ADD_CLAUSES]
       |> THEN <| ASM_MESON_TAC [])

let TRANSITIVE_STEPWISE_LE = 
    prove((parse_term @"!R. (!x. R x x) /\ (!x y z. R x y /\ R y z ==> R x z) /\
        (!n. R n (SUC n))
        ==> !m n. m <= n ==> R m n"),
       REPEAT GEN_TAC
       |> THEN 
       <| MATCH_MP_TAC
              (TAUT(parse_term @"(a /\ a' ==> (c <=> b)) ==> a /\ a' /\ b ==> c"))
       |> THEN <| MATCH_ACCEPT_TAC TRANSITIVE_STEPWISE_LE_EQ)