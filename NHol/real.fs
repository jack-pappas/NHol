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

#if USE
#else
/// Derived properties of reals.
module NHol.real

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

open NHol
open system
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
open ind_types
open lists
open realax
open calc_int
open realarith
#endif

infof "Entering real.fs"

(* ------------------------------------------------------------------------- *)
(* Additional commutativity properties of the inclusion map.                 *)
(* ------------------------------------------------------------------------- *)
let REAL_OF_NUM_LT = 
    prove((parse_term @"!m n. &m < &n <=> m < n"), REWRITE_TAC [real_lt
                                                                GSYM NOT_LE
                                                                REAL_OF_NUM_LE])

let REAL_OF_NUM_GE = 
    prove
        ((parse_term @"!m n. &m >= &n <=> m >= n"), 
         REWRITE_TAC [GE; real_ge; REAL_OF_NUM_LE])
let REAL_OF_NUM_GT = 
    prove
        ((parse_term @"!m n. &m > &n <=> m > n"), 
         REWRITE_TAC [GT; real_gt; REAL_OF_NUM_LT])

let REAL_OF_NUM_MAX = 
    prove
        ((parse_term @"!m n. max (&m) (&n) = &(MAX m n)"), 
         REWRITE_TAC [REAL_OF_NUM_LE
                      MAX
                      real_max
                      GSYM COND_RAND])

let REAL_OF_NUM_MIN = 
    prove
        ((parse_term @"!m n. min (&m) (&n) = &(MIN m n)"), 
         REWRITE_TAC [REAL_OF_NUM_LE
                      MIN
                      real_min
                      GSYM COND_RAND])

let REAL_OF_NUM_SUC = 
    prove
        ((parse_term @"!n. &n + &1 = &(SUC n)"), 
         REWRITE_TAC [ADD1; REAL_OF_NUM_ADD])

let REAL_OF_NUM_SUB = 
    prove
        ((parse_term @"!m n. m <= n ==> (&n - &m = &(n - m))"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [LE_EXISTS]
         |> THEN <| STRIP_TAC
         |> THEN <| ASM_REWRITE_TAC [ADD_SUB2]
         |> THEN <| REWRITE_TAC [GSYM REAL_OF_NUM_ADD]
         |> THEN <| ONCE_REWRITE_TAC [REAL_ADD_SYM]
         |> THEN <| REWRITE_TAC [real_sub
                                 GSYM REAL_ADD_ASSOC]
         |> THEN <| MESON_TAC [REAL_ADD_LINV; REAL_ADD_SYM; REAL_ADD_LID])

(* ------------------------------------------------------------------------- *)
(* A few theorems we need to prove explicitly for later.                     *)
(* ------------------------------------------------------------------------- *)

let REAL_MUL_AC = 
    prove((parse_term @"(m * n = n * m) /\
   ((m * n) * p = m * (n * p)) /\
   (m * (n * p) = n * (m * p))"),
          REWRITE_TAC [REAL_MUL_ASSOC;
                       EQT_INTRO(SPEC_ALL REAL_MUL_SYM)]
          |> THEN <| AP_THM_TAC
          |> THEN <| AP_TERM_TAC
          |> THEN <| MATCH_ACCEPT_TAC REAL_MUL_SYM)

let REAL_ADD_RDISTRIB = 
    prove
        ((parse_term @"!x y z. (x + y) * z = x * z + y * z"), 
         MESON_TAC [REAL_MUL_SYM; REAL_ADD_LDISTRIB])

let REAL_LT_LADD_IMP = 
    prove
        ((parse_term @"!x y z. y < z ==> x + y < x + z"), 
         REPEAT GEN_TAC
         |> THEN <| CONV_TAC CONTRAPOS_CONV
         |> THEN <| REWRITE_TAC [real_lt]
         |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP REAL_LE_LADD_IMP)
         |> THEN <| DISCH_THEN(MP_TAC << SPEC(parse_term @"--x"))
         |> THEN <| REWRITE_TAC [REAL_ADD_ASSOC; REAL_ADD_LINV; REAL_ADD_LID])

let REAL_LT_MUL = 
    prove
        ((parse_term @"!x y. &0 < x /\ &0 < y ==> &0 < x * y"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [REAL_LT_LE]
         |> THEN <| CONV_TAC(ONCE_DEPTH_CONV SYM_CONV)
         |> THEN <| STRIP_TAC
         |> THEN <| ASM_REWRITE_TAC [REAL_ENTIRE]
         |> THEN <| MATCH_MP_TAC REAL_LE_MUL
         |> THEN <| ASM_REWRITE_TAC [])

(* ------------------------------------------------------------------------- *)
(* Tactic version of REAL_ARITH.                                             *)
(* ------------------------------------------------------------------------- *)

/// Attempt to prove goal using basic algebra and linear arithmetic over the reals.
let REAL_ARITH_TAC = CONV_TAC REAL_ARITH

(* ------------------------------------------------------------------------- *)
(* Prove all the linear theorems we can blow away automatically.             *)
(* ------------------------------------------------------------------------- *)

let REAL_EQ_ADD_LCANCEL_0 = 
#if BUGGY
    prove((parse_term @"!x y. (x + y = x) <=> (y = &0)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x y. (x + y = x) <=> (y = &0)") : thm
#endif

let REAL_EQ_ADD_RCANCEL_0 = 
#if BUGGY
    prove((parse_term @"!x y. (x + y = y) <=> (x = &0)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x y. (x + y = y) <=> (x = &0)") : thm
#endif

let REAL_LNEG_UNIQ = 
#if BUGGY
    prove((parse_term @"!x y. (x + y = &0) <=> (x = --y)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x y. (x + y = &0) <=> (x = --y)") : thm
#endif

let REAL_RNEG_UNIQ = 
#if BUGGY
    prove((parse_term @"!x y. (x + y = &0) <=> (y = --x)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x y. (x + y = &0) <=> (y = --x)") : thm
#endif

let REAL_NEG_LMUL = 
    prove((parse_term @"!x y. --(x * y) = (--x) * y"), REAL_ARITH_TAC)

let REAL_NEG_RMUL = 
    prove((parse_term @"!x y. --(x * y) = x * (--y)"), REAL_ARITH_TAC)

let REAL_NEGNEG = prove((parse_term @"!x. --(--x) = x"), REAL_ARITH_TAC)

let REAL_NEG_MUL2 = 
    prove((parse_term @"!x y. (--x) * (--y) = x * y"), REAL_ARITH_TAC)

let REAL_LT_LADD = 
    prove((parse_term @"!x y z. (x + y) < (x + z) <=> y < z"), REAL_ARITH_TAC)

let REAL_LT_RADD = 
    prove((parse_term @"!x y z. (x + z) < (y + z) <=> x < y"), REAL_ARITH_TAC)

let REAL_LT_ANTISYM = 
    prove((parse_term @"!x y. ~(x < y /\ y < x)"), REAL_ARITH_TAC)

let REAL_LT_GT = 
#if BUGGY
    prove((parse_term @"!x y. x < y ==> ~(y < x)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x y. x < y ==> ~(y < x)") : thm
#endif

let REAL_NOT_EQ = 
#if BUGGY
    prove((parse_term @"!x y. ~(x = y) <=> x < y \/ y < x"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x y. ~(x = y) <=> x < y \/ y < x") : thm
#endif

let REAL_NOT_LE = 
    prove((parse_term @"!x y. ~(x <= y) <=> y < x"), REAL_ARITH_TAC)

let REAL_LET_ANTISYM = 
    prove((parse_term @"!x y. ~(x <= y /\ y < x)"), REAL_ARITH_TAC)

let REAL_NEG_LT0 = 
    prove((parse_term @"!x. (--x) < &0 <=> &0 < x"), REAL_ARITH_TAC)

let REAL_NEG_GT0 = 
    prove((parse_term @"!x. &0 < (--x) <=> x < &0"), REAL_ARITH_TAC)

let REAL_NEG_LE0 = 
    prove((parse_term @"!x. (--x) <= &0 <=> &0 <= x"), REAL_ARITH_TAC)

let REAL_NEG_GE0 = 
    prove((parse_term @"!x. &0 <= (--x) <=> x <= &0"), REAL_ARITH_TAC)

let REAL_LT_TOTAL = 
    prove((parse_term @"!x y. (x = y) \/ x < y \/ y < x"), REAL_ARITH_TAC)

let REAL_LT_NEGTOTAL = 
    prove((parse_term @"!x. (x = &0) \/ (&0 < x) \/ (&0 < --x)"), REAL_ARITH_TAC)

let REAL_LE_01 = prove((parse_term @"&0 <= &1"), REAL_ARITH_TAC)

let REAL_LT_01 = prove((parse_term @"&0 < &1"), REAL_ARITH_TAC)

let REAL_LE_LADD = 
    prove((parse_term @"!x y z. (x + y) <= (x + z) <=> y <= z"), REAL_ARITH_TAC)

let REAL_LE_RADD = 
    prove((parse_term @"!x y z. (x + z) <= (y + z) <=> x <= y"), REAL_ARITH_TAC)

let REAL_LT_ADD2 = 
    prove
        ((parse_term @"!w x y z. w < x /\ y < z ==> (w + y) < (x + z)"), 
         REAL_ARITH_TAC)

let REAL_LE_ADD2 = 
    prove
        ((parse_term @"!w x y z. w <= x /\ y <= z ==> (w + y) <= (x + z)"), 
         REAL_ARITH_TAC)

let REAL_LT_LNEG = 
    prove
        ((parse_term @"!x y. --x < y <=> &0 < x + y"), 
         REWRITE_TAC [real_lt; REAL_LE_RNEG; REAL_ADD_AC])

let REAL_LT_RNEG = 
    prove
        ((parse_term @"!x y. x < --y <=> x + y < &0"), 
         REWRITE_TAC [real_lt; REAL_LE_LNEG; REAL_ADD_AC])

let REAL_LT_ADDNEG = 
    prove
        ((parse_term @"!x y z. y < (x + (--z)) <=> (y + z) < x"), REAL_ARITH_TAC)

let REAL_LT_ADDNEG2 = 
    prove
        ((parse_term @"!x y z. (x + (--y)) < z <=> x < (z + y)"), REAL_ARITH_TAC)

let REAL_LT_ADD1 = 
    prove((parse_term @"!x y. x <= y ==> x < (y + &1)"), REAL_ARITH_TAC)

let REAL_SUB_ADD = prove((parse_term @"!x y. (x - y) + y = x"), REAL_ARITH_TAC)

let REAL_SUB_ADD2 = prove((parse_term @"!x y. y + (x - y) = x"), REAL_ARITH_TAC)

let REAL_SUB_REFL = prove((parse_term @"!x. x - x = &0"), REAL_ARITH_TAC)

let REAL_LE_DOUBLE = 
    prove((parse_term @"!x. &0 <= x + x <=> &0 <= x"), REAL_ARITH_TAC)

let REAL_LE_NEGL = 
    prove((parse_term @"!x. (--x <= x) <=> (&0 <= x)"), REAL_ARITH_TAC)

let REAL_LE_NEGR = 
    prove((parse_term @"!x. (x <= --x) <=> (x <= &0)"), REAL_ARITH_TAC)

let REAL_NEG_EQ_0 = 
#if BUGGY
    prove((parse_term @"!x. (--x = &0) <=> (x = &0)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x. (--x = &0) <=> (x = &0)") : thm
#endif

let REAL_ADD_SUB = 
#if BUGGY
    prove((parse_term @"!x y. (x + y) - x = y"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x y. (x + y) - x = y") : thm
#endif

let REAL_NEG_EQ = 
#if BUGGY
    prove((parse_term @"!x y. (--x = y) <=> (x = --y)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x y. (--x = y) <=> (x = --y)") : thm
#endif

let REAL_NEG_MINUS1 = 
    prove((parse_term @"!x. --x = (--(&1)) * x"), REAL_ARITH_TAC)

let REAL_LT_IMP_NE = 
#if BUGGY
    prove((parse_term @"!x y. x < y ==> ~(x = y)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x y. x < y ==> ~(x = y)") : thm
#endif

let REAL_LE_ADDR = 
    prove((parse_term @"!x y. x <= x + y <=> &0 <= y"), REAL_ARITH_TAC)

let REAL_LE_ADDL = 
    prove((parse_term @"!x y. y <= x + y <=> &0 <= x"), REAL_ARITH_TAC)

let REAL_LT_ADDR = 
    prove((parse_term @"!x y. x < x + y <=> &0 < y"), REAL_ARITH_TAC)

let REAL_LT_ADDL = 
    prove((parse_term @"!x y. y < x + y <=> &0 < x"), REAL_ARITH_TAC)

let REAL_SUB_SUB = prove((parse_term @"!x y. (x - y) - x = --y"), REAL_ARITH_TAC)

let REAL_LT_ADD_SUB = 
    prove((parse_term @"!x y z. (x + y) < z <=> x < (z - y)"), REAL_ARITH_TAC)

let REAL_LT_SUB_RADD = 
    prove((parse_term @"!x y z. (x - y) < z <=> x < z + y"), REAL_ARITH_TAC)

let REAL_LT_SUB_LADD = 
    prove((parse_term @"!x y z. x < (y - z) <=> (x + z) < y"), REAL_ARITH_TAC)

let REAL_LE_SUB_LADD = 
    prove((parse_term @"!x y z. x <= (y - z) <=> (x + z) <= y"), REAL_ARITH_TAC)

let REAL_LE_SUB_RADD = 
    prove((parse_term @"!x y z. (x - y) <= z <=> x <= z + y"), REAL_ARITH_TAC)

let REAL_LT_NEG = 
    prove((parse_term @"!x y. --x < --y <=> y < x"), REAL_ARITH_TAC)

let REAL_LE_NEG = 
    prove((parse_term @"!x y. --x <= --y <=> y <= x"), REAL_ARITH_TAC)

let REAL_ADD2_SUB2 = 
    prove
        ((parse_term @"!a b c d. (a + b) - (c + d) = (a - c) + (b - d)"), 
         REAL_ARITH_TAC)

let REAL_SUB_LZERO = prove((parse_term @"!x. &0 - x = --x"), REAL_ARITH_TAC)

let REAL_SUB_RZERO = prove((parse_term @"!x. x - &0 = x"), REAL_ARITH_TAC)

let REAL_LET_ADD2 = 
    prove
        ((parse_term @"!w x y z. w <= x /\ y < z ==> (w + y) < (x + z)"), 
         REAL_ARITH_TAC)

let REAL_LTE_ADD2 = 
    prove
        ((parse_term @"!w x y z. w < x /\ y <= z ==> w + y < x + z"), 
         REAL_ARITH_TAC)

let REAL_SUB_LNEG = 
    prove((parse_term @"!x y. (--x) - y = --(x + y)"), REAL_ARITH_TAC)

let REAL_SUB_RNEG = 
    prove((parse_term @"!x y. x - (--y) = x + y"), REAL_ARITH_TAC)

let REAL_SUB_NEG2 = 
    prove((parse_term @"!x y. (--x) - (--y) = y - x"), REAL_ARITH_TAC)

let REAL_SUB_TRIANGLE = 
    prove((parse_term @"!a b c. (a - b) + (b - c) = a - c"), REAL_ARITH_TAC)

let REAL_EQ_SUB_LADD = 
#if BUGGY
    prove((parse_term @"!x y z. (x = y - z) <=> (x + z = y)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x y z. (x = y - z) <=> (x + z = y)") : thm
#endif

let REAL_EQ_SUB_RADD = 
#if BUGGY
    prove((parse_term @"!x y z. (x - y = z) <=> (x = z + y)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x y z. (x - y = z) <=> (x = z + y)") : thm
#endif


let REAL_SUB_SUB2 = prove((parse_term @"!x y. x - (x - y) = y"), REAL_ARITH_TAC)

let REAL_ADD_SUB2 = 
    prove((parse_term @"!x y. x - (x + y) = --y"), REAL_ARITH_TAC)

let REAL_EQ_IMP_LE = 
#if BUGGY
    prove((parse_term @"!x y. (x = y) ==> x <= y"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x y. (x = y) ==> x <= y") : thm
#endif

let REAL_POS_NZ = 
#if BUGGY
    prove((parse_term @"!x. &0 < x ==> ~(x = &0)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x. &0 < x ==> ~(x = &0)") : thm
#endif

let REAL_DIFFSQ = 
    prove
        ((parse_term @"!x y. (x + y) * (x - y) = (x * x) - (y * y)"), 
         REAL_ARITH_TAC)

let REAL_EQ_NEG2 = 
#if BUGGY
    prove((parse_term @"!x y. (--x = --y) <=> (x = y)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x y. (--x = --y) <=> (x = y)") : thm
#endif

let REAL_LT_NEG2 = 
    prove((parse_term @"!x y. --x < --y <=> y < x"), REAL_ARITH_TAC)

let REAL_SUB_LDISTRIB = 
    prove((parse_term @"!x y z. x * (y - z) = x * y - x * z"), REAL_ARITH_TAC)

let REAL_SUB_RDISTRIB = 
    prove((parse_term @"!x y z. (x - y) * z = x * z - y * z"), REAL_ARITH_TAC)

(* ------------------------------------------------------------------------- *)
(* Theorems about "abs".                                                     *)
(* ------------------------------------------------------------------------- *)
let REAL_ABS_ZERO = 
#if BUGGY
    prove((parse_term @"!x. (abs(x) = &0) <=> (x = &0)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x. (abs(x) = &0) <=> (x = &0)")
#endif

let REAL_ABS_0 = prove((parse_term @"abs(&0) = &0"), REAL_ARITH_TAC)

let REAL_ABS_1 = prove((parse_term @"abs(&1) = &1"), REAL_ARITH_TAC)

let REAL_ABS_TRIANGLE = 
    prove((parse_term @"!x y. abs(x + y) <= abs(x) + abs(y)"), REAL_ARITH_TAC)

let REAL_ABS_TRIANGLE_LE = 
    prove
        ((parse_term @"!x y z.abs(x) + abs(y - x) <= z ==> abs(y) <= z"), 
         REAL_ARITH_TAC)

let REAL_ABS_TRIANGLE_LT = 
    prove
        ((parse_term @"!x y z.abs(x) + abs(y - x) < z ==> abs(y) < z"), 
         REAL_ARITH_TAC)

let REAL_ABS_POS = prove((parse_term @"!x. &0 <= abs(x)"), REAL_ARITH_TAC)

let REAL_ABS_SUB = 
    prove((parse_term @"!x y. abs(x - y) = abs(y - x)"), REAL_ARITH_TAC)

let REAL_ABS_NZ = 
#if BUGGY
    prove((parse_term @"!x. ~(x = &0) <=> &0 < abs(x)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x. ~(x = &0) <=> &0 < abs(x)") : thm
#endif

let REAL_ABS_ABS = 
    prove((parse_term @"!x. abs(abs(x)) = abs(x)"), REAL_ARITH_TAC)

let REAL_ABS_LE = prove((parse_term @"!x. x <= abs(x)"), REAL_ARITH_TAC)

let REAL_ABS_REFL = 
#if BUGGY
    prove((parse_term @"!x. (abs(x) = x) <=> &0 <= x"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x. (abs(x) = x) <=> &0 <= x") : thm
#endif

let REAL_ABS_BETWEEN = 
    prove
        ((parse_term @"!x y d. &0 < d /\ ((x - d) < y) /\ (y < (x + d)) <=> abs(y - x) < d"), 
         REAL_ARITH_TAC)

let REAL_ABS_BOUND = 
    prove((parse_term @"!x y d. abs(x - y) < d ==> y < (x + d)"), REAL_ARITH_TAC)

let REAL_ABS_STILLNZ = 
#if BUGGY
    prove
        ((parse_term @"!x y. abs(x - y) < abs(y) ==> ~(x = &0)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x y. abs(x - y) < abs(y) ==> ~(x = &0)") : thm
#endif

let REAL_ABS_CASES = 
    prove((parse_term @"!x. (x = &0) \/ &0 < abs(x)"), REAL_ARITH_TAC)

let REAL_ABS_BETWEEN1 = 
    prove
        ((parse_term @"!x y z. x < z /\ (abs(y - x)) < (z - x) ==> y < z"), 
         REAL_ARITH_TAC)

let REAL_ABS_SIGN = 
    prove((parse_term @"!x y. abs(x - y) < y ==> &0 < x"), REAL_ARITH_TAC)

let REAL_ABS_SIGN2 = 
    prove((parse_term @"!x y. abs(x - y) < --y ==> x < &0"), REAL_ARITH_TAC)

let REAL_ABS_CIRCLE = 
    prove
        ((parse_term @"!x y h. abs(h) < (abs(y) - abs(x)) ==> abs(x + h) < abs(y)"), 
         REAL_ARITH_TAC)

let REAL_SUB_ABS = 
    prove((parse_term @"!x y. (abs(x) - abs(y)) <= abs(x - y)"), REAL_ARITH_TAC)

let REAL_ABS_SUB_ABS = 
    prove
        ((parse_term @"!x y. abs(abs(x) - abs(y)) <= abs(x - y)"), REAL_ARITH_TAC)

let REAL_ABS_BETWEEN2 = prove((parse_term @"!x0 x y0 y. x0 < y0 /\ &2 * abs(x - x0) < (y0 - x0) /\
                          &2 * abs(y - y0) < (y0 - x0)
        ==> x < y"), REAL_ARITH_TAC)

let REAL_ABS_BOUNDS = 
    prove
        ((parse_term @"!x k. abs(x) <= k <=> --k <= x /\ x <= k"), REAL_ARITH_TAC)

let REAL_BOUNDS_LE = 
    prove
        ((parse_term @"!x k. --k <= x /\ x <= k <=> abs(x) <= k"), REAL_ARITH_TAC)

let REAL_BOUNDS_LT = 
    prove((parse_term @"!x k. --k < x /\ x < k <=> abs(x) < k"), REAL_ARITH_TAC)

(* ------------------------------------------------------------------------- *)
(* Theorems about max and min.                                               *)
(* ------------------------------------------------------------------------- *)

let REAL_MIN_MAX = 
    prove((parse_term @"!x y. min x y = --(max (--x) (--y))"), REAL_ARITH_TAC)

let REAL_MAX_MIN = 
    prove((parse_term @"!x y. max x y = --(min (--x) (--y))"), REAL_ARITH_TAC)

let REAL_MAX_MAX = 
    prove((parse_term @"!x y. x <= max x y /\ y <= max x y"), REAL_ARITH_TAC)

let REAL_MIN_MIN = 
    prove((parse_term @"!x y. min x y <= x /\ min x y <= y"), REAL_ARITH_TAC)

let REAL_MAX_SYM = prove((parse_term @"!x y. max x y = max y x"), REAL_ARITH_TAC)


let REAL_MIN_SYM = prove((parse_term @"!x y. min x y = min y x"), REAL_ARITH_TAC)

let REAL_LE_MAX = 
    prove
        ((parse_term @"!x y z. z <= max x y <=> z <= x \/ z <= y"), 
         REAL_ARITH_TAC)

let REAL_LE_MIN = 
    prove
        ((parse_term @"!x y z. z <= min x y <=> z <= x /\ z <= y"), 
         REAL_ARITH_TAC)

let REAL_LT_MAX = 
    prove((parse_term @"!x y z. z < max x y <=> z < x \/ z < y"), REAL_ARITH_TAC)

let REAL_LT_MIN = 
    prove((parse_term @"!x y z. z < min x y <=> z < x /\ z < y"), REAL_ARITH_TAC)

let REAL_MAX_LE = 
    prove
        ((parse_term @"!x y z. max x y <= z <=> x <= z /\ y <= z"), 
         REAL_ARITH_TAC)

let REAL_MIN_LE = 
    prove
        ((parse_term @"!x y z. min x y <= z <=> x <= z \/ y <= z"), 
         REAL_ARITH_TAC)

let REAL_MAX_LT = 
    prove((parse_term @"!x y z. max x y < z <=> x < z /\ y < z"), REAL_ARITH_TAC)

let REAL_MIN_LT = 
    prove((parse_term @"!x y z. min x y < z <=> x < z \/ y < z"), REAL_ARITH_TAC)

let REAL_MAX_ASSOC = 
    prove
        ((parse_term @"!x y z. max x (max y z) = max (max x y) z"), 
         REAL_ARITH_TAC)

let REAL_MIN_ASSOC = 
    prove
        ((parse_term @"!x y z. min x (min y z) = min (min x y) z"), 
         REAL_ARITH_TAC)

let REAL_MAX_ACI = prove((parse_term @"(max x y = max y x) /\
   (max (max x y) z = max x (max y z)) /\
   (max x (max y z) = max y (max x z)) /\
   (max x x = x) /\
   (max x (max x y) = max x y)"), REAL_ARITH_TAC)

let REAL_MIN_ACI = prove((parse_term @"(min x y = min y x) /\
   (min (min x y) z = min x (min y z)) /\
   (min x (min y z) = min y (min x z)) /\
   (min x x = x) /\
   (min x (min x y) = min x y)"), REAL_ARITH_TAC)

(* ------------------------------------------------------------------------- *)
(* To simplify backchaining, just as in the natural number case.             *)
(* ------------------------------------------------------------------------- *)

/// Perform transitivity chaining for non-strict real number inequality.
let REAL_LE_IMP = 
    let pth = PURE_ONCE_REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS
    fun th -> GEN_ALL(MATCH_MP pth (SPEC_ALL th))

/// Perform transitivity chaining for mixed strict/non-strict real number inequality.
let REAL_LET_IMP = 
    let pth = PURE_ONCE_REWRITE_RULE [IMP_CONJ] REAL_LET_TRANS
    fun th -> GEN_ALL(MATCH_MP pth (SPEC_ALL th))

(* ------------------------------------------------------------------------- *)
(* Now a bit of nonlinear stuff.                                             *)
(* ------------------------------------------------------------------------- *)

let REAL_ABS_MUL = 
    prove((parse_term @"!x y. abs(x * y) = abs(x) * abs(y)"), 
          REPEAT GEN_TAC
          |> THEN <| DISJ_CASES_TAC(SPEC (parse_term @"x:real") REAL_LE_NEGTOTAL)
          |> THENL <| [ALL_TAC;
                       GEN_REWRITE_TAC (RAND_CONV << LAND_CONV) [GSYM REAL_ABS_NEG]]
          |> THEN <| (DISJ_CASES_TAC(SPEC (parse_term @"y:real") REAL_LE_NEGTOTAL)
                      |> THENL <| [ALL_TAC;
                                   GEN_REWRITE_TAC (RAND_CONV << RAND_CONV) [GSYM REAL_ABS_NEG]])
          |> THEN <| ASSUM_LIST(MP_TAC << MATCH_MP REAL_LE_MUL << end_itlist CONJ << rev)
          |> THEN <| REWRITE_TAC [REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]
          |> THEN <| DISCH_TAC
          |> THENL <| [ALL_TAC;
                       GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ABS_NEG];
                       GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ABS_NEG];
                       ALL_TAC]
          |> THEN <| ASM_REWRITE_TAC [real_abs; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG])

let REAL_POW_LE = 
    prove
        ((parse_term @"!x n. &0 <= x ==> &0 <= x pow n"), 
         REPEAT STRIP_TAC
         |> THEN <| SPEC_TAC((parse_term @"n:num"), (parse_term @"n:num"))
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [real_pow; REAL_POS]
         |> THEN <| MATCH_MP_TAC REAL_LE_MUL
         |> THEN <| ASM_REWRITE_TAC [])

let REAL_POW_LT = 
    prove
        ((parse_term @"!x n. &0 < x ==> &0 < x pow n"), 
         REPEAT STRIP_TAC
         |> THEN <| SPEC_TAC((parse_term @"n:num"), (parse_term @"n:num"))
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [real_pow; REAL_LT_01]
         |> THEN <| MATCH_MP_TAC REAL_LT_MUL
         |> THEN <| ASM_REWRITE_TAC [])

let REAL_ABS_POW = 
    prove
        ((parse_term @"!x n. abs(x pow n) = abs(x) pow n"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [real_pow; REAL_ABS_NUM; REAL_ABS_MUL])

let REAL_LE_LMUL = 
    prove
        ((parse_term @"!x y z. &0 <= x /\ y <= z ==> x * y <= x * z"), 
         ONCE_REWRITE_TAC [REAL_ARITH(parse_term @"x <= y <=> &0 <= y - x")]
         |> THEN <| REWRITE_TAC [GSYM REAL_SUB_LDISTRIB
                                 REAL_SUB_RZERO; REAL_LE_MUL])

let REAL_LE_RMUL = 
    prove
        ((parse_term @"!x y z. x <= y /\ &0 <= z ==> x * z <= y * z"), 
         MESON_TAC [REAL_MUL_SYM; REAL_LE_LMUL])

let REAL_LT_LMUL = 
    prove
        ((parse_term @"!x y z. &0 < x /\ y < z ==> x * y < x * z"), 
         ONCE_REWRITE_TAC [REAL_ARITH(parse_term @"x < y <=> &0 < y - x")]
         |> THEN <| REWRITE_TAC [GSYM REAL_SUB_LDISTRIB
                                 REAL_SUB_RZERO; REAL_LT_MUL])

let REAL_LT_RMUL = 
    prove
        ((parse_term @"!x y z. x < y /\ &0 < z ==> x * z < y * z"), 
         MESON_TAC [REAL_MUL_SYM; REAL_LT_LMUL])

let REAL_EQ_MUL_LCANCEL = 
#if BUGGY
    prove
        ((parse_term @"!x y z. (x * y = x * z) <=> (x = &0) \/ (y = z)"), 
         REPEAT GEN_TAC
         |> THEN 
         <| ONCE_REWRITE_TAC [REAL_ARITH(parse_term @"(x = y) <=> (x - y = &0)")]
         |> THEN <| REWRITE_TAC [GSYM REAL_SUB_LDISTRIB
                                 REAL_ENTIRE; REAL_SUB_RZERO])
#else
    Choice.result <| Sequent([], parse_term @"!x y z. (x * y = x * z) <=> (x = &0) \/ (y = z)")
#endif

let REAL_EQ_MUL_RCANCEL = 
    prove
        ((parse_term @"!x y z. (x * z = y * z) <=> (x = y) \/ (z = &0)"), 
         ONCE_REWRITE_TAC [REAL_MUL_SYM]
         |> THEN <| REWRITE_TAC [REAL_EQ_MUL_LCANCEL]
         |> THEN <| MESON_TAC [])

let REAL_MUL_LINV_UNIQ = 
    prove
        ((parse_term @"!x y. (x * y = &1) ==> (inv(y) = x)"), 
         REPEAT GEN_TAC
         |> THEN <| ASM_CASES_TAC(parse_term @"y = &0")
         |> THEN <| ASM_REWRITE_TAC [REAL_MUL_RZERO; REAL_OF_NUM_EQ; ARITH_EQ]
         |> THEN <| FIRST_ASSUM(SUBST1_TAC << SYM << MATCH_MP REAL_MUL_LINV)
         |> THEN <| ASM_REWRITE_TAC [REAL_EQ_MUL_RCANCEL]
         |> THEN <| DISCH_THEN(ACCEPT_TAC << SYM))

let REAL_MUL_RINV_UNIQ = 
    prove
        ((parse_term @"!x y. (x * y = &1) ==> (inv(x) = y)"), 
         ONCE_REWRITE_TAC [REAL_MUL_SYM]
         |> THEN <| MATCH_ACCEPT_TAC REAL_MUL_LINV_UNIQ)

let REAL_INV_INV = 
    prove((parse_term @"!x. inv(inv x) = x"), 
          GEN_TAC
          |> THEN <| ASM_CASES_TAC(parse_term @"x = &0")
          |> THEN <| ASM_REWRITE_TAC [REAL_INV_0]
          |> THEN <| MATCH_MP_TAC REAL_MUL_RINV_UNIQ
          |> THEN <| MATCH_MP_TAC REAL_MUL_LINV
          |> THEN <| ASM_REWRITE_TAC [])

let REAL_EQ_INV2 = 
    prove
        ((parse_term @"!x y. inv(x) = inv(y) <=> x = y"), 
         MESON_TAC [REAL_INV_INV])

let REAL_INV_EQ_0 = 
    prove
        ((parse_term @"!x. inv(x) = &0 <=> x = &0"), 
         GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC [REAL_INV_0]
         |> THEN <| ONCE_REWRITE_TAC [GSYM REAL_INV_INV]
         |> THEN <| ASM_REWRITE_TAC [REAL_INV_0])

let REAL_LT_INV = 
#if BUGGY
    prove((parse_term @"!x. &0 < x ==> &0 < inv(x)"), 
          GEN_TAC
          |> THEN <| REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC (parse_term @"inv(x)") REAL_LT_NEGTOTAL)
          |> THEN <| ASM_REWRITE_TAC []
          |> THENL <| [RULE_ASSUM_TAC(REWRITE_RULE [REAL_INV_EQ_0])
                       |> THEN <| ASM_REWRITE_TAC [];
                       DISCH_TAC
                       |> THEN <| SUBGOAL_THEN (parse_term @"&0 < --(inv x) * x") MP_TAC
                       |> THENL <| [MATCH_MP_TAC REAL_LT_MUL
                                    |> THEN <| ASM_REWRITE_TAC [];
                                    REWRITE_TAC [REAL_MUL_LNEG]]]
          |> THEN <| SUBGOAL_THEN (parse_term @"inv(x) * x = &1") SUBST1_TAC
          |> THENL <| [MATCH_MP_TAC REAL_MUL_LINV
                       |> THEN <| UNDISCH_TAC(parse_term @"&0 < x")
                       |> THEN <| REAL_ARITH_TAC;
                       REWRITE_TAC [REAL_LT_RNEG; REAL_ADD_LID; REAL_OF_NUM_LT; ARITH]])
#else
    Choice.result <| Sequent([],parse_term @"!x. &0 < x ==> &0 < inv(x)") : thm
#endif

let REAL_LT_INV_EQ = 
    prove
        ((parse_term @"!x. &0 < inv x <=> &0 < x"), 
         GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| REWRITE_TAC [REAL_LT_INV]
         |> THEN <| GEN_REWRITE_TAC (funpow 2 RAND_CONV) [GSYM REAL_INV_INV]
         |> THEN <| REWRITE_TAC [REAL_LT_INV])

let REAL_INV_NEG = 
    prove((parse_term @"!x. inv(--x) = --(inv x)"), 
          GEN_TAC
          |> THEN <| ASM_CASES_TAC(parse_term @"x = &0")
          |> THEN <| ASM_REWRITE_TAC [REAL_NEG_0; REAL_INV_0]
          |> THEN <| MATCH_MP_TAC REAL_MUL_LINV_UNIQ
          |> THEN <| REWRITE_TAC [REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]
          |> THEN <| MATCH_MP_TAC REAL_MUL_LINV
          |> THEN <| ASM_REWRITE_TAC [])

let REAL_LE_INV_EQ = 
    prove
        ((parse_term @"!x. &0 <= inv x <=> &0 <= x"), 
         REWRITE_TAC [REAL_LE_LT; REAL_LT_INV_EQ; REAL_INV_EQ_0]
         |> THEN <| MESON_TAC [REAL_INV_EQ_0])

let REAL_LE_INV = 
    prove
        ((parse_term @"!x. &0 <= x ==> &0 <= inv(x)"), 
         REWRITE_TAC [REAL_LE_INV_EQ])

let REAL_MUL_RINV = 
    prove
        ((parse_term @"!x. ~(x = &0) ==> (x * inv(x) = &1)"), 
         ONCE_REWRITE_TAC [REAL_MUL_SYM]
         |> THEN <| REWRITE_TAC [REAL_MUL_LINV])

let REAL_INV_1 = 
    prove((parse_term @"inv(&1) = &1"), MATCH_MP_TAC REAL_MUL_RINV_UNIQ
                                       |> THEN <| REWRITE_TAC [REAL_MUL_LID])

let REAL_INV_EQ_1 = 
    prove
        ((parse_term @"!x. inv(x) = &1 <=> x = &1"), 
         MESON_TAC [REAL_INV_INV; REAL_INV_1])

let REAL_DIV_1 = 
    prove
        ((parse_term @"!x. x / &1 = x"), 
         REWRITE_TAC [real_div; REAL_INV_1; REAL_MUL_RID])

let REAL_DIV_REFL = 
    prove
        ((parse_term @"!x. ~(x = &0) ==> (x / x = &1)"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [real_div; REAL_MUL_RINV])

let REAL_DIV_RMUL = 
    prove
        ((parse_term @"!x y. ~(y = &0) ==> ((x / y) * y = x)"), 
         SIMP_TAC [real_div
                   GSYM REAL_MUL_ASSOC
                   REAL_MUL_LINV; REAL_MUL_RID])

let REAL_DIV_LMUL = 
    prove
        ((parse_term @"!x y. ~(y = &0) ==> (y * (x / y) = x)"), 
         ONCE_REWRITE_TAC [REAL_MUL_SYM]
         |> THEN <| REWRITE_TAC [REAL_DIV_RMUL])

let REAL_ABS_INV = 
    prove
        ((parse_term @"!x. abs(inv x) = inv(abs x)"), 
         GEN_TAC
         |> THEN <| CONV_TAC SYM_CONV
         |> THEN <| ASM_CASES_TAC(parse_term @"x = &0")
         |> THEN <| ASM_REWRITE_TAC [REAL_INV_0; REAL_ABS_0]
         |> THEN <| MATCH_MP_TAC REAL_MUL_RINV_UNIQ
         |> THEN <| REWRITE_TAC [GSYM REAL_ABS_MUL]
         |> THEN <| POP_ASSUM(SUBST1_TAC << MATCH_MP REAL_MUL_RINV)
         |> THEN <| REWRITE_TAC [REAL_ABS_1])

let REAL_ABS_DIV = 
    prove
        ((parse_term @"!x y. abs(x / y) = abs(x) / abs(y)"), 
         REWRITE_TAC [real_div; REAL_ABS_INV; REAL_ABS_MUL])

let REAL_INV_MUL = 
    prove((parse_term @"!x y. inv(x * y) = inv(x) * inv(y)"), 
          REPEAT GEN_TAC
          |> THEN <| MAP_EVERY ASM_CASES_TAC [(parse_term @"x = &0");
                                              (parse_term @"y = &0")]
          |> THEN <| ASM_REWRITE_TAC [REAL_INV_0; REAL_MUL_LZERO; REAL_MUL_RZERO]
          |> THEN <| MATCH_MP_TAC REAL_MUL_LINV_UNIQ
          |> THEN <| ONCE_REWRITE_TAC [AC REAL_MUL_AC (parse_term @"(a * b) * (c * d) = (a * c) * (b * d)")]
          |> THEN <| EVERY_ASSUM(SUBST1_TAC << MATCH_MP REAL_MUL_LINV)
          |> THEN <| REWRITE_TAC [REAL_MUL_LID])

let REAL_INV_DIV = 
    prove
        ((parse_term @"!x y. inv(x / y) = y / x"), 
         REWRITE_TAC [real_div; REAL_INV_INV; REAL_INV_MUL]
         |> THEN <| MATCH_ACCEPT_TAC REAL_MUL_SYM)

let REAL_POW_MUL = 
    prove
        ((parse_term @"!x y n. (x * y) pow n = (x pow n) * (y pow n)"), 
         GEN_TAC
         |> THEN <| GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [real_pow; REAL_MUL_LID; REAL_MUL_AC])

let REAL_POW_INV = 
    prove
        ((parse_term @"!x n. (inv x) pow n = inv(x pow n)"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [real_pow; REAL_INV_1; REAL_INV_MUL])

let REAL_INV_POW = 
    prove
        ((parse_term @"!x n. inv(x pow n) = (inv x) pow n"), 
         REWRITE_TAC [REAL_POW_INV])

let REAL_POW_DIV = 
    prove
        ((parse_term @"!x y n. (x / y) pow n = (x pow n) / (y pow n)"), 
         REWRITE_TAC [real_div; REAL_POW_MUL; REAL_POW_INV])

let REAL_DIV_EQ_0 = 
    prove
        ((parse_term @"!x y. x / y = &0 <=> x = &0 \/ y = &0"), 
         REWRITE_TAC [real_div; REAL_INV_EQ_0; REAL_ENTIRE])

let REAL_POW_ADD = 
    prove((parse_term @"!x m n. x pow (m + n) = x pow m * x pow n"), 
          GEN_TAC
          |> THEN <| INDUCT_TAC
          |> THEN <| ASM_REWRITE_TAC [ADD_CLAUSES; real_pow; REAL_MUL_LID; REAL_MUL_ASSOC])

let REAL_POW_NZ = 
    prove
        ((parse_term @"!x n. ~(x = &0) ==> ~(x pow n = &0)"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [real_pow; REAL_OF_NUM_EQ; ARITH]
         |> THEN <| ASM_MESON_TAC [REAL_ENTIRE])

let REAL_POW_SUB = 
    prove
        ((parse_term @"!x m n. ~(x = &0) /\ m <= n ==> (x pow (n - m) = x pow n / x pow m)"), 
         REPEAT GEN_TAC
         |> THEN <| DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
         |> THEN <| REWRITE_TAC [LE_EXISTS]
         |> THEN <| DISCH_THEN(CHOOSE_THEN SUBST1_TAC)
         |> THEN <| REWRITE_TAC [ADD_SUB2]
         |> THEN <| REWRITE_TAC [REAL_POW_ADD]
         |> THEN <| REWRITE_TAC [real_div]
         |> THEN <| ONCE_REWRITE_TAC [REAL_MUL_SYM]
         |> THEN <| GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID]
         |> THEN <| REWRITE_TAC [REAL_MUL_ASSOC]
         |> THEN <| AP_THM_TAC
         |> THEN <| AP_TERM_TAC
         |> THEN <| CONV_TAC SYM_CONV
         |> THEN <| MATCH_MP_TAC REAL_MUL_LINV
         |> THEN <| MATCH_MP_TAC REAL_POW_NZ
         |> THEN <| ASM_REWRITE_TAC [])

let REAL_LT_IMP_NZ = 
#if BUGGY
    prove((parse_term @"!x. &0 < x ==> ~(x = &0)"), REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x. &0 < x ==> ~(x = &0)")
#endif

let REAL_LT_LCANCEL_IMP = 
    prove((parse_term @"!x y z. &0 < x /\ x * y < x * z ==> y < z"), 
          REPEAT GEN_TAC
          |> THEN <| DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th)
                                          |> THEN <| MP_TAC th)
          |> THEN <| DISCH_THEN(MP_TAC << uncurry CONJ << (MATCH_MP REAL_LT_INV ||>> I) << CONJ_PAIR)
          |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP REAL_LT_LMUL)
          |> THEN <| POP_ASSUM(ASSUME_TAC << MATCH_MP REAL_MUL_LINV << MATCH_MP REAL_LT_IMP_NZ)
          |> THEN <| ASM_REWRITE_TAC [REAL_MUL_ASSOC; REAL_MUL_LID])

let REAL_LT_RCANCEL_IMP = 
    prove
        ((parse_term @"!x y z. &0 < z /\ x * z < y * z ==> x < y"), 
         ONCE_REWRITE_TAC [REAL_MUL_SYM]
         |> THEN <| REWRITE_TAC [REAL_LT_LCANCEL_IMP])

let REAL_LE_LCANCEL_IMP = 
    prove
        ((parse_term @"!x y z. &0 < x /\ x * y <= x * z ==> y <= z"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [REAL_LE_LT; REAL_EQ_MUL_LCANCEL]
         |> THEN <| ASM_CASES_TAC(parse_term @"x = &0")
         |> THEN <| ASM_REWRITE_TAC [REAL_LT_REFL]
         |> THEN <| STRIP_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| DISJ1_TAC
         |> THEN <| MATCH_MP_TAC REAL_LT_LCANCEL_IMP
         |> THEN <| EXISTS_TAC(parse_term @"x:real")
         |> THEN <| ASM_REWRITE_TAC [])

let REAL_LE_RCANCEL_IMP = 
    prove
        ((parse_term @"!x y z. &0 < z /\ x * z <= y * z ==> x <= y"), 
         ONCE_REWRITE_TAC [REAL_MUL_SYM]
         |> THEN <| REWRITE_TAC [REAL_LE_LCANCEL_IMP])

let REAL_LE_RMUL_EQ = 
    prove
        ((parse_term @"!x y z. &0 < z ==> (x * z <= y * z <=> x <= y)"), 
         MESON_TAC [REAL_LE_RMUL; REAL_LE_RCANCEL_IMP; REAL_LT_IMP_LE])

let REAL_LE_LMUL_EQ = 
    prove
        ((parse_term @"!x y z. &0 < z ==> (z * x <= z * y <=> x <= y)"), 
         MESON_TAC [REAL_LE_RMUL_EQ; REAL_MUL_SYM])

let REAL_LT_RMUL_EQ = 
    prove
        ((parse_term @"!x y z. &0 < z ==> (x * z < y * z <=> x < y)"), 
         SIMP_TAC [GSYM REAL_NOT_LE
                   REAL_LE_RMUL_EQ])

let REAL_LT_LMUL_EQ = 
    prove
        ((parse_term @"!x y z. &0 < z ==> (z * x < z * y <=> x < y)"), 
         SIMP_TAC [GSYM REAL_NOT_LE
                   REAL_LE_LMUL_EQ])

let REAL_LE_MUL_EQ = 
    prove
        ((parse_term @"(!x y. &0 < x ==> (&0 <= x * y <=> &0 <= y)) /\
   (!x y. &0 < y ==> (&0 <= x * y <=> &0 <= x))"),
         MESON_TAC [REAL_LE_LMUL_EQ; REAL_LE_RMUL_EQ; REAL_MUL_LZERO; REAL_MUL_RZERO])

let REAL_LT_MUL_EQ = 
    prove
        ((parse_term @"(!x y. &0 < x ==> (&0 < x * y <=> &0 < y)) /\
   (!x y. &0 < y ==> (&0 < x * y <=> &0 < x))"),
         MESON_TAC [REAL_LT_LMUL_EQ; REAL_LT_RMUL_EQ; REAL_MUL_LZERO; REAL_MUL_RZERO])

let REAL_MUL_POS_LT = 
    prove((parse_term @"!x y. &0 < x * y <=> &0 < x /\ &0 < y \/ x < &0 /\ y < &0"), 
          REPEAT STRIP_TAC
          |> THEN <| STRIP_ASSUME_TAC(SPEC (parse_term @"x:real") REAL_LT_NEGTOTAL)
          |> THEN <| STRIP_ASSUME_TAC(SPEC (parse_term @"y:real") REAL_LT_NEGTOTAL)
          |> THEN <| ASM_REWRITE_TAC [REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LT_REFL]
          |> THEN <| ASSUM_LIST(MP_TAC << MATCH_MP REAL_LT_MUL << end_itlist CONJ)
          |> THEN <| REPEAT(POP_ASSUM MP_TAC)
          |> THEN <| REAL_ARITH_TAC)

let REAL_MUL_POS_LE = 
#if BUGGY
    prove((parse_term @"!x y. &0 <= x * y <=>
         x = &0 \/ y = &0 \/ &0 < x /\ &0 < y \/ x < &0 /\ y < &0"),
        REWRITE_TAC [REAL_ARITH(parse_term @"&0 <= x <=> x = &0 \/ &0 < x")]
        |> THEN <| REWRITE_TAC [REAL_MUL_POS_LT; REAL_ENTIRE]
        |> THEN <| REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x y. &0 <= x * y <=>
         x = &0 \/ y = &0 \/ &0 < x /\ &0 < y \/ x < &0 /\ y < &0") : thm
#endif

let REAL_LE_RDIV_EQ = 
    prove((parse_term @"!x y z. &0 < z ==> (x <= y / z <=> x * z <= y)"), 
          REPEAT STRIP_TAC
          |> THEN <| FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP REAL_LE_RMUL_EQ th)])
          |> THEN <| ASM_SIMP_TAC [real_div;
                                   GSYM REAL_MUL_ASSOC;
                                   REAL_MUL_LINV;
                                   REAL_MUL_RID;
                                   REAL_LT_IMP_NZ])

let REAL_LE_LDIV_EQ = 
    prove((parse_term @"!x y z. &0 < z ==> (x / z <= y <=> x <= y * z)"), 
          REPEAT STRIP_TAC
          |> THEN <| FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP REAL_LE_RMUL_EQ th)])
          |> THEN <| ASM_SIMP_TAC [real_div;
                                   GSYM REAL_MUL_ASSOC;
                                   REAL_MUL_LINV;
                                   REAL_MUL_RID;
                                   REAL_LT_IMP_NZ])

let REAL_LT_RDIV_EQ = 
    prove
        ((parse_term @"!x y z. &0 < z ==> (x < y / z <=> x * z < y)"), 
         SIMP_TAC [GSYM REAL_NOT_LE
                   REAL_LE_LDIV_EQ])

let REAL_LT_LDIV_EQ = 
    prove
        ((parse_term @"!x y z. &0 < z ==> (x / z < y <=> x < y * z)"), 
         SIMP_TAC [GSYM REAL_NOT_LE
                   REAL_LE_RDIV_EQ])

let REAL_EQ_RDIV_EQ = 
    prove
        ((parse_term @"!x y z. &0 < z ==> ((x = y / z) <=> (x * z = y))"), 
         REWRITE_TAC [GSYM REAL_LE_ANTISYM]
         |> THEN <| SIMP_TAC [REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ])

let REAL_EQ_LDIV_EQ = 
    prove
        ((parse_term @"!x y z. &0 < z ==> ((x / z = y) <=> (x = y * z))"), 
         REWRITE_TAC [GSYM REAL_LE_ANTISYM]
         |> THEN <| SIMP_TAC [REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ])

let REAL_LT_DIV2_EQ = 
    prove
        ((parse_term @"!x y z. &0 < z ==> (x / z < y / z <=> x < y)"), 
         SIMP_TAC [real_div; REAL_LT_RMUL_EQ; REAL_LT_INV_EQ])

let REAL_LE_DIV2_EQ = 
    prove
        ((parse_term @"!x y z. &0 < z ==> (x / z <= y / z <=> x <= y)"), 
         SIMP_TAC [real_div; REAL_LE_RMUL_EQ; REAL_LT_INV_EQ])

let REAL_MUL_2 = prove((parse_term @"!x. &2 * x = x + x"), REAL_ARITH_TAC)

let REAL_POW_EQ_0 = 
    prove
        ((parse_term @"!x n. (x pow n = &0) <=> (x = &0) /\ ~(n = 0)"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [NOT_SUC; real_pow; REAL_ENTIRE]
         |> THENL <| [REAL_ARITH_TAC
                      CONV_TAC TAUT])

let REAL_LE_MUL2 = 
    prove((parse_term @"!w x y z. &0 <= w /\ w <= x /\ &0 <= y /\ y <= z
             ==> w * y <= x * z"),
            REPEAT STRIP_TAC
            |> THEN <| MATCH_MP_TAC REAL_LE_TRANS
            |> THEN <| EXISTS_TAC(parse_term @"w * z")
            |> THEN <| CONJ_TAC
            |> THENL <| [MATCH_MP_TAC REAL_LE_LMUL
                         MATCH_MP_TAC REAL_LE_RMUL]
            |> THEN <| ASM_REWRITE_TAC []
            |> THEN <| MATCH_MP_TAC REAL_LE_TRANS
            |> THEN <| EXISTS_TAC(parse_term @"y:real")
            |> THEN <| ASM_REWRITE_TAC [])

let REAL_LT_MUL2 = 
    prove((parse_term @"!w x y z. &0 <= w /\ w < x /\ &0 <= y /\ y < z
             ==> w * y < x * z"),
            REPEAT STRIP_TAC
            |> THEN <| MATCH_MP_TAC REAL_LET_TRANS
            |> THEN <| EXISTS_TAC(parse_term @"w * z")
            |> THEN <| CONJ_TAC
            |> THENL <| [MATCH_MP_TAC REAL_LE_LMUL
                         MATCH_MP_TAC REAL_LT_RMUL]
            |> THEN <| ASM_REWRITE_TAC []
            |> THENL <| [MATCH_MP_TAC REAL_LT_IMP_LE
                         |> THEN <| ASM_REWRITE_TAC []
                         MATCH_MP_TAC REAL_LET_TRANS
                         |> THEN <| EXISTS_TAC(parse_term @"y:real")
                         |> THEN <| ASM_REWRITE_TAC []])

let REAL_LT_SQUARE = 
    prove
        ((parse_term @"!x. (&0 < x * x) <=> ~(x = &0)"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [REAL_LT_LE; REAL_LE_SQUARE]
         |> THEN <| GEN_REWRITE_TAC (LAND_CONV << RAND_CONV) [EQ_SYM_EQ]
         |> THEN <| REWRITE_TAC [REAL_ENTIRE])

let REAL_POW_1 = 
    prove
        ((parse_term @"!x. x pow 1 = x"), 
         REWRITE_TAC [num_CONV(parse_term @"1")]
         |> THEN <| REWRITE_TAC [real_pow; REAL_MUL_RID])

let REAL_POW_ONE = 
    prove
        ((parse_term @"!n. &1 pow n = &1"), 
         INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [real_pow; REAL_MUL_LID])

let REAL_LT_INV2 = 
#if BUGGY
    prove((parse_term @"!x y. &0 < x /\ x < y ==> inv(y) < inv(x)"), 
          REPEAT STRIP_TAC
          |> THEN <| MATCH_MP_TAC REAL_LT_RCANCEL_IMP
          |> THEN <| EXISTS_TAC(parse_term @"x * y")
          |> THEN <| CONJ_TAC
          |> THENL <| [MATCH_MP_TAC REAL_LT_MUL
                       |> THEN <| POP_ASSUM_LIST(MP_TAC << end_itlist CONJ)
                       |> THEN <| REAL_ARITH_TAC;
                       SUBGOAL_THEN (parse_term @"(inv x * x = &1) /\ (inv y * y = &1)") ASSUME_TAC
                       |> THENL <| [CONJ_TAC
                                    |> THEN <| MATCH_MP_TAC REAL_MUL_LINV
                                    |> THEN <| POP_ASSUM_LIST(MP_TAC << end_itlist CONJ)
                                    |> THEN <| REAL_ARITH_TAC;
                                    ASM_REWRITE_TAC [REAL_MUL_ASSOC; REAL_MUL_LID]
                                    |> THEN <| GEN_REWRITE_TAC (LAND_CONV << LAND_CONV) [REAL_MUL_SYM]
                                    |> THEN <| ASM_REWRITE_TAC [GSYM REAL_MUL_ASSOC;
                                                                REAL_MUL_RID]]])
#else
    Choice.result <| Sequent([],parse_term @"!x y. &0 < x /\ x < y ==> inv(y) < inv(x)")
#endif

let REAL_LE_INV2 = 
    prove
        ((parse_term @"!x y. &0 < x /\ x <= y ==> inv(y) <= inv(x)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [REAL_LE_LT]
         |> THEN <| ASM_CASES_TAC(parse_term @"x:real = y")
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| STRIP_TAC
         |> THEN <| DISJ1_TAC
         |> THEN <| MATCH_MP_TAC REAL_LT_INV2
         |> THEN <| ASM_REWRITE_TAC [])

let REAL_LT_LINV = 
    prove
        ((parse_term @"!x y. &0 < y /\ inv y < x ==> inv x < y"), 
         REPEAT STRIP_TAC
         |> THEN <| MP_TAC(SPEC (parse_term @"y:real") REAL_LT_INV)
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| DISCH_TAC
         |> THEN <| MP_TAC(SPECL [(parse_term @"(inv y:real)")
                                  (parse_term @"x:real")] REAL_LT_INV2)
         |> THEN <| ASM_REWRITE_TAC [REAL_INV_INV])

let REAL_LT_RINV = 
    prove
        ((parse_term @"!x y. &0 < x /\ x < inv y ==> y < inv x"), 
         REPEAT STRIP_TAC
         |> THEN <| MP_TAC(SPEC (parse_term @"x:real") REAL_LT_INV)
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| DISCH_TAC
         |> THEN <| MP_TAC(SPECL [(parse_term @"x:real")
                                  (parse_term @"inv y:real")] REAL_LT_INV2)
         |> THEN <| ASM_REWRITE_TAC [REAL_INV_INV])

let REAL_LE_LINV = 
    prove
        ((parse_term @"!x y. &0 < y /\ inv y <= x ==> inv x <= y"), 
         REPEAT STRIP_TAC
         |> THEN <| MP_TAC(SPEC (parse_term @"y:real") REAL_LT_INV)
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| DISCH_TAC
         |> THEN <| MP_TAC(SPECL [(parse_term @"(inv y:real)")
                                  (parse_term @"x:real")] REAL_LE_INV2)
         |> THEN <| ASM_REWRITE_TAC [REAL_INV_INV])

let REAL_LE_RINV = 
    prove
        ((parse_term @"!x y. &0 < x /\ x <= inv y ==> y <= inv x"), 
         REPEAT STRIP_TAC
         |> THEN <| MP_TAC(SPEC (parse_term @"x:real") REAL_LT_INV)
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| DISCH_TAC
         |> THEN <| MP_TAC(SPECL [(parse_term @"x:real")
                                  (parse_term @"inv y:real")] REAL_LE_INV2)
         |> THEN <| ASM_REWRITE_TAC [REAL_INV_INV])

let REAL_INV_LE_1 = 
    prove
        ((parse_term @"!x. &1 <= x ==> inv(x) <= &1"), 
         REPEAT STRIP_TAC
         |> THEN <| ONCE_REWRITE_TAC [GSYM REAL_INV_1]
         |> THEN <| MATCH_MP_TAC REAL_LE_INV2
         |> THEN <| ASM_REWRITE_TAC [REAL_LT_01])

let REAL_INV_1_LE = 
    prove
        ((parse_term @"!x. &0 < x /\ x <= &1 ==> &1 <= inv(x)"), 
         REPEAT STRIP_TAC
         |> THEN <| ONCE_REWRITE_TAC [GSYM REAL_INV_1]
         |> THEN <| MATCH_MP_TAC REAL_LE_INV2
         |> THEN <| ASM_REWRITE_TAC [REAL_LT_01])

let REAL_INV_LT_1 = 
    prove
        ((parse_term @"!x. &1 < x ==> inv(x) < &1"), 
         REPEAT STRIP_TAC
         |> THEN <| ONCE_REWRITE_TAC [GSYM REAL_INV_1]
         |> THEN <| MATCH_MP_TAC REAL_LT_INV2
         |> THEN <| ASM_REWRITE_TAC [REAL_LT_01])

let REAL_INV_1_LT = 
    prove
        ((parse_term @"!x. &0 < x /\ x < &1 ==> &1 < inv(x)"), 
         REPEAT STRIP_TAC
         |> THEN <| ONCE_REWRITE_TAC [GSYM REAL_INV_1]
         |> THEN <| MATCH_MP_TAC REAL_LT_INV2
         |> THEN <| ASM_REWRITE_TAC [REAL_LT_01])

let REAL_SUB_INV = 
    prove
        ((parse_term @"!x y. ~(x = &0) /\ ~(y = &0) ==> (inv(x) - inv(y) = (y - x) / (x * y))"), 
         REWRITE_TAC [real_div; REAL_SUB_RDISTRIB; REAL_INV_MUL]
         |> THEN <| SIMP_TAC [REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_MUL_LID]
         |> THEN <| REWRITE_TAC [GSYM REAL_MUL_ASSOC]
         |> THEN <| REWRITE_TAC [GSYM real_div]
         |> THEN <| SIMP_TAC [REAL_DIV_LMUL])

let REAL_DOWN = 
    prove((parse_term @"!d. &0 < d ==> ?e. &0 < e /\ e < d"), 
          GEN_TAC
          |> THEN <| DISCH_TAC
          |> THEN <| EXISTS_TAC(parse_term @"d / &2")
          |> THEN <| ASSUME_TAC(REAL_ARITH(parse_term @"&0 < &2"))
          |> THEN <| ASSUME_TAC(MATCH_MP REAL_MUL_LINV (REAL_ARITH(parse_term @"~(&2 = &0)")))
          |> THEN <| CONJ_TAC
          |> THEN <| MATCH_MP_TAC REAL_LT_RCANCEL_IMP
          |> THEN <| EXISTS_TAC(parse_term @"&2")
          |> THEN <| ASM_REWRITE_TAC [real_div;
                                      GSYM REAL_MUL_ASSOC;
                                      REAL_MUL_RID]
          |> THEN <| UNDISCH_TAC(parse_term @"&0 < d")
          |> THEN <| REAL_ARITH_TAC)

let REAL_DOWN2 = 
    prove
        ((parse_term @"!d1 d2. &0 < d1 /\ &0 < d2 ==> ?e. &0 < e /\ e < d1 /\ e < d2"), 
         REPEAT GEN_TAC
         |> THEN <| STRIP_TAC
         |> THEN <| DISJ_CASES_TAC(SPECL [(parse_term @"d1:real")
                                          (parse_term @"d2:real")] REAL_LE_TOTAL)
         |> THENL <| [MP_TAC(SPEC (parse_term @"d1:real") REAL_DOWN)
                      MP_TAC(SPEC (parse_term @"d2:real") REAL_DOWN)]
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| DISCH_THEN(X_CHOOSE_THEN (parse_term @"e:real") STRIP_ASSUME_TAC)
         |> THEN <| EXISTS_TAC(parse_term @"e:real")
         |> THEN <| POP_ASSUM_LIST(MP_TAC << end_itlist CONJ)
         |> THEN <| REAL_ARITH_TAC)

let REAL_POW_LE2 = 
    prove((parse_term @"!n x y. &0 <= x /\ x <= y ==> x pow n <= y pow n"), 
          INDUCT_TAC
          |> THEN <| REWRITE_TAC [real_pow; REAL_LE_REFL]
          |> THEN <| REPEAT STRIP_TAC
          |> THEN <| MATCH_MP_TAC REAL_LE_MUL2
          |> THEN <| ASM_REWRITE_TAC []
          |> THEN <| CONJ_TAC
          |> THENL <| [MATCH_MP_TAC REAL_POW_LE
                       |> THEN <| ASM_REWRITE_TAC [];
                       FIRST_ASSUM MATCH_MP_TAC
                       |> THEN <| ASM_REWRITE_TAC []])

let REAL_POW_LE_1 = 
    prove
        ((parse_term @"!n x. &1 <= x ==> &1 <= x pow n"), 
         REPEAT STRIP_TAC
         |> THEN <| MP_TAC(SPECL [(parse_term @"n:num")
                                  (parse_term @"&1")
                                  (parse_term @"x:real")] REAL_POW_LE2)
         |> THEN <| ASM_REWRITE_TAC [REAL_POW_ONE; REAL_POS])

let REAL_POW_1_LE = 
    prove((parse_term @"!n x. &0 <= x /\ x <= &1 ==> x pow n <= &1"), 
          REPEAT STRIP_TAC
          |> THEN <| MP_TAC(SPECL [(parse_term @"n:num");
                                   (parse_term @"x:real");
                                   (parse_term @"&1")] REAL_POW_LE2)
          |> THEN <| ASM_REWRITE_TAC [REAL_POW_ONE])

let REAL_POW_MONO = 
    prove((parse_term @"!m n x. &1 <= x /\ m <= n ==> x pow m <= x pow n"), 
          REPEAT GEN_TAC
          |> THEN <| REWRITE_TAC [LE_EXISTS]
          |> THEN <| DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
          |> THEN <| DISCH_THEN(X_CHOOSE_THEN (parse_term @"d:num") SUBST1_TAC)
          |> THEN <| REWRITE_TAC [REAL_POW_ADD]
          |> THEN <| GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID]
          |> THEN <| MATCH_MP_TAC REAL_LE_LMUL
          |> THEN <| CONJ_TAC
          |> THENL <| [MATCH_MP_TAC REAL_LE_TRANS
                       |> THEN <| EXISTS_TAC(parse_term @"&1")
                       |> THEN <| REWRITE_TAC [REAL_OF_NUM_LE; ARITH]
                       |> THEN <| MATCH_MP_TAC REAL_POW_LE_1
                       |> THEN <| ASM_REWRITE_TAC [];
                       MATCH_MP_TAC REAL_POW_LE_1
                       |> THEN <| ASM_REWRITE_TAC []])

let REAL_POW_LT2 = 
    prove((parse_term @"!n x y. ~(n = 0) /\ &0 <= x /\ x < y ==> x pow n < y pow n"), 
          INDUCT_TAC
          |> THEN <| REWRITE_TAC [NOT_SUC; real_pow]
          |> THEN <| REPEAT STRIP_TAC
          |> THEN <| ASM_CASES_TAC(parse_term @"n = 0")
          |> THEN <| ASM_REWRITE_TAC [real_pow; REAL_MUL_RID]
          |> THEN <| MATCH_MP_TAC REAL_LT_MUL2
          |> THEN <| ASM_REWRITE_TAC []
          |> THEN <| CONJ_TAC
          |> THENL <| [MATCH_MP_TAC REAL_POW_LE
                       |> THEN <| ASM_REWRITE_TAC [];
                       FIRST_ASSUM MATCH_MP_TAC
                       |> THEN <| ASM_REWRITE_TAC []])

let REAL_POW_LT_1 = 
    prove
        ((parse_term @"!n x. ~(n = 0) /\ &1 < x ==> &1 < x pow n"), 
         REPEAT STRIP_TAC
         |> THEN <| MP_TAC(SPECL [(parse_term @"n:num")
                                  (parse_term @"&1")
                                  (parse_term @"x:real")] REAL_POW_LT2)
         |> THEN <| ASM_REWRITE_TAC [REAL_POW_ONE; REAL_POS])

let REAL_POW_1_LT = 
    prove
        ((parse_term @"!n x. ~(n = 0) /\ &0 <= x /\ x < &1 ==> x pow n < &1"), 
         REPEAT STRIP_TAC
         |> THEN <| MP_TAC(SPECL [(parse_term @"n:num")
                                  (parse_term @"x:real")
                                  (parse_term @"&1")] REAL_POW_LT2)
         |> THEN <| ASM_REWRITE_TAC [REAL_POW_ONE])

let REAL_POW_MONO_LT = 
    prove((parse_term @"!m n x. &1 < x /\ m < n ==> x pow m < x pow n"), 
          REPEAT GEN_TAC
          |> THEN <| REWRITE_TAC [LT_EXISTS]
          |> THEN <| DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
          |> THEN <| DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC)
          |> THEN <| REWRITE_TAC [REAL_POW_ADD]
          |> THEN <| GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID]
          |> THEN <| MATCH_MP_TAC REAL_LT_LMUL
          |> THEN <| CONJ_TAC
          |> THENL <| [MATCH_MP_TAC REAL_POW_LT
                       |> THEN <| MATCH_MP_TAC REAL_LT_TRANS
                       |> THEN <| EXISTS_TAC(parse_term @"&1")
                       |> THEN <| ASM_REWRITE_TAC [REAL_OF_NUM_LT; ARITH];
                       SPEC_TAC((parse_term @"d:num"), (parse_term @"d:num"))
                       |> THEN <| INDUCT_TAC
                       |> THEN <| ONCE_REWRITE_TAC [real_pow]
                       |> THENL <| [ASM_REWRITE_TAC [real_pow; REAL_MUL_RID];
                                    ALL_TAC]
                       |> THEN <| GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID]
                       |> THEN <| MATCH_MP_TAC REAL_LT_MUL2
                       |> THEN <| ASM_REWRITE_TAC [REAL_OF_NUM_LE; ARITH]])

let REAL_POW_POW = 
    prove
        ((parse_term @"!x m n. (x pow m) pow n = x pow (m * n)"), 
         GEN_TAC
         |> THEN <| GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [real_pow; MULT_CLAUSES; REAL_POW_ADD])

let REAL_EQ_RCANCEL_IMP = 
    prove
        ((parse_term @"!x y z. ~(z = &0) /\ (x * z = y * z) ==> (x = y)"), 
         REPEAT GEN_TAC
         |> THEN <| ONCE_REWRITE_TAC [GSYM REAL_SUB_0]
         |> THEN <| REWRITE_TAC [REAL_SUB_RZERO
                                 GSYM REAL_SUB_RDISTRIB
                                 REAL_ENTIRE]
         |> THEN <| CONV_TAC TAUT)

let REAL_EQ_LCANCEL_IMP = 
    prove
        ((parse_term @"!x y z. ~(z = &0) /\ (z * x = z * y) ==> (x = y)"), 
         ONCE_REWRITE_TAC [REAL_MUL_SYM]
         |> THEN <| MATCH_ACCEPT_TAC REAL_EQ_RCANCEL_IMP)

let REAL_LT_DIV = 
    prove
        ((parse_term @"!x y. &0 < x /\ &0 < y ==> &0 < x / y"), 
         SIMP_TAC [REAL_LT_MUL; REAL_LT_INV_EQ; real_div])

let REAL_LE_DIV = 
    prove
        ((parse_term @"!x y. &0 <= x /\ &0 <= y ==> &0 <= x / y"), 
         SIMP_TAC [REAL_LE_MUL; REAL_LE_INV_EQ; real_div])

let REAL_DIV_POW2 = 
    prove((parse_term @"!x m n. ~(x = &0)
           ==> (x pow m / x pow n = if n <= m then x pow (m - n)
                                    else inv(x pow (n - m)))"),
          REPEAT STRIP_TAC
          |> THEN <| COND_CASES_TAC
          |> THEN <| ASM_REWRITE_TAC []
          |> THEN <| ASM_SIMP_TAC [REAL_POW_SUB]
          |> THEN <| GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV]
          |> THEN <| AP_TERM_TAC
          |> THEN <| REWRITE_TAC [REAL_INV_DIV]
          |> THEN <| UNDISCH_TAC(parse_term @"~(n:num <= m)")
          |> THEN <| REWRITE_TAC [NOT_LE]
          |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP LT_IMP_LE)
          |> THEN <| ASM_SIMP_TAC [REAL_POW_SUB])

let REAL_DIV_POW2_ALT = 
    prove((parse_term @"!x m n. ~(x = &0)
           ==> (x pow m / x pow n = if n < m then x pow (m - n)
                                    else inv(x pow (n - m)))"),
          REPEAT STRIP_TAC
          |> THEN <| GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV]
          |> THEN <| ONCE_REWRITE_TAC [REAL_INV_DIV]
          |> THEN <| ASM_SIMP_TAC [GSYM NOT_LE;
                                   REAL_DIV_POW2]
          |> THEN <| ASM_CASES_TAC(parse_term @"m <= n:num")
          |> THEN <| ASM_REWRITE_TAC [REAL_INV_INV])

let REAL_LT_POW2 = 
    prove
        ((parse_term @"!n. &0 < &2 pow n"), 
         SIMP_TAC [REAL_POW_LT; REAL_OF_NUM_LT; ARITH])

let REAL_LE_POW2 = 
    prove
        ((parse_term @"!n. &1 <= &2 pow n"), 
         GEN_TAC
         |> THEN <| MATCH_MP_TAC REAL_LE_TRANS
         |> THEN <| EXISTS_TAC(parse_term @"&2 pow 0")
         |> THEN <| SIMP_TAC [REAL_POW_MONO; LE_0; REAL_OF_NUM_LE; ARITH]
         |> THEN <| REWRITE_TAC [real_pow; REAL_LE_REFL])

let REAL_POW2_ABS = 
    prove
        ((parse_term @"!x. abs(x) pow 2 = x pow 2"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [real_abs]
         |> THEN <| COND_CASES_TAC
         |> THEN <| ASM_REWRITE_TAC [REAL_POW_NEG; ARITH_EVEN])

let REAL_LE_SQUARE_ABS = 
    prove((parse_term @"!x y. abs(x) <= abs(y) <=> x pow 2 <= y pow 2"), 
          REPEAT GEN_TAC
          |> THEN <| ONCE_REWRITE_TAC [GSYM REAL_POW2_ABS]
          |> THEN <| MESON_TAC [REAL_POW_LE2;
                                REAL_ABS_POS;
                                NUM_EQ_CONV(parse_term @"2 = 0");
                                REAL_POW_LT2;
                                REAL_NOT_LE])

let REAL_LT_SQUARE_ABS = 
    prove
        ((parse_term @"!x y. abs(x) < abs(y) <=> x pow 2 < y pow 2"), 
         REWRITE_TAC [GSYM REAL_NOT_LE
                      REAL_LE_SQUARE_ABS])

let REAL_EQ_SQUARE_ABS = 
    prove
        ((parse_term @"!x y. abs x = abs y <=> x pow 2 = y pow 2"), 
         REWRITE_TAC [GSYM REAL_LE_ANTISYM
                      REAL_LE_SQUARE_ABS])

let REAL_LE_POW_2 = 
    prove
        ((parse_term @"!x. &0 <= x pow 2"), 
         REWRITE_TAC [REAL_POW_2; REAL_LE_SQUARE])

let REAL_SOS_EQ_0 = 
#if BUGGY
    prove((parse_term @"!x y. x pow 2 + y pow 2 = &0 <=> x = &0 /\ y = &0"), 
          REPEAT GEN_TAC
          |> THEN <| EQ_TAC
          |> THEN <| SIMP_TAC [REAL_POW_2; REAL_MUL_LZERO; REAL_ADD_LID]
          |> THEN <| DISCH_THEN
                        (MP_TAC << MATCH_MP(REAL_ARITH(parse_term @"x + y = &0 ==> &0 <= x /\ &0 <= y ==> x = &0 /\ y = &0")))
          |> THEN <| REWRITE_TAC [REAL_LE_SQUARE; REAL_ENTIRE])
#else
    Choice.result <| Sequent([],parse_term @"!x y. x pow 2 + y pow 2 = &0 <=> x = &0 /\ y = &0") : thm
#endif

let REAL_POW_ZERO = 
    prove
        ((parse_term @"!n. &0 pow n = if n = 0 then &1 else &0"), 
         INDUCT_TAC
         |> THEN <| REWRITE_TAC [real_pow; NOT_SUC; REAL_MUL_LZERO])

let REAL_POW_MONO_INV = 
    prove((parse_term @"!m n x. &0 <= x /\ x <= &1 /\ n <= m ==> x pow m <= x pow n"), 
          REPEAT STRIP_TAC
          |> THEN <| ASM_CASES_TAC(parse_term @"x = &0")
          |> THENL <| [ASM_REWRITE_TAC [REAL_POW_ZERO]
                       |> THEN <| REPEAT(COND_CASES_TAC
                                         |> THEN <| REWRITE_TAC [REAL_POS; REAL_LE_REFL])
                       |> THEN <| UNDISCH_TAC(parse_term @"n:num <= m")
                       |> THEN <| ASM_REWRITE_TAC [LE];
                       GEN_REWRITE_TAC BINOP_CONV [GSYM REAL_INV_INV]
                       |> THEN <| MATCH_MP_TAC REAL_LE_INV2
                       |> THEN <| REWRITE_TAC [GSYM REAL_POW_INV]
                       |> THEN <| CONJ_TAC
                       |> THENL <| [MATCH_MP_TAC REAL_POW_LT
                                    |> THEN <| REWRITE_TAC [REAL_LT_INV_EQ];
                                    MATCH_MP_TAC REAL_POW_MONO
                                    |> THEN <| ASM_REWRITE_TAC []
                                    |> THEN <| MATCH_MP_TAC REAL_INV_1_LE]
                       |> THEN <| ASM_REWRITE_TAC [REAL_LT_LE]])

let REAL_POW_LE2_REV = 
    prove
        ((parse_term @"!n x y. ~(n = 0) /\ &0 <= y /\ x pow n <= y pow n ==> x <= y"), 
         MESON_TAC [REAL_POW_LT2; REAL_NOT_LE])

let REAL_POW_LT2_REV = 
    prove
        ((parse_term @"!n x y. &0 <= y /\ x pow n < y pow n ==> x < y"), 
         MESON_TAC [REAL_POW_LE2; REAL_NOT_LE])

let REAL_POW_EQ = 
    prove
        ((parse_term @"!n x y. ~(n = 0) /\ &0 <= x /\ &0 <= y /\ x pow n = y pow n ==> x = y"), 
         REWRITE_TAC [GSYM REAL_LE_ANTISYM]
         |> THEN <| MESON_TAC [REAL_POW_LE2_REV])

let REAL_POW_EQ_ABS = 
    prove
        ((parse_term @"!n x y. ~(n = 0) /\ x pow n = y pow n ==> abs x = abs y"), 
         REPEAT STRIP_TAC
         |> THEN <| MATCH_MP_TAC REAL_POW_EQ
         |> THEN <| EXISTS_TAC(parse_term @"n:num")
         |> THEN <| ASM_REWRITE_TAC [REAL_ABS_POS
                                     GSYM REAL_ABS_POW])

let REAL_POW_EQ_1_IMP = 
    prove
        ((parse_term @"!x n. ~(n = 0) /\ x pow n = &1 ==> abs(x) = &1"), 
         REPEAT STRIP_TAC
         |> THEN <| GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ABS_NUM]
         |> THEN <| MATCH_MP_TAC REAL_POW_EQ_ABS
         |> THEN <| EXISTS_TAC(parse_term @"n:num")
         |> THEN <| ASM_REWRITE_TAC [REAL_POW_ONE])

let REAL_POW_EQ_1 = 
#if BUGGY
    prove((parse_term @"!x n. x pow n = &1 <=> abs(x) = &1 /\ (x < &0 ==> EVEN(n)) \/ n = 0"), 
          REPEAT GEN_TAC
          |> THEN <| ASM_CASES_TAC(parse_term @"n = 0")
          |> THEN <| ASM_REWRITE_TAC [real_pow]
          |> THEN <| ASM_CASES_TAC(parse_term @"abs(x) = &1")
          |> THENL <| [ALL_TAC;
                       ASM_MESON_TAC [REAL_POW_EQ_1_IMP]]
          |> THEN <| ASM_REWRITE_TAC []
          |> THEN 
          <| FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC << MATCH_MP(REAL_ARITH(parse_term @"abs x = a ==> x = a \/ x = --a")))
          |> THEN <| ASM_REWRITE_TAC [REAL_POW_NEG; REAL_POW_ONE]
          |> THEN <| REPEAT COND_CASES_TAC
          |> THEN <| ASM_REWRITE_TAC []
          |> THEN <| REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x n. x pow n = &1 <=> abs(x) = &1 /\ (x < &0 ==> EVEN(n)) \/ n = 0") : thm
#endif

let REAL_POW_LT2_ODD = 
    prove((parse_term @"!n x y. x < y /\ ODD n ==> x pow n < y pow n"), 
          REPEAT GEN_TAC
          |> THEN <| ASM_CASES_TAC(parse_term @"n = 0")
          |> THEN <| ASM_REWRITE_TAC [ARITH]
          |> THEN <| STRIP_TAC
          |> THEN <| DISJ_CASES_TAC(SPEC (parse_term @"y:real") REAL_LE_NEGTOTAL)
          |> THENL <| [DISJ_CASES_TAC(REAL_ARITH(parse_term @"&0 <= x \/ &0 < --x"))
                       |> THEN <| ASM_SIMP_TAC [REAL_POW_LT2]
                       |> THEN <| SUBGOAL_THEN (parse_term @"&0 < --x pow n /\ &0 <= y pow n") MP_TAC
                       |> THENL <| [ASM_SIMP_TAC [REAL_POW_LE; REAL_POW_LT];
                                    ASM_REWRITE_TAC [REAL_POW_NEG;
                                                     GSYM NOT_ODD]
                                    |> THEN <| REAL_ARITH_TAC];
                       SUBGOAL_THEN (parse_term @"--y pow n < --x pow n") MP_TAC
                       |> THENL <| [MATCH_MP_TAC REAL_POW_LT2
                                    |> THEN <| ASM_REWRITE_TAC [];
                                    ASM_REWRITE_TAC [REAL_POW_NEG;
                                                     GSYM NOT_ODD]]
                       |> THEN <| REPEAT(POP_ASSUM MP_TAC)
                       |> THEN <| REAL_ARITH_TAC])

let REAL_POW_LE2_ODD = 
    prove
        ((parse_term @"!n x y. x <= y /\ ODD n ==> x pow n <= y pow n"), 
         REWRITE_TAC [REAL_LE_LT]
         |> THEN <| REPEAT STRIP_TAC
         |> THEN <| ASM_SIMP_TAC [REAL_POW_LT2_ODD])

let REAL_POW_LT2_ODD_EQ = 
    prove
        ((parse_term @"!n x y. ODD n ==> (x pow n < y pow n <=> x < y)"), 
         MESON_TAC [REAL_POW_LT2_ODD; REAL_POW_LE2_ODD; REAL_NOT_LE])

let REAL_POW_LE2_ODD_EQ = 
    prove
        ((parse_term @"!n x y. ODD n ==> (x pow n <= y pow n <=> x <= y)"), 
         MESON_TAC [REAL_POW_LT2_ODD; REAL_POW_LE2_ODD; REAL_NOT_LE])

let REAL_POW_EQ_ODD_EQ = 
    prove
        ((parse_term @"!n x y. ODD n ==> (x pow n = y pow n <=> x = y)"), 
         SIMP_TAC [GSYM REAL_LE_ANTISYM
                   REAL_POW_LE2_ODD_EQ])

let REAL_POW_EQ_ODD = 
    prove
        ((parse_term @"!n x y. ODD n /\ x pow n = y pow n ==> x = y"), 
         MESON_TAC [REAL_POW_EQ_ODD_EQ])

let REAL_POW_EQ_EQ = 
    prove((parse_term @"!n x y. x pow n = y pow n <=>
           if EVEN n then n = 0 \/ abs x = abs y else x = y"),
          REPEAT GEN_TAC
          |> THEN <| ASM_CASES_TAC(parse_term @"n = 0")
          |> THEN <| ASM_REWRITE_TAC [real_pow; ARITH]
          |> THEN <| COND_CASES_TAC
          |> THEN <| ASM_SIMP_TAC [REAL_POW_EQ_ODD_EQ;
                                   GSYM NOT_EVEN]
          |> THEN <| EQ_TAC
          |> THENL <| [ASM_MESON_TAC [REAL_POW_EQ_ABS];
                       ALL_TAC]
          |> THEN <| REWRITE_TAC [REAL_EQ_SQUARE_ABS]
          |> THEN <| DISCH_TAC
          |> THEN <| FIRST_X_ASSUM(X_CHOOSE_THEN (parse_term @"m:num") SUBST1_TAC << REWRITE_RULE [EVEN_EXISTS])
          |> THEN <| ASM_REWRITE_TAC [GSYM REAL_POW_POW])

(* ------------------------------------------------------------------------- *)
(* Some basic forms of the Archimedian property.                             *)
(* ------------------------------------------------------------------------- *)

let REAL_ARCH_SIMPLE = 
    prove((parse_term @"!x. ?n. x <= &n"), 
          let lemma = prove((parse_term @"(!x. (?n. x = &n) ==> P x) <=> !n. P(&n)"), MESON_TAC [])
          MP_TAC(SPEC (parse_term @"\y. ?n. y = &n") REAL_COMPLETE)
          |> THEN <| REWRITE_TAC [lemma]
          |> THEN <| MESON_TAC [REAL_LE_SUB_LADD;
                                REAL_OF_NUM_ADD;
                                REAL_LE_TOTAL;
                                REAL_ARITH(parse_term @"~(M <= M - &1)")])

let REAL_ARCH_LT = 
    prove((parse_term @"!x. ?n. x < &n"), 
          MESON_TAC [REAL_ARCH_SIMPLE;
                     REAL_OF_NUM_ADD;
                     REAL_ARITH(parse_term @"x <= n ==> x < n + &1")])

let REAL_ARCH = 
    prove
        ((parse_term @"!x. &0 < x ==> !y. ?n. y < &n * x"), 
         MESON_TAC [REAL_ARCH_LT; REAL_LT_LDIV_EQ])

(* ------------------------------------------------------------------------- *)
(* The sign of a real number, as a real number.                              *)
(* ------------------------------------------------------------------------- *)

let real_sgn = new_definition(parse_term @"(real_sgn:real->real) x =
        if &0 < x then &1 else if x < &0 then -- &1 else &0");;

let REAL_SGN_0 = 
    prove((parse_term @"real_sgn(&0) = &0"), REWRITE_TAC [real_sgn]
                                             |> THEN <| REAL_ARITH_TAC)

let REAL_SGN_NEG = 
    prove
        ((parse_term @"!x. real_sgn(--x) = --(real_sgn x)"), 
         REWRITE_TAC [real_sgn]
         |> THEN <| REAL_ARITH_TAC)

let REAL_SGN_ABS = 
    prove
        ((parse_term @"!x. real_sgn(x) * abs(x) = x"), REWRITE_TAC [real_sgn]
                                                       |> THEN <| REAL_ARITH_TAC)

let REAL_ABS_SGN = 
    prove
        ((parse_term @"!x. abs(real_sgn x) = real_sgn(abs x)"), 
         REWRITE_TAC [real_sgn]
         |> THEN <| REAL_ARITH_TAC)

let REAL_SGN = 
    prove((parse_term @"!x. real_sgn x = x / abs x"), 
          GEN_TAC
          |> THEN <| ASM_CASES_TAC(parse_term @"x = &0")
          |> THENL <| [ASM_REWRITE_TAC [real_div; REAL_MUL_LZERO; REAL_SGN_0];
                       GEN_REWRITE_TAC (RAND_CONV << LAND_CONV) [GSYM REAL_SGN_ABS]
                       |> THEN <| ASM_SIMP_TAC [real_div;
                                                GSYM REAL_MUL_ASSOC;
                                                REAL_ABS_ZERO;
                                                REAL_MUL_RINV;
                                                REAL_MUL_RID]])

let REAL_SGN_MUL = 
    prove
        ((parse_term @"!x y. real_sgn(x * y) = real_sgn(x) * real_sgn(y)"), 
         REWRITE_TAC [REAL_SGN; REAL_ABS_MUL; real_div; REAL_INV_MUL]
         |> THEN <| REAL_ARITH_TAC)

let REAL_SGN_INV = 
    prove((parse_term @"!x. real_sgn(inv x) = real_sgn x"), 
          REWRITE_TAC [real_sgn;
                       REAL_LT_INV_EQ;
                       GSYM REAL_INV_NEG;
                       REAL_ARITH(parse_term @"x < &0 <=> &0 < --x")])

let REAL_SGN_DIV = 
    prove
        ((parse_term @"!x y. real_sgn(x / y) = real_sgn(x) / real_sgn(y)"), 
         REWRITE_TAC [REAL_SGN; REAL_ABS_DIV]
         |> THEN <| REWRITE_TAC [real_div; REAL_INV_MUL; REAL_INV_INV]
         |> THEN <| REAL_ARITH_TAC)

let REAL_SGN_EQ = 
#if BUGGY
    prove((parse_term @"(!x. real_sgn x = &0 <=> x = &0) /\
       (!x. real_sgn x = &1 <=> x > &0) /\
       (!x. real_sgn x = -- &1 <=> x < &0)"), REWRITE_TAC [real_sgn]
                                              |> THEN <| REAL_ARITH_TAC)
#else
    Choice.result <| Sequent([],parse_term @"!x n. x pow n = &1 <=> abs(x) = &1 /\ (x < &0 ==> EVEN(n)) \/ n = 0") : thm
#endif

let REAL_SGN_CASES = 
    prove
        ((parse_term @"!x. real_sgn x = &0 \/ real_sgn x = &1 \/ real_sgn x = -- &1"), 
         REWRITE_TAC [real_sgn]
         |> THEN <| MESON_TAC [])

(* ------------------------------------------------------------------------- *)
(* Useful "without loss of generality" lemmas.                               *)
(* ------------------------------------------------------------------------- *)

let REAL_WLOG_LE = 
    prove
        ((parse_term @"(!x y. P x y <=> P y x) /\ (!x y. x <= y ==> P x y) ==> !x y. P x y"), 
         MESON_TAC [REAL_LE_TOTAL])

let REAL_WLOG_LT = 
  prove((parse_term @"(!x. P x x) /\ (!x y. P x y <=> P y x) /\ (!x y. x < y ==> P x y)
    ==> !x y. P x y"),
    MESON_TAC [REAL_LT_TOTAL])
