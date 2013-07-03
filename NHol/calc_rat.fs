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
/// Calculation with rational-valued reals.
module NHol.calc_rat

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

open NHol
open lib
open fusion
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
open real

(* ------------------------------------------------------------------------- *)
(* Constant for decimal fractions written #xxx.yyy                           *)
(* ------------------------------------------------------------------------- *)
let DECIMAL = new_definition(parse_term "DECIMAL x y = &x / &y")

(* ------------------------------------------------------------------------- *)
(* Various handy lemmas.                                                     *)
(* ------------------------------------------------------------------------- *)
let RAT_LEMMA1 = 
    prove((parse_term "~(y1 = &0) /\ ~(y2 = &0) ==>
      ((x1 / y1) + (x2 / y2) = (x1 * y2 + x2 * y1) * inv(y1) * inv(y2))"),
     STRIP_TAC
     |> THEN <| REWRITE_TAC [real_div; REAL_ADD_RDISTRIB]
     |> THEN <| BINOP_TAC
     |> THENL <| [REWRITE_TAC [GSYM REAL_MUL_ASSOC]
                  |> THEN <| AP_TERM_TAC
                  |> THEN 
                  <| ONCE_REWRITE_TAC 
                         [AC REAL_MUL_AC (parse_term "a * b * c = (b * a) * c")]
                  REWRITE_TAC [REAL_MUL_ASSOC]
                  |> THEN <| AP_THM_TAC
                  |> THEN <| AP_TERM_TAC]
     |> THEN <| GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID]
     |> THEN <| REWRITE_TAC [GSYM REAL_MUL_ASSOC]
     |> THEN <| REWRITE_TAC [REAL_EQ_MUL_LCANCEL]
     |> THEN <| DISJ2_TAC
     |> THEN <| CONV_TAC SYM_CONV
     |> THEN <| MATCH_MP_TAC REAL_MUL_RINV
     |> THEN <| ASM_REWRITE_TAC [])

let RAT_LEMMA2 = 
    prove((parse_term "&0 < y1 /\ &0 < y2 ==>
      ((x1 / y1) + (x2 / y2) = (x1 * y2 + x2 * y1) * inv(y1) * inv(y2))"),
     DISCH_TAC
     |> THEN <| MATCH_MP_TAC RAT_LEMMA1
     |> THEN <| POP_ASSUM MP_TAC
     |> THEN <| ONCE_REWRITE_TAC [GSYM CONTRAPOS_THM]
     |> THEN <| REWRITE_TAC [DE_MORGAN_THM]
     |> THEN <| STRIP_TAC
     |> THEN <| ASM_REWRITE_TAC [REAL_LT_REFL])

let RAT_LEMMA3 = 
    prove((parse_term "&0 < y1 /\ &0 < y2 ==>
      ((x1 / y1) - (x2 / y2) = (x1 * y2 - x2 * y1) * inv(y1) * inv(y2))"),
     DISCH_THEN(MP_TAC << GEN_ALL << MATCH_MP RAT_LEMMA2)
     |> THEN <| REWRITE_TAC [real_div]
     |> THEN <| DISCH_TAC
     |> THEN <| ASM_REWRITE_TAC [real_sub
                                 GSYM REAL_MUL_LNEG])

let RAT_LEMMA4 = 
    prove
        ((parse_term 
              "&0 < y1 /\ &0 < y2 ==> (x1 / y1 <= x2 / y2 <=> x1 * y2 <= x2 * y1)"), 
         let lemma = 
             prove
                 ((parse_term "&0 < y ==> (&0 <= x * y <=> &0 <= x)"), 
                  DISCH_TAC
                  |> THEN <| EQ_TAC
                  |> THEN <| DISCH_TAC
                  |> THENL <| [SUBGOAL_THEN (parse_term "&0 <= x * (y * inv y)") 
                                   MP_TAC
                               |> THENL <| [REWRITE_TAC [REAL_MUL_ASSOC]
                                            |> THEN <| MATCH_MP_TAC REAL_LE_MUL
                                            |> THEN <| ASM_REWRITE_TAC []
                                            |> THEN <| MATCH_MP_TAC REAL_LE_INV
                                            |> THEN 
                                            <| MATCH_MP_TAC REAL_LT_IMP_LE
                                            |> THEN <| ASM_REWRITE_TAC []
                                            SUBGOAL_THEN 
                                                (parse_term "y * inv y = &1") 
                                                (fun th -> 
                                                    REWRITE_TAC 
                                                        [th; REAL_MUL_RID])
                                            |> THEN 
                                            <| MATCH_MP_TAC REAL_MUL_RINV
                                            |> THEN 
                                            <| UNDISCH_TAC(parse_term "&0 < y")
                                            |> THEN <| REAL_ARITH_TAC]
                               MATCH_MP_TAC REAL_LE_MUL
                               |> THEN <| ASM_REWRITE_TAC []
                               |> THEN <| MATCH_MP_TAC REAL_LT_IMP_LE
                               |> THEN <| ASM_REWRITE_TAC []])
         ONCE_REWRITE_TAC [CONJ_SYM]
         |> THEN <| DISCH_TAC
         |> THEN 
         <| ONCE_REWRITE_TAC [REAL_ARITH(parse_term "a <= b <=> &0 <= b - a")]
         |> THEN <| FIRST_ASSUM(fun th -> REWRITE_TAC [MATCH_MP RAT_LEMMA3 th])
         |> THEN <| MATCH_MP_TAC EQ_TRANS
         |> THEN <| EXISTS_TAC(parse_term "&0 <= (x2 * y1 - x1 * y2) * inv y2")
         |> THEN <| REWRITE_TAC [REAL_MUL_ASSOC]
         |> THEN <| CONJ_TAC
         |> THEN <| MATCH_MP_TAC lemma
         |> THEN <| MATCH_MP_TAC REAL_LT_INV
         |> THEN <| ASM_REWRITE_TAC [])

let RAT_LEMMA5 = 
    prove
        ((parse_term 
              "&0 < y1 /\ &0 < y2 ==> ((x1 / y1 = x2 / y2) <=> (x1 * y2 = x2 * y1))"), 
         REPEAT DISCH_TAC
         |> THEN <| REWRITE_TAC [GSYM REAL_LE_ANTISYM]
         |> THEN 
         <| MATCH_MP_TAC
                (TAUT
                     (parse_term 
                          "(a <=> a') /\ (b <=> b') ==> (a /\ b <=> a' /\ b')"))
         |> THEN <| CONJ_TAC
         |> THEN <| MATCH_MP_TAC RAT_LEMMA4
         |> THEN <| ASM_REWRITE_TAC [])

(* ------------------------------------------------------------------------- *)
(* Create trivial rational from integer or decimal, and postconvert back.    *)
(* ------------------------------------------------------------------------- *)
let REAL_INT_RAT_CONV = 
    let pth = 
        prove
            ((parse_term "(&x = &x / &1) /\
     (--(&x) = --(&x) / &1) /\
     (DECIMAL x y = &x / &y) /\
     (--(DECIMAL x y) = --(&x) / &y)"), 
             REWRITE_TAC [REAL_DIV_1; DECIMAL]
             |> THEN <| REWRITE_TAC [real_div; REAL_MUL_LNEG])
    TRY_CONV(GEN_REWRITE_CONV I [pth])

(* ------------------------------------------------------------------------- *)
(* Relational operations.                                                    *)
(* ------------------------------------------------------------------------- *)
let REAL_RAT_LE_CONV = 
    let pth = 
        prove
            ((parse_term 
                  "&0 < y1 ==> &0 < y2 ==> (x1 / y1 <= x2 / y2 <=> x1 * y2 <= x2 * y1)"), 
             REWRITE_TAC [IMP_IMP; RAT_LEMMA4])
    let x1 = (parse_term "x1:real")
    let x2 = (parse_term "x2:real")
    let y1 = (parse_term "y1:real")
    let y2 = (parse_term "y2:real")
    let dest_le = dest_binop(parse_term "(<=)")
    let dest_div = dest_binop(parse_term "(/)")
    let RAW_REAL_RAT_LE_CONV tm = 
        let l, r = dest_le tm
        let lx, ly = dest_div l
        let rx, ry = dest_div r
        let th0 = 
            INST [lx, x1
                  ly, y1
                  rx, x2
                  ry, y2] pth
        let th1 = funpow 2 (MP_CONV REAL_INT_LT_CONV) th0
        let th2 = (BINOP_CONV REAL_INT_MUL_CONV
                   |> THENC <| REAL_INT_LE_CONV)(rand(concl th1))
        TRANS th1 th2
    BINOP_CONV REAL_INT_RAT_CONV
    |> THENC <| RAW_REAL_RAT_LE_CONV

let REAL_RAT_LT_CONV = 
    let pth = 
        prove
            ((parse_term 
                  "&0 < y1 ==> &0 < y2 ==> (x1 / y1 < x2 / y2 <=> x1 * y2 < x2 * y1)"), 
             REWRITE_TAC [IMP_IMP]
             |> THEN 
             <| GEN_REWRITE_TAC (RAND_CONV << ONCE_DEPTH_CONV) 
                    [GSYM REAL_NOT_LE]
             |> THEN <| SIMP_TAC [TAUT(parse_term "(~a <=> ~b) <=> (a <=> b)")
                                  RAT_LEMMA4])
    let x1 = (parse_term "x1:real")
    let x2 = (parse_term "x2:real")
    let y1 = (parse_term "y1:real")
    let y2 = (parse_term "y2:real")
    let dest_lt = dest_binop(parse_term "(<)")
    let dest_div = dest_binop(parse_term "(/)")
    let RAW_REAL_RAT_LT_CONV tm = 
        let l, r = dest_lt tm
        let lx, ly = dest_div l
        let rx, ry = dest_div r
        let th0 = 
            INST [lx, x1
                  ly, y1
                  rx, x2
                  ry, y2] pth
        let th1 = funpow 2 (MP_CONV REAL_INT_LT_CONV) th0
        let th2 = (BINOP_CONV REAL_INT_MUL_CONV
                   |> THENC <| REAL_INT_LT_CONV)(rand(concl th1))
        TRANS th1 th2
    BINOP_CONV REAL_INT_RAT_CONV
    |> THENC <| RAW_REAL_RAT_LT_CONV

let REAL_RAT_GE_CONV = GEN_REWRITE_CONV I [real_ge]
                       |> THENC <| REAL_RAT_LE_CONV
let REAL_RAT_GT_CONV = GEN_REWRITE_CONV I [real_gt]
                       |> THENC <| REAL_RAT_LT_CONV

let REAL_RAT_EQ_CONV = 
    let pth = 
        prove
            ((parse_term 
                  "&0 < y1 ==> &0 < y2 ==> ((x1 / y1 = x2 / y2) <=> (x1 * y2 = x2 * y1))"), 
             REWRITE_TAC [IMP_IMP; RAT_LEMMA5])
    let x1 = (parse_term "x1:real")
    let x2 = (parse_term "x2:real")
    let y1 = (parse_term "y1:real")
    let y2 = (parse_term "y2:real")
    let dest_eq = dest_binop(parse_term "(=) :real->real->bool")
    let dest_div = dest_binop(parse_term "(/)")
    let RAW_REAL_RAT_EQ_CONV tm = 
        let l, r = dest_eq tm
        let lx, ly = dest_div l
        let rx, ry = dest_div r
        let th0 = 
            INST [lx, x1
                  ly, y1
                  rx, x2
                  ry, y2] pth
        let th1 = funpow 2 (MP_CONV REAL_INT_LT_CONV) th0
        let th2 = (BINOP_CONV REAL_INT_MUL_CONV
                   |> THENC <| REAL_INT_EQ_CONV)(rand(concl th1))
        TRANS th1 th2
    BINOP_CONV REAL_INT_RAT_CONV
    |> THENC <| RAW_REAL_RAT_EQ_CONV

(* ------------------------------------------------------------------------- *)
(* The unary operations; all easy.                                           *)
(* ------------------------------------------------------------------------- *)
let REAL_RAT_NEG_CONV = 
    let pth = 
        prove
            ((parse_term "(--(&0) = &0) /\
     (--(--(&n)) = &n) /\
     (--(&m / &n) = --(&m) / &n) /\
     (--(--(&m) / &n) = &m / &n) /\
     (--(DECIMAL m n) = --(&m) / &n)"), 
             REWRITE_TAC 
                 [real_div; REAL_INV_NEG; REAL_MUL_LNEG; REAL_NEG_NEG; 
                  REAL_NEG_0; DECIMAL])
    let ptm = (parse_term "(--)")
    let conv1 = GEN_REWRITE_CONV I [pth]
    fun tm -> 
        try 
            conv1 tm
        with
        | Failure _ -> 
            try 
                let l, r = dest_comb tm
                if l = ptm && is_realintconst r && dest_realintconst r >/ num_0
                then REFL tm
                else fail()
            with
            | Failure _ -> failwith "REAL_RAT_NEG_CONV"

let REAL_RAT_ABS_CONV = 
    let pth = 
        prove
            ((parse_term "(abs(&n) = &n) /\
     (abs(--(&n)) = &n) /\
     (abs(&m / &n) = &m / &n) /\
     (abs(--(&m) / &n) = &m / &n) /\
     (abs(DECIMAL m n) = &m / &n) /\
     (abs(--(DECIMAL m n)) = &m / &n)"), 
             REWRITE_TAC [DECIMAL; REAL_ABS_DIV; REAL_ABS_NEG; REAL_ABS_NUM])
    GEN_REWRITE_CONV I [pth]

let REAL_RAT_INV_CONV = 
    let pth1 = 
        prove
            ((parse_term "(inv(&0) = &0) /\
     (inv(&1) = &1) /\
     (inv(-- &1) = --(&1)) /\
     (inv(&1 / &n) = &n) /\
     (inv(-- &1 / &n) = -- &n)"), 
             REWRITE_TAC 
                 [REAL_INV_0; REAL_INV_1; REAL_INV_NEG; REAL_INV_DIV; REAL_DIV_1]
             |> THEN 
             <| REWRITE_TAC 
                    [real_div; REAL_INV_NEG; REAL_MUL_RNEG; REAL_INV_1; 
                     REAL_MUL_RID])
    let pth2 = 
        prove
            ((parse_term "(inv(&n) = &1 / &n) /\
     (inv(--(&n)) = --(&1) / &n) /\
     (inv(&m / &n) = &n / &m) /\
     (inv(--(&m) / &n) = --(&n) / &m) /\
     (inv(DECIMAL m n) = &n / &m) /\
     (inv(--(DECIMAL m n)) = --(&n) / &m)"), 
             REWRITE_TAC [DECIMAL; REAL_INV_DIV]
             |> THEN 
             <| REWRITE_TAC 
                    [REAL_INV_NEG; real_div; REAL_MUL_RNEG; REAL_MUL_AC; 
                     REAL_MUL_LID; REAL_MUL_LNEG; REAL_INV_MUL; REAL_INV_INV])
    GEN_REWRITE_CONV I [pth1]
    |> ORELSEC <| GEN_REWRITE_CONV I [pth2]

(* ------------------------------------------------------------------------- *)
(* Addition.                                                                 *)
(* ------------------------------------------------------------------------- *)
let REAL_RAT_ADD_CONV = 
  let pth = 
    prove ((parse_term "&0 < y1 ==> &0 < y2 ==> &0 < y3 ==>
     ((x1 * y2 + x2 * y1) * y3 = x3 * y1 * y2)
     ==> (x1 / y1 + x2 / y2 = x3 / y3)"),
     REPEAT DISCH_TAC
     |> THEN <| MP_TAC RAT_LEMMA2
     |> THEN <| ASM_REWRITE_TAC []
     |> THEN <| DISCH_THEN SUBST1_TAC
     |> THEN <| REWRITE_TAC [GSYM REAL_INV_MUL
                             GSYM real_div]
     |> THEN <| SUBGOAL_THEN (parse_term "&0 < y1 * y2 /\ &0 < y3") MP_TAC
     |> THENL <| [ASM_REWRITE_TAC []
                  |> THEN <| MATCH_MP_TAC REAL_LT_MUL
                  |> THEN <| ASM_REWRITE_TAC []
                  DISCH_THEN(fun th -> ASM_REWRITE_TAC [MATCH_MP RAT_LEMMA5 th])])
  let dest_divop = dest_binop(parse_term "(/)")
  let dest_addop = dest_binop(parse_term "(+)")
  let x1 = (parse_term "x1:real")
  let x2 = (parse_term "x2:real")
  let x3 = (parse_term "x3:real")
  let y1 = (parse_term "y1:real")
  let y2 = (parse_term "y2:real")
  let y3 = (parse_term "y3:real")
  let RAW_REAL_RAT_ADD_CONV tm = 
         let r1, r2 = dest_addop tm
         let x1', y1' = dest_divop r1
         let x2', y2' = dest_divop r2
         let x1n = dest_realintconst x1'
         let y1n = dest_realintconst y1'
         let x2n = dest_realintconst x2'
         let y2n = dest_realintconst y2'
         let x3n = x1n */ y2n +/ x2n */ y1n
         let y3n = y1n */ y2n
         let d = gcd_num x3n y3n
         let x3n' = quo_num x3n d
         let y3n' = quo_num y3n d
         let x3n'', y3n'' = 
             if y3n' >/ Int 0
             then x3n', y3n'
             else minus_num x3n', minus_num y3n'
         let x3' = mk_realintconst x3n''
         let y3' = mk_realintconst y3n''
         let th0 = 
             INST [x1', x1
                   y1', y1
                   x2', x2
                   y2', y2
                   x3', x3
                   y3', y3] pth
         let th1 = funpow 3 (MP_CONV REAL_INT_LT_CONV) th0
         let tm2, tm3 = dest_eq(fst(dest_imp(concl th1)))
         let th2 = (LAND_CONV(BINOP_CONV REAL_INT_MUL_CONV
                              |> THENC <| REAL_INT_ADD_CONV)
                    |> THENC <| REAL_INT_MUL_CONV) tm2
         let th3 = (RAND_CONV REAL_INT_MUL_CONV
                    |> THENC <| REAL_INT_MUL_CONV) tm3
         MP th1 (TRANS th2 (SYM th3))
  BINOP_CONV REAL_INT_RAT_CONV
  |> THENC <| RAW_REAL_RAT_ADD_CONV
  |> THENC <| TRY_CONV(GEN_REWRITE_CONV I [REAL_DIV_1])
 
(* ------------------------------------------------------------------------- *)
(* Subtraction.                                                              *)
(* ------------------------------------------------------------------------- *)
let REAL_RAT_SUB_CONV = 
    let pth = prove((parse_term "x - y = x + --y"), REWRITE_TAC [real_sub])
    GEN_REWRITE_CONV I [pth]
    |> THENC <| RAND_CONV REAL_RAT_NEG_CONV
    |> THENC <| REAL_RAT_ADD_CONV

(* ------------------------------------------------------------------------- *)
(* Multiplication.                                                           *)
(* ------------------------------------------------------------------------- *)
let REAL_RAT_MUL_CONV = 
    let pth_nocancel = 
        prove
            ((parse_term "(x1 / y1) * (x2 / y2) = (x1 * x2) / (y1 * y2)"), 
             REWRITE_TAC [real_div; REAL_INV_MUL; REAL_MUL_AC])
    let pth_cancel = 
      prove((parse_term "~(d1 = &0) /\ ~(d2 = &0) /\
        (d1 * u1 = x1) /\ (d2 * u2 = x2) /\
        (d2 * v1 = y1) /\ (d1 * v2 = y2)
        ==> ((x1 / y1) * (x2 / y2) = (u1 * u2) / (v1 * v2))"),
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
        |> THEN <| DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
        |> THEN <| DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC << SYM))
        |> THEN <| ASM_REWRITE_TAC [real_div; REAL_INV_MUL]
        |> THEN <| ONCE_REWRITE_TAC [AC REAL_MUL_AC (parse_term "((d1 * u1) * (id2 * iv1)) * ((d2 * u2) * id1 * iv2) = (u1 * u2) * (iv1 * iv2) * (id2 * d2) * (id1 * d1)")]
        |> THEN <| ASM_SIMP_TAC [REAL_MUL_LINV; REAL_MUL_RID])
    let dest_divop = dest_binop(parse_term "(/)")
    let dest_mulop = dest_binop(parse_term "(*)")
    let x1 = (parse_term "x1:real")
    let x2 = (parse_term "x2:real")
    let y1 = (parse_term "y1:real")
    let y2 = (parse_term "y2:real")
    let u1 = (parse_term "u1:real")
    let u2 = (parse_term "u2:real")
    let v1 = (parse_term "v1:real")
    let v2 = (parse_term "v2:real")
    let d1 = (parse_term "d1:real")
    let d2 = (parse_term "d2:real")
    let RAW_REAL_RAT_MUL_CONV tm = 
        let r1, r2 = dest_mulop tm
        let x1', y1' = dest_divop r1
        let x2', y2' = dest_divop r2
        let x1n = dest_realintconst x1'
        let y1n = dest_realintconst y1'
        let x2n = dest_realintconst x2'
        let y2n = dest_realintconst y2'
        let d1n = gcd_num x1n y2n
        let d2n = gcd_num x2n y1n
        if d1n = num_1 && d2n = num_1
        then 
            let th0 = 
                INST [x1', x1
                      y1', y1
                      x2', x2
                      y2', y2] pth_nocancel
            let th1 = BINOP_CONV REAL_INT_MUL_CONV (rand(concl th0))
            TRANS th0 th1
        else 
            let u1n = quo_num x1n d1n
            let u2n = quo_num x2n d2n
            let v1n = quo_num y1n d2n
            let v2n = quo_num y2n d1n
            let u1' = mk_realintconst u1n
            let u2' = mk_realintconst u2n
            let v1' = mk_realintconst v1n
            let v2' = mk_realintconst v2n
            let d1' = mk_realintconst d1n
            let d2' = mk_realintconst d2n
            let th0 = 
                INST [x1', x1
                      y1', y1
                      x2', x2
                      y2', y2
                      u1', u1
                      v1', v1
                      u2', u2
                      v2', v2
                      d1', d1
                      d2', d2] pth_cancel
            let th1 = EQT_ELIM(REAL_INT_REDUCE_CONV(lhand(concl th0)))
            let th2 = MP th0 th1
            let th3 = BINOP_CONV REAL_INT_MUL_CONV (rand(concl th2))
            TRANS th2 th3
    BINOP_CONV REAL_INT_RAT_CONV
    |> THENC <| RAW_REAL_RAT_MUL_CONV
    |> THENC <| TRY_CONV(GEN_REWRITE_CONV I [REAL_DIV_1])

(* ------------------------------------------------------------------------- *)
(* Division.                                                                 *)
(* ------------------------------------------------------------------------- *)
let REAL_RAT_DIV_CONV = 
    let pth = prove((parse_term "x / y = x * inv(y)"), REWRITE_TAC [real_div])
    GEN_REWRITE_CONV I [pth]
    |> THENC <| RAND_CONV REAL_RAT_INV_CONV
    |> THENC <| REAL_RAT_MUL_CONV

(* ------------------------------------------------------------------------- *)
(* Powers.                                                                   *)
(* ------------------------------------------------------------------------- *)
let REAL_RAT_POW_CONV = 
    let pth = 
        prove
            ((parse_term "(x / y) pow n = (x pow n) / (y pow n)"), 
             REWRITE_TAC [REAL_POW_DIV])
    REAL_INT_POW_CONV
    |> ORELSEC <| (LAND_CONV REAL_INT_RAT_CONV
                   |> THENC <| GEN_REWRITE_CONV I [pth]
                   |> THENC <| BINOP_CONV REAL_INT_POW_CONV)

(* ------------------------------------------------------------------------- *)
(* Max and min.                                                              *)
(* ------------------------------------------------------------------------- *)
let REAL_RAT_MAX_CONV = 
    REWR_CONV real_max
    |> THENC <| RATOR_CONV(RATOR_CONV(RAND_CONV REAL_RAT_LE_CONV))
    |> THENC <| GEN_REWRITE_CONV I [COND_CLAUSES]

let REAL_RAT_MIN_CONV = 
    REWR_CONV real_min
    |> THENC <| RATOR_CONV(RATOR_CONV(RAND_CONV REAL_RAT_LE_CONV))
    |> THENC <| GEN_REWRITE_CONV I [COND_CLAUSES]

(* ------------------------------------------------------------------------- *)
(* Everything.                                                               *)
(* ------------------------------------------------------------------------- *)
let REAL_RAT_RED_CONV = 
    let gconv_net = 
        itlist (uncurry net_of_conv) [(parse_term "x <= y"), REAL_RAT_LE_CONV
                                      (parse_term "x < y"), REAL_RAT_LT_CONV
                                      (parse_term "x >= y"), REAL_RAT_GE_CONV
                                      (parse_term "x > y"), REAL_RAT_GT_CONV
                                      (parse_term "x:real = y"), 
                                      REAL_RAT_EQ_CONV
                                      (parse_term "--x"), 
                                      CHANGED_CONV REAL_RAT_NEG_CONV
                                      (parse_term "abs(x)"), REAL_RAT_ABS_CONV
                                      (parse_term "inv(x)"), REAL_RAT_INV_CONV
                                      (parse_term "x + y"), REAL_RAT_ADD_CONV
                                      (parse_term "x - y"), REAL_RAT_SUB_CONV
                                      (parse_term "x * y"), REAL_RAT_MUL_CONV
                                      (parse_term "x / y"), 
                                      CHANGED_CONV REAL_RAT_DIV_CONV
                                      (parse_term "x pow n"), REAL_RAT_POW_CONV
                                      (parse_term "max x y"), REAL_RAT_MAX_CONV
                                      (parse_term "min x y"), REAL_RAT_MIN_CONV] 
            (basic_net())
    REWRITES_CONV gconv_net

let REAL_RAT_REDUCE_CONV = DEPTH_CONV REAL_RAT_RED_CONV

(* ------------------------------------------------------------------------- *)
(* Real normalizer dealing with rational constants.                          *)
(* ------------------------------------------------------------------------- *)
let REAL_POLY_NEG_CONV, REAL_POLY_ADD_CONV, REAL_POLY_SUB_CONV, REAL_POLY_MUL_CONV, REAL_POLY_POW_CONV, REAL_POLY_CONV_001 = 
    SEMIRING_NORMALIZERS_CONV REAL_POLY_CLAUSES REAL_POLY_NEG_CLAUSES 
        (is_ratconst, REAL_RAT_ADD_CONV, REAL_RAT_MUL_CONV, REAL_RAT_POW_CONV) 
        (<)

(* ------------------------------------------------------------------------- *)
(* Extend normalizer to handle "inv" and division by rational constants, and *)
(* normalize inside nested "max", "min" and "abs" terms.                     *)
(* ------------------------------------------------------------------------- *)
let REAL_POLY_CONV = 
    let neg_tm = (parse_term "(--):real->real")
    let inv_tm = (parse_term "inv:real->real")
    let add_tm = (parse_term "(+):real->real->real")
    let sub_tm = (parse_term "(-):real->real->real")
    let mul_tm = (parse_term "(*):real->real->real")
    let div_tm = (parse_term "(/):real->real->real")
    let pow_tm = (parse_term "(pow):real->num->real")
    let abs_tm = (parse_term "abs:real->real")
    let max_tm = (parse_term "max:real->real->real")
    let min_tm = (parse_term "min:real->real->real")
    let div_conv = REWR_CONV real_div
    let rec REAL_POLY_CONV tm = 
        if not(is_comb tm) || is_ratconst tm
        then REFL tm
        else 
            let lop, r = dest_comb tm
            if lop = neg_tm
            then 
                let th1 = AP_TERM lop (REAL_POLY_CONV r)
                TRANS th1 (REAL_POLY_NEG_CONV(rand(concl th1)))
            elif lop = inv_tm
            then 
                let th1 = AP_TERM lop (REAL_POLY_CONV r)
                TRANS th1 (TRY_CONV REAL_RAT_INV_CONV (rand(concl th1)))
            elif lop = abs_tm
            then AP_TERM lop (REAL_POLY_CONV r)
            elif not(is_comb lop)
            then REFL tm
            else 
                let op, l = dest_comb lop
                if op = pow_tm
                then 
                    let th1 = AP_THM (AP_TERM op (REAL_POLY_CONV l)) r
                    TRANS th1 (TRY_CONV REAL_POLY_POW_CONV (rand(concl th1)))
                elif op = add_tm || op = mul_tm || op = sub_tm
                then 
                    let th1 = 
                        MK_COMB(AP_TERM op (REAL_POLY_CONV l), REAL_POLY_CONV r)
                    let fn = 
                        if op = add_tm
                        then REAL_POLY_ADD_CONV
                        elif op = mul_tm
                        then REAL_POLY_MUL_CONV
                        else REAL_POLY_SUB_CONV
                    TRANS th1 (fn(rand(concl th1)))
                elif op = div_tm
                then 
                    let th1 = div_conv tm
                    TRANS th1 (REAL_POLY_CONV(rand(concl th1)))
                elif op = min_tm || op = max_tm
                then MK_COMB(AP_TERM op (REAL_POLY_CONV l), REAL_POLY_CONV r)
                else REFL tm
    REAL_POLY_CONV

(* ------------------------------------------------------------------------- *)
(* Basic ring and ideal conversions.                                         *)
(* ------------------------------------------------------------------------- *)
 //let REAL_RING,real_ideal_cofactors =
 //  let REAL_INTEGRAL = prove
 //   ((parse_term "(!x. &0 * x = &0) /\
 //     (!x y z. (x + y = x + z) <=> (y = z)) /\
 //     (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))"),
 //    REWRITE_TAC[MULT_CLAUSES; EQ_ADD_LCANCEL] |>THEN<|
 //    REWRITE_TAC[GSYM REAL_OF_NUM_EQ;
 //                GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] |>THEN<|
 //    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] |>THEN<|
 //    REWRITE_TAC[GSYM REAL_ENTIRE] |>THEN<| REAL_ARITH_TAC)
 //  let REAL_RABINOWITSCH = prove
 //   ((parse_term "!x y:real. ~(x = y) <=> ?z. (x - y) * z = &1"),
 //    REPEAT GEN_TAC |>THEN<|
 //    GEN_REWRITE_TAC (LAND_CONV << RAND_CONV) [GSYM REAL_SUB_0] |>THEN<|
 //    MESON_TAC[REAL_MUL_RINV; REAL_MUL_LZERO; REAL_ARITH (parse_term "~(&1 = &0)")])
 //  let init = GEN_REWRITE_CONV ONCE_DEPTH_CONV [DECIMAL]
 //  let real_ty = (parse_type ":real") in
 //  let pure,ideal =
 //    RING_AND_IDEAL_CONV
 //        (rat_of_term,term_of_rat,REAL_RAT_EQ_CONV,
 //         (parse_term "(--):real->real"),(parse_term "(+):real->real->real"),(parse_term "(-):real->real->real"),
 //         (parse_term "(inv):real->real"),(parse_term "(*):real->real->real"),(parse_term "(/):real->real->real"),
 //         (parse_term "(pow):real->num->real"),
 //         REAL_INTEGRAL,REAL_RABINOWITSCH,REAL_POLY_CONV) in
 //  (fun tm -> let th = init tm in EQ_MP (SYM th) (pure(rand(concl th)))),
 //  (fun tms tm -> if forall (fun t -> type_of t = real_ty) (tm::tms)
 //                 then ideal tms tm
 //                 else failwith
 //                   "real_ideal_cofactors: not all terms have type :real");;
(* ------------------------------------------------------------------------- *)
(* Conversion for ideal membership.                                          *)
(* ------------------------------------------------------------------------- *)
 //let REAL_IDEAL_CONV =
 //  let mk_add = mk_binop (parse_term "( + ):real->real->real")
 //  let mk_mul = mk_binop (parse_term "( * ):real->real->real") in
 //  fun tms tm ->
 //    let cfs = real_ideal_cofactors tms tm in
 //    let tm' = end_itlist mk_add (map2 mk_mul cfs tms) in
 //    let th = REAL_POLY_CONV tm and th' = REAL_POLY_CONV tm' in
 //    TRANS th (SYM th');;
(* ------------------------------------------------------------------------- *)
(* Further specialize GEN_REAL_ARITH and REAL_ARITH (final versions).        *)
(* ------------------------------------------------------------------------- *)
let GEN_REAL_ARITH PROVER = 
    GEN_REAL_ARITH
        (term_of_rat, REAL_RAT_EQ_CONV, REAL_RAT_GE_CONV, REAL_RAT_GT_CONV, 
         REAL_POLY_CONV, REAL_POLY_NEG_CONV, REAL_POLY_ADD_CONV, 
         REAL_POLY_MUL_CONV, PROVER)

let REAL_ARITH = 
    let init = GEN_REWRITE_CONV ONCE_DEPTH_CONV [DECIMAL]
    let pure = GEN_REAL_ARITH REAL_LINEAR_PROVER
    fun tm -> 
        let th = init tm
        EQ_MP (SYM th) (pure(rand(concl th)))

let REAL_ARITH_TAC = CONV_TAC REAL_ARITH
let ASM_REAL_ARITH_TAC = REPEAT
                             (FIRST_X_ASSUM
                                  (MP_TAC << check(not << is_forall << concl)))
                         |> THEN <| REAL_ARITH_TAC