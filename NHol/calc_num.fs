(*

Copyright 1998 University of Cambridge
Copyright 1998-2007 John Harrison
Copyright 2013 Jack Pappas, Eric Taucher, Domenico Masini

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
/// Calculation with natural numbers.
module NHol.calc_num

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
//open pair
open nums
open recursion
open arith
//open wf
#endif

(* ------------------------------------------------------------------------- *)
(* Simple rule to get rid of NUMERAL constant.                               *)
(* ------------------------------------------------------------------------- *)

/// Remove instances of the NUMERAL constant from a theorem.
let DENUMERAL = GEN_REWRITE_RULE DEPTH_CONV [NUMERAL];;

(* ------------------------------------------------------------------------- *)
(* Big collection of rewrites to do trivial arithmetic.                      *)
(*                                                                           *)
(* Note that we have none for DIV and MOD, and that PRE and SUB are a bit    *)
(* inefficient; log(n)^2 instead of log(n).                                  *)
(* ------------------------------------------------------------------------- *)

let ARITH_ZERO = 
 prove
  ((parse_term @"(NUMERAL 0 = 0) /\
    (BIT0 _0 = _0)"),
   REWRITE_TAC[NUMERAL; BIT0; DENUMERAL ADD_CLAUSES]);;

let ARITH_SUC = 
 prove
  ((parse_term @"(!n. SUC(NUMERAL n) = NUMERAL(SUC n)) /\
    (SUC _0 = BIT1 _0) /\
    (!n. SUC (BIT0 n) = BIT1 n) /\
    (!n. SUC (BIT1 n) = BIT0 (SUC n))"),
   REWRITE_TAC[NUMERAL; BIT0; BIT1; DENUMERAL ADD_CLAUSES]);;

let ARITH_PRE = 
 prove
  ((parse_term @"(!n. PRE(NUMERAL n) = NUMERAL(PRE n)) /\
    (PRE _0 = _0) /\
    (!n. PRE(BIT0 n) = if n = _0 then _0 else BIT1 (PRE n)) /\
    (!n. PRE(BIT1 n) = BIT0 n)"),
   REWRITE_TAC[NUMERAL; BIT1; BIT0; DENUMERAL PRE] |>THEN<| INDUCT_TAC |>THEN<|
   REWRITE_TAC[NUMERAL; DENUMERAL PRE; DENUMERAL ADD_CLAUSES; DENUMERAL NOT_SUC;
               ARITH_ZERO]);;

let ARITH_ADD = 
 prove
  ((parse_term @"(!m n. NUMERAL(m) + NUMERAL(n) = NUMERAL(m + n)) /\
    (_0 + _0 = _0) /\
    (!n. _0 + BIT0 n = BIT0 n) /\
    (!n.        _0 + BIT1 n = BIT1 n) /\
    (!n.   BIT0 n + _0 = BIT0 n) /\
    (!n.   BIT1 n + _0 = BIT1 n) /\
    (!m n. BIT0 m + BIT0 n = BIT0 (m + n)) /\
    (!m n. BIT0 m + BIT1 n = BIT1 (m + n)) /\
    (!m n. BIT1 m + BIT0 n = BIT1 (m + n)) /\
    (!m n. BIT1 m + BIT1 n = BIT0 (SUC(m + n)))"),
   PURE_REWRITE_TAC[NUMERAL; BIT0; BIT1; DENUMERAL ADD_CLAUSES; SUC_INJ] |>THEN<|
   REWRITE_TAC[ADD_AC]);;

let ARITH_MULT = 
 prove
  ((parse_term @"(!m n. NUMERAL(m) * NUMERAL(n) = NUMERAL(m * n)) /\
    (_0 * _0 = _0) /\
    (!n. _0 * BIT0 n = _0) /\
    (!n. _0 * BIT1 n = _0) /\
    (!n. BIT0 n * _0 = _0) /\
    (!n. BIT1 n * _0 = _0) /\
    (!m n. BIT0 m * BIT0 n = BIT0 (BIT0 (m * n))) /\
    (!m n. BIT0 m * BIT1 n = BIT0 m + BIT0 (BIT0 (m * n))) /\
    (!m n. BIT1 m * BIT0 n = BIT0 n + BIT0 (BIT0 (m * n))) /\
    (!m n. BIT1 m * BIT1 n = BIT1 m + BIT0 n + BIT0 (BIT0 (m * n)))"),
   PURE_REWRITE_TAC[NUMERAL; BIT0; BIT1; DENUMERAL MULT_CLAUSES;
                    DENUMERAL ADD_CLAUSES; SUC_INJ] |>THEN<|
   REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; ADD_AC]);;
 
let ARITH_EXP = 
 prove
     ((parse_term @"(!m n. (NUMERAL m) EXP (NUMERAL n) = NUMERAL(m EXP n)) /\
       (_0 EXP _0 = BIT1 _0) /\
       (!m. (BIT0 m) EXP _0 = BIT1 _0) /\
       (!m. (BIT1 m) EXP _0 = BIT1 _0) /\
       (!n. _0 EXP (BIT0 n) = (_0 EXP n) * (_0 EXP n)) /\
       (!m n. (BIT0 m) EXP (BIT0 n) = ((BIT0 m) EXP n) * ((BIT0 m) EXP n)) /\
       (!m n. (BIT1 m) EXP (BIT0 n) = ((BIT1 m) EXP n) * ((BIT1 m) EXP n)) /\
       (!n. _0 EXP (BIT1 n) = _0) /\
       (!m n. (BIT0 m) EXP (BIT1 n) =
            BIT0 m * ((BIT0 m) EXP n) * ((BIT0 m) EXP n)) /\
       (!m n. (BIT1 m) EXP (BIT1 n) =
            BIT1 m * ((BIT1 m) EXP n) * ((BIT1 m) EXP n))"),
      REWRITE_TAC[NUMERAL] |>THEN<| REPEAT STRIP_TAC |>THEN<|
      TRY(GEN_REWRITE_TAC (LAND_CONV << RAND_CONV) [BIT0; BIT1]) |>THEN<|
      REWRITE_TAC[DENUMERAL EXP; DENUMERAL MULT_CLAUSES; EXP_ADD]);;

let ARITH_EVEN =
 prove
   ((parse_term @"(!n. EVEN(NUMERAL n) <=> EVEN n) /\
     (EVEN _0 <=> T) /\
     (!n. EVEN(BIT0 n) <=> T) /\
     (!n. EVEN(BIT1 n) <=> F)"),
    REWRITE_TAC[NUMERAL; BIT1; BIT0; DENUMERAL EVEN; EVEN_ADD]);;

let ARITH_ODD =
 prove
   ((parse_term @"(!n. ODD(NUMERAL n) <=> ODD n) /\
     (ODD _0 <=> F) /\
     (!n. ODD(BIT0 n) <=> F) /\
     (!n. ODD(BIT1 n) <=> T)"),
    REWRITE_TAC[NUMERAL; BIT1; BIT0; DENUMERAL ODD; ODD_ADD]);;

let ARITH_LE =
 prove
   ((parse_term @"(!m n. NUMERAL m <= NUMERAL n <=> m <= n) /\
     ((_0 <= _0) <=> T) /\
     (!n. (BIT0 n <= _0) <=> n <= _0) /\
     (!n. (BIT1 n <= _0) <=> F) /\
     (!n. (_0 <= BIT0 n) <=> T) /\
     (!n. (_0 <= BIT1 n) <=> T) /\
     (!m n. (BIT0 m <= BIT0 n) <=> m <= n) /\
     (!m n. (BIT0 m <= BIT1 n) <=> m <= n) /\
     (!m n. (BIT1 m <= BIT0 n) <=> m < n) /\
     (!m n. (BIT1 m <= BIT1 n) <=> m <= n)"),
    REWRITE_TAC[NUMERAL; BIT1; BIT0; DENUMERAL NOT_SUC;
        DENUMERAL(GSYM NOT_SUC); SUC_INJ] |>THEN<|
    REWRITE_TAC[DENUMERAL LE_0] |>THEN<| REWRITE_TAC[DENUMERAL LE; GSYM MULT_2] |>THEN<|
    REWRITE_TAC[LE_MULT_LCANCEL; SUC_INJ;
                DENUMERAL MULT_EQ_0; DENUMERAL NOT_SUC] |>THEN<|
    REWRITE_TAC[DENUMERAL NOT_SUC] |>THEN<| REWRITE_TAC[LE_SUC_LT] |>THEN<|
    REWRITE_TAC[LT_MULT_LCANCEL] |>THEN<|
    SUBGOAL_THEN (parse_term @"2 = SUC 1") (fun th -> REWRITE_TAC[th]) |>THENL<|
     [REWRITE_TAC[NUMERAL; BIT0; BIT1; DENUMERAL ADD_CLAUSES];
      REWRITE_TAC[DENUMERAL NOT_SUC; NOT_SUC; EQ_MULT_LCANCEL] |>THEN<|
      REWRITE_TAC[ONCE_REWRITE_RULE[DISJ_SYM] LE_LT] |>THEN<|
      MAP_EVERY X_GEN_TAC [(parse_term @"m:num"); (parse_term @"n:num")] |>THEN<|
      SUBGOAL_THEN (parse_term @"~(SUC 1 * m = SUC (SUC 1 * n))")
        (fun th -> REWRITE_TAC[th]) |>THEN<|
      DISCH_THEN(MP_TAC << AP_TERM (parse_term @"EVEN")) |>THEN<|
      REWRITE_TAC[EVEN_MULT; EVEN_ADD; NUMERAL; BIT1; EVEN]]);;

let ARITH_LT =
 prove
   ((parse_term @"(!m n. NUMERAL m < NUMERAL n <=> m < n) /\
     ((_0 < _0) <=> F) /\
     (!n. (BIT0 n < _0) <=> F) /\
     (!n. (BIT1 n < _0) <=> F) /\
     (!n. (_0 < BIT0 n) <=> _0 < n) /\
     (!n. (_0 < BIT1 n) <=> T) /\
     (!m n. (BIT0 m < BIT0 n) <=> m < n) /\
     (!m n. (BIT0 m < BIT1 n) <=> m <= n) /\
     (!m n. (BIT1 m < BIT0 n) <=> m < n) /\
     (!m n. (BIT1 m < BIT1 n) <=> m < n)"),
    REWRITE_TAC[NUMERAL; GSYM NOT_LE; ARITH_LE] |>THEN<|
    REWRITE_TAC[DENUMERAL LE]);;

let ARITH_GE = REWRITE_RULE[GSYM GE; GSYM GT] ARITH_LE;;

let ARITH_GT = REWRITE_RULE[GSYM GE; GSYM GT] ARITH_LT;;

let ARITH_EQ =
 prove
   ((parse_term @"(!m n. (NUMERAL m = NUMERAL n) <=> (m = n)) /\
     ((_0 = _0) <=> T) /\
     (!n. (BIT0 n = _0) <=> (n = _0)) /\
     (!n. (BIT1 n = _0) <=> F) /\
     (!n. (_0 = BIT0 n) <=> (_0 = n)) /\
     (!n. (_0 = BIT1 n) <=> F) /\
     (!m n. (BIT0 m = BIT0 n) <=> (m = n)) /\
     (!m n. (BIT0 m = BIT1 n) <=> F) /\
     (!m n. (BIT1 m = BIT0 n) <=> F) /\
     (!m n. (BIT1 m = BIT1 n) <=> (m = n))"),
    REWRITE_TAC[NUMERAL; GSYM LE_ANTISYM; ARITH_LE] |>THEN<|
    REWRITE_TAC[LET_ANTISYM; LTE_ANTISYM; DENUMERAL LE_0]);;

let ARITH_SUB =
 prove
   ((parse_term @"(!m n. NUMERAL m - NUMERAL n = NUMERAL(m - n)) /\
     (_0 - _0 = _0) /\
     (!n. _0 - BIT0 n = _0) /\
     (!n. _0 - BIT1 n = _0) /\
     (!n. BIT0 n - _0 = BIT0 n) /\
     (!n. BIT1 n - _0 = BIT1 n) /\
     (!m n. BIT0 m - BIT0 n = BIT0 (m - n)) /\
     (!m n. BIT0 m - BIT1 n = PRE(BIT0 (m - n))) /\
     (!m n. BIT1 m - BIT0 n = if n <= m then BIT1 (m - n) else _0) /\
     (!m n. BIT1 m - BIT1 n = BIT0 (m - n))"),
    REWRITE_TAC[NUMERAL; DENUMERAL SUB_0] |>THEN<| PURE_REWRITE_TAC[BIT0; BIT1] |>THEN<|
    REWRITE_TAC[GSYM MULT_2; SUB_SUC; LEFT_SUB_DISTRIB] |>THEN<|
    REWRITE_TAC[SUB] |>THEN<| REPEAT GEN_TAC |>THEN<| COND_CASES_TAC |>THEN<|
    REWRITE_TAC[DENUMERAL SUB_EQ_0] |>THEN<|
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) |>THEN<|
    ASM_REWRITE_TAC[LE_SUC_LT; LT_MULT_LCANCEL; ARITH_EQ] |>THEN<|
    POP_ASSUM(CHOOSE_THEN SUBST1_TAC << REWRITE_RULE[LE_EXISTS]) |>THEN<|
    REWRITE_TAC[ADD1; LEFT_ADD_DISTRIB] |>THEN<|
    REWRITE_TAC[ADD_SUB2; GSYM ADD_ASSOC]);;

let ARITH = 
  end_itlist CONJ
    [ARITH_ZERO; ARITH_SUC; ARITH_PRE;
     ARITH_ADD; ARITH_MULT; ARITH_EXP;
     ARITH_EVEN; ARITH_ODD;
     ARITH_EQ; ARITH_LE; ARITH_LT; ARITH_GE; ARITH_GT;
     ARITH_SUB];;

(* ------------------------------------------------------------------------- *)
(* Now more delicate conversions for situations where efficiency matters.    *)
(* ------------------------------------------------------------------------- *)

// NUM_EQ_CONV: Proves equality or inequality of two numerals.
// NUM_LE_CONV: Proves whether one numeral is less than or equal to another.
// NUM_LT_CONV: Proves whether one numeral is less than another.
// NUM_GE_CONV: Proves whether one numeral is greater than or equal to another.
// NUM_GT_CONV: Proves whether one numeral is greater than another.
let NUM_EQ_CONV,NUM_LE_CONV,NUM_LT_CONV,NUM_GE_CONV,NUM_GT_CONV =
    let ARITH_GE',ARITH_GT' = 
     (CONJ_PAIR << prove)
      ((parse_term @"(NUMERAL m >= NUMERAL n <=> n <= m) /\
        (NUMERAL m > NUMERAL n <=> n < m)"),
         REWRITE_TAC[GE; GT; NUMERAL])
    let NUM_EQ_CONV' =
      REPEATC(GEN_REWRITE_CONV I [CONJUNCT2 ARITH_EQ])
    let NUM_LL_CONV' =
      REPEATC(GEN_REWRITE_CONV I [CONJUNCT2 ARITH_LE; CONJUNCT2 ARITH_LT]) in
    let GEN_NUM_REL_CONV th cnv = 
     GEN_REWRITE_CONV I [th] |>THENC<| cnv in
     GEN_NUM_REL_CONV (CONJUNCT1 ARITH_EQ) NUM_EQ_CONV',
     GEN_NUM_REL_CONV (CONJUNCT1 ARITH_LE) NUM_LL_CONV',
     GEN_NUM_REL_CONV (CONJUNCT1 ARITH_LT) NUM_LL_CONV',
     GEN_NUM_REL_CONV ARITH_GE' NUM_LL_CONV',
     GEN_NUM_REL_CONV ARITH_GT' NUM_LL_CONV';;

/// Proves whether a natural number numeral is even.
let NUM_EVEN_CONV =
    let tth,rths = CONJ_PAIR ARITH_EVEN in
    GEN_REWRITE_CONV I [tth] |>THENC<| GEN_REWRITE_CONV I [rths];;

/// Proves whether a natural number numeral is odd.
let NUM_ODD_CONV =
    let tth,rths = CONJ_PAIR ARITH_ODD in
    GEN_REWRITE_CONV I [tth] |>THENC<| GEN_REWRITE_CONV I [rths];;

// NUM_SUC_CONV: Proves what the successor of a natural number numeral is.
// NUM_ADD_CONV: Proves what the sum of two natural number numerals is.
// NUM_MULT_CONV: Proves what the product of two natural number numerals is.
// NUM_EXP_CONV: Proves what the exponential of two natural number numerals is.
let NUM_SUC_CONV,NUM_ADD_CONV,NUM_MULT_CONV,NUM_EXP_CONV =
    let NUM_SUC_CONV,NUM_ADD_CONV',NUM_ADD_CONV =
      let std_tm = rand (parse_term @"2") in
      let bit0_tm,bz_tm = dest_comb std_tm in
      let bit1_tm,zero_tm = dest_comb bz_tm in
      let n_tm = (parse_term @"n:num") 
      let m_tm = (parse_term @"m:num") in
      let sths = 
          (CONJUNCTS << prove)
            ((parse_term @"(SUC _0 = BIT1 _0) /\
              (SUC(BIT0 n) = BIT1 n) /\
              (SUC(BIT1 n) = BIT0(SUC n))"),
              SUBST1_TAC(SYM(SPEC (parse_term @"_0") NUMERAL)) |>THEN<|
              REWRITE_TAC[BIT0; BIT1] |>THEN<|
              REWRITE_TAC[ADD_CLAUSES])
      match sths with
      | [sth_z; sth_0; sth_1] ->
          let aths =
           (CONJUNCTS << prove)
            ((parse_term @"(_0 + n = n) /\
              (n + _0 = n) /\
              (BIT0 m + BIT0 n = BIT0 (m + n)) /\
              (BIT0 m + BIT1 n = BIT1 (m + n)) /\
              (BIT1 m + BIT0 n = BIT1 (m + n)) /\
              (BIT1 m + BIT1 n = BIT0 (SUC (m + n)))"),
             SUBST1_TAC(SYM(SPEC (parse_term @"_0") NUMERAL)) |>THEN<|
             REWRITE_TAC[BIT0; BIT1] |>THEN<|
             REWRITE_TAC[ADD_CLAUSES] |>THEN<| REWRITE_TAC[ADD_AC])
          match aths with
          | [ath_0x; ath_x0; ath_00; ath_01; ath_10; ath_11] ->
              let cths =
                  (CONJUNCTS << prove)
                    ((parse_term @"(SUC(_0 + n) = SUC n) /\
                      (SUC(n + _0) = SUC n) /\
                      (SUC(BIT0 m + BIT0 n) = BIT1(m + n)) /\
                      (SUC(BIT0 m + BIT1 n) = BIT0(SUC(m + n))) /\
                      (SUC(BIT1 m + BIT0 n) = BIT0(SUC(m + n))) /\
                      (SUC(BIT1 m + BIT1 n) = BIT1(SUC (m + n)))"),
                     SUBST1_TAC(SYM(SPEC (parse_term @"_0") NUMERAL)) |>THEN<|
                     REWRITE_TAC[BIT0; BIT1] |>THEN<|
                     REWRITE_TAC[ADD_CLAUSES] |>THEN<| REWRITE_TAC[ADD_AC])
              match cths with
              | [cth_0x; cth_x0; cth_00; cth_01; cth_10; cth_11] ->
                  let pth_suc =
                   prove
                    ((parse_term @"SUC(NUMERAL n) = NUMERAL(SUC n)"),
                     REWRITE_TAC[NUMERAL])
                  let pth_add =
                   prove
                    ((parse_term @"NUMERAL m + NUMERAL n = NUMERAL(m + n)"),
                     REWRITE_TAC[NUMERAL]) in
                  let rec raw_suc_conv tm =
                    let otm = rand tm in
                    if otm = zero_tm then sth_z else
                    let btm,ntm = dest_comb otm in
                    if btm = bit0_tm then INST [ntm,n_tm] sth_0 else
                    let th = INST [ntm,n_tm] sth_1 in
                    let ltm,rtm = dest_comb(rand(concl th)) in
                    TRANS th (AP_TERM ltm (raw_suc_conv rtm)) in
                  let rec raw_add_conv tm =
                    let atm,rtm = dest_comb tm in
                    let ltm = rand atm in
                    if ltm = zero_tm then INST [rtm,n_tm] ath_0x
                    else if rtm = zero_tm then INST [ltm,n_tm] ath_x0 else
                    let lbit,larg = dest_comb ltm
                    let rbit,rarg = dest_comb rtm in
                    if lbit = bit0_tm then
                       if rbit = bit0_tm then
                          let th = INST [larg,m_tm; rarg,n_tm] ath_00 in
                          let ltm,rtm = dest_comb(rand(concl th)) in
                          TRANS th (AP_TERM ltm (raw_add_conv rtm))
                       else
                          let th = INST [larg,m_tm; rarg,n_tm] ath_01 in
                          let ltm,rtm = dest_comb(rand(concl th)) in
                          TRANS th (AP_TERM ltm (raw_add_conv rtm))
                    else
                       if rbit = bit0_tm then
                          let th = INST [larg,m_tm; rarg,n_tm] ath_10 in
                          let ltm,rtm = dest_comb(rand(concl th)) in
                          TRANS th (AP_TERM ltm (raw_add_conv rtm))
                       else
                          let th = INST [larg,m_tm; rarg,n_tm] ath_11 in
                          let ltm,rtm = dest_comb(rand(concl th)) in
                          TRANS th (AP_TERM ltm (raw_adc_conv rtm))
                  and raw_adc_conv tm =
                    let atm,rtm = dest_comb(rand tm) in
                    let ltm = rand atm in
                    if ltm = zero_tm then
                       let th = INST [rtm,n_tm] cth_0x in
                       TRANS th (raw_suc_conv (rand(concl th)))
                    else if rtm = zero_tm then
                       let th = INST [ltm,n_tm] cth_x0 in
                       TRANS th (raw_suc_conv (rand(concl th)))
                    else
                       let lbit,larg = dest_comb ltm
                       let rbit,rarg = dest_comb rtm in
                       if lbit = bit0_tm then
                          if rbit = bit0_tm then
                             let th = INST [larg,m_tm; rarg,n_tm] cth_00 in
                             let ltm,rtm = dest_comb(rand(concl th)) in
                             TRANS th (AP_TERM ltm (raw_add_conv rtm))
                          else
                             let th = INST [larg,m_tm; rarg,n_tm] cth_01 in
                             let ltm,rtm = dest_comb(rand(concl th)) in
                             TRANS th (AP_TERM ltm (raw_adc_conv rtm))
                       else
                          if rbit = bit0_tm then
                             let th = INST [larg,m_tm; rarg,n_tm] cth_10 in
                             let ltm,rtm = dest_comb(rand(concl th)) in
                             TRANS th (AP_TERM ltm (raw_adc_conv rtm))
                          else
                             let th = INST [larg,m_tm; rarg,n_tm] cth_11 in
                             let ltm,rtm = dest_comb(rand(concl th)) in
                             TRANS th (AP_TERM ltm (raw_adc_conv rtm)) in
                  let NUM_SUC_CONV tm =
                    let th = INST [rand(rand tm),n_tm] pth_suc in
                    let ctm = concl th in
                    if lhand ctm <> tm then failwith "NUM_SUC_CONV" else
                    let ltm,rtm = dest_comb(rand ctm) in
                    TRANS th (AP_TERM ltm (raw_suc_conv rtm))
                  let NUM_ADD_CONV tm =
                    let atm,rtm = dest_comb tm in
                    let ltm = rand atm in
                    let th = INST [rand ltm,m_tm; rand rtm,n_tm] pth_add in
                    let ctm = concl th in
                    if lhand ctm <> tm then failwith "NUM_ADD_CONV" else
                    let ltm,rtm = dest_comb(rand(concl th)) in
                    TRANS th (AP_TERM ltm (raw_add_conv rtm)) in
                  NUM_SUC_CONV,raw_add_conv,NUM_ADD_CONV
              | _ -> failwith "cths: Unhandled case."
          | _ -> failwith "aths: Unhandled case."
      | _ -> failwith "sths: Unhandled case."

    let NUM_MULT_CONV' =
      let p_tm  = (parse_term @"p:num")
      let x_tm  = (parse_term @"x:num")
      let y_tm  = (parse_term @"y:num")
      let u_tm  = (parse_term @"u:num")
      let v_tm  = (parse_term @"v:num")
      let w_tm  = (parse_term @"w:num")
      let z_tm  = (parse_term @"z:num")
      let u_tm' = (parse_term @"u':num")
      let w_tm' = (parse_term @"w':num")
      let a_tm  = (parse_term @"a:num")
      let b_tm  = (parse_term @"b:num")
      let c_tm  = (parse_term @"c:num")
      let d_tm  = (parse_term @"d:num")
      let e_tm  = (parse_term @"e:num")
      let c_tm' = (parse_term @"c':num")
      let d_tm' = (parse_term @"d':num")
      let e_tm' = (parse_term @"e':num")
      let s_tm  = (parse_term @"s:num")
      let t_tm  = (parse_term @"t:num")
      let q_tm  = (parse_term @"q:num")
      let r_tm  = (parse_term @"r:num") in
      let pth =
       prove
        ((parse_term @"(u' + v = x) ==>
         (w' + z = y) ==>
         (p * u = u') ==>
         (p * w = w') ==>
         (u + v = a) ==>
         (w + z = b) ==>
         (a * b = c) ==>
         (u' * w = d) ==>
         (v * z = e) ==>
         (p * e = e') ==>
         (p * d = d') ==>
         (p * c = c') ==>
         (d' + e = s) ==>
         (d + e' = t) ==>
         (s + c' = q) ==>
         (r + t = q) ==> (x * y = r)"),
        MAP_EVERY (K (DISCH_THEN(SUBST1_TAC << SYM))) (0--14) |>THEN<|
        REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] |>THEN<|
        REWRITE_TAC[MULT_AC] |>THEN<|
        ONCE_REWRITE_TAC[AC ADD_AC
         (parse_term @"a + (b + c) + d + e = (a + c + d) + (b + e)")] |>THEN<|
        SIMP_TAC[EQ_ADD_RCANCEL] |>THEN<| REWRITE_TAC[ADD_AC]) in
      let dest_mul = dest_binop (parse_term @"(* )") in
      let mk_raw_numeral =
        let Z = Choice.get <| mk_const("_0",[])
        let BIT0 = Choice.get <| mk_const("BIT0",[])
        let BIT1 = Choice.get <| mk_const("BIT1",[]) in
        let rec mk_num n =
          if n = Int 0 then Z else
          mk_comb((if mod_num n (Int 2) = Int 0 then BIT0 else BIT1),
                  mk_num(quo_num n (Int 2))) in
        mk_num in
      let rec dest_raw_numeral tm =
        if 
         try 
          fst(dest_const tm) = "_0" 
          with 
          | Failure _ -> false 
        then Int 0 
        else
          let l,r = dest_comb tm in
          let n = Int 2 * dest_raw_numeral r in
          let cn = fst(dest_const l) in
          if cn = "BIT0" then n
          elif cn = "BIT1" then n + Int 1
          else failwith "dest_raw_numeral" in
      let rec sizeof_rawnumeral tm =
        if is_const tm then 0 
        else
          1 + sizeof_rawnumeral(rand tm) in
      let MULTIPLICATION_TABLE =
        let pth =
         prove
          ((parse_term @"(_0 * x = _0) /\
           (x * _0 = _0) /\
           (BIT1 _0 * x = x) /\
           (x * BIT1 _0 = x)"),
          REWRITE_TAC[BIT1; DENUMERAL MULT_CLAUSES]) in
        let mk_mul = mk_binop (parse_term @"(* )") in
        let odds = map (fun x -> 2 * x + 1) (0--7) in
        let nums = map (fun n -> mk_raw_numeral(Int n)) odds in
        let pairs = allpairs mk_mul nums nums in
        let ths = map (REWRITE_CONV[ARITH]) pairs in
        GEN_REWRITE_CONV I (pth::ths) in
      let NUM_MULT_EVEN_CONV' =
        let pth =
         prove
          ((parse_term @"(BIT0 x * y = BIT0(x * y)) /\
           (x * BIT0 y = BIT0(x * y))"),
          REWRITE_TAC[BIT0; BIT1; DENUMERAL MULT_CLAUSES;
                      DENUMERAL ADD_CLAUSES] |>THEN<|
          REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC]) in
        GEN_REWRITE_CONV I [pth] in
      let right_th =
       prove
        ((parse_term @"s * BIT1 x = s + BIT0 (s * x)"),
        REWRITE_TAC[BIT0; BIT1; DENUMERAL ADD_CLAUSES;
                    DENUMERAL MULT_CLAUSES] |>THEN<|
        REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC])
      let left_th =
       prove
        ((parse_term @"BIT1 x * s = s + BIT0 (x * s)"),
        REWRITE_TAC[BIT0; BIT1; DENUMERAL ADD_CLAUSES;
                    DENUMERAL MULT_CLAUSES] |>THEN<|
        REWRITE_TAC[RIGHT_ADD_DISTRIB; ADD_AC]) in
      let LEFT_REWR_CONV = REWR_CONV left_th
      let RIGHT_REWR_CONV = REWR_CONV right_th in
      let rec NUM_MULT_CONV' tm =
        try 
         MULTIPLICATION_TABLE tm
        with 
        | Failure _ -> 
          try
            let th1 = NUM_MULT_EVEN_CONV' tm in
            let l,r = dest_comb(rand(concl th1)) in
            TRANS th1 (AP_TERM l (NUM_MULT_CONV' r))
          with 
          | Failure _ ->
           let xtm,ytm = dest_mul tm in
           let x = dest_raw_numeral xtm
           let y = dest_raw_numeral ytm in
           let NX = sizeof_rawnumeral xtm
           let NY = sizeof_rawnumeral ytm in
           let N2 = max NX NY in
           let N = (N2 + 1) / 2 in
           if NX < N || (N < 32 && NX < NY) then
             NUM_MULT_RIGHT_CONV' tm
           else if NY < N || N < 32 then
             NUM_MULT_LEFT_CONV' tm
           else
           let p = power_num (Int 2) (Int N) in
           let u = quo_num x p
           let w = quo_num y p in
           let u' = p * u
           let w' = p * w in
           let v = x - u'
           let z = y - w' in
           let a = u + v
           let b = w + z in
           let c = a * b in
           let d = u' * w
           let e = v * z in
           let e' = p * e
           let d' = p * d
           let c' = p * c in
           let s = d' + e
           let t = d + e' in
           let q = s + c' in
           let r = x * y in
           let ptm  = mk_raw_numeral p
           let xtm  = mk_raw_numeral x
           let ytm  = mk_raw_numeral y
           let utm  = mk_raw_numeral u
           let vtm  = mk_raw_numeral v
           let wtm  = mk_raw_numeral w
           let ztm  = mk_raw_numeral z
           let utm' = mk_raw_numeral u'
           let wtm' = mk_raw_numeral w'
           let atm  = mk_raw_numeral a
           let btm  = mk_raw_numeral b
           let ctm  = mk_raw_numeral c
           let dtm  = mk_raw_numeral d
           let etm  = mk_raw_numeral e
           let ctm' = mk_raw_numeral c'
           let dtm' = mk_raw_numeral d'
           let etm' = mk_raw_numeral e'
           let stm  = mk_raw_numeral s
           let ttm  = mk_raw_numeral t
           let qtm  = mk_raw_numeral q
           let rtm  = mk_raw_numeral r in
           let th0 = 
            INST
             [ptm,p_tm; xtm,x_tm; ytm,y_tm; utm,u_tm; vtm,v_tm; wtm,w_tm;
              ztm,z_tm; utm',u_tm'; wtm',w_tm'; atm,a_tm; btm,b_tm; ctm,c_tm;
              dtm,d_tm; etm,e_tm; ctm',c_tm'; dtm',d_tm'; etm',e_tm'; stm,s_tm;
              ttm,t_tm; qtm,q_tm; rtm,r_tm] pth in
           let th1 = MP th0 (NUM_ADD_CONV' (lhand(lhand(concl th0)))) in
           let th2 = MP th1 (NUM_ADD_CONV' (lhand(lhand(concl th1)))) in
           let th3 = MP th2 (NUM_MULT_CONV' (lhand(lhand(concl th2)))) in
           let th4 = MP th3 (NUM_MULT_CONV' (lhand(lhand(concl th3)))) in
           let th5 = MP th4 (NUM_ADD_CONV' (lhand(lhand(concl th4)))) in
           let th6 = MP th5 (NUM_ADD_CONV' (lhand(lhand(concl th5)))) in
           let th7 = MP th6 (NUM_MULT_CONV' (lhand(lhand(concl th6)))) in
           let th8 = MP th7 (NUM_MULT_CONV' (lhand(lhand(concl th7)))) in
           let th9 = MP th8 (NUM_MULT_CONV' (lhand(lhand(concl th8)))) in
           let tha = MP th9 (NUM_MULT_CONV' (lhand(lhand(concl th9)))) in
           let thb = MP tha (NUM_MULT_CONV' (lhand(lhand(concl tha)))) in
           let thc = MP thb (NUM_MULT_CONV' (lhand(lhand(concl thb)))) in
           let thd = MP thc (NUM_ADD_CONV' (lhand(lhand(concl thc)))) in
           let the = MP thd (NUM_ADD_CONV' (lhand(lhand(concl thd)))) in
           let thf = MP the (NUM_ADD_CONV' (lhand(lhand(concl the)))) in
           MP thf (NUM_ADD_CONV' (lhand(lhand(concl thf))))
      and NUM_MULT_RIGHT_CONV' tm =
         (RIGHT_REWR_CONV |>THENC<|
          (RAND_CONV(RAND_CONV NUM_MULT_CONV')) |>THENC<|
          NUM_ADD_CONV') tm
      and NUM_MULT_LEFT_CONV' tm =
         (LEFT_REWR_CONV |>THENC<|
          (RAND_CONV(RAND_CONV NUM_MULT_CONV')) |>THENC<|
          NUM_ADD_CONV') tm in
      NUM_MULT_CONV' in

    let NUM_MULT_CONV =
      let tconv = REWR_CONV(CONJUNCT1 ARITH_MULT) in
      tconv |>THENC<| RAND_CONV NUM_MULT_CONV' in

    let NUM_EXP_CONV =
      let pth0 =
       prove
        ((parse_term @"(x EXP n = y) ==> (y * y = z) ==> (x EXP (BIT0 n) = z)"),
         REPEAT(DISCH_THEN(SUBST1_TAC << SYM)) |>THEN<|
         REWRITE_TAC[BIT0; EXP_ADD])
      let pth1 =
       prove
        ((parse_term @"(x EXP n = y) ==> (y * y = w) ==> (x * w = z) ==> (x EXP (BIT1 n) = z)"),
        REPEAT(DISCH_THEN(SUBST1_TAC << SYM)) |>THEN<|
        REWRITE_TAC[BIT1; EXP_ADD; EXP])
      let pth =
       prove
        ((parse_term @"x EXP _0 = BIT1 _0"),
         MP_TAC (CONJUNCT1 EXP) |>THEN<| REWRITE_TAC[NUMERAL; BIT1] |>THEN<|
         DISCH_THEN MATCH_ACCEPT_TAC)
      let tth =
       prove
        ((parse_term @"(NUMERAL x) EXP (NUMERAL n) = x EXP n"),
         REWRITE_TAC[NUMERAL])
      let fth =
       prove
        ((parse_term @"x = NUMERAL x"),
         REWRITE_TAC[NUMERAL])
      let n = (parse_term @"n:num") 
      let w = (parse_term @"w:num") 
      let x = (parse_term @"x:num")
      let y = (parse_term @"y:num") 
      let z = (parse_term @"z:num")
      let Z = (parse_term @"_0") 
      let BIT0 = (parse_term @"BIT0")
      let mul = (parse_term @"(*)") in
      let tconv = GEN_REWRITE_CONV I [tth] in
      let rec NUM_EXP_CONV l r =
        if r = Z then INST [l,x] pth else
        let b,r' = dest_comb r in
        if b = BIT0 then
          let th1 = NUM_EXP_CONV l r' in
          let tm1 = rand(concl th1) in
          let th2 = NUM_MULT_CONV' (mk_binop mul tm1 tm1) in
          let tm2 = rand(concl th2) in
          MP (MP (INST [l,x; r',n; tm1,y; tm2,z] pth0) th1) th2
        else
          let th1 = NUM_EXP_CONV l r' in
          let tm1 = rand(concl th1) in
          let th2 = NUM_MULT_CONV' (mk_binop mul tm1 tm1) in
          let tm2 = rand(concl th2) in
          let th3 = NUM_MULT_CONV' (mk_binop mul l tm2) in
          let tm3 = rand(concl th3) in
          MP (MP (MP (INST [l,x; r',n; tm1,y; tm2,w; tm3,z] pth1) th1) th2) th3 in
      fun tm -> try let th = tconv tm in
                    let lop,r = dest_comb (rand(concl th)) in
                    let _,l = dest_comb lop in
                    let th' = NUM_EXP_CONV l r in
                    let tm' = rand(concl th') in
                    TRANS (TRANS th th') (INST [tm',x] fth)
                with Failure _ as e ->
                    nestedFailwith e "NUM_EXP_CONV" in
    NUM_SUC_CONV,NUM_ADD_CONV,NUM_MULT_CONV,NUM_EXP_CONV;;

/// Proves what the cutoff predecessor of a natural number numeral is.
let NUM_PRE_CONV =
    let tth =
     prove
      ((parse_term @"PRE 0 = 0"),
       REWRITE_TAC[PRE]) in
    let pth =
     prove
      ((parse_term @"(SUC m = n) ==> (PRE n = m)"),
       DISCH_THEN(SUBST1_TAC << SYM) |>THEN<| REWRITE_TAC[PRE])
    let m = (parse_term @"m:num") 
    let n = (parse_term @"n:num") in
    let suc = (parse_term @"SUC") in
    let pre = (parse_term @"PRE") in
    fun tm -> try let l,r = dest_comb tm in
                  if not (l = pre) then fail() else
                  let x = dest_numeral r in
                  if x = Int 0 then tth else
                  let tm' = mk_numeral (x - Int 1) in
                  let th1 = NUM_SUC_CONV (mk_comb(suc,tm')) in
                  MP (INST [tm',m; r,n] pth) th1
              with Failure _ as e -> nestedFailwith e "NUM_PRE_CONV";;

/// Proves what the cutoff difference of two natural number numerals is.
let NUM_SUB_CONV =
    let pth0 =
     prove
      ((parse_term @"p <= n ==> (p - n = 0)"),
       REWRITE_TAC[SUB_EQ_0])
    let pth1 =
     prove
      ((parse_term @"(m + n = p) ==> (p - n = m)"),
       DISCH_THEN(SUBST1_TAC << SYM) |>THEN<|
       REWRITE_TAC[ADD_SUB])
    let m = (parse_term @"m:num") 
    let n = (parse_term @"n:num") 
    let p = (parse_term @"p:num")
    let minus = (parse_term @"(-)")
    let plus = (parse_term @"(+)")
    let le = (parse_term @"(<=)") in
    fun tm -> try let l,r = dest_binop minus tm in
                  let ln = dest_numeral l
                  let rn = dest_numeral r in
                  if  ln <= rn then
                    let pth = INST [l,p; r,n] pth0
                    let th0 = EQT_ELIM(NUM_LE_CONV (mk_binop le l r)) in
                    MP pth th0
                  else
                    let kn = ln - rn in
                    let k = mk_numeral kn in
                    let pth = INST [k,m; l,p; r,n] pth1
                    let th0 = NUM_ADD_CONV (mk_binop plus k r) in
                    MP pth th0
              with Failure _ as e -> nestedFailwith e "NUM_SUB_CONV";;

// NUM_DIV_CONV: Proves what the truncated quotient of two natural number numerals is.
// NUM_MOD_CONV: Proves what the remainder on dividing one natural number numeral by another is.
let NUM_DIV_CONV,NUM_MOD_CONV =
    let pth =
     prove
      ((parse_term @"(q * n + r = m) ==> r < n ==> (m DIV n = q) /\ (m MOD n = r)"),
       MESON_TAC[DIVMOD_UNIQ])
    let m = (parse_term @"m:num") 
    let n = (parse_term @"n:num") 
    let q = (parse_term @"q:num") 
    let r = (parse_term @"r:num")
    let dtm = (parse_term @"(DIV)") 
    let mtm = (parse_term @"(MOD)") in
    let NUM_DIVMOD_CONV x y =
      let k = quo_num x y
      let l = mod_num x y in
      let th0 = INST [mk_numeral x,m; mk_numeral y,n;
                      mk_numeral k,q; mk_numeral l,r] pth in
      let tm0 = lhand(lhand(concl th0)) in
      let th1 = (LAND_CONV NUM_MULT_CONV |>THENC<| NUM_ADD_CONV) tm0 in
      let th2 = MP th0 th1 in
      let tm2 = lhand(concl th2) in
      MP th2 (EQT_ELIM(NUM_LT_CONV tm2)) in
    (fun tm -> try let xt,yt = dest_binop dtm tm in
                   CONJUNCT1(NUM_DIVMOD_CONV (dest_numeral xt) (dest_numeral yt))
               with Failure _ as e -> nestedFailwith e "NUM_DIV_CONV"),
    (fun tm -> try let xt,yt = dest_binop mtm tm in
                   CONJUNCT2(NUM_DIVMOD_CONV (dest_numeral xt) (dest_numeral yt))
               with Failure _ as e -> nestedFailwith e "NUM_MOD_CONV");;

/// Proves what the factorial of a natural number numeral is.
let NUM_FACT_CONV =
    let suc = (parse_term @"SUC")
    let mul = (parse_term @"(*)") in
    let pth_0 =
     prove
      ((parse_term @"FACT 0 = 1"),
       REWRITE_TAC[FACT])
    let pth_suc =
     prove
      ((parse_term @"(SUC x = y) ==> (FACT x = w) ==> (y * w = z) ==> (FACT y = z)"),
       REPEAT (DISCH_THEN(SUBST1_TAC << SYM)) |>THEN<|
       REWRITE_TAC[FACT])
    let w = (parse_term @"w:num") 
    let x = (parse_term @"x:num") 
    let y = (parse_term @"y:num") 
    let z = (parse_term @"z:num") in
    let mksuc n =
      let n' = n - (Int 1) in
      NUM_SUC_CONV (mk_comb(suc,mk_numeral n')) in
    let rec NUM_FACT_CONV n =
      if n = Int 0 then pth_0 else
      let th0 = mksuc n in
      let tmx = rand(lhand(concl th0)) in
      let tm0 = rand(concl th0) in
      let th1 = NUM_FACT_CONV (n - Int 1) in
      let tm1 = rand(concl th1) in
      let th2 = NUM_MULT_CONV (mk_binop mul tm0 tm1) in
      let tm2 = rand(concl th2) in
      let pth = INST [tmx,x; tm0, y; tm1,w; tm2,z] pth_suc in
      MP (MP (MP pth th0) th1) th2 in
    fun tm ->
      try let l,r = dest_comb tm in
          if fst(dest_const l) = "FACT"
          then NUM_FACT_CONV (dest_numeral r)
          else fail()
      with Failure _ as e -> nestedFailwith e "NUM_FACT_CONV";;

/// Proves what the maximum of two natural number numerals is.
let NUM_MAX_CONV =
    REWR_CONV MAX |>THENC<|
    RATOR_CONV(RATOR_CONV(RAND_CONV NUM_LE_CONV)) |>THENC<|
    GEN_REWRITE_CONV I [COND_CLAUSES];;

/// Proves what the minimum of two natural number numerals is.
let NUM_MIN_CONV =
    REWR_CONV MIN |>THENC<|
    RATOR_CONV(RATOR_CONV(RAND_CONV NUM_LE_CONV)) |>THENC<|
    GEN_REWRITE_CONV I [COND_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* Final hack-together.                                                      *)
(* ------------------------------------------------------------------------- *)

/// Performs relational operation on natural number numerals by proof.
let NUM_REL_CONV : conv =
    let gconv_net = 
     itlist (uncurry net_of_conv)
      [(parse_term @"NUMERAL m < NUMERAL n"),NUM_LT_CONV;
       (parse_term @"NUMERAL m <= NUMERAL n"),NUM_LE_CONV;
       (parse_term @"NUMERAL m > NUMERAL n"),NUM_GT_CONV;
       (parse_term @"NUMERAL m >= NUMERAL n"),NUM_GE_CONV;
       (parse_term @"NUMERAL m = NUMERAL n"),NUM_EQ_CONV]
      (basic_net()) in
    REWRITES_CONV gconv_net;;

/// Performs one arithmetic or relational operation on natural number numerals by proof.
let NUM_RED_CONV =
    let gconv_net = 
     itlist (uncurry net_of_conv)
      [(parse_term @"SUC(NUMERAL n)"),NUM_SUC_CONV;
       (parse_term @"PRE(NUMERAL n)"),NUM_PRE_CONV;
       (parse_term @"FACT(NUMERAL n)"),NUM_FACT_CONV;
       (parse_term @"NUMERAL m < NUMERAL n"),NUM_LT_CONV;
       (parse_term @"NUMERAL m <= NUMERAL n"),NUM_LE_CONV;
       (parse_term @"NUMERAL m > NUMERAL n"),NUM_GT_CONV;
       (parse_term @"NUMERAL m >= NUMERAL n"),NUM_GE_CONV;
       (parse_term @"NUMERAL m = NUMERAL n"),NUM_EQ_CONV;
       (parse_term @"EVEN(NUMERAL n)"),NUM_EVEN_CONV;
       (parse_term @"ODD(NUMERAL n)"),NUM_ODD_CONV;
       (parse_term @"NUMERAL m + NUMERAL n"),NUM_ADD_CONV;
       (parse_term @"NUMERAL m - NUMERAL n"),NUM_SUB_CONV;
       (parse_term @"NUMERAL m * NUMERAL n"),NUM_MULT_CONV;
       (parse_term @"(NUMERAL m) EXP (NUMERAL n)"),NUM_EXP_CONV;
       (parse_term @"(NUMERAL m) DIV (NUMERAL n)"),NUM_DIV_CONV;
       (parse_term @"(NUMERAL m) MOD (NUMERAL n)"),NUM_MOD_CONV;
       (parse_term @"MAX (NUMERAL m) (NUMERAL n)"),NUM_MAX_CONV;
       (parse_term @"MIN (NUMERAL m) (NUMERAL n)"),NUM_MIN_CONV]
      (basic_net()) in
    REWRITES_CONV gconv_net;;

/// Evaluate subexpressions built up from natural number numerals, by proof.
let NUM_REDUCE_CONV = DEPTH_CONV NUM_RED_CONV;;

/// Evaluate subexpressions of goal built up from natural number numerals.
let NUM_REDUCE_TAC = CONV_TAC NUM_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* I do like this after all...                                               *)
(* ------------------------------------------------------------------------- *)

/// Provides definitional axiom for a nonzero numeral.
let num_CONV =
    let SUC_tm = (parse_term @"SUC") in
    fun tm ->
      let n = dest_numeral tm - Int 1 in
      if n < Int 0 then failwith "num_CONV" else
      let tm' = mk_numeral n in
      SYM(NUM_SUC_CONV (mk_comb(SUC_tm,tm')));;

(* ------------------------------------------------------------------------- *)
(* Expands "!n. n < numeral-constant ==> P(n)" into all the cases.           *)
(* ------------------------------------------------------------------------- *)

/// <summary>
/// Expand a numerical range <c>!i. i < n ==> P[i]</c>.
/// </summary>
let EXPAND_CASES_CONV =
    let pth_base =
     prove
      ((parse_term @"(!n. n < 0 ==> P n) <=> T"),
       REWRITE_TAC[LT])
    let pth_step =
     prove
      ((parse_term @"(!n. n < SUC k ==> P n) <=> (!n. n < k ==> P n) /\ P k"),
       REWRITE_TAC[LT] |>THEN<| MESON_TAC[]) in
    let base_CONV = GEN_REWRITE_CONV I [pth_base]
    let step_CONV =
      BINDER_CONV(LAND_CONV(RAND_CONV num_CONV)) |>THENC<|
      GEN_REWRITE_CONV I [pth_step] in
    let rec conv tm =
      (base_CONV |>ORELSEC<| (step_CONV |>THENC<| LAND_CONV conv)) tm in
    conv |>THENC<| (REWRITE_CONV[GSYM CONJ_ASSOC]);;
