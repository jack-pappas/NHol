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
/// Calculation with integer-valued reals.
module NHol.calc_int

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
open realax
#endif

(* ------------------------------------------------------------------------- *)
(* Syntax operations on integer constants of type ":real".                   *)
(* ------------------------------------------------------------------------- *)
/// Tests if a term is an integer literal of type :real.
let is_realintconst tm = 
    match tm with
    | Comb(Const("real_of_num", _), n) -> is_numeral n
    | Comb(Const("real_neg", _), Comb(Const("real_of_num", _), n)) -> 
        is_numeral n && not(dest_numeral n = num_0)
    | _ -> false

/// Converts an integer literal of type :real to an F# number.
let dest_realintconst tm = 
    match tm with
    | Comb(Const("real_of_num", _), n) -> dest_numeral n
    | Comb(Const("real_neg", _), Comb(Const("real_of_num", _), n)) -> 
        let nn = dest_numeral n
        if nn <> num_0
        then minus_num(dest_numeral n)
        else failwith "dest_realintconst"
    | _ -> failwith "dest_realintconst"

/// Converts an F# number to a canonical integer literal of type :real.
let mk_realintconst = 
    let cast_tm = (parse_term @"real_of_num")
    let neg_tm = (parse_term @"(--)")
    let mk_numconst n = Choice.get <| mk_comb(cast_tm, mk_numeral n)
    fun x -> 
        if x < num_0
        then Choice.get <| mk_comb(neg_tm, mk_numconst(minus_num x))
        else mk_numconst x

/// Tests if a term is a canonical rational literal of type :real.
let is_ratconst tm = 
    match tm with
    | Comb(Comb(Const("real_div", _), p), q) -> 
        is_realintconst p && is_realintconst q 
        && (let m = dest_realintconst p
            let n = dest_realintconst q
            n > num_1 && gcd_num m n = num_1)
    | _ -> is_realintconst tm

/// Converts a canonical rational literal of type :real to an F# number.
let rat_of_term tm = 
    match tm with
    | Comb(Comb(Const("real_div", _), p), q) -> 
        let m = dest_realintconst p
        let n = dest_realintconst q
        if n > num_1 && gcd_num m n = num_1
        then m / n
        else failwith "rat_of_term"
    | _ -> dest_realintconst tm

/// Converts F# number to canonical rational literal of type :real.
let term_of_rat = 
    let div_tm = (parse_term @"(/)")
    fun x -> 
        let p, q = numdom x
        let ptm = mk_realintconst p
        if q = num_1
        then ptm
        else Choice.get <| mk_comb(Choice.get <| mk_comb(div_tm, ptm), mk_realintconst q)

(* ------------------------------------------------------------------------- *)
(* Some elementary "bootstrapping" lemmas we need below.                     *)
(* ------------------------------------------------------------------------- *)
let REAL_ADD_AC = prove((parse_term @"(m + n = n + m) /\
   ((m + n) + p = m + (n + p)) /\
   (m + (n + p) = n + (m + p))"), MESON_TAC [REAL_ADD_ASSOC; REAL_ADD_SYM])

let REAL_ADD_RINV = 
    prove
        ((parse_term @"!x. x + --x = &0"), 
         MESON_TAC [REAL_ADD_SYM; REAL_ADD_LINV])

let REAL_EQ_ADD_LCANCEL = 
    prove
        ((parse_term @"!x y z. (x + y = x + z) <=> (y = z)"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| POP_ASSUM(MP_TAC << AP_TERM(parse_term @"(+) (--x)"))
         |> THEN <| REWRITE_TAC [REAL_ADD_ASSOC; REAL_ADD_LINV; REAL_ADD_LID])

let REAL_EQ_ADD_RCANCEL = 
    prove
        ((parse_term @"!x y z. (x + z = y + z) <=> (x = y)"), 
         MESON_TAC [REAL_ADD_SYM; REAL_EQ_ADD_LCANCEL])
let REAL_MUL_RZERO = 
    prove
        ((parse_term @"!x. x * &0 = &0"), 
         MESON_TAC [REAL_EQ_ADD_RCANCEL; REAL_ADD_LDISTRIB; REAL_ADD_LID])
let REAL_MUL_LZERO = 
    prove
        ((parse_term @"!x. &0 * x = &0"), 
         MESON_TAC [REAL_MUL_SYM; REAL_MUL_RZERO])
let REAL_NEG_NEG = 
    prove
        ((parse_term @"!x. --(--x) = x"), 
         MESON_TAC 
             [REAL_EQ_ADD_RCANCEL; REAL_ADD_LINV; REAL_ADD_SYM; REAL_ADD_LINV])
let REAL_MUL_RNEG = 
    prove
        ((parse_term @"!x y. x * (--y) = -- (x * y)"), 
         MESON_TAC 
             [REAL_EQ_ADD_RCANCEL; REAL_ADD_LDISTRIB; REAL_ADD_LINV; 
              REAL_MUL_RZERO])
let REAL_MUL_LNEG = 
    prove
        ((parse_term @"!x y. (--x) * y = -- (x * y)"), 
         MESON_TAC [REAL_MUL_SYM; REAL_MUL_RNEG])

let REAL_NEG_ADD = 
    prove
        ((parse_term @"!x y. --(x + y) = --x + --y"), 
         REPEAT GEN_TAC
         |> THEN 
         <| MATCH_MP_TAC
                (GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL REAL_EQ_ADD_RCANCEL))))
         |> THEN <| EXISTS_TAC(parse_term @"x + y")
         |> THEN <| REWRITE_TAC [REAL_ADD_LINV]
         |> THEN 
         <| ONCE_REWRITE_TAC 
                [AC REAL_ADD_AC 
                     (parse_term @"(a + b) + (c + d) = (a + c) + (b + d)")]
         |> THEN <| REWRITE_TAC [REAL_ADD_LINV; REAL_ADD_LID])

let REAL_ADD_RID = 
    prove((parse_term @"!x. x + &0 = x"), MESON_TAC [REAL_ADD_SYM; REAL_ADD_LID])
let REAL_NEG_0 = 
    prove((parse_term @"--(&0) = &0"), MESON_TAC [REAL_ADD_LINV; REAL_ADD_RID])

let REAL_LE_LNEG = 
    prove
        ((parse_term @"!x y. --x <= y <=> &0 <= x + y"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP REAL_LE_LADD_IMP)
         |> THENL 
         <| [DISCH_THEN(MP_TAC << SPEC(parse_term @"x:real"))
             |> THEN 
             <| REWRITE_TAC [ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LINV]
             DISCH_THEN(MP_TAC << SPEC(parse_term @"--x"))
             |> THEN 
             <| REWRITE_TAC [REAL_ADD_LINV
                             REAL_ADD_ASSOC
                             REAL_ADD_LID
                             ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LID]])

let REAL_LE_NEG2 = 
    prove
        ((parse_term @"!x y. --x <= --y <=> y <= x"), 
         REPEAT GEN_TAC
         |> THEN <| GEN_REWRITE_TAC (RAND_CONV << LAND_CONV) [GSYM REAL_NEG_NEG]
         |> THEN <| REWRITE_TAC [REAL_LE_LNEG]
         |> THEN <| AP_TERM_TAC
         |> THEN <| MATCH_ACCEPT_TAC REAL_ADD_SYM)

let REAL_LE_RNEG = 
    prove
        ((parse_term @"!x y. x <= --y <=> x + y <= &0"), 
         REPEAT GEN_TAC
         |> THEN <| GEN_REWRITE_TAC (LAND_CONV << LAND_CONV) [GSYM REAL_NEG_NEG]
         |> THEN <| REWRITE_TAC [REAL_LE_LNEG
                                 GSYM REAL_NEG_ADD]
         |> THEN <| GEN_REWRITE_TAC RAND_CONV [GSYM REAL_LE_NEG2]
         |> THEN <| AP_THM_TAC
         |> THEN <| AP_TERM_TAC
         |> THEN <| REWRITE_TAC [GSYM REAL_ADD_LINV]
         |> THEN <| REWRITE_TAC [REAL_NEG_ADD; REAL_NEG_NEG]
         |> THEN <| MATCH_ACCEPT_TAC REAL_ADD_SYM)

let REAL_OF_NUM_POW = 
    prove
        ((parse_term @"!x n. (&x) pow n = &(x EXP n)"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [real_pow; EXP; REAL_OF_NUM_MUL])

let REAL_POW_NEG = 
    prove
        ((parse_term @"!x n. (--x) pow n = if EVEN n then x pow n else --(x pow n)"), 
         GEN_TAC
         |> THEN <| INDUCT_TAC
         |> THEN <| ASM_REWRITE_TAC [real_pow; EVEN]
         |> THEN <| ASM_CASES_TAC(parse_term @"EVEN n")
         |> THEN <| ASM_REWRITE_TAC [REAL_MUL_RNEG; REAL_MUL_LNEG; REAL_NEG_NEG])

let REAL_ABS_NUM = 
    prove
        ((parse_term @"!n. abs(&n) = &n"), 
         REWRITE_TAC [real_abs; REAL_OF_NUM_LE; LE_0])
let REAL_ABS_NEG = 
    prove
        ((parse_term @"!x. abs(--x) = abs x"), 
         REWRITE_TAC [real_abs; REAL_LE_RNEG; REAL_NEG_NEG; REAL_ADD_LID]
         |> THEN <| MESON_TAC [REAL_LE_TOTAL; REAL_LE_ANTISYM; REAL_NEG_0])

(* ------------------------------------------------------------------------- *)
(* First, the conversions on integer constants.                              *)
(* ------------------------------------------------------------------------- *)
// REAL_INT_LE_CONV: Conversion to prove whether one integer literal of type :real is <= another.
// REAL_INT_LT_CONV: Conversion to prove whether one integer literal of type :real is < another.
// REAL_INT_GE_CONV: Conversion to prove whether one integer literal of type :real is >= another.
// REAL_INT_GT_CONV: Conversion to prove whether one integer literal of type :real is < another.
// REAL_INT_EQ_CONV: Conversion to prove whether one integer literal of type :real is equal to another.
let REAL_INT_LE_CONV, REAL_INT_LT_CONV, REAL_INT_GE_CONV, REAL_INT_GT_CONV, REAL_INT_EQ_CONV = 
    let tth = TAUT (parse_term @"(F /\ F <=> F) /\ (F /\ T <=> F) /\
          (T /\ F <=> F) /\ (T /\ T <=> T)")
    let nth = TAUT (parse_term @"(~T <=> F) /\ (~F <=> T)")
    let NUM2_EQ_CONV = BINOP_CONV NUM_EQ_CONV
                       |> THENC <| GEN_REWRITE_CONV I [tth]
    let NUM2_NE_CONV = RAND_CONV NUM2_EQ_CONV
                       |> THENC <| GEN_REWRITE_CONV I [nth]
    let lefuncs =
        (CONJUNCTS << prove) 
          ((parse_term @"(--(&m) <= &n <=> T) /\
             (&m <= &n <=> m <= n) /\
             (--(&m) <= --(&n) <=> n <= m) /\
             (&m <= --(&n) <=> (m = 0) /\ (n = 0))"), 
             REWRITE_TAC [REAL_LE_NEG2]
             |> THEN <| REWRITE_TAC [REAL_LE_LNEG; REAL_LE_RNEG]
             |> THEN <| REWRITE_TAC [REAL_OF_NUM_ADD; REAL_OF_NUM_LE; LE_0]
             |> THEN <| REWRITE_TAC [LE; ADD_EQ_0])
    match lefuncs with
    | [pth_le1; pth_le2a; pth_le2b; pth_le3] ->
        let REAL_INT_LE_CONV = 
            FIRST_CONV [GEN_REWRITE_CONV I [pth_le1]
                        GEN_REWRITE_CONV I [pth_le2a; pth_le2b]
                        |> THENC <| NUM_LE_CONV
                        GEN_REWRITE_CONV I [pth_le3]
                        |> THENC <| NUM2_EQ_CONV]
        let ltfuncs =
            (CONJUNCTS << prove)
              ((parse_term @"(&m < --(&n) <=> F) /\
                (&m < &n <=> m < n) /\
                (--(&m) < --(&n) <=> n < m) /\
                (--(&m) < &n <=> ~((m = 0) /\ (n = 0)))"), 
                REWRITE_TAC [pth_le1; pth_le2a; pth_le2b; pth_le3; GSYM NOT_LE; real_lt] 
                |> THEN <| CONV_TAC TAUT)
        match ltfuncs with
        | [pth_lt1; pth_lt2a; pth_lt2b; pth_lt3] ->
            let REAL_INT_LT_CONV = 
                FIRST_CONV [GEN_REWRITE_CONV I [pth_lt1]
                            GEN_REWRITE_CONV I [pth_lt2a; pth_lt2b]
                            |> THENC <| NUM_LT_CONV
                            GEN_REWRITE_CONV I [pth_lt3]
                            |> THENC <| NUM2_NE_CONV]
            let gefuncs =
                (CONJUNCTS << prove)
                  ((parse_term @"(&m >= --(&n) <=> T) /\
                    (&m >= &n <=> n <= m) /\
                    (--(&m) >= --(&n) <=> m <= n) /\
                    (--(&m) >= &n <=> (m = 0) /\ (n = 0))"), 
                    REWRITE_TAC [pth_le1; pth_le2a; pth_le2b; pth_le3; real_ge]
                    |> THEN <| CONV_TAC TAUT)
            match gefuncs with                                              
            | [pth_ge1; pth_ge2a; pth_ge2b; pth_ge3] ->
                let REAL_INT_GE_CONV = 
                    FIRST_CONV [GEN_REWRITE_CONV I [pth_ge1]
                                GEN_REWRITE_CONV I [pth_ge2a; pth_ge2b]
                                |> THENC <| NUM_LE_CONV
                                GEN_REWRITE_CONV I [pth_ge3]
                                |> THENC <| NUM2_EQ_CONV]
                let gtfuncs =
                    (CONJUNCTS << prove)
                      ((parse_term @"(--(&m) > &n <=> F) /\
                        (&m > &n <=> n < m) /\
                        (--(&m) > --(&n) <=> m < n) /\
                        (&m > --(&n) <=> ~((m = 0) /\ (n = 0)))"), 
                        REWRITE_TAC [pth_lt1; pth_lt2a; pth_lt2b; pth_lt3; real_gt]
                        |> THEN <| CONV_TAC TAUT)
                match gtfuncs with
                | [pth_gt1; pth_gt2a; pth_gt2b; pth_gt3] -> 
                    let REAL_INT_GT_CONV = 
                        FIRST_CONV [GEN_REWRITE_CONV I [pth_gt1]
                                    GEN_REWRITE_CONV I [pth_gt2a; pth_gt2b]
                                    |> THENC <| NUM_LT_CONV
                                    GEN_REWRITE_CONV I [pth_gt3]
                                    |> THENC <| NUM2_NE_CONV]
                    let eqfuncs =
                        (CONJUNCTS << prove)
                          ((parse_term @"((&m = &n) <=> (m = n)) /\
                            ((--(&m) = --(&n)) <=> (m = n)) /\
                            ((--(&m) = &n) <=> (m = 0) /\ (n = 0)) /\
                            ((&m = --(&n)) <=> (m = 0) /\ (n = 0))"), 
                            REWRITE_TAC [GSYM REAL_LE_ANTISYM; GSYM LE_ANTISYM]
                            |> THEN <| REWRITE_TAC [pth_le1; pth_le2a; pth_le2b; pth_le3; LE; LE_0]
                            |> THEN <| CONV_TAC TAUT)
                    match eqfuncs with
                    | [pth_eq1a; pth_eq1b; pth_eq2a; pth_eq2b] ->
                        let REAL_INT_EQ_CONV = 
                            FIRST_CONV [GEN_REWRITE_CONV I [pth_eq1a; pth_eq1b]
                                        |> THENC <| NUM_EQ_CONV
                                        GEN_REWRITE_CONV I [pth_eq2a; pth_eq2b]
                                        |> THENC <| NUM2_EQ_CONV]
                        REAL_INT_LE_CONV, REAL_INT_LT_CONV, REAL_INT_GE_CONV, REAL_INT_GT_CONV, REAL_INT_EQ_CONV
                    | _ -> failwith "eqfuncs: Unhandled case."
                | _ -> failwith "gtfuncs: Unhandled case."
            | _ -> failwith "gefuncs: Unhandled case."
        | _ -> failwith "ltfuncs: Unhandled case."
    | _ -> failwith "lefuncs: Unhandled case."

/// Conversion to negate an integer literal of type :real.
let REAL_INT_NEG_CONV = 
    let pth = prove((parse_term @"(--(&0) = &0) /\
     (--(--(&x)) = &x)"), REWRITE_TAC [REAL_NEG_NEG; REAL_NEG_0])
    GEN_REWRITE_CONV I [pth]

/// Conversion to perform multiplication on two integer literals of type :real.
let REAL_INT_MUL_CONV = 
    let pth0 = prove((parse_term @"(&0 * &x = &0) /\
     (&0 * --(&x) = &0) /\
     (&x * &0 = &0) /\
     (--(&x) * &0 = &0)"), REWRITE_TAC [REAL_MUL_LZERO; REAL_MUL_RZERO])
    let pth1, pth2 = (CONJ_PAIR << prove)((parse_term @"((&m * &n = &(m * n)) /\
      (--(&m) * --(&n) = &(m * n))) /\
     ((--(&m) * &n = --(&(m * n))) /\
      (&m * --(&n) = --(&(m * n))))"), REWRITE_TAC 
                                           [REAL_MUL_LNEG; REAL_MUL_RNEG; 
                                            REAL_NEG_NEG]
                                       |> THEN <| REWRITE_TAC [REAL_OF_NUM_MUL])
    FIRST_CONV [GEN_REWRITE_CONV I [pth0]
                GEN_REWRITE_CONV I [pth1]
                |> THENC <| RAND_CONV NUM_MULT_CONV
                GEN_REWRITE_CONV I [pth2]
                |> THENC <| RAND_CONV(RAND_CONV NUM_MULT_CONV)]

/// Conversion to perform addition on two integer literals of type :real.
let REAL_INT_ADD_CONV = 
    let neg_tm = (parse_term @"(--)")
    let amp_tm = (parse_term @"&")
    let add_tm = (parse_term @"(+)")
    let dest = Choice.get << dest_binop(parse_term @"(+)")
    let m_tm = (parse_term @"m:num")
    let n_tm = (parse_term @"n:num")
    let pth0 = prove((parse_term @"(--(&m) + &m = &0) /\
     (&m + --(&m) = &0)"), REWRITE_TAC [REAL_ADD_LINV; REAL_ADD_RINV])

    let pth1, pth2, pth3, pth4, pth5, pth6 = 
        let pthFuncs =
            (CONJUNCTS << prove)
              ((parse_term @"(--(&m) + --(&n) = --(&(m + n))) /\
                (--(&m) + &(m + n) = &n) /\
                (--(&(m + n)) + &m = --(&n)) /\
                (&(m + n) + --(&m) = &n) /\
                (&m + --(&(m + n)) = --(&n)) /\
                (&m + &n = &(m + n))"), 
                  REWRITE_TAC [GSYM REAL_OF_NUM_ADD; REAL_NEG_ADD]
                  |> THEN <| REWRITE_TAC [REAL_ADD_ASSOC; REAL_ADD_LINV; REAL_ADD_LID]
                  |> THEN <| REWRITE_TAC [REAL_ADD_RINV; REAL_ADD_LID]
                  |> THEN <| ONCE_REWRITE_TAC [REAL_ADD_SYM]
                  |> THEN <| REWRITE_TAC [REAL_ADD_ASSOC; REAL_ADD_LINV; REAL_ADD_LID]
                  |> THEN <| REWRITE_TAC [REAL_ADD_RINV; REAL_ADD_LID])
        match pthFuncs with
        |  [pth1; pth2; pth3; pth4; pth5; pth6] -> pth1, pth2, pth3, pth4, pth5, pth6
        | _ -> failwith "pthFuncs: Unhandled case."

    GEN_REWRITE_CONV I [pth0]
    |> ORELSEC <| (fun tm -> 
        try 
            let l, r = dest tm
            if Choice.get <| rator l = neg_tm
            then 
                if Choice.get <| rator r = neg_tm
                then 
                    let th1 = 
                        INST [Choice.get <| rand(Choice.get <| rand l), m_tm
                              Choice.get <| rand(Choice.get <| rand r), n_tm] pth1
                    let tm1 = Choice.get <| rand(Choice.get <| rand(Choice.get <| rand(concl th1)))
                    let th2 = AP_TERM neg_tm (AP_TERM amp_tm (NUM_ADD_CONV tm1))
                    TRANS th1 th2
                else 
                    let m = Choice.get <| rand(Choice.get <| rand l)
                    let n = Choice.get <| rand r
                    let m' = dest_numeral m
                    let n' = dest_numeral n
                    if m' <= n'
                    then 
                        let p = mk_numeral(n' - m')
                        let th1 = 
                            INST [m, m_tm
                                  p, n_tm] pth2
                        let th2 = NUM_ADD_CONV(Choice.get <| rand(Choice.get <| rand(lhand(concl th1))))
                        let th3 = AP_TERM (Choice.get <| rator tm) (AP_TERM amp_tm (SYM th2))
                        TRANS th3 th1
                    else 
                        let p = mk_numeral(m' - n')
                        let th1 = 
                            INST [n, m_tm
                                  p, n_tm] pth3
                        let th2 = 
                            NUM_ADD_CONV(Choice.get <| rand(Choice.get <| rand(lhand(lhand(concl th1)))))
                        let th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2))
                        let th4 = AP_THM (AP_TERM add_tm th3) (Choice.get <| rand tm)
                        TRANS th4 th1
            elif Choice.get <| rator r = neg_tm
            then 
                let m = Choice.get <| rand l
                let n = Choice.get <| rand(Choice.get <| rand r)
                let m' = dest_numeral m
                let n' = dest_numeral n
                if n' <= m'
                then 
                    let p = mk_numeral(m' - n')
                    let th1 = 
                        INST [n, m_tm
                              p, n_tm] pth4
                    let th2 = NUM_ADD_CONV(Choice.get <| rand(lhand(lhand(concl th1))))
                    let th3 = AP_TERM add_tm (AP_TERM amp_tm (SYM th2))
                    let th4 = AP_THM th3 (Choice.get <| rand tm)
                    TRANS th4 th1
                else 
                    let p = mk_numeral(n' - m')
                    let th1 = 
                        INST [m, m_tm
                              p, n_tm] pth5
                    let th2 = NUM_ADD_CONV(Choice.get <| rand(Choice.get <| rand(Choice.get <| rand(lhand(concl th1)))))
                    let th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2))
                    let th4 = AP_TERM (Choice.get <| rator tm) th3
                    TRANS th4 th1
            else 
                let th1 = 
                    INST [Choice.get <| rand l, m_tm
                          Choice.get <| rand r, n_tm] pth6
                let tm1 = Choice.get <| rand(Choice.get <| rand(concl th1))
                let th2 = AP_TERM amp_tm (NUM_ADD_CONV tm1)
                TRANS th1 th2
        with
        | Failure _ as e -> nestedFailwith e "REAL_INT_ADD_CONV")

/// Conversion to perform subtraction on two integer literals of type :real.
let REAL_INT_SUB_CONV = 
    GEN_REWRITE_CONV I [real_sub]
    |> THENC <| TRY_CONV(RAND_CONV REAL_INT_NEG_CONV)
    |> THENC <| REAL_INT_ADD_CONV

/// Conversion to perform exponentiation on a integer literal of type :real.
let REAL_INT_POW_CONV = 
    let pth1, pth2 = 
        (CONJ_PAIR << prove)
            ((parse_term @"(&x pow n = &(x EXP n)) /\
     ((--(&x)) pow n = if EVEN n then &(x EXP n) else --(&(x EXP n)))"), 
             REWRITE_TAC [REAL_OF_NUM_POW; REAL_POW_NEG])
    let tth = 
        prove
            ((parse_term @"((if T then x:real else y) = x) /\ ((if F then x:real else y) = y)"), 
             REWRITE_TAC [])
    let neg_tm = (parse_term @"(--)")
    (GEN_REWRITE_CONV I [pth1]
     |> THENC <| RAND_CONV NUM_EXP_CONV)
    |> ORELSEC <| (GEN_REWRITE_CONV I [pth2]
                   |> THENC <| RATOR_CONV(RATOR_CONV(RAND_CONV NUM_EVEN_CONV))
                   |> THENC <| GEN_REWRITE_CONV I [tth]
                   |> THENC <| (fun tm -> 
                       if Choice.get <| rator tm = neg_tm
                       then RAND_CONV (RAND_CONV NUM_EXP_CONV) tm
                       else RAND_CONV NUM_EXP_CONV tm))

/// Conversion to produce absolute value of an integer literal of type :real.
let REAL_INT_ABS_CONV = 
    let pth = prove((parse_term @"(abs(--(&x)) = &x) /\
     (abs(&x) = &x)"), REWRITE_TAC [REAL_ABS_NEG; REAL_ABS_NUM])
    GEN_REWRITE_CONV I [pth]

/// Performs one arithmetic or relational operation on integer literals of type :real.
let REAL_INT_RED_CONV = 
    let gconv_net = 
        itlist (uncurry net_of_conv) [(parse_term @"x <= y"), REAL_INT_LE_CONV
                                      (parse_term @"x < y"), REAL_INT_LT_CONV
                                      (parse_term @"x >= y"), REAL_INT_GE_CONV
                                      (parse_term @"x > y"), REAL_INT_GT_CONV
                                      (parse_term @"x:real = y"), 
                                      REAL_INT_EQ_CONV
                                      (parse_term @"--x"), 
                                      CHANGED_CONV REAL_INT_NEG_CONV
                                      (parse_term @"abs(x)"), REAL_INT_ABS_CONV
                                      (parse_term @"x + y"), REAL_INT_ADD_CONV
                                      (parse_term @"x - y"), REAL_INT_SUB_CONV
                                      (parse_term @"x * y"), REAL_INT_MUL_CONV
                                      (parse_term @"x pow n"), REAL_INT_POW_CONV] 
            (basic_net())
    REWRITES_CONV gconv_net

/// Evaluate subexpressions built up from integer literals of type :real, by proof.
let REAL_INT_REDUCE_CONV = DEPTH_CONV REAL_INT_RED_CONV
