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
/// Universal linear real decision procedure.
module NHol.realarith

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

open ExtCore.Control
open ExtCore.Control.Collections

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
//open ind_types
//open lists
open realax
open calc_int
#endif

logger.Trace("Entering realarith.fs")

(* ------------------------------------------------------------------------- *)
(* Some lemmas needed now just to drive the decision procedure.              *)
(* ------------------------------------------------------------------------- *)

let REAL_LTE_TOTAL = 
    prove((parse_term @"!x y. x < y \/ y <= x"), REWRITE_TAC [real_lt]
                                                 |> THEN <| CONV_TAC TAUT)

let REAL_LET_TOTAL = 
    prove((parse_term @"!x y. x <= y \/ y < x"), REWRITE_TAC [real_lt]
                                                 |> THEN <| CONV_TAC TAUT)
let REAL_LT_IMP_LE = 
    prove
        ((parse_term @"!x y. x < y ==> x <= y"), 
         MESON_TAC [real_lt; REAL_LE_TOTAL])

let REAL_LTE_TRANS = 
    prove
        ((parse_term @"!x y z. x < y /\ y <= z ==> x < z"), 
         MESON_TAC [real_lt; REAL_LE_TRANS])

let REAL_LET_TRANS = 
    prove
        ((parse_term @"!x y z. x <= y /\ y < z ==> x < z"), 
         MESON_TAC [real_lt; REAL_LE_TRANS])

let REAL_LT_TRANS = 
    prove
        ((parse_term @"!x y z. x < y /\ y < z ==> x < z"), 
         MESON_TAC [REAL_LTE_TRANS; REAL_LT_IMP_LE])

let REAL_LE_ADD = 
    prove
        ((parse_term @"!x y. &0 <= x /\ &0 <= y ==> &0 <= x + y"), 
         MESON_TAC [REAL_LE_LADD_IMP; REAL_ADD_RID; REAL_LE_TRANS])

let REAL_LTE_ANTISYM = 
    prove((parse_term @"!x y. ~(x < y /\ y <= x)"), MESON_TAC [real_lt])

let REAL_SUB_LE = 
    prove
        ((parse_term @"!x y. &0 <= (x - y) <=> y <= x"), 
         REWRITE_TAC [real_sub
                      GSYM REAL_LE_LNEG
                      REAL_LE_NEG2])

let REAL_NEG_SUB = 
    prove
        ((parse_term @"!x y. --(x - y) = y - x"), 
         REWRITE_TAC [real_sub; REAL_NEG_ADD; REAL_NEG_NEG]
         |> THEN <| REWRITE_TAC [REAL_ADD_AC])

let REAL_LE_LT = 
    prove
        ((parse_term @"!x y. x <= y <=> x < y \/ (x = y)"), 
         REWRITE_TAC [real_lt]
         |> THEN <| MESON_TAC [REAL_LE_ANTISYM; REAL_LE_TOTAL])

let REAL_SUB_LT = 
    prove
        ((parse_term @"!x y. &0 < (x - y) <=> y < x"), 
         REWRITE_TAC [real_lt]
         |> THEN <| ONCE_REWRITE_TAC [GSYM REAL_NEG_SUB]
         |> THEN <| REWRITE_TAC [REAL_LE_LNEG; REAL_ADD_RID; REAL_SUB_LE])

let REAL_NOT_LT = 
    prove((parse_term @"!x y. ~(x < y) <=> y <= x"), REWRITE_TAC [real_lt])

let REAL_SUB_0 = 
    prove
        ((parse_term @"!x y. (x - y = &0) <=> (x = y)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [GSYM REAL_LE_ANTISYM]
         |> THEN <| GEN_REWRITE_TAC (LAND_CONV << LAND_CONV) [GSYM REAL_NOT_LT]
         |> THEN <| REWRITE_TAC [REAL_SUB_LE; REAL_SUB_LT]
         |> THEN <| REWRITE_TAC [REAL_NOT_LT])

let REAL_LT_LE = 
    prove
        ((parse_term @"!x y. x < y <=> x <= y /\ ~(x = y)"), 
         MESON_TAC [real_lt; REAL_LE_TOTAL; REAL_LE_ANTISYM])

let REAL_LT_REFL = 
    prove((parse_term @"!x. ~(x < x)"), REWRITE_TAC [real_lt; REAL_LE_REFL])

let REAL_LTE_ADD = 
    prove
        ((parse_term @"!x y. &0 < x /\ &0 <= y ==> &0 < x + y"), 
         MESON_TAC [REAL_LE_LADD_IMP; REAL_ADD_RID; REAL_LTE_TRANS])

let REAL_LET_ADD = 
    prove
        ((parse_term @"!x y. &0 <= x /\ &0 < y ==> &0 < x + y"), 
         MESON_TAC [REAL_LTE_ADD; REAL_ADD_SYM])

let REAL_LT_ADD = 
    prove
        ((parse_term @"!x y. &0 < x /\ &0 < y ==> &0 < x + y"), 
         MESON_TAC [REAL_LT_IMP_LE; REAL_LTE_ADD])

let REAL_ENTIRE = 
    prove((parse_term @"!x y. (x * y = &0) <=> (x = &0) \/ (y = &0)"), 
          REPEAT GEN_TAC
          |> THEN <| EQ_TAC
          |> THEN <| STRIP_TAC
          |> THEN <| ASM_REWRITE_TAC [REAL_MUL_LZERO; REAL_MUL_RZERO]
          |> THEN <| ASM_CASES_TAC(parse_term @"x = &0")
          |> THEN <| ASM_REWRITE_TAC []
          |> THEN <| FIRST_ASSUM(MP_TAC << AP_TERM(parse_term @"(*) (inv x)"))
          |> THEN <| REWRITE_TAC [REAL_MUL_ASSOC]
          |> THEN <| FIRST_ASSUM(fun th -> REWRITE_TAC [MATCH_MP REAL_MUL_LINV th])
          |> THEN <| REWRITE_TAC [REAL_MUL_LID; REAL_MUL_RZERO])

let REAL_LE_NEGTOTAL = 
    prove
        ((parse_term @"!x. &0 <= x \/ &0 <= --x"), 
         REWRITE_TAC [REAL_LE_RNEG; REAL_ADD_LID; REAL_LE_TOTAL])

let REAL_LE_SQUARE = 
    prove((parse_term @"!x. &0 <= x * x"), 
          GEN_TAC
          |> THEN <| DISJ_CASES_TAC(SPEC (parse_term @"x:real") REAL_LE_NEGTOTAL)
          |> THEN <| POP_ASSUM(fun th -> MP_TAC(MATCH_MP REAL_LE_MUL (CONJ th th)))
          |> THEN <| REWRITE_TAC [REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG])

let REAL_MUL_RID = 
    prove((parse_term @"!x. x * &1 = x"), MESON_TAC [REAL_MUL_LID; REAL_MUL_SYM])

let REAL_POW_2 = 
    prove
        ((parse_term @"!x. x pow 2 = x * x"), 
         REWRITE_TAC [num_CONV(parse_term @"2")
                      num_CONV(parse_term @"1")]
         |> THEN <| REWRITE_TAC [real_pow; REAL_MUL_RID])

let REAL_POLY_CLAUSES = 
    prove((parse_term @"(!x y z. x + (y + z) = (x + y) + z) /\
   (!x y. x + y = y + x) /\
   (!x. &0 + x = x) /\
   (!x y z. x * (y * z) = (x * y) * z) /\
   (!x y. x * y = y * x) /\
   (!x. &1 * x = x) /\
   (!x. &0 * x = &0) /\
   (!x y z. x * (y + z) = x * y + x * z) /\
   (!x. x pow 0 = &1) /\
   (!x n. x pow (SUC n) = x * x pow n)"),
          REWRITE_TAC [real_pow; REAL_ADD_LDISTRIB; REAL_MUL_LZERO]
          |> THEN <| REWRITE_TAC [REAL_MUL_ASSOC; REAL_ADD_LID; REAL_MUL_LID]
          |> THEN <| REWRITE_TAC [REAL_ADD_AC]
          |> THEN <| REWRITE_TAC [REAL_MUL_SYM])

let REAL_POLY_NEG_CLAUSES = 
    prove
        ((parse_term @"(!x. --x = --(&1) * x) /\
   (!x y. x - y = x + --(&1) * y)"), 
         REWRITE_TAC [REAL_MUL_LNEG; real_sub; REAL_MUL_LID])

let REAL_POS = 
    prove((parse_term @"!n. &0 <= &n"), REWRITE_TAC [REAL_OF_NUM_LE; LE_0])

(* ------------------------------------------------------------------------- *)
(* Data structure for Positivstellensatz refutations.                        *)
(* ------------------------------------------------------------------------- *)

type positivstellensatz = 
    | Axiom_eq of int
    | Axiom_le of int
    | Axiom_lt of int
    | Rational_eq of num
    | Rational_le of num
    | Rational_lt of num
    | Square of term
    | Eqmul of term * positivstellensatz
    | Sum of positivstellensatz * positivstellensatz
    | Product of positivstellensatz * positivstellensatz

(* ------------------------------------------------------------------------- *)
(* Parametrized reals decision procedure.                                    *)
(*                                                                           *)
(* This is a bootstrapping version, and subsequently gets overwritten twice  *)
(* with more specialized versions, once here and finally in "calc_rat.ml".   *)
(* ------------------------------------------------------------------------- *)

let GEN_REAL_ARITH_001 = 
    let pth = 
        prove
            ((parse_term @"(x < y <=> y - x > &0) /\
     (x <= y <=> y - x >= &0) /\
     (x > y <=> x - y > &0) /\
     (x >= y <=> x - y >= &0) /\
     ((x = y) <=> (x - y = &0)) /\
     (~(x < y) <=> x - y >= &0) /\
     (~(x <= y) <=> x - y > &0) /\
     (~(x > y) <=> y - x >= &0) /\
     (~(x >= y) <=> y - x > &0) /\
     (~(x = y) <=> x - y > &0 \/ --(x - y) > &0)"), 
             REWRITE_TAC 
                 [real_gt; real_ge; REAL_SUB_LT; REAL_SUB_LE; REAL_NEG_SUB]
             |> THEN <| REWRITE_TAC [REAL_SUB_0; real_lt]
             |> THEN <| MESON_TAC [REAL_LE_ANTISYM])
    let pth_final = TAUT(parse_term @"(~p ==> F) ==> p")
    let pth_add = 
        prove
            ((parse_term @"((x = &0) /\ (y = &0) ==> (x + y = &0)) /\
     ((x = &0) /\ y >= &0 ==> x + y >= &0) /\
     ((x = &0) /\ y > &0 ==> x + y > &0) /\
     (x >= &0 /\ (y = &0) ==> x + y >= &0) /\
     (x >= &0 /\ y >= &0 ==> x + y >= &0) /\
     (x >= &0 /\ y > &0 ==> x + y > &0) /\
     (x > &0 /\ (y = &0) ==> x + y > &0) /\
     (x > &0 /\ y >= &0 ==> x + y > &0) /\
     (x > &0 /\ y > &0 ==> x + y > &0)"), 
             SIMP_TAC [REAL_ADD_LID; REAL_ADD_RID; real_ge; real_gt]
             |> THEN <| REWRITE_TAC [REAL_LE_LT]
             |> THEN <| MESON_TAC [REAL_ADD_LID; REAL_ADD_RID; REAL_LT_ADD])

    let pth_mul = 
        prove((parse_term @"((x = &0) /\ (y = &0) ==> (x * y = &0)) /\
         ((x = &0) /\ y >= &0 ==> (x * y = &0)) /\
         ((x = &0) /\ y > &0 ==> (x * y = &0)) /\
         (x >= &0 /\ (y = &0) ==> (x * y = &0)) /\
         (x >= &0 /\ y >= &0 ==> x * y >= &0) /\
         (x >= &0 /\ y > &0 ==> x * y >= &0) /\
         (x > &0 /\ (y = &0) ==> (x * y = &0)) /\
         (x > &0 /\ y >= &0 ==> x * y >= &0) /\
         (x > &0 /\ y > &0 ==> x * y > &0)"),
              SIMP_TAC [REAL_MUL_LZERO; REAL_MUL_RZERO; real_ge; real_gt]
              |> THEN <| SIMP_TAC [REAL_LT_LE; REAL_LE_MUL]
              |> THEN <| MESON_TAC [REAL_ENTIRE])

    let pth_emul = 
        prove
            ((parse_term @"(y = &0) ==> !x. x * y = &0"), 
             SIMP_TAC [REAL_MUL_RZERO])

    let pth_square = 
        prove
            ((parse_term @"!x. x * x >= &0"), 
             REWRITE_TAC [real_ge; REAL_POW_2; REAL_LE_SQUARE])

    let MATCH_MP_RULE th = 
        let net = 
            Choice.List.fold (fun acc th -> 
                choice {
                    let! th = th
                    let! tm1 = lhand(concl th)
                    return! net_of_conv tm1 (PART_MATCH lhand (Choice.result th)) acc
                }) empty_net (CONJUNCTS th) 

        fun th -> 
            choice {
                let! net = net
                let! th = th
                return! MP (REWRITES_CONV net (concl th)) (Choice.result th)
            }

    let x_tm = (parse_term @"x:real")
    let y_tm = (parse_term @"y:real")
    let neg_tm = (parse_term @"(--):real->real")
    let gt_tm = (parse_term @"(>):real->real->bool")
    let ge_tm = (parse_term @"(>=):real->real->bool")
    let eq_tm = (parse_term @"(=):real->real->bool")
    let p_tm = (parse_term @"p:bool")
    let or_tm = (parse_term @"(\/)")
    let false_tm = (parse_term @"F")
    let z_tm = (parse_term @"&0 :real")
    let xy_lt = (parse_term @"(x:real) < y")
    let xy_nlt = (parse_term @"~((x:real) < y)")
    let xy_le = (parse_term @"(x:real) <= y")
    let xy_nle = (parse_term @"~((x:real) <= y)")
    let xy_gt = (parse_term @"(x:real) > y")
    let xy_ngt = (parse_term @"~((x:real) > y)")
    let xy_ge = (parse_term @"(x:real) >= y")
    let xy_nge = (parse_term @"~((x:real) >= y)")
    let xy_eq = (parse_term @"x:real = y")
    let xy_ne = (parse_term @"~(x:real = y)")
    let is_ge = is_binop ge_tm
    let is_gt = is_binop gt_tm
    let is_req = is_binop eq_tm

    fun (mk_numeric, NUMERIC_EQ_CONV, NUMERIC_GE_CONV, NUMERIC_GT_CONV, POLY_CONV, POLY_NEG_CONV, POLY_ADD_CONV, POLY_MUL_CONV, absconv1, absconv2, prover) -> 
        // This is the specialized and incorrect version 
        let REWRITES_CONV (net : net<int * (term -> 'T)>) tm = 
            choice { 
                let! pconvs = lookup tm net
                // NOTE: using Some here is incorrect, since the condition is always satisfied
                // It should be changed to Choice.toOption later.
                match tryfind (fun (_, cnv) -> Some <| cnv tm) pconvs with
                | Some result -> return result
                | None -> return! Choice.failwith "tryfind" |> Choice.mapError(fun e -> nestedFailure e "REWRITES_CONV") }
            // TEMP : Until call sites can be modified, we have to raise the exception
            // contained in the error value (if the result of this function is an error).
            |> ExtCore.Choice.bindOrRaise

        let REAL_INEQ_CONV pth tm = 
            choice {
                let! lop, r = dest_comb tm
                let! tm1 = rand lop
                let! th = INST [tm1, x_tm; r, y_tm] pth
                let! tm2 = rand(concl th)
                return! TRANS (Choice.result th) (LAND_CONV POLY_CONV tm2)
            }

        let REAL_LT_CONV, REAL_LE_CONV, REAL_GT_CONV, REAL_GE_CONV, REAL_EQ_CONV, REAL_NOT_LT_CONV, REAL_NOT_LE_CONV, REAL_NOT_GT_CONV, REAL_NOT_GE_CONV = 
            let realEqFuncs = map REAL_INEQ_CONV (CONJUNCTS pth)
            match realEqFuncs with
            | [real_lt_conv; real_le_conv; real_gt_conv; real_ge_conv; real_eq_conv; real_not_lt_conv; real_not_le_conv; 
               real_not_gt_conv; real_not_ge_conv; _] -> 
                real_lt_conv, real_le_conv, real_gt_conv, real_ge_conv, real_eq_conv, real_not_lt_conv, real_not_le_conv, 
                real_not_gt_conv, real_not_ge_conv
            | _ -> 
                let failTac = fun _ -> Choice.failwith "realEqFuncs: Unhandled case."
                failTac, failTac, failTac, failTac, failTac, failTac, failTac, failTac, failTac

        let REAL_NOT_EQ_CONV = 
            let pth = last(CONJUNCTS pth)
            fun tm -> 
                choice {
                    let! l, r = dest_eq tm
                    let! th = INST [l, x_tm; r, y_tm] pth
                    let! tm1 = rand(concl th)
                    let! tm2 = lhand tm1
                    let! tm3 = lhand tm2
                    let th_p = POLY_CONV tm3
                    let th_x = AP_TERM neg_tm th_p
                    let th_n = CONV_RULE (RAND_CONV POLY_NEG_CONV) th_x
                    let th' = MK_DISJ (AP_THM (AP_TERM gt_tm th_p) z_tm) (AP_THM (AP_TERM gt_tm th_n) z_tm)
                    return! TRANS (Choice.result th) th'
                }

        let net_single = 
            itlist (uncurry(fun x y -> Choice.get << net_of_conv x y)) 
                [xy_lt, REAL_LT_CONV;
                 xy_nlt, (fun t -> (Choice.bind REAL_NOT_LT_CONV << rand) t);
                 xy_le, REAL_LE_CONV;
                 xy_nle, (fun t -> (Choice.bind REAL_NOT_LE_CONV << rand) t);
                 xy_gt, REAL_GT_CONV;
                 xy_ngt, (fun t -> (Choice.bind REAL_NOT_GT_CONV << rand) t);
                 xy_ge, REAL_GE_CONV;
                 xy_nge, (fun t -> (Choice.bind REAL_NOT_GE_CONV << rand) t);
                 xy_eq, REAL_EQ_CONV;
                 xy_ne, (fun t -> (Choice.bind REAL_NOT_EQ_CONV << rand) t)] empty_net

        let net_double = 
            itlist (uncurry(fun x y -> Choice.get << net_of_conv x y)) 
                [xy_lt, (fun t -> REAL_LT_CONV t, REAL_NOT_LT_CONV t);
                 xy_le, (fun t -> REAL_LE_CONV t, REAL_NOT_LE_CONV t);
                 xy_gt, (fun t -> REAL_GT_CONV t, REAL_NOT_GT_CONV t);
                 xy_ge, (fun t -> REAL_GE_CONV t, REAL_NOT_GE_CONV t);
                 xy_eq, (fun t -> REAL_EQ_CONV t, REAL_NOT_EQ_CONV t)] empty_net

        let REAL_INEQ_NORM_CONV = REWRITES_CONV net_single
        let REAL_INEQ_NORM_DCONV = REWRITES_CONV net_double
        let NNF_NORM_CONV = GEN_NNF_CONV false (REAL_INEQ_NORM_CONV, REAL_INEQ_NORM_DCONV)

        let MUL_RULE = 
            let rules = MATCH_MP_RULE pth_mul
            fun th -> CONV_RULE (LAND_CONV POLY_MUL_CONV) (rules th)

        let ADD_RULE = 
            let rules = MATCH_MP_RULE pth_add
            fun th -> CONV_RULE (LAND_CONV POLY_ADD_CONV) (rules th)

        let EMUL_RULE = 
            let rule = MATCH_MP pth_emul
            fun tm th -> CONV_RULE (LAND_CONV POLY_MUL_CONV) (SPEC tm (rule th))

        let SQUARE_RULE t = CONV_RULE (LAND_CONV POLY_MUL_CONV) (SPEC t pth_square)

        let hol_of_positivstellensatz(eqs, les, lts) = 
            let rec translate prf = 
                choice {
                    match prf with
                    | Axiom_eq n -> 
                        return! el n eqs
                    | Axiom_le n -> 
                        return! el n les
                    | Axiom_lt n -> 
                        return! el n lts
                    | Rational_eq x -> 
                        let! tm0 = mk_numeric x
                        let! tm1 = mk_comb(eq_tm, tm0)
                        let! tm2 = mk_comb(tm1, z_tm)
                        return! EQT_ELIM(NUMERIC_EQ_CONV tm2)
                    | Rational_le x -> 
                        let! tm0 = mk_numeric x
                        let! tm1 = mk_comb(ge_tm, tm0) 
                        let! tm2 = mk_comb(tm1, z_tm)
                        return! EQT_ELIM(NUMERIC_GE_CONV tm2)
                    | Rational_lt x -> 
                        let! tm0 = mk_numeric x
                        let! tm1 = mk_comb(gt_tm, tm0)
                        let! tm2 = mk_comb(tm1, z_tm)
                        return! EQT_ELIM(NUMERIC_GT_CONV tm2)
                    | Square t -> 
                        return! SQUARE_RULE t
                    | Eqmul(t, p) -> 
                        return! EMUL_RULE t (translate p)
                    | Sum(p1, p2) -> 
                        return! ADD_RULE(CONJ (translate p1) (translate p2))
                    | Product(p1, p2) -> 
                        return! MUL_RULE(CONJ (translate p1) (translate p2))
                }

            fun prf -> 
                CONV_RULE (FIRST_CONV [NUMERIC_GE_CONV; NUMERIC_GT_CONV; NUMERIC_EQ_CONV]) (translate prf)

        let init_conv = 
            TOP_DEPTH_CONV BETA_CONV
            |> THENC <| PRESIMP_CONV
            |> THENC <| NNF_CONV
            |> THENC <| DEPTH_BINOP_CONV or_tm CONDS_ELIM_CONV
            |> THENC <| NNF_NORM_CONV
            |> THENC <| SKOLEM_CONV
            |> THENC <| PRENEX_CONV
            |> THENC <| WEAK_DNF_CONV

        let rec overall dun ths = 
            choice {
                match ths with
                | [] -> 
                    let! eq, ne = Choice.List.partition (Choice.map(is_req << concl)) dun
                    let! le, nl = Choice.List.partition (Choice.map(is_ge << concl)) ne
                    let! lt = Choice.List.filter (Choice.map (is_gt << concl)) nl
                    return! prover hol_of_positivstellensatz (eq, le, lt)
                | th :: oths -> 
                    let! tm = Choice.map concl th
                    if is_conj tm then 
                        let th1, th2 = CONJ_PAIR th
                        return! overall dun (th1 :: th2 :: oths)
                    elif is_disj tm then 
                        let! tm1 = lhand tm
                        let th1 = overall dun (ASSUME tm1 :: oths)
                        let! tm2 = rand tm
                        let th2 = overall dun (ASSUME tm2 :: oths)
                        return! DISJ_CASES th th1 th2
                    else 
                        return! overall (th :: dun) oths
            }

        fun tm -> 
            choice {
                let NNF_NORM_CONV' = 
                    GEN_NNF_CONV false (CACHE_CONV REAL_INEQ_NORM_CONV, fun t -> Choice.failwith "", Choice.failwith "")

                let rec absremover t = 
                    (TOP_DEPTH_CONV(absconv1
                                    |> THENC <| BINOP_CONV(LAND_CONV POLY_CONV))
                     |> THENC <| TRY_CONV(absconv2
                                          |> THENC <| NNF_NORM_CONV'
                                          |> THENC <| BINOP_CONV absremover)) t

                let! th0 = Choice.bind init_conv (mk_neg tm)
                let! tm0 = rand(concl th0)
                let th = 
                    choice {
                        if tm0 = false_tm then 
                            return! fst(EQ_IMP_RULE (Choice.result th0))
                        else 
                            let evs, bod = strip_exists tm0
                            let avs, ibod = strip_forall bod
                            let! th1 = itlist MK_FORALL avs (DEPTH_BINOP_CONV or_tm absremover ibod)
                            let! tm1 = rand(concl th1)
                            let th2 = overall [] [SPECL avs (ASSUME tm1)]
                            let th3 = itlist SIMPLE_CHOOSE evs (PROVE_HYP (EQ_MP (Choice.result th1) (ASSUME bod)) th2)
                            let! tm2 = mk_neg tm
                            return! DISCH_ALL(PROVE_HYP (EQ_MP (Choice.result th0) (ASSUME tm2)) th3)
                    }
                return! MP (INST [tm, p_tm] pth_final) th
            }

(* ------------------------------------------------------------------------- *)
(* Linear prover. This works over the rationals in general, but is designed  *)
(* to be OK on integers provided the input contains only integers.           *)
(* ------------------------------------------------------------------------- *)

/// Refute real equations and inequations by linear reasoning (not intended for general use).
let REAL_LINEAR_PROVER = 
    let linear_add = combine (+/) (fun z -> z =/ num_0)
    let linear_cmul c = mapf(fun x -> c */ x)
    let one_tm = (parse_term @"&1")

    let contradictory p (e, _) = 
        (is_undefined e && not(p num_0)) 
        // It seems fine to use Option.get here
        || (dom e = [one_tm] && not(p(Option.get <| apply e one_tm)))

    let rec linear_ineqs vars (les, lts) = 
        find (contradictory(fun x -> x >/ num_0)) lts
        |> Option.toChoiceWithError "find"
        |> Choice.bindError (fun _ ->
            find (contradictory(fun x -> x >=/ num_0)) les
            |> Option.toChoiceWithError "find"
            |> Choice.bindError (fun _ -> 
                if vars = [] then 
                    Choice.failwith "linear_ineqs: no contradiction"
                else 
                    let ineqs = les @ lts
                    let blowup v = 
                        length(filter (fun (e, _) -> tryapplyd e v num_0 >/ num_0) ineqs) 
                        * length(filter (fun (e, _) -> tryapplyd e v num_0 </ num_0) ineqs)
                    let v = fst(hd(sort (fun (_, i) (_, j) -> i < j) (map (fun v -> v, blowup v) vars)))
                    let addup (e1, p1) (e2, p2) acc = 
                        let c1 = tryapplyd e1 v num_0
                        let c2 = tryapplyd e2 v num_0
                        if c1 */ c2 >=/ num_0 then acc
                        else 
                            let e1' = linear_cmul (abs_num c2) e1
                            let e2' = linear_cmul (abs_num c1) e2
                            let p1' = Product(Rational_lt(abs_num c2), p1)
                            let p2' = Product(Rational_lt(abs_num c1), p2)
                            (linear_add e1' e2', Sum(p1', p2')) :: acc
                    let les0, les1 = partition (fun (e, _) -> tryapplyd e v num_0 =/ num_0) les
                    let lts0, lts1 = partition (fun (e, _) -> tryapplyd e v num_0 =/ num_0) lts
                    let lesp, lesn = partition (fun (e, _) -> tryapplyd e v num_0 >/ num_0) les1
                    let ltsp, ltsn = partition (fun (e, _) -> tryapplyd e v num_0 >/ num_0) lts1
                    let les' = itlist (fun ep1 -> itlist (addup ep1) lesp) lesn les0
                    let lts' = 
                        itlist (fun ep1 -> itlist (addup ep1) (lesp @ ltsp)) ltsn 
                            (itlist (fun ep1 -> itlist (addup ep1) (lesn @ ltsn)) ltsp lts0)
                    linear_ineqs (subtract vars [v]) (les', lts')))

    let rec linear_eqs(eqs, les, lts) = 
        find (contradictory(fun x -> x =/ num_0)) eqs
        |> Option.toChoiceWithError "find"
        |> Choice.bindError (fun _ ->
            choice {
                match eqs with
                | [] -> 
                    let vars = subtract (itlist (union << dom << fst) (les @ lts) []) [one_tm]
                    return! linear_ineqs vars (les, lts)
                | (e, p) :: es -> 
                    if is_undefined e then 
                        return! linear_eqs(es, les, lts)
                    else 
                        let! x, c = choose(undefine one_tm e)
                        let xform(t, q as inp) = 
                            choice {
                                let d = tryapplyd t x num_0
                                if d =/ num_0 then 
                                    return inp
                                else 
                                    let k = minus_num d */ abs_num c
                                    let e' = linear_cmul k e
                                    let t' = linear_cmul (abs_num c) t
                                    let! tm1 = term_of_rat k
                                    let p' = Eqmul(tm1, p)
                                    let q' = Product(Rational_lt(abs_num c), q)
                                    return linear_add e' t', Sum(p', q')
                            }

                        let! es1 = Choice.List.map xform es
                        let! les1 = Choice.List.map xform les
                        let! lts1 = Choice.List.map xform lts
                        return! linear_eqs(es1, les1, lts1)
              })

    let linear_prover = 
        fun (eq, le, lt) -> 
            let eqs = map2 (fun p n -> p, Axiom_eq n) eq (0 -- (length eq - 1))
            let les = map2 (fun p n -> p, Axiom_le n) le (0 -- (length le - 1))
            let lts = map2 (fun p n -> p, Axiom_lt n) lt (0 -- (length lt - 1))
            linear_eqs(eqs, les, lts)

    let lin_of_hol = 
        let one_tm = (parse_term @"&1")
        let zero_tm = (parse_term @"&0")
        let add_tm = (parse_term @"(+):real->real->real")
        let mul_tm = (parse_term @"(*):real->real->real")
        let rec lin_of_hol tm =    
            choice {
                if tm = zero_tm then 
                    return undefined
                elif not(is_comb tm) then 
                    return (tm |=> Int 1)
                elif is_ratconst tm then 
                    let! tm1 = rat_of_term tm
                    return (one_tm |=> tm1)
                else 
                    let! lop, r = dest_comb tm
                    if not(is_comb lop) then 
                        return (tm |=> Int 1)
                    else 
                        let! op, l = dest_comb lop
                        if op = add_tm then
                            let! l' = lin_of_hol l
                            let! r' = lin_of_hol r
                            return linear_add l' r'
                        elif op = mul_tm && is_ratconst l then 
                            let! tm1 = rat_of_term l
                            return (r |=> tm1)
                        else 
                            return (tm |=> Int 1)
            }
        lin_of_hol

    let is_alien tm = 
        match tm with
        | Comb(Const("real_of_num", _), n) when not(is_numeral n) -> true
        | _ -> false

    let n_tm = (parse_term @"n:num")

    let pth = REWRITE_RULE [GSYM real_ge] (SPEC n_tm REAL_POS)

    fun translator (eq, le, lt) -> 
        choice {
            let! eq_pols = Choice.List.map (Choice.bind lin_of_hol << Choice.bind lhand << Choice.map concl) eq
            let! le_pols = Choice.List.map (Choice.bind lin_of_hol << Choice.bind lhand << Choice.map concl) le
            let! lt_pols = Choice.List.map (Choice.bind lin_of_hol << Choice.bind lhand << Choice.map concl) lt
            let aliens = filter is_alien (itlist (union << dom) (eq_pols @ le_pols @ lt_pols) [])
            let le_pols' = le_pols @ map (fun v -> (v |=> Int 1)) aliens
            let! _, proof = linear_prover(eq_pols, le_pols', lt_pols)
            
            let le0 = map (fun a -> 
                            choice {
                                let! tm1 = rand a
                                return! INST [tm1, n_tm] pth
                            }) aliens

            let le' = le @ le0
            return! translator (eq, le', lt) proof
        }

(* ------------------------------------------------------------------------- *)
(* Bootstrapping REAL_ARITH: trivial abs-elim and only integer constants.    *)
(* ------------------------------------------------------------------------- *)

let REAL_ARITH_001 = 
    let REAL_POLY_NEG_CONV, REAL_POLY_ADD_CONV, REAL_POLY_SUB_CONV, REAL_POLY_MUL_CONV, REAL_POLY_POW_CONV, REAL_POLY_CONV = 
        SEMIRING_NORMALIZERS_CONV REAL_POLY_CLAUSES REAL_POLY_NEG_CLAUSES 
            (is_realintconst, REAL_INT_ADD_CONV, REAL_INT_MUL_CONV, 
             REAL_INT_POW_CONV) (<)
    let rule = 
        GEN_REAL_ARITH_001
            (mk_realintconst, REAL_INT_EQ_CONV, REAL_INT_GE_CONV, 
             REAL_INT_GT_CONV, REAL_POLY_CONV, REAL_POLY_NEG_CONV, 
             REAL_POLY_ADD_CONV, REAL_POLY_MUL_CONV, NO_CONV, NO_CONV, 
             REAL_LINEAR_PROVER)
    let deabs_conv = REWRITE_CONV [real_abs; real_max; real_min]
    fun tm -> 
        choice {
            let! th1 = deabs_conv tm
            let! tm1 = rand(concl th1)
            return! EQ_MP (SYM (Choice.result th1)) (rule tm1)
        }

(* ------------------------------------------------------------------------- *)
(* Slightly less parametrized GEN_REAL_ARITH with more intelligent           *)
(* elimination of abs, max and min hardwired in.                             *)
(* ------------------------------------------------------------------------- *)

/// Initial normalization and proof reconstruction wrapper for real decision procedure.
let GEN_REAL_ARITH = 
    let ABSMAXMIN_ELIM_CONV1 = 
     GEN_REWRITE_CONV I [time REAL_ARITH_001 (parse_term @"(--(&1) * abs(x) >= r <=>
       --(&1) * x >= r /\ &1 * x >= r) /\
      (--(&1) * abs(x) + a >= r <=>
       a + --(&1) * x >= r /\ a + &1 * x >= r) /\
      (a + --(&1) * abs(x) >= r <=>
       a + --(&1) * x >= r /\ a + &1 * x >= r) /\
      (a + --(&1) * abs(x) + b >= r <=>
       a + --(&1) * x + b >= r /\ a + &1 * x + b >= r) /\
      (a + b + --(&1) * abs(x) >= r <=>
       a + b + --(&1) * x >= r /\ a + b + &1 * x >= r) /\
      (a + b + --(&1) * abs(x) + c >= r <=>
       a + b + --(&1) * x + c >= r /\ a + b + &1 * x + c >= r) /\
      (--(&1) * max x y >= r <=>
       --(&1) * x >= r /\ --(&1) * y >= r) /\
      (--(&1) * max x y + a >= r <=>
       a + --(&1) * x >= r /\ a + --(&1) * y >= r) /\
      (a + --(&1) * max x y >= r <=>
       a + --(&1) * x >= r /\ a + --(&1) * y >= r) /\
      (a + --(&1) * max x y + b >= r <=>
       a + --(&1) * x + b >= r /\ a + --(&1) * y  + b >= r) /\
      (a + b + --(&1) * max x y >= r <=>
       a + b + --(&1) * x >= r /\ a + b + --(&1) * y >= r) /\
      (a + b + --(&1) * max x y + c >= r <=>
       a + b + --(&1) * x + c >= r /\ a + b + --(&1) * y  + c >= r) /\
      (&1 * min x y >= r <=>
       &1 * x >= r /\ &1 * y >= r) /\
      (&1 * min x y + a >= r <=>
       a + &1 * x >= r /\ a + &1 * y >= r) /\
      (a + &1 * min x y >= r <=>
       a + &1 * x >= r /\ a + &1 * y >= r) /\
      (a + &1 * min x y + b >= r <=>
       a + &1 * x + b >= r /\ a + &1 * y  + b >= r) /\
      (a + b + &1 * min x y >= r <=>
       a + b + &1 * x >= r /\ a + b + &1 * y >= r) /\
      (a + b + &1 * min x y + c >= r <=>
       a + b + &1 * x + c >= r /\ a + b + &1 * y  + c >= r) /\
      (min x y >= r <=>
        x >= r /\  y >= r) /\
      (min x y + a >= r <=>
       a + x >= r /\ a + y >= r) /\
      (a + min x y >= r <=>
       a + x >= r /\ a + y >= r) /\
      (a + min x y + b >= r <=>
       a + x + b >= r /\ a + y  + b >= r) /\
      (a + b + min x y >= r <=>
       a + b + x >= r /\ a + b + y >= r) /\
      (a + b + min x y + c >= r <=>
       a + b + x + c >= r /\ a + b + y + c >= r) /\
      (--(&1) * abs(x) > r <=>
       --(&1) * x > r /\ &1 * x > r) /\
      (--(&1) * abs(x) + a > r <=>
       a + --(&1) * x > r /\ a + &1 * x > r) /\
      (a + --(&1) * abs(x) > r <=>
       a + --(&1) * x > r /\ a + &1 * x > r) /\
      (a + --(&1) * abs(x) + b > r <=>
       a + --(&1) * x + b > r /\ a + &1 * x + b > r) /\
      (a + b + --(&1) * abs(x) > r <=>
       a + b + --(&1) * x > r /\ a + b + &1 * x > r) /\
      (a + b + --(&1) * abs(x) + c > r <=>
       a + b + --(&1) * x + c > r /\ a + b + &1 * x + c > r) /\
      (--(&1) * max x y > r <=>
       --(&1) * x > r /\ --(&1) * y > r) /\
      (--(&1) * max x y + a > r <=>
       a + --(&1) * x > r /\ a + --(&1) * y > r) /\
      (a + --(&1) * max x y > r <=>
       a + --(&1) * x > r /\ a + --(&1) * y > r) /\
      (a + --(&1) * max x y + b > r <=>
       a + --(&1) * x + b > r /\ a + --(&1) * y  + b > r) /\
      (a + b + --(&1) * max x y > r <=>
       a + b + --(&1) * x > r /\ a + b + --(&1) * y > r) /\
      (a + b + --(&1) * max x y + c > r <=>
       a + b + --(&1) * x + c > r /\ a + b + --(&1) * y  + c > r) /\
      (min x y > r <=>
        x > r /\  y > r) /\
      (min x y + a > r <=>
       a + x > r /\ a + y > r) /\
      (a + min x y > r <=>
       a + x > r /\ a + y > r) /\
      (a + min x y + b > r <=>
       a + x + b > r /\ a + y  + b > r) /\
      (a + b + min x y > r <=>
       a + b + x > r /\ a + b + y > r) /\
      (a + b + min x y + c > r <=>
       a + b + x + c > r /\ a + b + y + c > r)")]
    let ABSMAXMIN_ELIM_CONV2 = 
        let pth_abs = 
            prove
                ((parse_term @"P(abs x) <=> (x >= &0 /\ P x) \/ (&0 > x /\ P (--x))"), 
                 REWRITE_TAC [real_abs; real_gt; real_ge]
                 |> THEN <| COND_CASES_TAC
                 |> THEN <| ASM_REWRITE_TAC [real_lt])

        let pth_max = 
            prove
                ((parse_term @"P(max x y) <=> (y >= x /\ P y) \/ (x > y /\ P x)"), 
                 REWRITE_TAC [real_max; real_gt; real_ge]
                 |> THEN <| COND_CASES_TAC
                 |> THEN <| ASM_REWRITE_TAC [real_lt])

        let pth_min = 
            prove
                ((parse_term @"P(min x y) <=> (y >= x /\ P x) \/ (x > y /\ P y)"), 
                 REWRITE_TAC [real_min; real_gt; real_ge]
                 |> THEN <| COND_CASES_TAC
                 |> THEN <| ASM_REWRITE_TAC [real_lt])

        let abs_tm = (parse_term @"real_abs")
        let p_tm = (parse_term @"P:real->bool")
        let x_tm = (parse_term @"x:real")
        let y_tm = (parse_term @"y:real")
        let is_max = is_binop(parse_term @"real_max")
        let is_min = is_binop(parse_term @"real_min")

        let is_abs t = 
            // It's safe to use Choice.get here
            is_comb t && Choice.get <| rator t = abs_tm

        let eliminate_construct p c tm = 
            choice {
                let! t = find_term (fun t -> p t && free_in t tm) tm
                let! ty1 = type_of t
                let v = genvar ty1
                let! tm1 = subst [v, t] tm
                let! tm2 = mk_abs(v, tm1)
                let! tm3 = mk_comb(tm2, t)
                let! th0 = SYM(BETA_CONV tm3)
                let! tm4 = rand(concl th0)
                let! p, ax = dest_comb tm4
                return! CONV_RULE (RAND_CONV(BINOP_CONV(RAND_CONV BETA_CONV))) (TRANS (Choice.result th0) (c p ax))
            }

        let elim_abs = 
            eliminate_construct is_abs (fun p ax -> 
                    choice {
                        let! tm1 = rand ax
                        return! INST [p, p_tm; tm1, x_tm] pth_abs
                    })

        let elim_max = 
            eliminate_construct is_max (fun p ax -> 
                    choice {
                        let! ax, y = dest_comb ax
                        let! tm1 = rand ax
                        return! INST [p, p_tm; tm1, x_tm; y, y_tm] pth_max
                    })

        let elim_min = 
            eliminate_construct is_min (fun p ax -> 
                    choice {
                        let! ax, y = dest_comb ax
                        let! tm1 = rand ax
                        return! INST [p, p_tm; tm1, x_tm; y, y_tm] pth_min
                    })

        FIRST_CONV [elim_abs; elim_max; elim_min]

    fun (mkconst, EQ, GE, GT, NORM, NEG, ADD, MUL, PROVER) -> 
        GEN_REAL_ARITH_001(mkconst, EQ, GE, GT, NORM, NEG, ADD, MUL, ABSMAXMIN_ELIM_CONV1, ABSMAXMIN_ELIM_CONV2, PROVER)

(* ------------------------------------------------------------------------- *)
(* Incorporate that. This gets overwritten again in "calc_rat.ml".           *)
(* ------------------------------------------------------------------------- *)

/// Attempt to prove term using basic algebra and linear arithmetic over the reals.
let REAL_ARITH = 
    let REAL_POLY_NEG_CONV, REAL_POLY_ADD_CONV, REAL_POLY_SUB_CONV, REAL_POLY_MUL_CONV, REAL_POLY_POW_CONV, REAL_POLY_CONV = 
        SEMIRING_NORMALIZERS_CONV REAL_POLY_CLAUSES REAL_POLY_NEG_CLAUSES 
            (is_realintconst, REAL_INT_ADD_CONV, REAL_INT_MUL_CONV, 
             REAL_INT_POW_CONV) (<)
    GEN_REAL_ARITH
        (mk_realintconst, REAL_INT_EQ_CONV, REAL_INT_GE_CONV, REAL_INT_GT_CONV, 
         REAL_POLY_CONV, REAL_POLY_NEG_CONV, REAL_POLY_ADD_CONV, 
         REAL_POLY_MUL_CONV, REAL_LINEAR_PROVER)
