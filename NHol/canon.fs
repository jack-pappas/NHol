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
/// Tools for putting terms in canonical forms.
module NHol.canon

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
#endif

(* ------------------------------------------------------------------------- *)
(* Pre-simplification.                                                       *)
(* ------------------------------------------------------------------------- *)

/// Applies basic propositional simplications and some miniscoping.
let (PRESIMP_CONV : conv) = 
    GEN_REWRITE_CONV TOP_DEPTH_CONV 
        [NOT_CLAUSES; AND_CLAUSES; OR_CLAUSES; IMP_CLAUSES; EQ_CLAUSES; 
         FORALL_SIMP; EXISTS_SIMP; EXISTS_OR_THM; FORALL_AND_THM; 
         LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM; LEFT_FORALL_OR_THM; 
         RIGHT_FORALL_OR_THM]

(* ------------------------------------------------------------------------- *)
(* ACI rearrangements of conjunctions and disjunctions. This is much faster  *)
(* than AC xxx_ACI on large problems, as well as being more controlled.      *)
(* ------------------------------------------------------------------------- *)

/// Proves equivalence of two conjunctions containing same set of conjuncts.
let (CONJ_ACI_RULE : conv) = 

    let rec mk_fun th fn = 
      choice {
        let! tm = Choice.map concl th
        if is_conj tm then 
            let th1, th2 = CONJ_PAIR th
            let! fn' = mk_fun th2 fn
            return! mk_fun th1 fn'
        else
            // NOTE: add this to fall back to thm0
            let! th = th 
            return (tm |-> th) fn
      }

    and use_fun fn tm = 
      choice {
        if is_conj tm then 
            let! l, r = dest_conj tm
            return! CONJ (use_fun fn l) (use_fun fn r)
        else 
            return! apply fn tm
                    |> Option.toChoiceWithError "apply"
      }

    fun fm -> 
        choice {
            let! p, p' = dest_eq fm
            if p = p' then 
                return! REFL p
            else
                let! fn = mk_fun (ASSUME p) undefined
                let th = use_fun fn p'
                let! fn' = mk_fun (ASSUME p') undefined
                let th' = use_fun fn' p
                return! IMP_ANTISYM_RULE (DISCH_ALL th) (DISCH_ALL th')
        }

/// Proves equivalence of two disjunctions containing same set of disjuncts.
let (DISJ_ACI_RULE : conv) = 
    let pth_left = UNDISCH(TAUT(parse_term @"~(a \/ b) ==> ~a"))
    let pth_right = UNDISCH(TAUT(parse_term @"~(a \/ b) ==> ~b"))
    let pth = repeat (Choice.toOption << Choice.map Choice.result << UNDISCH) (TAUT(parse_term @"~a ==> ~b ==> ~(a \/ b)"))
    let pth_neg = UNDISCH(TAUT(parse_term @"(~a <=> ~b) ==> (a <=> b)"))

    let a_tm = (parse_term @"a:bool")
    let b_tm = (parse_term @"b:bool")

    let NOT_DISJ_PAIR th = 
        choice {
            let! p, q = (Choice.bind dest_disj << Choice.bind rand << Choice.map concl) th
            let ilist =  [p, a_tm; q, b_tm]
            return PROVE_HYP th (INST ilist pth_left), PROVE_HYP th (INST ilist pth_right)
        }
        |> Choice.getOrFailure2 "NOT_DISJ_PAIR"

    let NOT_DISJ th1 th2 = 
        choice {
            let! tm1 = Choice.bind (rand << concl) th1
            let! tm2 = Choice.bind (rand << concl) th2
            let th3 = INST [tm1, a_tm; tm2, b_tm] pth
            return! PROVE_HYP th1 (PROVE_HYP th2 th3)
        }

    let rec mk_fun th fn = 
      choice {
        let! tm = Choice.bind (rand << concl) th
        if is_disj tm then 
            let th1, th2 = NOT_DISJ_PAIR th
            let! fn' = mk_fun th2 fn
            return! mk_fun th1 fn'
        else
            let! th = th 
            return (tm |-> th) fn
      }

    and use_fun fn tm = 
      choice {
        if is_disj tm then 
            let! l, r = dest_disj tm
            return! NOT_DISJ (use_fun fn l) (use_fun fn r)
        else 
            return! apply fn tm |> Option.toChoiceWithError "apply"
      }

    fun fm -> 
        choice {
            let! p, p' = dest_eq fm        
            if p = p' then 
                return! REFL p
            else 
                let! neg_p = mk_neg p
                let! neg_p' = mk_neg p'
                let! fn = mk_fun (ASSUME neg_p) undefined
                let th = use_fun fn p'
                let! fn' = mk_fun (ASSUME neg_p') undefined
                let th' = use_fun fn' p
                let th1 = IMP_ANTISYM_RULE (DISCH_ALL th) (DISCH_ALL th')
                return! PROVE_HYP th1 (INST [p, a_tm; p', b_tm] pth_neg)
        }

(* ------------------------------------------------------------------------- *)
(* Order canonically, right-associate and remove duplicates.                 *)
(* ------------------------------------------------------------------------- *)

/// Puts an iterated conjunction in canonical form.
let CONJ_CANON_CONV tm : Protected<thm0> = 
    choice {
        let! tm' = list_mk_conj(setify(conjuncts tm))
        let! tm1 = mk_eq(tm, tm')
        return! CONJ_ACI_RULE tm1
    }

/// Puts an iterated disjunction in canonical form.
let DISJ_CANON_CONV tm : Protected<thm0> = 
    choice {
        let! tm' = list_mk_disj(setify(disjuncts tm))
        let! tm1 = mk_eq(tm, tm')
        return! DISJ_ACI_RULE tm1
    }

(* ------------------------------------------------------------------------- *)
(* General NNF conversion. The user supplies some conversion to be applied   *)
(* to atomic formulas.                                                       *)
(*                                                                           *)
(* "Iff"s are split conjunctively or disjunctively according to the flag     *)
(* argument (conjuctively = true) until a universal quantifier (modulo       *)
(* current parity) is passed; after that they are split conjunctively. This  *)
(* is appropriate when the result is passed to a disjunctive splitter        *)
(* followed by a clausal form inner core, such as MESON.                     *)
(*                                                                           *)
(* To avoid some duplicate computation, this function will in general        *)
(* enter a recursion where it simultaneously computes NNF representations    *)
(* for "p" and "~p", so the user needs to supply an atomic "conversion"      *)
(* that does the same.                                                       *)
(* ------------------------------------------------------------------------- *)

/// General NNF (negation normal form) conversion.
let (GEN_NNF_CONV : bool -> conv * (term -> Protected<thm0> * Protected<thm0>) -> conv) = 
    let and_tm = (parse_term @"(/\)")
    let or_tm = (parse_term @"(\/)")
    let not_tm = (parse_term @"(~)")
    let pth_not_not = TAUT(parse_term @"~ ~ p = p")
    let pth_not_and = TAUT(parse_term @"~(p /\ q) <=> ~p \/ ~q")
    let pth_not_or = TAUT(parse_term @"~(p \/ q) <=> ~p /\ ~q")
    let pth_imp = TAUT(parse_term @"p ==> q <=> ~p \/ q")
    let pth_not_imp = TAUT(parse_term @"~(p ==> q) <=> p /\ ~q")
    let pth_eq = TAUT(parse_term @"(p <=> q) <=> p /\ q \/ ~p /\ ~q")
    let pth_not_eq = TAUT(parse_term @"~(p <=> q) <=> p /\ ~q \/ ~p /\ q")
    let pth_eq' = TAUT(parse_term @"(p <=> q) <=> (p \/ ~q) /\ (~p \/ q)")
    let pth_not_eq' = TAUT(parse_term @"~(p <=> q) <=> (p \/ q) /\ (~p \/ ~q)")

    let pth_triple = 
        let pth_notFuncs =
            (CONJUNCTS << prove)
              ((parse_term @"(~((!) P) <=> ?x:A. ~(P x)) /\
                (~((?) P) <=> !x:A. ~(P x)) /\
                (~((?!) P) <=> (!x:A. ~(P x)) \/ ?x y. P x /\ P y /\ ~(y = x))"), 
                  REPEAT CONJ_TAC
                  |> THEN <| GEN_REWRITE_TAC (LAND_CONV << funpow 2 RAND_CONV) [GSYM ETA_AX]
                  |> THEN <| REWRITE_TAC [NOT_EXISTS_THM; NOT_FORALL_THM; EXISTS_UNIQUE_DEF; DE_MORGAN_THM; NOT_IMP]
                  |> THEN <| REWRITE_TAC [CONJ_ASSOC; EQ_SYM_EQ])
        match pth_notFuncs with
        | [pth_not_forall; pth_not_exists; pth_not_exu] -> Choice.result (pth_not_forall, pth_not_exists, pth_not_exu)
        | _ -> Choice.failwith "pth_notFuncs: Unhandled case."

    let pth_exu = 
        prove
            ((parse_term @"((?!) P) <=> (?x:A. P x) /\ !x y. ~(P x) \/ ~(P y) \/ (y = x)"), 
             GEN_REWRITE_TAC (LAND_CONV << RAND_CONV) [GSYM ETA_AX]
             |> THEN <| REWRITE_TAC [EXISTS_UNIQUE_DEF; TAUT(parse_term @"a /\ b ==> c <=> ~a \/ ~b \/ c")]
             |> THEN <| REWRITE_TAC [EQ_SYM_EQ])

    let p_tm = (parse_term @"p:bool")
    let q_tm = (parse_term @"q:bool")

    let rec NNF_DCONV cf baseconvs tm = 
        choice {
            let! (pth_not_forall, pth_not_exists, pth_not_exu) = pth_triple

            match tm with
            | Comb(Comb(Const("/\\", _), l), r) -> 
                let th_lp, th_ln = NNF_DCONV cf baseconvs l
                let th_rp, th_rn = NNF_DCONV cf baseconvs r
                return 
                    MK_COMB(AP_TERM and_tm th_lp, th_rp), 
                    TRANS (INST [l, p_tm; r, q_tm] pth_not_and) 
                        (MK_COMB(AP_TERM or_tm th_ln, th_rn))
            | Comb(Comb(Const("\\/", _), l), r) -> 
                let th_lp, th_ln = NNF_DCONV cf baseconvs l
                let th_rp, th_rn = NNF_DCONV cf baseconvs r
                return
                    MK_COMB(AP_TERM or_tm th_lp, th_rp), 
                    TRANS (INST [l, p_tm; r, q_tm] pth_not_or) 
                        (MK_COMB(AP_TERM and_tm th_ln, th_rn))
            | Comb(Comb(Const("==>", _), l), r) -> 
                let th_lp, th_ln = NNF_DCONV cf baseconvs l
                let th_rp, th_rn = NNF_DCONV cf baseconvs r
                return
                    TRANS (INST [l, p_tm; r, q_tm] pth_imp) (MK_COMB(AP_TERM or_tm th_ln, th_rp)), 
                    TRANS (INST [l, p_tm; r, q_tm] pth_not_imp) 
                        (MK_COMB(AP_TERM and_tm th_lp, th_rn))
            | Comb(Comb(Const("=", Tyapp("fun", Tyapp("bool", _) :: _)), l), r) -> 
                let th_lp, th_ln = NNF_DCONV cf baseconvs l
                let th_rp, th_rn = NNF_DCONV cf baseconvs r
                if cf then 
                  return
                    TRANS (INST [l, p_tm; r, q_tm] pth_eq') 
                        (MK_COMB
                             (AP_TERM and_tm (MK_COMB(AP_TERM or_tm th_lp, th_rn)), 
                              MK_COMB(AP_TERM or_tm th_ln, th_rp))), 
                    TRANS (INST [l, p_tm; r, q_tm] pth_not_eq') 
                        (MK_COMB
                             (AP_TERM and_tm (MK_COMB(AP_TERM or_tm th_lp, th_rp)), 
                              MK_COMB(AP_TERM or_tm th_ln, th_rn)))
                else
                  return 
                    TRANS (INST [l, p_tm; r, q_tm] pth_eq) 
                        (MK_COMB
                             (AP_TERM or_tm (MK_COMB(AP_TERM and_tm th_lp, th_rp)), 
                              MK_COMB(AP_TERM and_tm th_ln, th_rn))), 
                    TRANS (INST [l, p_tm; r, q_tm] pth_not_eq) 
                        (MK_COMB
                             (AP_TERM or_tm (MK_COMB(AP_TERM and_tm th_lp, th_rn)), 
                              MK_COMB(AP_TERM and_tm th_ln, th_rp)))

            | Comb(Const("!", Tyapp("fun", Tyapp("fun", ty :: _) :: _)) as q, (Abs(x, t) as bod)) -> 
                let th_p, th_n = NNF_DCONV true baseconvs t
                 
                let th0 = AP_TERM q (ABS x th_p)
                let! ty1 = mk_fun_ty ty bool_ty
                let th1 = INST [bod,mk_var("P", ty1)] (INST_TYPE [ty,aty] pth_not_forall)
                let! tm1 = mk_comb(bod, x)
                let th2 = TRANS (AP_TERM not_tm (BETA tm1)) th_n
                return th0, TRANS th1 (MK_EXISTS x th2)

            | Comb(Const("?", Tyapp("fun", Tyapp("fun", ty :: _) :: _)) as q, (Abs(x, t) as bod)) -> 
                let th_p, th_n = NNF_DCONV cf baseconvs t
                 
                let th0 = AP_TERM q (ABS x th_p)
                let! ty1 = mk_fun_ty ty bool_ty
                let th1 = INST [bod,mk_var("P", ty1)] (INST_TYPE [ty,aty] pth_not_exists)
                let! tm1 = mk_comb(bod, x)
                let th2 = TRANS (AP_TERM not_tm (BETA tm1)) th_n
                return th0, TRANS th1 (MK_FORALL x th2)

            | Comb(Const("?!", Tyapp("fun", Tyapp("fun", ty :: _) :: _)), (Abs(x, t) as bod)) -> 
                let! y = variant (x :: frees t) x
                let th_p, th_n = NNF_DCONV cf baseconvs t
                let! eq = mk_eq(y, x)
                let eth_p, eth_n = baseconvs eq
                let! tm1 = mk_comb(bod, x)
                let bth = BETA tm1
                let! tm2 = mk_comb(bod, y)
                let bth' = BETA_CONV tm2
                let th_p' = INST [y, x] th_p
                let th_n' = INST [y, x] th_n
                let th1 = 
                    mk_fun_ty ty bool_ty
                    |> Choice.bind (fun ty' ->
                        INST [bod, mk_var("P", ty')] 
                            (INST_TYPE [ty, aty] pth_exu))
                let th1' = 
                    mk_fun_ty ty bool_ty
                    |> Choice.bind (fun ty' ->
                        INST [bod, mk_var("P", ty')] 
                            (INST_TYPE [ty, aty] pth_not_exu))

                let th2 = 
                    MK_COMB
                        (AP_TERM and_tm (MK_EXISTS x (TRANS bth th_p)), 
                         MK_FORALL x 
                             (MK_FORALL y 
                                  (MK_COMB
                                       (AP_TERM or_tm 
                                            (TRANS (AP_TERM not_tm bth) th_n), 
                                        MK_COMB
                                            (AP_TERM or_tm 
                                                 (TRANS (AP_TERM not_tm bth') th_n'), 
                                             eth_p)))))
                let th2' = 
                    MK_COMB
                        (AP_TERM or_tm 
                             (MK_FORALL x (TRANS (AP_TERM not_tm bth) th_n)), 
                         MK_EXISTS x 
                             (MK_EXISTS y 
                                  (MK_COMB
                                       (AP_TERM and_tm (TRANS bth th_p), 
                                        MK_COMB
                                            (AP_TERM and_tm (TRANS bth' th_p'), 
                                             eth_n)))))
                return TRANS th1 th2, TRANS th1' th2'

            | Comb(Const("~", _), t) -> 
                let th1, th2 = NNF_DCONV cf baseconvs t
                return th2, TRANS (INST [t, p_tm] pth_not_not) th1
            | _ -> 
                let v = 
                    match baseconvs tm with
                    | (Success _, Success _) as tm' -> tm'
                    | _ -> REFL tm, Choice.bind REFL (mk_neg tm)
                return v
        }
        |> Choice.getOrFailure2 "NNF_DCONV"

    let rec NNF_CONV cf (base1, base2 as baseconvs) tm = 
        choice {
            match tm with
            | Comb(Comb(Const("/\\", _), l), r) -> 
                let th_lp = NNF_CONV cf baseconvs l
                let th_rp = NNF_CONV cf baseconvs r
                return! MK_COMB(AP_TERM and_tm th_lp, th_rp)
            | Comb(Comb(Const("\\/", _), l), r) -> 
                let th_lp = NNF_CONV cf baseconvs l
                let th_rp = NNF_CONV cf baseconvs r
                return! MK_COMB(AP_TERM or_tm th_lp, th_rp)
            | Comb(Comb(Const("==>", _), l), r) -> 
                let th_ln = NNF_CONV' cf baseconvs l
                let th_rp = NNF_CONV cf baseconvs r
                return! TRANS (INST [l, p_tm; r, q_tm] pth_imp) (MK_COMB(AP_TERM or_tm th_ln, th_rp))
            | Comb(Comb(Const("=", Tyapp("fun", Tyapp("bool", _) :: _)), l), r) -> 
                let th_lp, th_ln = NNF_DCONV cf base2 l
                let th_rp, th_rn = NNF_DCONV cf base2 r
                if cf then
                    return!  
                      TRANS (INST [l, p_tm; r, q_tm] pth_eq') 
                        (MK_COMB
                             (AP_TERM and_tm (MK_COMB(AP_TERM or_tm th_lp, th_rn)), 
                              MK_COMB(AP_TERM or_tm th_ln, th_rp)))
                else
                    return!  
                      TRANS (INST [l, p_tm; r, q_tm] pth_eq) 
                        (MK_COMB
                             (AP_TERM or_tm (MK_COMB(AP_TERM and_tm th_lp, th_rp)), 
                              MK_COMB(AP_TERM and_tm th_ln, th_rn)))
            | Comb(Const("!", Tyapp("fun", Tyapp("fun", ty :: _) :: _)) as q, (Abs(x, t))) -> 
                let th_p = NNF_CONV true baseconvs t
                return! AP_TERM q (ABS x th_p)
            | Comb(Const("?", Tyapp("fun", Tyapp("fun", ty :: _) :: _)) as q, (Abs(x, t))) -> 
                let th_p = NNF_CONV cf baseconvs t
                return! AP_TERM q (ABS x th_p)
            | Comb(Const("?!", Tyapp("fun", Tyapp("fun", ty :: _) :: _)), (Abs(x, t) as bod)) -> 
                let! y = variant (x :: frees t) x
                let th_p, th_n = NNF_DCONV cf base2 t
                let! eq = mk_eq(y, x)
                let eth_p, eth_n = base2 eq
                let! tm1 = mk_comb(bod, x)
                let bth = BETA tm1
                let! tm2 = mk_comb(bod, y)
                let bth' = BETA_CONV tm2
                let th_n' = INST [y, x] th_n
                let! ty1 = mk_fun_ty ty bool_ty
                let th1 = 
                    INST [bod, mk_var("P", ty1)] (INST_TYPE [ty, aty] pth_exu)
                let th2 = 
                    MK_COMB
                        (AP_TERM and_tm (MK_EXISTS x (TRANS bth th_p)), 
                     
                            MK_FORALL x 
                                (MK_FORALL y 
                                    (MK_COMB
                                        (AP_TERM or_tm (TRANS (AP_TERM not_tm bth) th_n), 
                                        MK_COMB(AP_TERM or_tm (TRANS (AP_TERM not_tm bth') th_n'), eth_p)))))
                return! TRANS th1 th2
            
            | Comb(Const("~", _), t) -> 
                return! NNF_CONV' cf baseconvs t
            | _ -> 
                return! 
                    base1 tm
                    |> Choice.bindError (fun _ -> REFL tm)
        }

    and NNF_CONV' cf (base1, base2 as baseconvs) tm = 
        choice {
            let! (pth_not_forall, pth_not_exists, pth_not_exu) = pth_triple

            match tm with
            | Comb(Comb(Const("/\\", _), l), r) -> 
                let th_ln = NNF_CONV' cf baseconvs l
                let th_rn = NNF_CONV' cf baseconvs r
                return!
                  TRANS (INST [l, p_tm; r, q_tm] pth_not_and) 
                    (MK_COMB(AP_TERM or_tm th_ln, th_rn))
            | Comb(Comb(Const("\\/", _), l), r) -> 
                let th_ln = NNF_CONV' cf baseconvs l
                let th_rn = NNF_CONV' cf baseconvs r
                return!
                  TRANS (INST [l, p_tm; r, q_tm] pth_not_or) 
                    (MK_COMB(AP_TERM and_tm th_ln, th_rn))
            | Comb(Comb(Const("==>", _), l), r) -> 
                let th_lp = NNF_CONV cf baseconvs l
                let th_rn = NNF_CONV' cf baseconvs r
                return!
                  TRANS (INST [l, p_tm; r, q_tm] pth_not_imp) 
                    (MK_COMB(AP_TERM and_tm th_lp, th_rn))
            | Comb(Comb(Const("=", Tyapp("fun", Tyapp("bool", _) :: _)), l), r) -> 
                let th_lp, th_ln = NNF_DCONV cf base2 l
                let th_rp, th_rn = NNF_DCONV cf base2 r
                if cf then
                    return! 
                      TRANS (INST [l, p_tm; r, q_tm] pth_not_eq') 
                        (MK_COMB(AP_TERM and_tm (MK_COMB(AP_TERM or_tm th_lp, th_rp)), 
                                                 MK_COMB(AP_TERM or_tm th_ln, th_rn)))
                else
                    return! 
                      TRANS (INST [l, p_tm; r, q_tm] pth_not_eq) 
                        (MK_COMB(AP_TERM or_tm (MK_COMB(AP_TERM and_tm th_lp, th_rn)), 
                                                MK_COMB(AP_TERM and_tm th_ln, th_rp)))

            | Comb(Const("!", Tyapp("fun", Tyapp("fun", ty :: _) :: _)), (Abs(x, t) as bod)) ->
                let th_n = NNF_CONV' cf baseconvs t
                let! ty1 = mk_fun_ty ty bool_ty
                let th1 = INST [bod, mk_var("P", ty1)] (INST_TYPE [ty, aty] pth_not_forall)

                let! tm2 = mk_comb(bod, x)
                let th2 = TRANS (AP_TERM not_tm (BETA tm2)) th_n
                return! TRANS th1 (MK_EXISTS x th2)
            
            | Comb(Const("?", Tyapp("fun", Tyapp("fun", ty :: _) :: _)), (Abs(x, t) as bod)) ->
                let th_n = NNF_CONV' true baseconvs t
                let! ty1 = mk_fun_ty ty bool_ty
                let th1 = INST [bod, mk_var("P", ty1)] (INST_TYPE [ty, aty] pth_not_exists)
                let! tm2 = mk_comb(bod, x)
                let th2 = TRANS (AP_TERM not_tm (BETA tm2)) th_n
                return! TRANS th1 (MK_FORALL x th2)
                
            | Comb(Const("?!", Tyapp("fun", Tyapp("fun", ty :: _) :: _)), (Abs(x, t) as bod)) -> 
                let! y = variant (x :: frees t) x
                let th_p, th_n = NNF_DCONV cf base2 t
                let! eq = mk_eq(y, x)
                let eth_p, eth_n = base2 eq
                let! tm1 = mk_comb(bod, x)
                let bth = BETA tm1
                let! tm2 = mk_comb(bod, y)
                let bth' = BETA_CONV tm2
                let th_p' = INST [y, x] th_p
                let! ty1 = mk_fun_ty ty bool_ty
                let th1' = INST [bod, mk_var("P", ty1)] (INST_TYPE [ty, aty] pth_not_exu)
                let th2' = 
                    MK_COMB
                        (AP_TERM or_tm 
                                (MK_FORALL x (TRANS (AP_TERM not_tm bth) th_n)), 
                            MK_EXISTS x 
                                (MK_EXISTS y 
                                    (MK_COMB
                                        (AP_TERM and_tm (TRANS bth th_p), 
                                        MK_COMB
                                            (AP_TERM and_tm (TRANS bth' th_p'), 
                                                eth_n)))))
                return! TRANS th1' th2'
            | Comb(Const("~", _), t) -> 
                let th1 = NNF_CONV cf baseconvs t
                return! TRANS (INST [t, p_tm] pth_not_not) th1
            | _ -> 
                let! tm' = mk_neg tm
                return! 
                    base1 tm'
                    |> Choice.bindError (fun _ -> REFL tm')
        }
    NNF_CONV

(* ------------------------------------------------------------------------- *)
(* Some common special cases.                                                *)
(* ------------------------------------------------------------------------- *)

/// Convert a term to negation normal form.
let NNF_CONV = 
    (GEN_NNF_CONV false (ALL_CONV, fun t -> REFL t, Choice.bind REFL (mk_neg t)) : conv)

/// Convert a term to negation normal form.
let NNFC_CONV = 
    (GEN_NNF_CONV true (ALL_CONV, fun t -> REFL t, Choice.bind REFL (mk_neg t)) : conv)

(* ------------------------------------------------------------------------- *)
(* Skolemize a term already in NNF (doesn't matter if it's not prenex).      *)
(* ------------------------------------------------------------------------- *)

/// Completely Skolemize a term already in negation normal form.
let SKOLEM_CONV = 
    GEN_REWRITE_CONV TOP_DEPTH_CONV 
        [EXISTS_OR_THM; LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM; 
         FORALL_AND_THM; LEFT_FORALL_OR_THM; RIGHT_FORALL_OR_THM; FORALL_SIMP; 
         EXISTS_SIMP]
    |> THENC <| GEN_REWRITE_CONV REDEPTH_CONV 
                   [RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM; OR_EXISTS_THM; 
                    RIGHT_OR_EXISTS_THM; LEFT_OR_EXISTS_THM; SKOLEM_THM]

(* ------------------------------------------------------------------------- *)
(* Put a term already in NNF into prenex form.                               *)
(* ------------------------------------------------------------------------- *)

/// Puts a term already in NNF into prenex form.
let (PRENEX_CONV : conv) = 
    GEN_REWRITE_CONV REDEPTH_CONV 
        [AND_FORALL_THM; LEFT_AND_FORALL_THM; RIGHT_AND_FORALL_THM; 
         LEFT_OR_FORALL_THM; RIGHT_OR_FORALL_THM; OR_EXISTS_THM; 
         LEFT_OR_EXISTS_THM; RIGHT_OR_EXISTS_THM; LEFT_AND_EXISTS_THM; 
         RIGHT_AND_EXISTS_THM]

(* ------------------------------------------------------------------------- *)
(* Weak and normal DNF conversion. The "weak" form gives a disjunction of    *)
(* conjunctions, but has no particular associativity at either level and     *)
(* may contain duplicates. The regular forms give canonical right-associate  *)
(* lists without duplicates, but do not remove subsumed disjuncts.           *)
(*                                                                           *)
(* In both cases the input term is supposed to be in NNF already. We do go   *)
(* inside quantifiers and transform their body, but don't move them.         *)
(* ------------------------------------------------------------------------- *)

// WEAK_DNF_CONV: Converts a term already in negation normal form into disjunctive normal form.
// DNF_CONV: Converts a term already in negation normal form into disjunctive normal form.
let WEAK_DNF_CONV, DNF_CONV = 
    let pth1 = TAUT(parse_term @"a /\ (b \/ c) <=> a /\ b \/ a /\ c")
    let pth2 = TAUT(parse_term @"(a \/ b) /\ c <=> a /\ c \/ b /\ c")
    let a_tm = (parse_term @"a:bool")
    let b_tm = (parse_term @"b:bool")
    let c_tm = (parse_term @"c:bool")

    let rec distribute tm = 
        choice {
            match tm with
            | Comb(Comb(Const("/\\", _), a), Comb(Comb(Const("\\/", _), b), c)) -> 
                let th = INST [a, a_tm; b, b_tm; c, c_tm] pth1
                let! tm1 = Choice.bind (rand << concl) th
                return! TRANS th (BINOP_CONV distribute tm1)
            | Comb(Comb(Const("/\\", _), Comb(Comb(Const("\\/", _), a), b)), c) -> 
                let th = INST [a, a_tm; b, b_tm; c, c_tm] pth2
                let! tm1 = Choice.bind (rand << concl) th
                return! TRANS th (BINOP_CONV distribute tm1)
            | _ -> 
                return! REFL tm
        }

    let strengthen = DEPTH_BINOP_CONV (parse_term @"(\/)") CONJ_CANON_CONV
                     |> THENC <| DISJ_CANON_CONV

    let rec weakdnf tm = 
        choice {
            match tm with
            | Comb(Const("!", _), Abs(_, _)) | Comb(Const("?", _), Abs(_, _)) -> 
                return! BINDER_CONV weakdnf tm
            | Comb(Comb(Const("\\/", _), _), _) -> 
                return! BINOP_CONV weakdnf tm
            | Comb(Comb(Const("/\\", _) as op, l), r) -> 
                let th = MK_COMB(AP_TERM op (weakdnf l), weakdnf r)
                let th1 = (Choice.bind distribute << Choice.bind rand << Choice.map concl) th
                return! TRANS th th1
            | _ -> 
                return! REFL tm
        }

    and substrongdnf tm = 
        choice {
            match tm with
            | Comb(Const("!", _), Abs(_, _)) | Comb(Const("?", _), Abs(_, _)) -> 
                return! BINDER_CONV strongdnf tm
            | Comb(Comb(Const("\\/", _), _), _) -> 
                return! BINOP_CONV substrongdnf tm
            | Comb(Comb(Const("/\\", _) as op, l), r) -> 
                let th = MK_COMB(AP_TERM op (substrongdnf l), substrongdnf r)
                return! TRANS th (distribute(Choice.get <| rand(concl <| Choice.get th)))
            | _ -> 
                return! REFL tm
        }

    and strongdnf tm = 
        choice {
            let th = substrongdnf tm
            let! tm1 = Choice.bind (rand << concl) th
            return! TRANS th (strengthen tm1)
        }

    weakdnf, strongdnf

(* ------------------------------------------------------------------------- *)
(* Likewise for CNF.                                                         *)
(* ------------------------------------------------------------------------- *)

// WEAK_CNF_CONV: Converts a term already in negation normal form into conjunctive normal form.
// CNF_CONV: Converts a term already in negation normal form into conjunctive normal form.
let WEAK_CNF_CONV, CNF_CONV = 
    let pth1 = TAUT(parse_term @"a \/ (b /\ c) <=> (a \/ b) /\ (a \/ c)")
    let pth2 = TAUT(parse_term @"(a /\ b) \/ c <=> (a \/ c) /\ (b \/ c)")
    let a_tm = (parse_term @"a:bool")
    let b_tm = (parse_term @"b:bool")
    let c_tm = (parse_term @"c:bool")

    let rec distribute tm = 
        choice {
            match tm with
            | Comb(Comb(Const("\\/", _), a), Comb(Comb(Const("/\\", _), b), c)) -> 
                let th = INST [a, a_tm; b, b_tm; c, c_tm] pth1
                let! tm1 = Choice.bind (rand << concl) th
                return! TRANS th (BINOP_CONV distribute tm1)
            | Comb(Comb(Const("\\/", _), Comb(Comb(Const("/\\", _), a), b)), c) -> 
                let th = INST [a, a_tm; b, b_tm; c, c_tm] pth2
                let! tm1 = Choice.bind (rand << concl) th
                return! TRANS th (BINOP_CONV distribute tm1)
            | _ -> 
                return! REFL tm
        }

    let strengthen = DEPTH_BINOP_CONV (parse_term @"(/\)") DISJ_CANON_CONV
                     |> THENC <| CONJ_CANON_CONV

    let rec weakcnf tm = 
        choice {
            match tm with
            | Comb(Const("!", _), Abs(_, _)) | Comb(Const("?", _), Abs(_, _)) -> 
                return! BINDER_CONV weakcnf tm
            | Comb(Comb(Const("/\\", _), _), _) -> 
                return! BINOP_CONV weakcnf tm
            | Comb(Comb(Const("\\/", _) as op, l), r) -> 
                let th = MK_COMB(AP_TERM op (weakcnf l), weakcnf r)
                let! tm1 = Choice.bind (rand << concl) th
                return! TRANS th (distribute tm1)
            | _ -> 
                return! REFL tm
        }

    and substrongcnf tm = 
        choice {
            match tm with
            | Comb(Const("!", _), Abs(_, _)) | Comb(Const("?", _), Abs(_, _)) -> 
                return! BINDER_CONV strongcnf tm
            | Comb(Comb(Const("/\\", _), _), _) -> 
                return! BINOP_CONV substrongcnf tm
            | Comb(Comb(Const("\\/", _) as op, l), r) -> 
                let th = MK_COMB(AP_TERM op (substrongcnf l), substrongcnf r)
                let! tm1 = Choice.bind (rand << concl) th
                return! TRANS th (distribute tm1)
            | _ -> 
                return! REFL tm
        }


    and strongcnf tm = 
        choice {
            let th = substrongcnf tm
            let! tm1 = Choice.bind (rand << concl) th
            return! TRANS th (strengthen tm1)
        }

    weakcnf, strongcnf

(* ------------------------------------------------------------------------- *)
(* Simply right-associate w.r.t. a binary operator.                          *)
(* ------------------------------------------------------------------------- *)

/// Right-associates a term with respect to an associative binary operator.
let ASSOC_CONV th : conv = 
    let v =
        choice {
            let th' = SYM(SPEC_ALL th)
            let! tm1 = Choice.bind (rhs << concl) th'
            let! opx, yopz = dest_comb tm1
            let! op, x = dest_comb opx
            let! y = lhand yopz
            let! z = rand yopz
            return (th', op, x, y, z)
        }
    let rec distrib tm = 
        choice {
            let! (th', op, x, y, z) = v
            match tm with
            | Comb(Comb(op', Comb(Comb(op'', p), q)), r) when op' = op && op'' = op -> 
                let th1 =  INST [p, x; q, y; r, z] th'
                let! tm1 = Choice.bind (rand << concl) th1
                let! l, r' = dest_comb tm1
                let th2 = AP_TERM l (distrib r')
                let! tm2 = Choice.bind (rand << concl) th
                let th3 = distrib tm2
                return! TRANS th1 (TRANS th2 th3)
            | _ -> 
                return! REFL tm
        }
    let rec assoc tm = 
        choice {
            let! (_, op, _, _, _) = v
            match tm with
            | Comb(Comb(op', p) as l, q) when op' = op -> 
                let th = AP_TERM l (assoc q)
                let! tm1 = Choice.bind (rand << concl) th
                return! TRANS th (distrib tm1)
            | _ -> 
                return! REFL tm
        }
    assoc

(* ------------------------------------------------------------------------- *)
(* Eliminate select terms from a goal.                                       *)
(* ------------------------------------------------------------------------- *)

/// Eliminate select terms from a goal.
let SELECT_ELIM_TAC = 
    let SELECT_ELIM_CONV = 
        let SELECT_ELIM_THM = 
            let pth = 
                prove
                    ((parse_term @"(P:A->bool)((@) P) <=> (?) P"), 
                     REWRITE_TAC [EXISTS_THM]
                     |> THEN <| BETA_TAC
                     |> THEN <| REFL_TAC)
            let ptm = (parse_term @"P:A->bool")
            fun tm -> 
                choice {
                    let! stm, atm = dest_comb tm
                    let! (s, _) = dest_const stm
                    if is_const stm && s = "@" then
                        let! ty1 = Choice.bind type_of (bndvar atm)
                        return! CONV_RULE (LAND_CONV BETA_CONV) (PINST [ty1, aty] [atm, ptm] pth)
                    else 
                        return! Choice.failwith "SELECT_ELIM_THM: not a select-term"
                }
        fun tm -> 
            choice {
                let! tms = find_terms is_select tm
                return! PURE_REWRITE_CONV (map SELECT_ELIM_THM tms) tm
            }

    let SELECT_ELIM_ICONV = 
        let SELECT_AX_THM = 
            let pth = ISPEC (parse_term @"P:A->bool") SELECT_AX
            let ptm = (parse_term @"P:A->bool")
            fun tm -> 
                choice {
                    let! stm, atm = dest_comb tm
                    let! (s, _) = dest_const stm
                    if is_const stm && s = "@" then 
                        let fvs = frees atm
                        let! ty1 = Choice.bind type_of (bndvar atm)
                        let th1 = PINST [ty1, aty] [atm, ptm] pth
                        let th2 = CONV_RULE (BINDER_CONV(BINOP_CONV BETA_CONV)) th1
                        return! GENL fvs th2
                    else 
                        return! Choice.failwith "SELECT_AX_THM: not a select-term"
                }

        let SELECT_ELIM_ICONV tm = 
            choice {
                let! t = find_term is_select tm
                let th1 = SELECT_AX_THM t
                let! tm1 = Choice.map concl th1
                let! itm = mk_imp(tm1, tm)
                let th2 = DISCH_ALL(MP (ASSUME itm) th1)
                let fvs = frees t
                let! ty1 = type_of t
                // NOTE: revise due to massivie changes
                let! fty = Choice.List.fold (fun acc x -> type_of x |> Choice.bind (fun y -> mk_fun_ty y acc)) ty1 fvs
                let fn = genvar fty
                let! atm = list_mk_abs(fvs, t)
                let! rawdef = mk_eq(fn, atm)
                let def = GENL fvs (SYM(RIGHT_BETAS fvs (ASSUME rawdef)))
                let! tm2 = Choice.bind (lhand << concl) th2
                let th3 = PURE_REWRITE_CONV [def] tm2
                let! tm3 = Choice.bind (rand << concl) th3
                let! gtm = mk_forall(fn, tm3)
                let th4 = EQ_MP (SYM th3) (SPEC fn (ASSUME gtm))
                let th5 = IMP_TRANS (DISCH gtm th4) th2
                return! MP (INST [atm, fn] (DISCH rawdef th5)) (REFL atm)
            }

        let rec SELECT_ELIMS_ICONV tm = 
            choice { 
                let th = SELECT_ELIM_ICONV tm
                let! tm' = Choice.bind (lhand << concl) th
                return! IMP_TRANS (SELECT_ELIMS_ICONV tm') th
            }
            |> Choice.bindError (fun e -> DISCH tm (ASSUME tm))

        SELECT_ELIMS_ICONV

    CONV_TAC SELECT_ELIM_CONV
    |> THEN <| W (MATCH_MP_TAC << SELECT_ELIM_ICONV << snd)

(* ------------------------------------------------------------------------- *)
(* Eliminate all lambda-terms except those part of quantifiers.              *)
(* ------------------------------------------------------------------------- *)

/// Eliminate lambda-terms that are not part of quantifiers from Boolean term.
let LAMBDA_ELIM_CONV = 
    let HALF_MK_ABS_CONV = 
        let pth = 
            prove
                ((parse_term @"(s = \x. t x) <=> (!x. s x = t x)"), 
                 REWRITE_TAC [FUN_EQ_THM])
        let rec conv vs tm = 
            if vs = [] then REFL tm
            else (GEN_REWRITE_CONV I [pth]
                  |> THENC <| BINDER_CONV(conv(tl vs))) tm
        conv

    let rec find_lambda tm = 
        choice {
            if is_abs tm then 
                return tm
            elif is_var tm || is_const tm then 
                return! Choice.failwith "find_lambda"
            elif is_abs tm then 
                return tm
            elif is_forall tm || is_exists tm || is_uexists tm then
                let! tm1 = Choice.bind body (rand tm) 
                return! find_lambda tm1
            else 
                let! l, r = dest_comb tm
                return! 
                    find_lambda l
                    |> Choice.bindError (fun _ -> find_lambda r)
        }

    let rec ELIM_LAMBDA conv tm = 
        conv tm        
        |> Choice.bindError (fun _ ->
            if is_abs tm then 
                ABS_CONV (ELIM_LAMBDA conv) tm
            elif is_var tm || is_const tm then REFL tm
            elif is_forall tm || is_exists tm || is_uexists tm then 
                BINDER_CONV (ELIM_LAMBDA conv) tm
            else COMB_CONV (ELIM_LAMBDA conv) tm)

    let APPLY_PTH = 
        let pth = 
            prove
                ((parse_term @"(!a. (a = c) ==> (P = Q a)) ==> (P <=> !a. (a = c) ==> Q a)"), 
                 SIMP_TAC [LEFT_FORALL_IMP_THM; EXISTS_REFL])
        MATCH_MP pth

    let LAMB1_CONV tm = 
        choice {
            let! atm = find_lambda tm
            let! v, bod = dest_abs atm
            let vs = frees atm
            let vs' = vs @ [v]
            let! aatm = list_mk_abs(vs, atm)
            let! ty1 = type_of aatm
            let f = genvar ty1
            let! eq = mk_eq(f, aatm)
            let th1 = SYM(RIGHT_BETAS vs (ASSUME eq))
            let th2 = ELIM_LAMBDA (GEN_REWRITE_CONV I [th1]) tm
            let th3 = APPLY_PTH(GEN f (DISCH_ALL th2))
            return! CONV_RULE (RAND_CONV(BINDER_CONV(LAND_CONV(HALF_MK_ABS_CONV vs')))) th3
        }

    let rec conv tm =          
        (LAMB1_CONV
        |> THENC <| conv) tm
        |> Choice.bindError (fun _ -> REFL tm)

    conv

(* ------------------------------------------------------------------------- *)
(* Eliminate conditionals; CONDS_ELIM_CONV aims for disjunctive splitting,   *)
(* for refutation procedures, and CONDS_CELIM_CONV for conjunctive.          *)
(* Both switch modes "sensibly" when going through a quantifier.             *)
(* ------------------------------------------------------------------------- *)

// CONDS_ELIM_CONV: Remove all conditional expressions from a Boolean formula.
// CONDS_CELIM_CONV: Remove all conditional expressions from a Boolean formula.
let CONDS_ELIM_CONV, CONDS_CELIM_CONV = 
    let th_cond = 
      prove ((parse_term @"((b <=> F) ==> x = x0) /\ ((b <=> T) ==> x = x1)
      ==> x = (b /\ x1 \/ ~b /\ x0)"),
        BOOL_CASES_TAC (parse_term @"b:bool")
        |> THEN <| ASM_REWRITE_TAC [])
    let th_cond' = 
      prove((parse_term @"((b <=> F) ==> x = x0) /\ ((b <=> T) ==> x = x1)
      ==> x = ((~b \/ x1) /\ (b \/ x0))"),
        BOOL_CASES_TAC(parse_term @"b:bool")
        |> THEN <| ASM_REWRITE_TAC [])
    let propsimps = basic_net()
    let false_tm = (parse_term @"F")
    let true_tm = (parse_term @"T")
    let match_th = MATCH_MP th_cond
    let match_th' = MATCH_MP th_cond'
    let propsimp_conv = DEPTH_CONV(REWRITES_CONV propsimps)

    let proptsimp_conv = 
        let cnv = TRY_CONV(REWRITES_CONV propsimps)
        BINOP_CONV cnv
        |> THENC <| cnv

    let rec find_conditional fvs tm = 
        choice {
            match tm with
            | Comb(s, t) -> 
                // NOTE: Choice.get is safe to use here
                if is_cond tm && intersect (frees(Choice.get <| lhand s)) fvs = [] then 
                    return tm
                else 
                    return!
                        find_conditional fvs s
                        |> Choice.bindError (fun _ -> find_conditional fvs t)
            | Abs(x, t) -> 
                return! find_conditional (x :: fvs) t
            | _ -> 
                return! Choice.failwith "find_conditional"
        }

    let rec CONDS_ELIM_CONV dfl tm = 
        choice { 
            let! t = find_conditional [] tm
            let! p = Choice.bind lhand (rator t)
            let th_new = 
                choice {
                    if p = false_tm || p = true_tm then 
                        return! propsimp_conv tm
                    else 
                        let! asm_0 = mk_eq(p, false_tm)
                        let! asm_1 = mk_eq(p, true_tm)
                        let! simp_0 = net_of_thm false (ASSUME asm_0) propsimps
                        let! simp_1 = net_of_thm false (ASSUME asm_1) propsimps
                        let th_0 = DISCH asm_0 (DEPTH_CONV (REWRITES_CONV simp_0) tm)
                        let th_1 = DISCH asm_1 (DEPTH_CONV (REWRITES_CONV simp_1) tm)
                        let th_2 = CONJ th_0 th_1
                        let th_3 = if dfl then match_th th_2 else match_th' th_2
                        return! TRANS th_3 (proptsimp_conv(Choice.get <| rand(concl <| Choice.get th_3)))
                }
            return! CONV_RULE (RAND_CONV(CONDS_ELIM_CONV dfl)) th_new
        }
        |> Choice.bindError (fun _ ->
            if is_neg tm then 
                RAND_CONV (CONDS_ELIM_CONV(not dfl)) tm
            elif is_conj tm || is_disj tm then 
                BINOP_CONV (CONDS_ELIM_CONV dfl) tm
            elif is_imp tm || is_iff tm then 
                COMB2_CONV (RAND_CONV(CONDS_ELIM_CONV(not dfl))) (CONDS_ELIM_CONV dfl) tm
            elif is_forall tm then 
                BINDER_CONV (CONDS_ELIM_CONV false) tm
            elif is_exists tm || is_uexists tm then 
                BINDER_CONV (CONDS_ELIM_CONV true) tm
            else REFL tm)

    CONDS_ELIM_CONV true, CONDS_ELIM_CONV false

(* ------------------------------------------------------------------------- *)
(* Fix up all head arities to be consistent, in "first order logic" style.   *)
(* Applied to the assumptions (not conclusion) in a goal.                    *)
(* ------------------------------------------------------------------------- *)

/// Fix up function arities for first-order proof search.
let (ASM_FOL_TAC : tactic) = 
    let rec get_heads lconsts tm (cheads, vheads as sofar) = 
        choice { 
            let! v, bod = dest_forall tm
            return! get_heads (subtract lconsts [v]) bod sofar
        }
        |> Choice.bindError (fun _ ->
            choice { 
                let! l, r = 
                    dest_conj tm
                    |> Choice.bindError (fun _ -> dest_disj tm)

                let! right = get_heads lconsts r sofar
                return! get_heads lconsts l right
            }
            |> Choice.bindError (fun _ ->
                choice { 
                    let! tm' = dest_neg tm
                    return! get_heads lconsts tm' sofar
                }
                |> Choice.bindError (fun _ ->
                    let hop, args = strip_comb tm
                    let len = length args
                    let newheads = 
                        if is_const hop || mem hop lconsts then 
                            (insert (hop, len) cheads, vheads)
                        elif len > 0 then 
                            (cheads, insert (hop, len) vheads)
                        else sofar
                    Choice.List.fold (fun acc x -> get_heads lconsts x acc) newheads args)))

    let get_thm_heads th sofar = 
        choice {
            let! tms1 = Choice.map hyp th
            let! tm1 = Choice.map concl th
            return! get_heads (freesl tms1) tm1 sofar
        }

    let APP_CONV = 
        let th = 
            prove((parse_term @"!(f:A->B) x. f x = I f x"), REWRITE_TAC [I_THM])
        REWR_CONV th

    let rec APP_N_CONV n tm = 
        if n = 1 then APP_CONV tm
        else (RATOR_CONV(APP_N_CONV(n - 1))
              |> THENC <| APP_CONV) tm

    let rec FOL_CONV hddata tm = 
        choice {
            if is_forall tm then 
                return! BINDER_CONV (FOL_CONV hddata) tm
            elif is_conj tm || is_disj tm then 
                return! BINOP_CONV (FOL_CONV hddata) tm
            else 
                let op, args = strip_comb tm
                let th = rev_itlist (C(curry MK_COMB)) (map (FOL_CONV hddata) args) (REFL op)
                let! tm' = Choice.bind (rand << concl) th
                let n = 
                    // OPTIMIZE : Replace the entire 'match' statement below with:
                    //assoc op hddata
                    //|> Option.map (fun x -> length args - x)
                    //|> Option.fill 0
                    match assoc op hddata with
                    | None -> 0
                    | Some x -> length args - x
                if n = 0 then 
                    return! th
                else 
                    return! TRANS th (APP_N_CONV n tm')
        }

    let GEN_FOL_CONV(cheads, vheads) = 
        let hddata = 
            if vheads = [] then 
                let hops = setify(map fst cheads)
                let getmin h = 
                    let ns = mapfilter (fun (k, n) -> 
                                if k = h then Some n else None) cheads
                    if length ns < 2 then 
                        Choice.fail()
                    else 
                        Choice.result (h, end_itlist min ns)

                mapfilter (Choice.toOption << getmin) hops
            else 
                map (fun t -> 
                    // It's safe to use Choice.get here
                    if is_const t && fst(Choice.get <| dest_const t) = "=" then t, 2
                    else t, 0) (setify(map fst (vheads @ cheads)))
        FOL_CONV hddata

    fun (asl, w as gl) -> 
        choice {
            let! headsp = Choice.List.fold (fun acc (_, th) -> get_thm_heads th acc) ([], []) asl
            return! RULE_ASSUM_TAC (CONV_RULE(GEN_FOL_CONV headsp)) gl
        }

(* ------------------------------------------------------------------------- *)
(* Depth conversion to apply at "atomic" formulas in "first-order" term.     *)
(* ------------------------------------------------------------------------- *)

/// Applies a conversion to the 'atomic subformulas' of a formula.
let rec PROP_ATOM_CONV conv tm = 
    match tm with
    | Comb((Const("!", _) | Const("?", _) | Const("?!", _)), Abs(_, _)) -> 
        BINDER_CONV (PROP_ATOM_CONV conv) tm
    | Comb(Comb((Const("/\\", _) | Const("\\/", _) | Const("==>", _) | (Const("=", Tyapp("fun", [Tyapp("bool", []); _])))), _), _) -> 
        BINOP_CONV (PROP_ATOM_CONV conv) tm
    | Comb(Const("~", _), _) -> 
        RAND_CONV (PROP_ATOM_CONV conv) tm
    | _ -> 
        TRY_CONV conv tm
