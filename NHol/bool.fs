﻿(*

Copyright 1998 University of Cambridge
Copyright 1998-2007 John Harrison
Copyright 2013 Jack Pappas, Anh-Dung Phan

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

/// Boolean theory including (intuitionistic) defs of logical connectives.
module NHol.bool

open FSharp.Compatibility.OCaml

open NHol
open lib
open fusion
open basics
open nets
open printer
open preterm
open parser
open equal

(* ------------------------------------------------------------------------- *)
(* Set up parse status of basic and derived logical constants.               *)
(* ------------------------------------------------------------------------- *)

parse_as_prefix "~"
parse_as_binder "\\"
parse_as_binder "!"
parse_as_binder "?"
parse_as_binder "?!"
parse_as_infix("==>", (4, "right"))
parse_as_infix("\\/", (6, "right"))
parse_as_infix("/\\", (8, "right"))

(* ------------------------------------------------------------------------- *)
(* Set up more orthodox notation for equations and equivalence.              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("<=>", (2, "right"))
override_interface("<=>", parse_term "(=):bool->bool->bool")
parse_as_infix("=", (12, "right"))

(* ------------------------------------------------------------------------- *)
(* Special syntax for Boolean equations (IFF).                               *)
(* ------------------------------------------------------------------------- *)

let is_iff tm = 
    match tm with
    | Comb(Comb(Const("=", Tyapp("fun", [Tyapp("bool", []); _])), l), r) -> true
    | _ -> false

let dest_iff tm = 
    match tm with
    | Comb(Comb(Const("=", Tyapp("fun", [Tyapp("bool", []); _])), l), r) -> (l, r)
    | _ -> failwith "dest_iff"

let mk_iff = 
    let eq_tm = parse_term "(<=>)"
    fun (l, r) -> mk_comb(mk_comb(eq_tm, l), r)

(* ------------------------------------------------------------------------- *)
(* Rule allowing easy instantiation of polymorphic proformas.                *)
(* ------------------------------------------------------------------------- *)

let PINST tyin tmin = 
    let iterm_fn = INST(map (I ||>> (inst tyin)) tmin)
    let itype_fn = INST_TYPE tyin
    fun th -> 
        try 
            iterm_fn(itype_fn th)
        with
        | Failure _ -> failwith "PINST"

(* ------------------------------------------------------------------------- *)
(* Useful derived deductive rule.                                            *)
(* ------------------------------------------------------------------------- *)

let PROVE_HYP ath bth = 
    if exists (aconv(concl ath)) (hyp bth) then EQ_MP (DEDUCT_ANTISYM_RULE ath bth) ath
    else bth

(* ------------------------------------------------------------------------- *)
(* Rules for T                                                               *)
(* ------------------------------------------------------------------------- *)

let T_DEF = new_basic_definition <| parse_term @"T = ((\p:bool. p) = (\p:bool. p))"
let TRUTH = EQ_MP (SYM T_DEF) (REFL(parse_term @"\p:bool. p"))

let EQT_ELIM th = 
    try 
        EQ_MP (SYM th) TRUTH
    with
    | Failure _ -> failwith "EQT_ELIM"

let EQT_INTRO = 
    let t = parse_term "t:bool"
    let pth = 
        let th1 = DEDUCT_ANTISYM_RULE (ASSUME t) TRUTH
        let th2 = EQT_ELIM(ASSUME(concl th1))
        DEDUCT_ANTISYM_RULE th2 th1
    fun th -> EQ_MP (INST [concl th, t] pth) th

(* ------------------------------------------------------------------------- *)
(* Rules for /\                                                              *)
(* ------------------------------------------------------------------------- *)

let AND_DEF = new_basic_definition <| parse_term @"(/\) = \p q. (\f:bool->bool->bool. f p q) = (\f. f T T)"
let mk_conj = mk_binary "/\\"
let list_mk_conj = end_itlist(curry mk_conj)

let CONJ = 
    let f = parse_term "f:bool->bool->bool"
    let p = parse_term "p:bool"
    let q = parse_term "q:bool"
    let pth() = 
        let pth = ASSUME p
        let qth = ASSUME q
        let th1 = MK_COMB(AP_TERM f (EQT_INTRO pth), EQT_INTRO qth)
        let th2 = ABS f th1
        let th3 = BETA_RULE(AP_THM (AP_THM AND_DEF p) q)
        EQ_MP (SYM th3) th2
    fun th1 th2 -> 
        let th = 
            INST [concl th1, p;
                  concl th2, q] <| pth()
        PROVE_HYP th2 (PROVE_HYP th1 th)

let CONJUNCT1 = 
    let P = parse_term "P:bool"
    let Q = parse_term "Q:bool"
    let pth = 
        let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM AND_DEF <| parse_term "P:bool")
        let th2 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th1 <| parse_term "Q:bool")
        let th3 = EQ_MP th2 (ASSUME <| parse_term @"P /\ Q")
        EQT_ELIM(BETA_RULE(AP_THM th3 <| parse_term @"\(p:bool) (q:bool). p"))
    fun th -> 
        try 
            let l, r = dest_conj(concl th)
            PROVE_HYP th (INST [l, P;
                                r, Q] pth)
        with
        | Failure _ -> failwith "CONJUNCT1"

let CONJUNCT2 = 
    let P = parse_term "P:bool"
    let Q = parse_term "Q:bool"
    let pth = 
        let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM AND_DEF <| parse_term "P:bool")
        let th2 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th1 <| parse_term "Q:bool")
        let th3 = EQ_MP th2 (ASSUME <| parse_term @"P /\ Q")
        EQT_ELIM(BETA_RULE(AP_THM th3 <| parse_term @"\(p:bool) (q:bool). q"))
    fun th -> 
        try 
            let l, r = dest_conj(concl th)
            PROVE_HYP th (INST [l, P;
                                r, Q] pth)
        with
        | Failure _ -> failwith "CONJUNCT2"

let CONJ_PAIR th = 
    try 
        CONJUNCT1 th, CONJUNCT2 th
    with
    | Failure _ -> failwith "CONJ_PAIR: Not a conjunction"

let CONJUNCTS = striplist CONJ_PAIR

(* ------------------------------------------------------------------------- *)
(* Rules for ==>                                                             *)
(* ------------------------------------------------------------------------- *)

let IMP_DEF = new_basic_definition <| parse_term @"(==>) = \p q. p /\ q <=> p"
let mk_imp = mk_binary "==>"

let MP = 
    let p = parse_term "p:bool"
    let q = parse_term "q:bool"
    let pth() = 
        let th1 = BETA_RULE(AP_THM (AP_THM IMP_DEF p) q)
        let th2 = EQ_MP th1 (ASSUME <| parse_term "p ==> q")
        CONJUNCT2(EQ_MP (SYM th2) (ASSUME <| parse_term "p:bool"))
    fun ith th -> 
        let ant, con = dest_imp(concl ith)
        if aconv ant (concl th) then 
            PROVE_HYP th (PROVE_HYP ith (INST [ant, p;
                                               con, q] <| pth()))
        else failwith "MP: theorems do not agree"

let DISCH = 
    let p = parse_term "p:bool"
    let q = parse_term "q:bool"
    let pth() = SYM(BETA_RULE(AP_THM (AP_THM IMP_DEF p) q))
    fun a th -> 
        let th1 = CONJ (ASSUME a) th
        let th2 = CONJUNCT1(ASSUME(concl th1))
        let th3 = DEDUCT_ANTISYM_RULE th1 th2
        let th4 = 
            INST [a, p;
                  concl th, q] <| pth()
        EQ_MP th4 th3

let rec DISCH_ALL th = 
    try 
        DISCH_ALL(DISCH (hd(hyp th)) th)
    with
    | Failure _ -> th

let UNDISCH th = 
    try 
        MP th (ASSUME(rand(rator(concl th))))
    with
    | Failure _ -> failwith "UNDISCH"

let rec UNDISCH_ALL th = 
    if is_imp(concl th) then UNDISCH_ALL(UNDISCH th)
    else th

let IMP_ANTISYM_RULE th1 th2 = DEDUCT_ANTISYM_RULE (UNDISCH th2) (UNDISCH th1)
let ADD_ASSUM tm th = MP (DISCH tm th) (ASSUME tm)

let EQ_IMP_RULE = 
    let peq = parse_term "p <=> q"
    let p, q = dest_iff peq
    let pth1() = DISCH peq (DISCH p (EQ_MP (ASSUME peq) (ASSUME p)))
    let pth2() = DISCH peq (DISCH q (EQ_MP (SYM(ASSUME peq)) (ASSUME q)))
    fun th -> 
        let l, r = dest_iff(concl th)
        MP (INST [l, p;
                  r, q] <| pth1()) th, MP (INST [l, p;
                                            r, q] <| pth2()) th

let IMP_TRANS = 
    let pq = parse_term "p ==> q"
    let qr = parse_term "q ==> r"
    let p, q = dest_imp pq
    let r = rand qr
    let pth() = itlist DISCH [pq; qr; p] (MP (ASSUME qr) (MP (ASSUME pq) (ASSUME p)))
    fun th1 th2 -> 
        let x, y = dest_imp(concl th1)
        let y', z = dest_imp(concl th2)
        if y <> y' then failwith "IMP_TRANS"
        else 
            MP (MP (INST [x, p;
                          y, q;
                          z, r] <| pth()) th1) th2

(* ------------------------------------------------------------------------- *)
(* Rules for !                                                               *)
(* ------------------------------------------------------------------------- *)

let FORALL_DEF = new_basic_definition <| parse_term @"(!) = \P:A->bool. P = \x. T"
let mk_forall = mk_binder "!"
let list_mk_forall(vs, bod) = itlist (curry mk_forall) vs bod

let SPEC = 
    let P = parse_term "P:A->bool"
    let x = parse_term "x:A"
    let pth() = 
        let th1 = EQ_MP (AP_THM FORALL_DEF <| parse_term "P:A->bool") (ASSUME <| parse_term "(!)(P:A->bool)")
        let th2 = AP_THM(CONV_RULE BETA_CONV th1) <| parse_term "x:A"
        let th3 = CONV_RULE (RAND_CONV BETA_CONV) th2
        DISCH_ALL(EQT_ELIM th3)
    fun tm th -> 
        try 
            let abs = rand(concl th)
            CONV_RULE BETA_CONV (MP (PINST [snd(dest_var(bndvar abs)), aty] [abs, P;
                                                                             tm, x] <| pth()) th)
        with
        | Failure _ -> failwith "SPEC"

let SPECL tms th = 
    try 
        rev_itlist SPEC tms th
    with
    | Failure _ -> failwith "SPECL"

let SPEC_VAR th = 
    let bv = variant (thm_frees th) (bndvar(rand(concl th)))
    bv, SPEC bv th

let rec SPEC_ALL th = 
    if is_forall(concl th) then SPEC_ALL(snd(SPEC_VAR th))
    else th

let ISPEC t th = 
    let x, _ = 
        try 
            dest_forall(concl th)
        with
        | Failure _ -> failwith "ISPEC: input theorem not universally quantified"
    let tyins = 
        try 
            type_match (snd(dest_var x)) (type_of t) []
        with
        | Failure _ -> failwith "ISPEC can't type-instantiate input theorem"
    try 
        SPEC t (INST_TYPE tyins th)
    with
    | Failure _ -> failwith "ISPEC: type variable(s) free in assumptions"

let ISPECL tms th = 
    try 
        if tms = [] then th
        else 
            let avs = fst(chop_list (length tms) (fst(strip_forall(concl th))))
            let tyins = itlist2 type_match (map (snd << dest_var) avs) (map type_of tms) []
            SPECL tms (INST_TYPE tyins th)
    with
    | Failure _ -> failwith "ISPECL"

let GEN = 
    let pth() = SYM(CONV_RULE (RAND_CONV BETA_CONV) (AP_THM FORALL_DEF <| parse_term "P:A->bool"))
    fun x -> 
        let qth = INST_TYPE [snd(dest_var x), aty] <| pth()
        let ptm = rand(rand(concl qth))
        fun th -> 
            let th' = ABS x (EQT_INTRO th)
            let phi = lhand(concl th')
            let rth = INST [phi, ptm] qth
            EQ_MP rth th'

let GENL = itlist GEN

let GEN_ALL th = 
    let asl, c = dest_thm th
    let vars = subtract (frees c) (freesl asl)
    GENL vars th

(* ------------------------------------------------------------------------- *)
(* Rules for ?                                                               *)
(* ------------------------------------------------------------------------- *)

let EXISTS_DEF = new_basic_definition <| parse_term @"(?) = \P:A->bool. !q. (!x. P x ==> q) ==> q"
let mk_exists = mk_binder "?"
let list_mk_exists(vs, bod) = itlist (curry mk_exists) vs bod

let EXISTS = 
    let P = parse_term "P:A->bool"
    let x = parse_term "x:A"
    let pth() = 
        let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM EXISTS_DEF P)
        let th2 = SPEC (parse_term "x:A") (ASSUME <| parse_term "!x:A. P x ==> Q")
        let th3 = DISCH (parse_term "!x:A. P x ==> Q") (MP th2 (ASSUME <| parse_term "(P:A->bool) x"))
        EQ_MP (SYM th1) (GEN (parse_term "Q:bool") th3)
    fun (etm, stm) th -> 
        try 
            let qf, abs = dest_comb etm
            let bth = BETA_CONV(mk_comb(abs, stm))
            let cth = 
                PINST [type_of stm, aty] [abs, P;
                                          stm, x] <| pth()
            PROVE_HYP (EQ_MP (SYM bth) th) cth
        with
        | Failure _ -> failwith "EXISTS"

let SIMPLE_EXISTS v th = EXISTS (mk_exists(v, concl th), v) th

let CHOOSE = 
    let P = parse_term "P:A->bool"
    let Q = parse_term "Q:bool"
    let pth() = 
        let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM EXISTS_DEF P)
        let th2 = SPEC (parse_term "Q:bool") (UNDISCH(fst(EQ_IMP_RULE th1)))
        DISCH_ALL(DISCH (parse_term "(?) (P:A->bool)") (UNDISCH th2))
    fun (v, th1) th2 -> 
        try 
            let abs = rand(concl th1)
            let bv, bod = dest_abs abs
            let cmb = mk_comb(abs, v)
            let pat = vsubst [v, bv] bod
            let th3 = CONV_RULE BETA_CONV (ASSUME cmb)
            let th4 = GEN v (DISCH cmb (MP (DISCH pat th2) th3))
            let th5 = 
                PINST [snd(dest_var v), aty] [abs, P;
                                              concl th2, Q] <| pth()
            MP (MP th5 th4) th1
        with
        | Failure _ -> failwith "CHOOSE"

let SIMPLE_CHOOSE v th = CHOOSE (v, ASSUME(mk_exists(v, hd(hyp th)))) th

(* ------------------------------------------------------------------------- *)
(* Rules for \/                                                              *)
(* ------------------------------------------------------------------------- *)

let OR_DEF = new_basic_definition <| parse_term @"(\/) = \p q. !r. (p ==> r) ==> (q ==> r) ==> r"
let mk_disj = mk_binary "\\/"
let list_mk_disj = end_itlist(curry mk_disj)

let DISJ1 = 
    let P = parse_term "P:bool"
    let Q = parse_term "Q:bool"
    let pth() = 
        let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM OR_DEF <| parse_term "P:bool")
        let th2 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th1 <| parse_term "Q:bool")
        let th3 = MP (ASSUME <| parse_term "P ==> t") (ASSUME <| parse_term "P:bool")
        let th4 = GEN (parse_term "t:bool") (DISCH (parse_term "P ==> t") (DISCH (parse_term "Q ==> t") th3))
        EQ_MP (SYM th2) th4
    fun th tm -> 
        try 
            PROVE_HYP th (INST [concl th, P;
                                tm, Q] <| pth())
        with
        | Failure _ -> failwith "DISJ1"

let DISJ2 = 
    let P = parse_term "P:bool"
    let Q = parse_term "Q:bool"
    let pth() = 
        let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM OR_DEF <| parse_term "P:bool")
        let th2 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th1 <| parse_term "Q:bool")
        let th3 = MP (ASSUME <| parse_term "Q ==> t") (ASSUME <| parse_term "Q:bool")
        let th4 = GEN (parse_term "t:bool") (DISCH (parse_term "P ==> t") (DISCH (parse_term "Q ==> t") th3))
        EQ_MP (SYM th2) th4
    fun tm th -> 
        try 
            PROVE_HYP th (INST [tm, P;
                                concl th, Q] <| pth())
        with
        | Failure _ -> failwith "DISJ2"

let DISJ_CASES = 
    let P = parse_term "P:bool"
    let Q = parse_term "Q:bool"
    let R = parse_term "R:bool"
    let pth() = 
        let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM OR_DEF <| parse_term "P:bool")
        let th2 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th1 <| parse_term "Q:bool")
        let th3 = SPEC (parse_term "R:bool") (EQ_MP th2 (ASSUME <| parse_term @"P \/ Q"))
        UNDISCH(UNDISCH th3)
    fun th0 th1 th2 -> 
        try 
            let c1 = concl th1
            let c2 = concl th2
            if not(aconv c1 c2) then failwith "DISJ_CASES"
            else 
                let l, r = dest_disj(concl th0)
                let th = 
                    INST [l, P;
                          r, Q;
                          c1, R] <| pth()
                PROVE_HYP (DISCH r th2) (PROVE_HYP (DISCH l th1) (PROVE_HYP th0 th))
        with
        | Failure _ -> failwith "DISJ_CASES"

let SIMPLE_DISJ_CASES th1 th2 = DISJ_CASES (ASSUME(mk_disj(hd(hyp th1), hd(hyp th2)))) th1 th2

(* ------------------------------------------------------------------------- *)
(* Rules for negation and falsity.                                           *)
(* ------------------------------------------------------------------------- *)

let F_DEF = new_basic_definition <| parse_term "F = !p:bool. p"
let NOT_DEF = new_basic_definition <| parse_term @"(~) = \p. p ==> F"

let mk_neg = 
    let neg_tm = parse_term "(~)"
    fun tm -> 
        try 
            mk_comb(neg_tm, tm)
        with
        | Failure _ -> failwith "mk_neg"

let NOT_ELIM = 
    let P = parse_term "P:bool"
    let pth() = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM NOT_DEF P)
    fun th -> 
        try 
            EQ_MP (INST [rand(concl th), P] <| pth()) th
        with
        | Failure _ -> failwith "NOT_ELIM"

let NOT_INTRO = 
    let P = parse_term "P:bool"
    let pth() = SYM(CONV_RULE (RAND_CONV BETA_CONV) (AP_THM NOT_DEF P))
    fun th -> 
        try 
            EQ_MP (INST [rand(rator(concl th)), P] <| pth()) th
        with
        | Failure _ -> failwith "NOT_INTRO"

let EQF_INTRO = 
    let P = parse_term "P:bool"
    let pth() = 
        let th1 = NOT_ELIM(ASSUME <| parse_term "~ P")
        let th2 = DISCH (parse_term "F") (SPEC P (EQ_MP F_DEF (ASSUME <| parse_term "F")))
        DISCH_ALL(IMP_ANTISYM_RULE th1 th2)
    fun th -> 
        try 
            MP (INST [rand(concl th), P] <| pth()) th
        with
        | Failure _ -> failwith "EQF_INTRO"

let EQF_ELIM = 
    let P = parse_term "P:bool"
    let pth() = 
        let th1 = EQ_MP (ASSUME <| parse_term "P = F") (ASSUME <| parse_term "P:bool")
        let th2 = DISCH P (SPEC (parse_term "F") (EQ_MP F_DEF th1))
        DISCH_ALL(NOT_INTRO th2)
    fun th -> 
        try 
            MP (INST [rand(rator(concl th)), P] <| pth()) th
        with
        | Failure _ -> failwith "EQF_ELIM"

let CONTR = 
    let P = parse_term "P:bool"
    let f_tm = parse_term "F"
    let pth() = SPEC P (EQ_MP F_DEF (ASSUME <| parse_term "F"))
    fun tm th -> 
        if concl th <> f_tm then failwith "CONTR"
        else PROVE_HYP th (INST [tm, P] <| pth())

(* ------------------------------------------------------------------------- *)
(* Rules for unique existence.                                               *)
(* ------------------------------------------------------------------------- *)

let EXISTS_UNIQUE_DEF = new_basic_definition <| parse_term @"(?!) = \P:A->bool. ((?) P) /\ (!x y. P x /\ P y ==> x = y)"
let mk_uexists = mk_binder "?!"

let EXISTENCE = 
    let P = parse_term "P:A->bool"
    let pth() = 
        let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM EXISTS_UNIQUE_DEF P)
        let th2 = UNDISCH(fst(EQ_IMP_RULE th1))
        DISCH_ALL(CONJUNCT1 th2)
    fun th -> 
        try 
            let abs = rand(concl th)
            let ty = snd(dest_var(bndvar abs))
            MP (PINST [ty, aty] [abs, P] <| pth()) th
        with
        | Failure _ -> failwith "EXISTENCE"