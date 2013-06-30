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
/// Derived rules for inductive definitions.
module NHol.ind_defs

open FSharp.Compatibility.OCaml
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

(* ------------------------------------------------------------------------- *)
(* Strip off exactly n arguments from combination.                           *)
(* ------------------------------------------------------------------------- *)
let strip_ncomb = 
    let rec strip(n, tm, acc) = 
        if n < 1
        then tm, acc
        else 
            let l, r = dest_comb tm
            strip(n - 1, l, r :: acc)
    fun n tm -> strip(n, tm, [])

(* ------------------------------------------------------------------------- *)
(* Expand lambda-term function definition with its arguments.                *)
(* ------------------------------------------------------------------------- *)
let RIGHT_BETAS = 
    rev_itlist(fun a -> CONV_RULE(RAND_CONV BETA_CONV) << C AP_THM a)

(* ------------------------------------------------------------------------- *)
(*      A, x = t |- P[x]                                                     *)
(*     ------------------ EXISTS_EQUATION                                    *)
(*        A |- ?x. P[x]                                                      *)
(* ------------------------------------------------------------------------- *)
let EXISTS_EQUATION = 
    let pth = 
        prove
            ((parse_term "!P t. (!x:A. (x = t) ==> P x) ==> (?) P"), 
             REWRITE_TAC [EXISTS_DEF]
             |> THEN <| BETA_TAC
             |> THEN <| REPEAT STRIP_TAC
             |> THEN <| FIRST_ASSUM MATCH_MP_TAC
             |> THEN <| EXISTS_TAC(parse_term "t:A")
             |> THEN <| FIRST_ASSUM MATCH_MP_TAC
             |> THEN <| REFL_TAC)
    fun tm th -> 
        let l, r = dest_eq tm
        let P = mk_abs(l, concl th)
        let th1 = BETA_CONV(mk_comb(P, l))
        let th2 = ISPECL [P; r] pth
        let th3 = EQ_MP (SYM th1) th
        let th4 = GEN l (DISCH tm th3)
        MP th2 th4

(* ========================================================================= *)
(* Part 1: The main part of the inductive definitions package.               *)
(* This proves that a certain definition yields the requires theorems.       *)
(* ========================================================================= *)
let derive_nonschematic_inductive_relations = 
    let getconcl tm = 
        let bod = repeat (snd << dest_forall) tm
        try 
            snd(dest_imp bod)
        with
        | Failure _ -> bod
    let CONJ_ACI_RULE = AC CONJ_ACI
    let SIMPLE_DISJ_PAIR th = 
        let l, r = dest_disj(hd(hyp th))
        PROVE_HYP (DISJ1 (ASSUME l) r) th, PROVE_HYP (DISJ2 l (ASSUME r)) th
    let HALF_BETA_EXPAND args th = GENL args (RIGHT_BETAS args th)
    let AND_IMPS_CONV tm = 
        let ths = CONJUNCTS(ASSUME tm)
        let avs = fst(strip_forall(concl(hd ths)))
        let thl = map (DISCH tm << UNDISCH << SPEC_ALL) ths
        let th1 = end_itlist SIMPLE_DISJ_CASES thl
        let tm1 = hd(hyp th1)
        let th2 = GENL avs (DISCH tm1 (UNDISCH th1))
        let tm2 = concl th2
        let th3 = DISCH tm2 (UNDISCH(SPEC_ALL(ASSUME tm2)))
        let thts, tht = nsplit SIMPLE_DISJ_PAIR (tl ths) th3
        let proc_fn th = 
            let t = hd(hyp th)
            GENL avs (DISCH t (UNDISCH th))
        let th4 = itlist (CONJ << proc_fn) thts (proc_fn tht)
        IMP_ANTISYM_RULE (DISCH_ALL th2) (DISCH_ALL th4)
    let t_tm = (parse_term "T")
    let calculate_simp_sequence = 
        let rec getequs(avs, plis) = 
            if plis = []
            then []
            else 
                let h :: t = plis
                let r = snd h
                if mem r avs
                then h :: (getequs(avs, filter ((<>) r << snd) t))
                else getequs(avs, t)
        fun avs plis -> 
            let oks = getequs(avs, plis)
            oks, subtract plis oks
    let FORALL_IMPS_CONV tm = 
        let avs, bod = strip_forall tm
        let th1 = DISCH tm (UNDISCH(SPEC_ALL(ASSUME tm)))
        let th2 = itlist SIMPLE_CHOOSE avs th1
        let tm2 = hd(hyp th2)
        let th3 = DISCH tm2 (UNDISCH th2)
        let th4 = ASSUME(concl th3)
        let ant = lhand bod
        let th5 = itlist SIMPLE_EXISTS avs (ASSUME ant)
        let th6 = GENL avs (DISCH ant (MP th4 th5))
        IMP_ANTISYM_RULE (DISCH_ALL th3) (DISCH_ALL th6)
    let canonicalize_clause cls args = 
        let avs, bimp = strip_forall cls
        let ant, con = 
            try 
                dest_imp bimp
            with
            | Failure _ -> t_tm, bimp
        let rel, xargs = strip_comb con
        let plis = zip args xargs
        let yes, no = calculate_simp_sequence avs plis
        let nvs = filter (not << C mem (map snd yes)) avs
        let eth = 
            if is_imp bimp
            then 
                let atm = itlist (curry mk_conj << mk_eq) (yes @ no) ant
                let ths, tth = nsplit CONJ_PAIR plis (ASSUME atm)
                let thl = 
                    map (fun t -> find (fun th -> lhs(concl th) = t) ths) args
                let th0 = MP (SPECL avs (ASSUME cls)) tth
                let th1 = rev_itlist (C(curry MK_COMB)) thl (REFL rel)
                let th2 = EQ_MP (SYM th1) th0
                let th3 = INST yes (DISCH atm th2)
                let tm4 = funpow (length yes) rand (lhand(concl th3))
                let th4 = itlist (CONJ << REFL << fst) yes (ASSUME tm4)
                let th5 = GENL args (GENL nvs (DISCH tm4 (MP th3 th4)))
                let th6 = SPECL nvs (SPECL (map snd plis) (ASSUME(concl th5)))
                let th7 = itlist (CONJ << REFL << snd) no (ASSUME ant)
                let th8 = GENL avs (DISCH ant (MP th6 th7))
                IMP_ANTISYM_RULE (DISCH_ALL th5) (DISCH_ALL th8)
            else 
                let atm = list_mk_conj(map mk_eq (yes @ no))
                let ths = CONJUNCTS(ASSUME atm)
                let thl = 
                    map (fun t -> find (fun th -> lhs(concl th) = t) ths) args
                let th0 = SPECL avs (ASSUME cls)
                let th1 = rev_itlist (C(curry MK_COMB)) thl (REFL rel)
                let th2 = EQ_MP (SYM th1) th0
                let th3 = INST yes (DISCH atm th2)
                let tm4 = funpow (length yes) rand (lhand(concl th3))
                let th4 = itlist (CONJ << REFL << fst) yes (ASSUME tm4)
                let th5 = GENL args (GENL nvs (DISCH tm4 (MP th3 th4)))
                let th6 = SPECL nvs (SPECL (map snd plis) (ASSUME(concl th5)))
                let th7 = end_itlist CONJ (map (REFL << snd) no)
                let th8 = GENL avs (MP th6 th7)
                IMP_ANTISYM_RULE (DISCH_ALL th5) (DISCH_ALL th8)
        let ftm = funpow (length args) (body << rand) (rand(concl eth))
        TRANS eth (itlist MK_FORALL args (FORALL_IMPS_CONV ftm))
    let canonicalize_clauses clauses = 
        let concls = map getconcl clauses
        let uncs = map strip_comb concls
        let rels = itlist (insert << fst) uncs []
        let xargs = map (C assoc uncs) rels
        let closed = list_mk_conj clauses
        let avoids = variables closed
        let flargs = make_args "a" avoids (map type_of (end_itlist (@) xargs))
        let zargs = zip rels (shareout xargs flargs)
        let cargs = map (fun (r, a) -> assoc r zargs) uncs
        let cthms = map2 canonicalize_clause clauses cargs
        let pclauses = map (rand << concl) cthms
        let collectclauses tm = 
            mapfilter (fun t -> 
                    if fst t = tm
                    then snd t
                    else fail()) (zip (map fst uncs) pclauses)
        let clausell = map collectclauses rels
        let cclausel = map list_mk_conj clausell
        let cclauses = list_mk_conj cclausel
        let oclauses = list_mk_conj pclauses
        let eth = CONJ_ACI_RULE(mk_eq(oclauses, cclauses))
        let pth = TRANS (end_itlist MK_CONJ cthms) eth
        TRANS pth (end_itlist MK_CONJ (map AND_IMPS_CONV cclausel))
    let derive_canon_inductive_relations clauses = 
        let closed = list_mk_conj clauses
        let clauses = conjuncts closed
        let vargs, bodies = unzip(map strip_forall clauses)
        let ants, concs = unzip(map dest_imp bodies)
        let rels = map (repeat rator) concs
        let avoids = variables closed
        let rels' = variants avoids rels
        let crels = zip rels' rels
        let prime_fn = subst crels
        let closed' = prime_fn closed
        let mk_def arg con = 
            mk_eq
                (repeat rator con, 
                 list_mk_abs
                     (arg, list_mk_forall(rels', mk_imp(closed', prime_fn con))))
        let deftms = map2 mk_def vargs concs
        let defthms = map2 HALF_BETA_EXPAND vargs (map ASSUME deftms)
        let mk_ind args th = 
            let th1 = fst(EQ_IMP_RULE(SPEC_ALL th))
            let ant = lhand(concl th1)
            let th2 = SPECL rels' (UNDISCH th1)
            GENL args (DISCH ant (UNDISCH th2))
        let indthms = map2 mk_ind vargs defthms
        let indthmr = end_itlist CONJ indthms
        let indthm = GENL rels' (DISCH closed' indthmr)
        let mconcs = 
            map2 (fun a t -> list_mk_forall(a, mk_imp(t, prime_fn t))) vargs 
                ants
        let monotm = mk_imp(concl indthmr, list_mk_conj mconcs)
        let monothm = 
            ASSUME(list_mk_forall(rels, list_mk_forall(rels', monotm)))
        let closthm = ASSUME closed'
        let monothms = 
            CONJUNCTS(MP (SPEC_ALL monothm) (MP (SPECL rels' indthm) closthm))
        let closthms = CONJUNCTS closthm
        let prove_rule mth (cth, dth) = 
            let avs, bod = strip_forall(concl mth)
            let th1 = IMP_TRANS (SPECL avs mth) (SPECL avs cth)
            let th2 = GENL rels' (DISCH closed' (UNDISCH th1))
            let th3 = EQ_MP (SYM(SPECL avs dth)) th2
            GENL avs (DISCH (lhand bod) th3)
        let rulethms = map2 prove_rule monothms (zip closthms defthms)
        let rulethm = end_itlist CONJ rulethms
        let dtms = map2 (curry list_mk_abs) vargs ants
        let double_fn = subst(zip dtms rels)
        let mk_unbetas tm dtm = 
            let avs, bod = strip_forall tm
            let il, r = dest_comb bod
            let i, l = dest_comb il
            let bth = RIGHT_BETAS avs (REFL dtm)
            let munb = AP_THM (AP_TERM i bth) r
            let iunb = AP_TERM (mk_comb(i, double_fn l)) bth
            let junb = AP_TERM (mk_comb(i, r)) bth
            let quantify = itlist MK_FORALL avs
            (quantify munb, (quantify iunb, quantify junb))
        let unths = map2 mk_unbetas clauses dtms
        let irthm = EQ_MP (SYM(end_itlist MK_CONJ (map fst unths))) rulethm
        let mrthm = MP (SPECL rels (SPECL dtms monothm)) irthm
        let imrth = 
            EQ_MP (SYM(end_itlist MK_CONJ (map (fst << snd) unths))) mrthm
        let ifthm = MP (SPECL dtms indthm) imrth
        let fthm = EQ_MP (end_itlist MK_CONJ (map (snd << snd) unths)) ifthm
        let mk_case th1 th2 = 
            let avs = fst(strip_forall(concl th1))
            GENL avs (IMP_ANTISYM_RULE (SPEC_ALL th1) (SPEC_ALL th2))
        let casethm = 
            end_itlist CONJ (map2 mk_case (CONJUNCTS fthm) (CONJUNCTS rulethm))
        CONJ rulethm (CONJ indthm casethm)
    fun tm -> 
        let clauses = conjuncts tm
        let canonthm = canonicalize_clauses clauses
        let canonthm' = SYM canonthm
        let pclosed = rand(concl canonthm)
        let pclauses = conjuncts pclosed
        let rawthm = derive_canon_inductive_relations pclauses
        let rulethm, otherthms = CONJ_PAIR rawthm
        let indthm, casethm = CONJ_PAIR otherthms
        let rulethm' = EQ_MP canonthm' rulethm
        let indthm' = CONV_RULE (ONCE_DEPTH_CONV(REWR_CONV canonthm')) indthm
        CONJ rulethm' (CONJ indthm' casethm)

(* ========================================================================= *)
(* Part 2: Tactic-integrated tools for proving monotonicity automatically.   *)
(* ========================================================================= *)
let MONO_AND = 
    ITAUT(parse_term "(A ==> B) /\ (C ==> D) ==> (A /\ C ==> B /\ D)")

let MONO_OR = ITAUT(parse_term "(A ==> B) /\ (C ==> D) ==> (A \/ C ==> B \/ D)")
let MONO_IMP = 
    ITAUT(parse_term "(B ==> A) /\ (C ==> D) ==> ((A ==> C) ==> (B ==> D))")
let MONO_NOT = ITAUT(parse_term "(B ==> A) ==> (~A ==> ~B)")

let MONO_FORALL = 
    prove
        ((parse_term "(!x:A. P x ==> Q x) ==> ((!x. P x) ==> (!x. Q x))"), 
         REPEAT STRIP_TAC
         |> THEN <| FIRST_ASSUM MATCH_MP_TAC
         |> THEN <| ASM_REWRITE_TAC [])

let MONO_EXISTS = 
    prove
        ((parse_term "(!x:A. P x ==> Q x) ==> ((?x. P x) ==> (?x. Q x))"), 
         DISCH_TAC
         |> THEN <| DISCH_THEN(X_CHOOSE_TAC(parse_term "x:A"))
         |> THEN <| EXISTS_TAC(parse_term "x:A")
         |> THEN <| FIRST_ASSUM MATCH_MP_TAC
         |> THEN <| ASM_REWRITE_TAC [])

(* ------------------------------------------------------------------------- *)
(* Assignable list of monotonicity theorems, so users can add their own.     *)
(* ------------------------------------------------------------------------- *)
let monotonicity_theorems = 
    ref [MONO_AND; MONO_OR; MONO_IMP; MONO_NOT; MONO_EXISTS; MONO_FORALL]

(* ------------------------------------------------------------------------- *)
(* Attempt to backchain through the monotonicity theorems.                   *)
(* ------------------------------------------------------------------------- *)
let MONO_TAC = 
    let imp = (parse_term "(==>)")
    let IMP_REFL = ITAUT(parse_term "!p. p ==> p")
    let BACKCHAIN_TAC th = 
        let match_fn = PART_MATCH (snd << dest_imp) th
        fun (asl, w) -> 
            let th1 = match_fn w
            let ant, con = dest_imp(concl th1)
            null_meta, [asl, ant], fun i _ -> 
                match _arg1 with
                | [t] -> MATCH_MP (INSTANTIATE i th1) t
    let MONO_ABS_TAC(asl, w) = 
        let ant, con = dest_imp w
        let vars = snd(strip_comb con)
        let rnum = length vars - 1
        let hd1, args1 = strip_ncomb rnum ant
        let hd2, args2 = strip_ncomb rnum con
        let th1 = rev_itlist (C AP_THM) args1 (BETA_CONV hd1)
        let th2 = rev_itlist (C AP_THM) args1 (BETA_CONV hd2)
        let th3 = MK_COMB(AP_TERM imp th1, th2)
        CONV_TAC (REWR_CONV th3) (asl, w)
    let APPLY_MONOTAC tacs (asl, w) = 
        let a, c = dest_imp w
        if aconv a c
        then ACCEPT_TAC (SPEC a IMP_REFL) (asl, w)
        else 
            let cn = 
                try 
                    fst(dest_const(repeat rator c))
                with
                | Failure _ -> ""
            tryfind (fun (k, t) -> 
                    if k = cn
                    then t(asl, w)
                    else fail()) tacs
    fun gl -> 
        let tacs = 
            itlist (fun th l -> 
                    let ft = repeat rator (funpow 2 rand (concl th))
                    let c = 
                        try 
                            fst(dest_const ft)
                        with
                        | Failure _ -> ""
                    (c, BACKCHAIN_TAC th
                        |> THEN <| REPEAT CONJ_TAC) :: l) 
                (!monotonicity_theorems) ["", MONO_ABS_TAC]
        let MONO_STEP_TAC = REPEAT GEN_TAC
                            |> THEN <| APPLY_MONOTAC tacs
        (REPEAT MONO_STEP_TAC
         |> THEN <| ASM_REWRITE_TAC []) gl

(* ------------------------------------------------------------------------- *)
(* Attempt to dispose of the non-equational assumption(s) of a theorem.      *)
(* ------------------------------------------------------------------------- *)
let prove_monotonicity_hyps = 
    let tac = 
        REPEAT GEN_TAC
        |> THEN <| DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)
        |> THEN <| REPEAT CONJ_TAC
        |> THEN <| MONO_TAC
    let prove_mth t = prove(t, tac)
    fun th -> 
        let mths = mapfilter prove_mth (filter (not << is_eq) (hyp th))
        itlist PROVE_HYP mths th

(* ========================================================================= *)
(* Part 3: The final user wrapper, with schematic variables added.           *)
(* ========================================================================= *)
let the_inductive_definitions = ref []

let prove_inductive_relations_exist, new_inductive_definition = 
    let rec pare_comb qvs tm = 
        if intersect (frees tm) qvs = [] & forall is_var (snd(strip_comb tm))
        then tm
        else pare_comb qvs (rator tm)
    let generalize_schematic_variables gflag vs = 
        let generalize_def tm th = 
            let l, r = dest_eq tm
            let lname, lty = dest_var l
            let l' = mk_var(lname, itlist (mk_fun_ty << type_of) vs lty)
            let r' = list_mk_abs(vs, r)
            let tm' = mk_eq(l', r')
            let th0 = RIGHT_BETAS vs (ASSUME tm')
            let th1 = INST [lhs(concl th0), l] (DISCH tm th)
            MP th1 th0
        fun th -> 
            let defs, others = partition is_eq (hyp th)
            let th1 = itlist generalize_def defs th
            if gflag
            then 
                let others' = 
                    map (fun t -> 
                            let fvs = frees t
                            SPECL fvs (ASSUME(list_mk_forall(fvs, t)))) others
                GENL vs (itlist PROVE_HYP others' th1)
            else th1
    let derive_existence th = 
        let defs = filter is_eq (hyp th)
        itlist EXISTS_EQUATION defs th
    let make_definitions th = 
        let defs = filter is_eq (hyp th)
        let dths = map new_definition defs
        let insts = zip (map (lhs << concl) dths) (map lhs defs)
        rev_itlist (C MP) dths (INST insts (itlist DISCH defs th))
    let unschematize_clauses clauses = 
        let schem = 
            map (fun cls -> 
                    let avs, bod = strip_forall cls
                    pare_comb avs (try 
                                       snd(dest_imp bod)
                                   with
                                   | Failure _ -> bod)) clauses
        let schems = setify schem
        if is_var(hd schem)
        then (clauses, [])
        elif not(length(setify(map (snd << strip_comb) schems)) = 1)
        then failwith "Schematic variables not used consistently"
        else 
            let avoids = variables(list_mk_conj clauses)
            let hack_fn tm = mk_var(fst(dest_var(repeat rator tm)), type_of tm)
            let grels = variants avoids (map hack_fn schems)
            let crels = zip grels schems
            let clauses' = map (subst crels) clauses
            clauses', snd(strip_comb(hd schems))
    let find_redefinition tm (rth, ith, cth as trip) = 
        if aconv tm (concl rth)
        then trip
        else failwith "find_redefinition"
    let prove_inductive_properties tm = 
        let clauses = conjuncts tm
        let clauses', fvs = unschematize_clauses clauses
        let th = derive_nonschematic_inductive_relations(list_mk_conj clauses')
        fvs, prove_monotonicity_hyps th
    let prove_inductive_relations_exist tm = 
        let fvs, th1 = prove_inductive_properties tm
        let th2 = generalize_schematic_variables true fvs th1
        derive_existence th2
    let new_inductive_definition tm = 
        try 
            let th = tryfind (find_redefinition tm) (!the_inductive_definitions)
            warn true "Benign redefinition of inductive predicate"
            th
        with
        | Failure _ -> 
            let fvs, th1 = prove_inductive_properties tm
            let th2 = generalize_schematic_variables true fvs th1
            let th3 = make_definitions th2
            let avs = fst(strip_forall(concl th3))
            let r, ic = CONJ_PAIR(SPECL avs th3)
            let i, c = CONJ_PAIR ic
            let thtr = GENL avs r, GENL avs i, GENL avs c
            the_inductive_definitions := thtr :: (!the_inductive_definitions)
            thtr
    prove_inductive_relations_exist, new_inductive_definition

(* ------------------------------------------------------------------------- *)
(* Derivation of "strong induction".                                         *)
(* ------------------------------------------------------------------------- *)
let derive_strong_induction = 
    let dest_ibod tm = 
        let avs, ibod = strip_forall tm
        let n = length avs
        let prator = funpow n rator
        let ant, con = dest_imp ibod
        n, (prator ant, prator con)
    let rec prove_triv tm = 
        if is_conj tm
        then CONJ (prove_triv(lhand tm)) (prove_triv(rand tm))
        else 
            let avs, bod = strip_forall tm
            let a, c = dest_imp bod
            let ths = CONJUNCTS(ASSUME a)
            let th = find (aconv c << concl) ths
            GENL avs (DISCH a th)
    let rec weaken_triv th = 
        if is_conj(concl th)
        then CONJ (weaken_triv(CONJUNCT1 th)) (weaken_triv(CONJUNCT2 th))
        else 
            let avs, bod = strip_forall(concl th)
            let th1 = SPECL avs th
            let a = fst(dest_imp(concl th1))
            GENL avs (DISCH a (CONJUNCT2(UNDISCH th1)))
    let MATCH_IMPS = MATCH_MP MONO_AND
    fun (rth, ith) -> 
        let ovs, ibod = strip_forall(concl ith)
        let iant, icon = dest_imp ibod
        let ns, prrs = unzip(map dest_ibod (conjuncts icon))
        let rs, ps = unzip prrs
        let gs = variants (variables ibod) ps
        let svs, tvs = chop_list (length ovs - length ns) ovs
        let sth = SPECL svs rth
        let jth = SPECL svs ith
        let gimps = subst (zip gs rs) icon
        let prs = 
            map2 
                (fun n (r, p) -> 
                    let tys, ty = nsplit dest_fun_ty (1 -- n) (type_of r)
                    let gvs = map genvar tys
                    list_mk_abs
                        (gvs, 
                         mk_conj(list_mk_comb(r, gvs), list_mk_comb(p, gvs)))) 
                ns prrs
        let modify_rule rcl itm = 
            let avs, bod = strip_forall itm
            if is_imp bod
            then 
                let a, c = dest_imp bod
                let mgoal = mk_imp(gimps, mk_imp(vsubst (zip gs ps) a, a))
                let mth = ASSUME(list_mk_forall(gs @ ps @ avs, mgoal))
                let ith_r = BETA_RULE(SPECL (prs @ rs @ avs) mth)
                let jth_r = MP ith_r (prove_triv(lhand(concl ith_r)))
                let t = lhand(concl jth_r)
                let kth_r = UNDISCH jth_r
                let ntm = list_mk_forall(avs, mk_imp(t, c))
                let lth_r = MP (SPECL avs rcl) kth_r
                let lth_p = UNDISCH(SPECL avs (ASSUME ntm))
                DISCH ntm (GENL avs (DISCH t (CONJ lth_r lth_p)))
            else 
                DISCH itm 
                    (GENL avs (CONJ (SPECL avs rcl) (SPECL avs (ASSUME itm))))
        let mimps = map2 modify_rule (CONJUNCTS sth) (conjuncts iant)
        let th1 = end_itlist (fun th th' -> MATCH_IMPS(CONJ th th')) mimps
        let th2 = BETA_RULE(SPECL prs jth)
        let th3 = IMP_TRANS th1 th2
        let nasm = lhand(concl th3)
        let th4 = GENL ps (DISCH nasm (weaken_triv(UNDISCH th3)))
        GENL svs (prove_monotonicity_hyps th4)