(*

Copyright 1998 University of Cambridge
Copyright 1998-2007 John Harrison
Copyright 2013 Jack Pappas

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

/// Basic rewriting and simplification tools.
module NHol.simp

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

(* ------------------------------------------------------------------------- *)
(* Generalized conversion (conversion plus a priority).                      *)
(* ------------------------------------------------------------------------- *)
type gconv = int * conv

(* ------------------------------------------------------------------------- *)
(* Primitive rewriting conversions: unconditional and conditional equations. *)
(* ------------------------------------------------------------------------- *)
let REWR_CONV = PART_MATCH lhs

let IMP_REWR_CONV = PART_MATCH(lhs << snd << dest_imp)

(* ------------------------------------------------------------------------- *)
(* Versions with ordered rewriting. We must have l' > r' for the rewrite     *)
(* |- l = r (or |- c ==> (l = r)) to apply.                                  *)
(* ------------------------------------------------------------------------- *)
let ORDERED_REWR_CONV ord th = 
    let basic_conv = REWR_CONV th
    fun tm -> 
        let thm = basic_conv tm
        let l, r = dest_eq(concl thm)
        if ord l r
        then thm
        else failwith "ORDERED_REWR_CONV: wrong orientation"

let ORDERED_IMP_REWR_CONV ord th = 
    let basic_conv = IMP_REWR_CONV th
    fun tm -> 
        let thm = basic_conv tm
        let l, r = dest_eq(rand(concl thm))
        if ord l r
        then thm
        else failwith "ORDERED_IMP_REWR_CONV: wrong orientation"

(* ------------------------------------------------------------------------- *)
(* Standard AC-compatible term ordering: a "dynamic" lexicographic ordering. *)
(*                                                                           *)
(* This is a slight hack to make AC normalization work. However I *think*    *)
(* it's properly AC compatible, i.e. monotonic and total, WF on ground terms *)
(* (over necessarily finite signature) and with the properties for any       *)
(* binary operator +:                                                        *)
(*                                                                           *)
(*         (x + y) + z > x + (y + z)                                         *)
(*         x + y > y + x                   iff x > y                         *)
(*         x + (y + z) > y + (x + z)       iff x > y                         *)
(*                                                                           *)
(* The idea is that when invoking lex ordering with identical head operator  *)
(* "f", one sticks "f" at the head of an otherwise arbitrary ordering on     *)
(* subterms (the built-in CAML one). This avoids the potentially inefficient *)
(* calculation of term size in the standard orderings.                       *)
(* ------------------------------------------------------------------------- *)
let term_order = 
    let rec lexify ord l1 l2 = 
        if l1 = []
        then false
        elif l2 = []
        then true
        else 
            let h1 = hd l1
            let h2 = hd l2
            ord h1 h2 || (h1 = h2 && lexify ord (tl l1) (tl l2))
    let rec dyn_order top tm1 tm2 = 
        let f1, args1 = strip_comb tm1
        let f2, args2 = strip_comb tm2
        if f1 = f2
        then lexify (dyn_order f1) args1 args2
        elif f2 = top
        then false
        elif f1 = top
        then true
        else f1 > f2
    dyn_order(parse_term "T")

(* ------------------------------------------------------------------------- *)
(* Create a gconv net for a theorem as a (cond) rewrite. The "rep" flag      *)
(* will cause any trivially looping rewrites to be modified, and any that    *)
(* are permutative to be ordered w.r.t. the standard order. The idea is that *)
(* this flag will be set iff the conversion is going to get repeated.        *)
(* This includes a completely ad hoc but useful special case for ETA_AX,     *)
(* which forces a first order match (otherwise it would loop on a lambda).   *)
(* ------------------------------------------------------------------------- *)
let net_of_thm rep th = 
    let tm = concl th
    let lconsts = freesl(hyp th)
    let matchable = can << term_match lconsts
    match tm with
    | Comb(Comb(Const("=", _), (Abs(x, Comb(Var(s, ty) as v, x')) as l)), v') when x' = x 
                                                                                   && v' = v 
                                                                                   && not
                                                                                          (x = v) -> 
        let conv tm = 
            match tm with
            | Abs(y, Comb(t, y')) when y = y' && not(free_in y t) -> 
                INSTANTIATE (term_match [] v t) th
            | _ -> failwith "REWR_CONV (ETA_AX special case)"
        enter lconsts (l, (1, conv))
    | Comb(Comb(Const("=", _), l), r) -> 
        if rep && free_in l r
        then 
            let th' = EQT_INTRO th
            enter lconsts (l, (1, REWR_CONV th'))
        elif rep && matchable l r && matchable r l
        then enter lconsts (l, (1, ORDERED_REWR_CONV term_order th))
        else enter lconsts (l, (1, REWR_CONV th))
    | Comb(Comb(_, t), Comb(Comb(Const("=", _), l), r)) -> 
        if rep && free_in l r
        then 
            let th' = DISCH t (EQT_INTRO(UNDISCH th))
            enter lconsts (l, (3, IMP_REWR_CONV th'))
        elif rep && matchable l r && matchable r l
        then enter lconsts (l, (3, ORDERED_IMP_REWR_CONV term_order th))
        else enter lconsts (l, (3, IMP_REWR_CONV th))

(* ------------------------------------------------------------------------- *)
(* Create a gconv net for a conversion with a term index.                    *)
(* ------------------------------------------------------------------------- *)
let net_of_conv tm conv sofar = enter [] (tm, (2, conv)) sofar

(* ------------------------------------------------------------------------- *)
(* Create a gconv net for a congruence rule (in canonical form!)             *)
(* ------------------------------------------------------------------------- *)
let net_of_cong th sofar = 
    let conc, n = repeat (fun (tm, m) -> snd(dest_imp tm), m + 1) (concl th, 0)
    if n = 0
    then failwith "net_of_cong: Non-implicational congruence"
    else 
        let pat = lhs conc
        let conv = GEN_PART_MATCH (lhand << funpow n rand) th
        enter [] (pat, (4, conv)) sofar

(* ------------------------------------------------------------------------- *)
(* Rewrite maker for ordinary and conditional rewrites (via "cf" flag).      *)
(*                                                                           *)
(* We follow Don in going from ~(s = t) to (s = t) = F *and* (t = s) = F.    *)
(* Well, why not? However, we don't abandon s = t where FV(t) is not a       *)
(* subset of FV(s) in favour of (s = t) = T, as he does.                     *)
(* Note: looping rewrites are not discarded here, only when netted.          *)
(* ------------------------------------------------------------------------- *)
let mk_rewrites = 
    let IMP_CONJ_CONV = 
        REWR_CONV(ITAUT(parse_term "p ==> q ==> r <=> p /\ q ==> r"))
    let IMP_EXISTS_RULE = 
        let cnv = 
            REWR_CONV(ITAUT(parse_term "(!x. P x ==> Q) <=> (?x. P x) ==> Q"))
        fun v th -> CONV_RULE cnv (GEN v th)
    let collect_condition oldhyps th = 
        let conds = subtract (hyp th) oldhyps
        if conds = []
        then th
        else 
            let jth = itlist DISCH conds th
            let kth = CONV_RULE (REPEATC IMP_CONJ_CONV) jth
            let cond, eqn = dest_imp(concl kth)
            let fvs = 
                subtract (subtract (frees cond) (frees eqn)) (freesl oldhyps)
            itlist IMP_EXISTS_RULE fvs kth
    let rec split_rewrites oldhyps cf th sofar = 
        let tm = concl th
        if is_forall tm
        then split_rewrites oldhyps cf (SPEC_ALL th) sofar
        elif is_conj tm
        then 
            split_rewrites oldhyps cf (CONJUNCT1 th) 
                (split_rewrites oldhyps cf (CONJUNCT2 th) sofar)
        elif is_imp tm && cf
        then split_rewrites oldhyps cf (UNDISCH th) sofar
        elif is_eq tm
        then 
            (if cf
             then collect_condition oldhyps th
             else th) :: sofar
        elif is_neg tm
        then 
            let ths = split_rewrites oldhyps cf (EQF_INTRO th) sofar
            if is_eq(rand tm)
            then split_rewrites oldhyps cf (EQF_INTRO(GSYM th)) ths
            else ths
        else split_rewrites oldhyps cf (EQT_INTRO th) sofar
    fun cf th sofar -> split_rewrites (hyp th) cf th sofar

(* ------------------------------------------------------------------------- *)
(* Rewriting (and application of other conversions) based on a convnet.      *)
(* ------------------------------------------------------------------------- *)
let REWRITES_CONV net tm = 
    let pconvs = lookup tm net
    try 
        tryfind (fun (_, cnv) -> cnv tm) pconvs
    with
    | Failure _ -> failwith "REWRITES_CONV"

(* ------------------------------------------------------------------------- *)
(* Decision procedures may accumulate their state in different ways (e.g.    *)
(* term nets and predicate-indexed lists of Horn clauses). To allow mixing   *)
(* of arbitrary types for state storage, we use a trick due to RJB via DRS.  *)
(* ------------------------------------------------------------------------- *)
type prover = 
    | Prover of conv * (thm list -> prover)

let mk_prover applicator augmentor = 
    let rec mk_prover state = 
        let apply = applicator state
        let augment thms = mk_prover(augmentor state thms)
        Prover(apply, augment)
    mk_prover

let augment (Prover(_, aug)) thms = aug thms
let apply_prover (Prover(conv, _)) tm = conv tm

(* ------------------------------------------------------------------------- *)
(* Type of simpsets. We have a convnet containing rewrites (implicational    *)
(* and otherwise), other term-indexed context-free conversions like          *)
(* BETA_CONV, and congruence rules. Then there is a list of provers that     *)
(* have their own way of storing and using context, and finally a rewrite    *)
(* maker function, to allow customization.                                   *)
(*                                                                           *)
(* We also have a type of (traversal) strategy, following Konrad.            *)
(* ------------------------------------------------------------------------- *)
type simpset = 
    | Simpset of gconv net * (strategy -> strategy) * prover list * (thm -> thm list -> thm list)

(* Rewrites & congruences *)
(* Prover for conditions  *)
(* Subprovers for prover  *)
(* Rewrite maker          *)
and strategy = simpset -> int -> term -> thm

(* ------------------------------------------------------------------------- *)
(* Very simple prover: recursively simplify then try provers.                *)
(* ------------------------------------------------------------------------- *)
let basic_prover strat (Simpset(net, prover, provers, rewmaker) as ss) lev tm = 
    let sth = 
        try 
            strat ss lev tm
        with
        | Failure _ -> REFL tm
    try 
        EQT_ELIM sth
    with
    | Failure _ -> 
        let tth = tryfind (fun pr -> apply_prover pr (rand(concl sth))) provers
        EQ_MP (SYM sth) tth

(* ------------------------------------------------------------------------- *)
(* Functions for changing or augmenting components of simpsets.              *)
(* ------------------------------------------------------------------------- *)
let ss_of_thms thms (Simpset(net, prover, provers, rewmaker)) = 
    let cthms = itlist rewmaker thms []
    let net' = itlist (net_of_thm true) cthms net
    Simpset(net', prover, provers, rewmaker)

let ss_of_conv keytm conv (Simpset(net, prover, provers, rewmaker)) = 
    let net' = net_of_conv keytm conv net
    Simpset(net', prover, provers, rewmaker)

let ss_of_congs thms (Simpset(net, prover, provers, rewmaker)) = 
    let net' = itlist net_of_cong thms net
    Simpset(net', prover, provers, rewmaker)

let ss_of_prover newprover (Simpset(net, _, provers, rewmaker)) = 
    Simpset(net, newprover, provers, rewmaker)
let ss_of_provers newprovers (Simpset(net, prover, provers, rewmaker)) = 
    Simpset(net, prover, newprovers @ provers, rewmaker)
let ss_of_maker newmaker (Simpset(net, prover, provers, _)) = 
    Simpset(net, prover, provers, newmaker)

(* ------------------------------------------------------------------------- *)
(* Perform a context-augmentation operation on a simpset.                    *)
(* ------------------------------------------------------------------------- *)
let AUGMENT_SIMPSET cth (Simpset(net, prover, provers, rewmaker)) = 
    let provers' = map (C augment [cth]) provers
    let cthms = rewmaker cth []
    let net' = itlist (net_of_thm true) cthms net
    Simpset(net', prover, provers', rewmaker)

(* ------------------------------------------------------------------------- *)
(* Depth conversions.                                                        *)
(* ------------------------------------------------------------------------- *)
let ONCE_DEPTH_SQCONV, DEPTH_SQCONV, REDEPTH_SQCONV, TOP_DEPTH_SQCONV, TOP_SWEEP_SQCONV = 
    let IMP_REWRITES_CONV strat (Simpset(net, prover, provers, rewmaker) as ss) 
        lev pconvs tm = 
        tryfind (fun (n, cnv) -> 
                if n >= 4
                then fail()
                else 
                    let th = cnv tm
                    let etm = concl th
                    if is_eq etm
                    then th
                    elif lev <= 0
                    then failwith "IMP_REWRITES_CONV: Too deep"
                    else 
                        let cth = prover strat ss (lev - 1) (lhand etm)
                        MP th cth) pconvs
    let rec RUN_SUB_CONV strat ss lev triv th = 
        let tm = concl th
        if is_imp tm
        then 
            let subtm = lhand tm
            let avs, bod = strip_forall subtm
            let (t, t'), ss', mk_fun = 
                try 
                    dest_eq bod, ss, I
                with
                | Failure _ -> 
                    let cxt, deq = dest_imp bod
                    dest_eq deq, AUGMENT_SIMPSET (ASSUME cxt) ss, DISCH cxt
            let eth, triv' = 
                try 
                    strat ss' lev t, false
                with
                | Failure _ -> REFL t, triv
            let eth' = GENL avs (mk_fun eth)
            let th' = 
                if is_var t'
                then INST [rand(concl eth), t'] th
                else GEN_PART_MATCH lhand th (concl eth')
            let th'' = MP th' eth'
            RUN_SUB_CONV strat ss lev triv' th''
        elif triv
        then fail()
        else th
    let GEN_SUB_CONV strat ss lev pconvs tm = 
        try 
            tryfind (fun (n, cnv) -> 
                    if n < 4
                    then fail()
                    else 
                        let th = cnv tm
                        RUN_SUB_CONV strat ss lev true th) pconvs
        with
        | Failure _ -> 
            if is_comb tm
            then 
                let l, r = dest_comb tm
                try 
                    let th1 = strat ss lev l
                    try 
                        let th2 = strat ss lev r
                        MK_COMB(th1, th2)
                    with
                    | Failure _ -> AP_THM th1 r
                with
                | Failure _ -> AP_TERM l (strat ss lev r)
            elif is_abs tm
            then 
                let v, bod = dest_abs tm
                let th = strat ss lev bod
                try 
                    ABS v th
                with
                | Failure _ -> 
                    let gv = genvar(type_of v)
                    let gbod = vsubst [gv, v] bod
                    let gth = ABS gv (strat ss lev gbod)
                    let gtm = concl gth
                    let l, r = dest_eq gtm
                    let v' = variant (frees gtm) v
                    let l' = alpha v' l
                    let r' = alpha v' r
                    EQ_MP (ALPHA gtm (mk_eq(l', r'))) gth
            else failwith "GEN_SUB_CONV"
    let rec ONCE_DEPTH_SQCONV (Simpset(net, prover, provers, rewmaker) as ss) 
            lev tm = 
        let pconvs = lookup tm net
        try 
            IMP_REWRITES_CONV ONCE_DEPTH_SQCONV ss lev pconvs tm
        with
        | Failure _ -> GEN_SUB_CONV ONCE_DEPTH_SQCONV ss lev pconvs tm
    let rec DEPTH_SQCONV (Simpset(net, prover, provers, rewmaker) as ss) lev tm = 
        let pconvs = lookup tm net
        try 
            let th1 = GEN_SUB_CONV DEPTH_SQCONV ss lev pconvs tm
            let tm1 = rand(concl th1)
            let pconvs1 = lookup tm1 net
            try 
                TRANS th1 (IMP_REWRITES_CONV DEPTH_SQCONV ss lev pconvs1 tm1)
            with
            | Failure _ -> th1
        with
        | Failure _ -> IMP_REWRITES_CONV DEPTH_SQCONV ss lev pconvs tm
    let rec REDEPTH_SQCONV (Simpset(net, prover, provers, rewmaker) as ss) lev 
            tm = 
        let pconvs = lookup tm net
        let th = 
            try 
                let th1 = GEN_SUB_CONV REDEPTH_SQCONV ss lev pconvs tm
                let tm1 = rand(concl th1)
                let pconvs1 = lookup tm1 net
                try 
                    TRANS th1 
                        (IMP_REWRITES_CONV REDEPTH_SQCONV ss lev pconvs1 tm1)
                with
                | Failure _ -> th1
            with
            | Failure _ -> IMP_REWRITES_CONV REDEPTH_SQCONV ss lev pconvs tm
        try 
            let th' = REDEPTH_SQCONV ss lev (rand(concl th))
            TRANS th th'
        with
        | Failure _ -> th
    let rec TOP_DEPTH_SQCONV (Simpset(net, prover, provers, rewmaker) as ss) lev 
            tm = 
        let pconvs = lookup tm net
        let th1 = 
            try 
                IMP_REWRITES_CONV TOP_DEPTH_SQCONV ss lev pconvs tm
            with
            | Failure _ -> GEN_SUB_CONV TOP_DEPTH_SQCONV ss lev pconvs tm
        try 
            let th2 = TOP_DEPTH_SQCONV ss lev (rand(concl th1))
            TRANS th1 th2
        with
        | Failure _ -> th1
    let rec TOP_SWEEP_SQCONV (Simpset(net, prover, provers, rewmaker) as ss) lev 
            tm = 
        let pconvs = lookup tm net
        try 
            let th1 = IMP_REWRITES_CONV TOP_SWEEP_SQCONV ss lev pconvs tm
            try 
                let th2 = TOP_SWEEP_SQCONV ss lev (rand(concl th1))
                TRANS th1 th2
            with
            | Failure _ -> th1
        with
        | Failure _ -> GEN_SUB_CONV TOP_SWEEP_SQCONV ss lev pconvs tm
    ONCE_DEPTH_SQCONV, DEPTH_SQCONV, REDEPTH_SQCONV, TOP_DEPTH_SQCONV, 
    TOP_SWEEP_SQCONV

(* ------------------------------------------------------------------------- *)
(* Maintenence of basic rewrites and conv nets for rewriting.                *)
(* ------------------------------------------------------------------------- *)
let set_basic_rewrites, extend_basic_rewrites, basic_rewrites, set_basic_convs, extend_basic_convs, basic_convs, basic_net = 
    let rewrites = ref([] : thm list)
    let conversions = ref ([] : (string * (term * conv)) list)
    let conv_net = ref(empty_net : gconv net)
    let rehash_convnet() = 
        conv_net := itlist (net_of_thm true) (!rewrites) 
               (itlist (fun (_, _) -> 
                        match _arg2 with
                        | pat, cnv -> net_of_conv pat cnv) (!conversions) 
                    empty_net)
    let set_basic_rewrites thl = 
        let canon_thl = itlist (mk_rewrites false) thl []
        rewrites := canon_thl
        rehash_convnet()
    let extend_basic_rewrites thl = 
        let canon_thl = itlist (mk_rewrites false) thl []
        rewrites := canon_thl @ !rewrites
        rehash_convnet()
    let basic_rewrites() = !rewrites
    let set_basic_convs cnvs = 
        conversions := cnvs
        rehash_convnet()
    let extend_basic_convs(name, patcong) = 
        (conversions 
         := (name, patcong) 
            :: filter (fun (name', _) -> name <> name') (!conversions)
         rehash_convnet())
    let basic_convs() = !conversions
    let basic_net() = !conv_net
    set_basic_rewrites, extend_basic_rewrites, basic_rewrites, set_basic_convs, 
    extend_basic_convs, basic_convs, basic_net

(* ------------------------------------------------------------------------- *)
(* Same thing for the default congruences.                                   *)
(* ------------------------------------------------------------------------- *)
let set_basic_congs, extend_basic_congs, basic_congs = 
    let congs = ref([] : thm list)
    (fun thl -> congs := thl), 
    (fun thl -> congs := union' equals_thm thl (!congs)), (fun () -> !congs)

(* ------------------------------------------------------------------------- *)
(* Main rewriting conversions.                                               *)
(* ------------------------------------------------------------------------- *)
let GENERAL_REWRITE_CONV rep (cnvl : conv -> conv) (builtin_net : gconv net) thl = 
    let thl_canon = itlist (mk_rewrites false) thl []
    let final_net = itlist (net_of_thm rep) thl_canon builtin_net
    cnvl(REWRITES_CONV final_net)

let GEN_REWRITE_CONV (cnvl : conv -> conv) thl = 
    GENERAL_REWRITE_CONV false cnvl empty_net thl
let PURE_REWRITE_CONV thl = 
    GENERAL_REWRITE_CONV true TOP_DEPTH_CONV empty_net thl
let REWRITE_CONV thl = 
    GENERAL_REWRITE_CONV true TOP_DEPTH_CONV (basic_net()) thl
let PURE_ONCE_REWRITE_CONV thl = 
    GENERAL_REWRITE_CONV false ONCE_DEPTH_CONV empty_net thl
let ONCE_REWRITE_CONV thl = 
    GENERAL_REWRITE_CONV false ONCE_DEPTH_CONV (basic_net()) thl

(* ------------------------------------------------------------------------- *)
(* Rewriting rules and tactics.                                              *)
(* ------------------------------------------------------------------------- *)
let GEN_REWRITE_RULE cnvl thl = CONV_RULE(GEN_REWRITE_CONV cnvl thl)

let PURE_REWRITE_RULE thl = CONV_RULE(PURE_REWRITE_CONV thl)
let REWRITE_RULE thl = CONV_RULE(REWRITE_CONV thl)
let PURE_ONCE_REWRITE_RULE thl = CONV_RULE(PURE_ONCE_REWRITE_CONV thl)
let ONCE_REWRITE_RULE thl = CONV_RULE(ONCE_REWRITE_CONV thl)
let PURE_ASM_REWRITE_RULE thl th = 
    PURE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
let ASM_REWRITE_RULE thl th = REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
let PURE_ONCE_ASM_REWRITE_RULE thl th = 
    PURE_ONCE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
let ONCE_ASM_REWRITE_RULE thl th = 
    ONCE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
let GEN_REWRITE_TAC cnvl thl = CONV_TAC(GEN_REWRITE_CONV cnvl thl)
let PURE_REWRITE_TAC thl = CONV_TAC(PURE_REWRITE_CONV thl)
let REWRITE_TAC thl = CONV_TAC(REWRITE_CONV thl)
let PURE_ONCE_REWRITE_TAC thl = CONV_TAC(PURE_ONCE_REWRITE_CONV thl)
let ONCE_REWRITE_TAC thl = CONV_TAC(ONCE_REWRITE_CONV thl)
let (PURE_ASM_REWRITE_TAC : thm list -> tactic) = ASM PURE_REWRITE_TAC
let (ASM_REWRITE_TAC : thm list -> tactic) = ASM REWRITE_TAC
let (PURE_ONCE_ASM_REWRITE_TAC : thm list -> tactic) = ASM PURE_ONCE_REWRITE_TAC
let (ONCE_ASM_REWRITE_TAC : thm list -> tactic) = ASM ONCE_REWRITE_TAC

(* ------------------------------------------------------------------------- *)
(* Simplification functions.                                                 *)
(* ------------------------------------------------------------------------- *)
let GEN_SIMPLIFY_CONV (strat : strategy) ss lev thl = 
    let ss' = itlist AUGMENT_SIMPSET thl ss
    TRY_CONV(strat ss' lev)

let ONCE_SIMPLIFY_CONV ss = GEN_SIMPLIFY_CONV ONCE_DEPTH_SQCONV ss 1
let SIMPLIFY_CONV ss = GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV ss 3

(* ------------------------------------------------------------------------- *)
(* Simple but useful default version.                                        *)
(* ------------------------------------------------------------------------- *)
let empty_ss = Simpset(empty_net, basic_prover, [], mk_rewrites true)

let basic_ss = 
    let rewmaker = mk_rewrites true
    fun thl -> 
        let cthms = itlist rewmaker thl []
        let net' = itlist (net_of_thm true) cthms (basic_net())
        let net'' = itlist net_of_cong (basic_congs()) net'
        Simpset(net'', basic_prover, [], rewmaker)

let SIMP_CONV thl = SIMPLIFY_CONV (basic_ss []) thl
let PURE_SIMP_CONV thl = SIMPLIFY_CONV empty_ss thl
let ONCE_SIMP_CONV thl = ONCE_SIMPLIFY_CONV (basic_ss []) thl
let SIMP_RULE thl = CONV_RULE(SIMP_CONV thl)
let PURE_SIMP_RULE thl = CONV_RULE(PURE_SIMP_CONV thl)
let ONCE_SIMP_RULE thl = CONV_RULE(ONCE_SIMP_CONV thl)
let SIMP_TAC thl = CONV_TAC(SIMP_CONV thl)
let PURE_SIMP_TAC thl = CONV_TAC(PURE_SIMP_CONV thl)
let ONCE_SIMP_TAC thl = CONV_TAC(ONCE_SIMP_CONV thl)
let ASM_SIMP_TAC = ASM SIMP_TAC
let PURE_ASM_SIMP_TAC = ASM PURE_SIMP_TAC
let ONCE_ASM_SIMP_TAC = ASM ONCE_SIMP_TAC

(* ------------------------------------------------------------------------- *)
(* Abbreviation tactics.                                                     *)
(* ------------------------------------------------------------------------- *)
let ABBREV_TAC tm = 
    let cvs, t = dest_eq tm
    let v, vs = strip_comb cvs
    let rs = list_mk_abs(vs, t)
    let eq = mk_eq(rs, v)
    let th1 = 
        itlist (fun v th -> CONV_RULE (LAND_CONV BETA_CONV) (AP_THM th v)) 
            (rev vs) (ASSUME eq)
    let th2 = SIMPLE_CHOOSE v (SIMPLE_EXISTS v (GENL vs th1))
    let th3 = PROVE_HYP (EXISTS (mk_exists(v, eq), rs) (REFL rs)) th2
    fun _ -> 
        match _arg1 with
        | asl, w as gl -> 
            let avoids = itlist (union << frees << concl << snd) asl (frees w)
            if mem v avoids
            then failwith "ABBREV_TAC: variable already used"
            else 
                CHOOSE_THEN (fun th -> 
                        RULE_ASSUM_TAC(PURE_ONCE_REWRITE_RULE [th])
                        |> THEN <| PURE_ONCE_REWRITE_TAC [th]
                        |> THEN <| ASSUME_TAC th) th3 gl

let EXPAND_TAC s = FIRST_ASSUM
                       (SUBST1_TAC << SYM 
                        << check((=) s << fst << dest_var << rhs << concl))
                   |> THEN <| BETA_TAC