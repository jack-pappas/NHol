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
/// Basic rewriting and simplification tools.
module NHol.simp

open System

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
#endif

(* ------------------------------------------------------------------------- *)
(* Generalized conversion (conversion plus a priority).                      *)
(* ------------------------------------------------------------------------- *)
type gconv = int * conv

(* ------------------------------------------------------------------------- *)
(* Primitive rewriting conversions: unconditional and conditional equations. *)
(* ------------------------------------------------------------------------- *)
/// Uses an instance of a given equation to rewrite a term.
let REWR_CONV = PART_MATCH lhs
/// Basic conditional rewriting conversion.
let IMP_REWR_CONV = PART_MATCH(lhs << snd << Choice.get << dest_imp)

(* ------------------------------------------------------------------------- *)
(* Versions with ordered rewriting. We must have l' > r' for the rewrite     *)
(* |- l = r (or |- c ==> (l = r)) to apply.                                  *)
(* ------------------------------------------------------------------------- *)
/// Basic rewriting conversion restricted by term order.
let ORDERED_REWR_CONV ord th = 
    let basic_conv = REWR_CONV th
    fun tm -> 
        let thm = basic_conv tm
        let l, r = Choice.get <| dest_eq(concl thm)
        if ord l r
        then thm
        else failwith "ORDERED_REWR_CONV: wrong orientation"

/// Basic conditional rewriting conversion restricted by term order.
let ORDERED_IMP_REWR_CONV ord th = 
    let basic_conv = IMP_REWR_CONV th
    fun tm -> 
        let thm = basic_conv tm
        let l, r = Choice.get <| dest_eq(Choice.get <| rand(concl thm))
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
/// Term order for use in AC-rewriting.
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
    dyn_order(parse_term @"T")

(* ------------------------------------------------------------------------- *)
(* Create a gconv net for a theorem as a (cond) rewrite. The "rep" flag      *)
(* will cause any trivially looping rewrites to be modified, and any that    *)
(* are permutative to be ordered w.r.t. the standard order. The idea is that *)
(* this flag will be set iff the conversion is going to get repeated.        *)
(* This includes a completely ad hoc but useful special case for ETA_AX,     *)
(* which forces a first order match (otherwise it would loop on a lambda).   *)
(* ------------------------------------------------------------------------- *)
/// Insert a theorem into a net as a (conditional) rewrite.
let net_of_thm rep th = 
    let tm = concl th
    let lconsts = freesl(hyp th)
    let matchable =
        /// Tests for failure.
        let can f x = 
            try f x |> ignore; true
            with Failure _ -> false
        
        can << term_match lconsts
    match tm with
    | Comb(Comb(Const("=", _), (Abs(x, Comb(Var(s, ty) as v, x')) as l)), v') 
        when x' = x && v' = v && not (x = v) -> 
        let conv tm = 
            match tm with
            | Abs(y, Comb(t, y')) when y = y' && not(free_in y t) -> 
                INSTANTIATE (term_match [] v t) th
            | _ -> failwith "REWR_CONV (ETA_AX special case)"
        Choice.get << enter lconsts (l, (1, conv))
    | Comb(Comb(Const("=", _), l), r) -> 
        if rep && free_in l r
        then 
            let th' = EQT_INTRO th
            Choice.get << enter lconsts (l, (1, REWR_CONV th'))
        elif rep && matchable l r && matchable r l
        then Choice.get << enter lconsts (l, (1, ORDERED_REWR_CONV term_order th))
        else Choice.get << enter lconsts (l, (1, REWR_CONV th))
    | Comb(Comb(_, t), Comb(Comb(Const("=", _), l), r)) -> 
        if rep && free_in l r
        then 
            let th' = DISCH t (EQT_INTRO(UNDISCH th))
            Choice.get << enter lconsts (l, (3, IMP_REWR_CONV th'))
        elif rep && matchable l r && matchable r l
        then Choice.get << enter lconsts (l, (3, ORDERED_IMP_REWR_CONV term_order th))
        else Choice.get << enter lconsts (l, (3, IMP_REWR_CONV th))
    | _ -> failwith "net_of_thm: Unhandled case."

(* ------------------------------------------------------------------------- *)
(* Create a gconv net for a conversion with a term index.                    *)
(* ------------------------------------------------------------------------- *)
// TODO : Add brief synopsis from hol-light reference manual.
let net_of_conv tm conv sofar = Choice.get <| enter [] (tm, (2, conv)) sofar

(* ------------------------------------------------------------------------- *)
(* Create a gconv net for a congruence rule (in canonical form!)             *)
(* ------------------------------------------------------------------------- *)
/// Add a congruence rule to a net.
let net_of_cong th sofar = 
    let conc, n = repeat (fun (tm, m) -> snd(Choice.get <| dest_imp tm), m + 1) (concl th, 0)
    if n = 0
    then failwith "net_of_cong: Non-implicational congruence"
    else 
        let pat = lhs conc
        let conv = GEN_PART_MATCH (lhand << funpow n (Choice.get << rand)) th
        Choice.get <| enter [] (pat, (4, conv)) sofar

(* ------------------------------------------------------------------------- *)
(* Rewrite maker for ordinary and conditional rewrites (via "cf" flag).      *)
(*                                                                           *)
(* We follow Don in going from ~(s = t) to (s = t) = F *and* (t = s) = F.    *)
(* Well, why not? However, we don't abandon s = t where FV(t) is not a       *)
(* subset of FV(s) in favour of (s = t) = T, as he does.                     *)
(* Note: looping rewrites are not discarded here, only when netted.          *)
(* ------------------------------------------------------------------------- *)
/// Turn theorem into list of (conditional) rewrites.
let mk_rewrites = 
    let IMP_CONJ_CONV = 
        REWR_CONV(ITAUT(parse_term @"p ==> q ==> r <=> p /\ q ==> r"))
    let IMP_EXISTS_RULE = 
        let cnv = 
            REWR_CONV(ITAUT(parse_term @"(!x. P x ==> Q) <=> (?x. P x) ==> Q"))
        fun v th -> CONV_RULE cnv (GEN v th)
    let collect_condition oldhyps th = 
        let conds = subtract (hyp th) oldhyps
        if conds = []
        then th
        else 
            let jth = itlist DISCH conds th
            let kth = CONV_RULE (REPEATC IMP_CONJ_CONV) jth
            let cond, eqn = Choice.get <| dest_imp(concl kth)
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
            if is_eq(Choice.get <| rand tm)
            then split_rewrites oldhyps cf (EQF_INTRO(GSYM th)) ths
            else ths
        else split_rewrites oldhyps cf (EQT_INTRO th) sofar
    fun cf th sofar -> split_rewrites (hyp th) cf th sofar

(* ------------------------------------------------------------------------- *)
(* Rewriting (and application of other conversions) based on a convnet.      *)
(* ------------------------------------------------------------------------- *)
/// Apply a prioritized conversion net to the term at the top level.
let REWRITES_CONV net tm = 
    let pconvs = Choice.get <| lookup tm net
    try 
        tryfind (fun (_, cnv) -> Some <| cnv tm) pconvs
        |> Option.getOrFailWith "tryfind"
    with
    | Failure _ as e ->
        nestedFailwith e "REWRITES_CONV"

(* ------------------------------------------------------------------------- *)
(* Decision procedures may accumulate their state in different ways (e.g.    *)
(* term nets and predicate-indexed lists of Horn clauses). To allow mixing   *)
(* of arbitrary types for state storage, we use a trick due to RJB via DRS.  *)
(* ------------------------------------------------------------------------- *)
type prover = 
    | Prover of conv * (thm list -> prover)

/// Construct a prover from applicator and state augmentation function.
let mk_prover applicator augmentor = 
    let rec mk_prover state = 
        let apply = applicator state
        let augment thms = mk_prover(augmentor state thms)
        Prover(apply, augment)
    mk_prover

/// Augments a prover's context with new theorems.
let augment (Prover(_, aug)) thms = aug thms
/// Apply a prover to a term.
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
/// The basic prover use function used in the simplifier.
let basic_prover strat (Simpset(net, prover, provers, rewmaker) as ss) lev tm = 
    let sth = 
        strat ss lev tm
        |> Choice.bindError (fun _ -> REFL tm)
    EQT_ELIM sth
    |> Choice.bindError (fun _ ->
        let tth = 
            tryfind (fun pr -> Choice.toOption <| apply_prover pr (Choice.get <| rand(concl sth))) provers
            |> Option.toChoiceWithError "tryfind"
        EQ_MP (SYM sth) tth)

(* ------------------------------------------------------------------------- *)
(* Functions for changing or augmenting components of simpsets.              *)
(* ------------------------------------------------------------------------- *)
/// Add theorems to a simpset.
let ss_of_thms thms (Simpset(net, prover, provers, rewmaker)) = 
    let cthms = itlist rewmaker thms []
    let net' = itlist (net_of_thm true) cthms net
    Simpset(net', prover, provers, rewmaker)

/// Add a new conversion to a simpset.
let ss_of_conv keytm conv (Simpset(net, prover, provers, rewmaker)) = 
    let net' = net_of_conv keytm conv net
    Simpset(net', prover, provers, rewmaker)

/// Add congruence rules to a simpset.
let ss_of_congs thms (Simpset(net, prover, provers, rewmaker)) = 
    let net' = itlist net_of_cong thms net
    Simpset(net', prover, provers, rewmaker)

/// Change the method of prover application in a simpset.
let ss_of_prover newprover (Simpset(net, _, provers, rewmaker)) = 
    Simpset(net, newprover, provers, rewmaker)
/// Add new provers to a simpset.
let ss_of_provers newprovers (Simpset(net, prover, provers, rewmaker)) = 
    Simpset(net, prover, newprovers @ provers, rewmaker)
/// Change the rewrite maker in a simpset.
let ss_of_maker newmaker (Simpset(net, prover, provers, _)) = 
    Simpset(net, prover, provers, newmaker)

(* ------------------------------------------------------------------------- *)
(* Perform a context-augmentation operation on a simpset.                    *)
(* ------------------------------------------------------------------------- *)
/// Augment context of a simpset with a list of theorems.
let AUGMENT_SIMPSET cth (Simpset(net, prover, provers, rewmaker)) = 
    let provers' = map (C augment [cth]) provers
    let cthms = rewmaker cth []
    let net' = itlist (net_of_thm true) cthms net
    Simpset(net', prover, provers', rewmaker)

(* ------------------------------------------------------------------------- *)
(* Depth conversions.                                                        *)
(* ------------------------------------------------------------------------- *)
// ONCE_DEPTH_SQCONV: Applies simplification to the first suitable sub-term(s) encountered in top-down order.
// DEPTH_SQCONV: Applies simplification repeatedly to all the sub-terms of a term, in bottom-up order.
// REDEPTH_SQCONV: Applies simplification bottom-up to all subterms, retraversing changed ones.
// TOP_DEPTH_SQCONV: Applies simplification top-down to all subterms, retraversing changed ones.
// TOP_SWEEP_SQCONV: Applies simplification top-down at all levels, but after descending to subterms, does not return to higher ones.
let ONCE_DEPTH_SQCONV, DEPTH_SQCONV, REDEPTH_SQCONV, TOP_DEPTH_SQCONV, TOP_SWEEP_SQCONV = 
    let IMP_REWRITES_CONV strat (Simpset(net, prover, provers, rewmaker) as ss) 
        lev pconvs tm = 
        tryfind (fun (n, cnv) -> 
                if n >= 4
                then None
                else 
                    let th = cnv tm
                    let etm = concl th
                    if is_eq etm
                    then Choice.toOption th
                    elif lev <= 0
                    then None
                    else 
                        let cth = prover strat ss (lev - 1) (lhand etm)
                        Choice.toOption <| MP th cth) pconvs
        |> Option.toChoiceWithError "IMP_REWRITES_CONV: Too deep"

    let rec RUN_SUB_CONV strat ss lev triv th = 
        let tm = concl th
        if is_imp tm
        then 
            let subtm = lhand tm
            let avs, bod = strip_forall subtm
            let (t, t'), ss', mk_fun = 
                try 
                    Choice.get <| dest_eq bod, ss, I
                with
                | Failure _ -> 
                    let cxt, deq = Choice.get <| dest_imp bod
                    Choice.get <| dest_eq deq, AUGMENT_SIMPSET (ASSUME cxt) ss, DISCH cxt
            let eth, triv' = 
                try 
                    strat ss' lev t, false
                with
                | Failure _ -> REFL t, triv
            let eth' = GENL avs (mk_fun eth)
            let th' = 
                if is_var t'
                then INST [Choice.get <| rand(concl eth), t'] th
                else GEN_PART_MATCH lhand th (concl eth')
            let th'' = MP th' eth'
            RUN_SUB_CONV strat ss lev triv' th''
        elif triv
        then fail()
        else th
    let GEN_SUB_CONV strat ss lev pconvs tm = 
        let v = 
            tryfind (fun (n, cnv) -> 
                    if n < 4
                    then None
                    else 
                        let th = cnv tm
                        Choice.toOption <| RUN_SUB_CONV strat ss lev true th) pconvs
            |> Option.toChoiceWithError "tryfind"
        v |> Choice.bindError (fun _ ->
                if is_comb tm
                then 
                    let l, r = Choice.get <| dest_comb tm
                    let v = 
                        let th1 = strat ss lev l
                        let v = 
                            let th2 = strat ss lev r
                            MK_COMB(th1, th2)
                        v |> Choice.bindError (fun _ -> AP_THM th1 r)
                    v |> Choice.bindError (fun _ -> AP_TERM l (strat ss lev r))
                elif is_abs tm
                then 
                    let v, bod = Choice.get <| dest_abs tm
                    let th = strat ss lev bod
                    let v' = 
                        ABS v th
                    v' |> Choice.bindError (fun _ ->
                            let gv = genvar(Choice.get <| type_of v)
                            let gbod = Choice.get <| vsubst [gv, v] bod
                            let gth = ABS gv (strat ss lev gbod)
                            let gtm = concl gth
                            let l, r = Choice.get <| dest_eq gtm
                            let v' = Choice.get <| variant (frees gtm) v
                            let l' = Choice.get <| alpha v' l
                            let r' = Choice.get <| alpha v' r
                            EQ_MP (ALPHA gtm (Choice.get <| mk_eq(l', r'))) gth)
                else Choice.failwith "GEN_SUB_CONV")

    let rec ONCE_DEPTH_SQCONV (Simpset(net, prover, provers, rewmaker) as ss) 
            lev tm = 
        let pconvs = Choice.get <| lookup tm net
        try 
            IMP_REWRITES_CONV ONCE_DEPTH_SQCONV ss lev pconvs tm
        with
        | Failure _ -> GEN_SUB_CONV ONCE_DEPTH_SQCONV ss lev pconvs tm
    let rec DEPTH_SQCONV (Simpset(net, prover, provers, rewmaker) as ss) lev tm = 
        let pconvs = Choice.get <| lookup tm net
        try 
            let th1 = GEN_SUB_CONV DEPTH_SQCONV ss lev pconvs tm
            let tm1 = Choice.get <| rand(concl th1)
            let pconvs1 = Choice.get <| lookup tm1 net
            try 
                TRANS th1 (IMP_REWRITES_CONV DEPTH_SQCONV ss lev pconvs1 tm1)
            with
            | Failure _ -> th1
        with
        | Failure _ -> IMP_REWRITES_CONV DEPTH_SQCONV ss lev pconvs tm
    let rec REDEPTH_SQCONV (Simpset(net, prover, provers, rewmaker) as ss) lev 
            tm = 
        let pconvs = Choice.get <| lookup tm net
        let th = 
            try 
                let th1 = GEN_SUB_CONV REDEPTH_SQCONV ss lev pconvs tm
                let tm1 = Choice.get <| rand(concl th1)
                let pconvs1 = Choice.get <| lookup tm1 net
                try 
                    TRANS th1 
                        (IMP_REWRITES_CONV REDEPTH_SQCONV ss lev pconvs1 tm1)
                with
                | Failure _ -> th1
            with
            | Failure _ -> IMP_REWRITES_CONV REDEPTH_SQCONV ss lev pconvs tm
        try 
            let th' = REDEPTH_SQCONV ss lev (Choice.get <| rand(concl th))
            TRANS th th'
        with
        | Failure _ -> th
    let rec TOP_DEPTH_SQCONV (Simpset(net, prover, provers, rewmaker) as ss) lev 
            tm = 
        let pconvs = Choice.get <| lookup tm net
        let th1 = 
            try 
                IMP_REWRITES_CONV TOP_DEPTH_SQCONV ss lev pconvs tm
            with
            | Failure _ -> GEN_SUB_CONV TOP_DEPTH_SQCONV ss lev pconvs tm
        try 
            let th2 = TOP_DEPTH_SQCONV ss lev (Choice.get <| rand(concl th1))
            TRANS th1 th2
        with
        | Failure _ -> th1
    let rec TOP_SWEEP_SQCONV (Simpset(net, prover, provers, rewmaker) as ss) lev 
            tm = 
        let pconvs = Choice.get <| lookup tm net
        try 
            let th1 = IMP_REWRITES_CONV TOP_SWEEP_SQCONV ss lev pconvs tm
            try 
                let th2 = TOP_SWEEP_SQCONV ss lev (Choice.get <| rand(concl th1))
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
// set_basic_rewrites: Assign the set of default rewrites used by rewriting and simplification.
// extend_basic_rewrites: Extend the set of default rewrites used by rewriting and simplification.
// basic_rewrites: Returns the set of built-in theorems used, by default, in rewriting.
// set_basic_convs: Assign the set of default conversions.
// extend_basic_convs: Extend the set of default conversions used by rewriting and simplification.
// basic_convs: List the current default conversions used in rewriting and simplification.
// basic_net: Returns the term net used to optimize access to default rewrites and conversions.
let set_basic_rewrites, extend_basic_rewrites, basic_rewrites, set_basic_convs, extend_basic_convs, basic_convs, basic_net = 
    let rewrites = ref([] : thm list)
    let conversions = ref ([] : (string * (term * conv)) list)
    let conv_net = ref(empty_net : gconv net)
    let rehash_convnet() = 
        conv_net := itlist (net_of_thm true) (!rewrites) 
               (itlist (fun (_, (pat,cnv)) -> net_of_conv pat cnv) (!conversions) 
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
// set_basic_congs: Change the set of basic congruences used by the simplifier.
// extend_basic_congs: Extends the set of congruence rules used by the simplifier.
// basic_congs: Lists the congruence rules used by the simplifier.
let set_basic_congs, extend_basic_congs, basic_congs = 
    let congs = ref([] : thm list)
    (fun thl -> congs := thl), 
    (fun thl -> congs := union' equals_thm thl (!congs)), (fun () -> !congs)

(* ------------------------------------------------------------------------- *)
(* Main rewriting conversions.                                               *)
(* ------------------------------------------------------------------------- *)
/// Rewrite with theorems as well as an existing net.
let GENERAL_REWRITE_CONV rep (cnvl : conv -> conv) (builtin_net : gconv net) thl = 
    let thl_canon = itlist (mk_rewrites false) thl []
    let final_net = itlist (net_of_thm rep) thl_canon builtin_net
    cnvl(REWRITES_CONV final_net)

/// Rewrites a term, selecting terms according to a user-specified strategy.
let GEN_REWRITE_CONV (cnvl : conv -> conv) thl = 
    GENERAL_REWRITE_CONV false cnvl empty_net thl
/// Rewrites a term with only the given list of rewrites.
let PURE_REWRITE_CONV thl = 
    GENERAL_REWRITE_CONV true TOP_DEPTH_CONV empty_net thl
/// Rewrites a term including built-in tautologies in the list of rewrites.
let REWRITE_CONV thl = 
    GENERAL_REWRITE_CONV true TOP_DEPTH_CONV (basic_net()) thl
/// Rewrites a term once with only the given list of rewrites.
let PURE_ONCE_REWRITE_CONV thl = 
    GENERAL_REWRITE_CONV false ONCE_DEPTH_CONV empty_net thl
/// Rewrites a term, including built-in tautologies in the list of rewrites.
let ONCE_REWRITE_CONV thl = 
    GENERAL_REWRITE_CONV false ONCE_DEPTH_CONV (basic_net()) thl

(* ------------------------------------------------------------------------- *)
(* Rewriting rules and tactics.                                              *)
(* ------------------------------------------------------------------------- *)
/// Rewrites a theorem, selecting terms according to a user-specified strategy.
let GEN_REWRITE_RULE cnvl thl = CONV_RULE(GEN_REWRITE_CONV cnvl thl)

/// Rewrites a theorem with only the given list of rewrites.
let PURE_REWRITE_RULE thl = CONV_RULE(PURE_REWRITE_CONV thl)
/// Rewrites a theorem including built-in tautologies in the list of rewrites.
let REWRITE_RULE thl = CONV_RULE(REWRITE_CONV thl)
/// Rewrites a theorem once with only the given list of rewrites.
let PURE_ONCE_REWRITE_RULE thl = CONV_RULE(PURE_ONCE_REWRITE_CONV thl)
/// Rewrites a theorem, including built-in tautologies in the list of rewrites.
let ONCE_REWRITE_RULE thl = CONV_RULE(ONCE_REWRITE_CONV thl)
/// Rewrites a theorem including the theorem's assumptions as rewrites.
let PURE_ASM_REWRITE_RULE thl th = 
    PURE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
/// Rewrites a theorem including built-in rewrites and the theorem's assumptions.
let ASM_REWRITE_RULE thl th = REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
/// Rewrites a theorem once, including the theorem's assumptions as rewrites.
let PURE_ONCE_ASM_REWRITE_RULE thl th = 
    PURE_ONCE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
let ONCE_ASM_REWRITE_RULE thl th = 
    ONCE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
/// Rewrites a goal, selecting terms according to a user-specified strategy.
let GEN_REWRITE_TAC cnvl thl = CONV_TAC(GEN_REWRITE_CONV cnvl thl)
/// Rewrites a goal with only the given list of rewrites.
let PURE_REWRITE_TAC thl = CONV_TAC(PURE_REWRITE_CONV thl)
/// Rewrites a goal including built-in tautologies in the list of rewrites.
let REWRITE_TAC thl = CONV_TAC(REWRITE_CONV thl)
/// Rewrites a goal using a supplied list of theorems, making one rewriting pass over the goal.
let PURE_ONCE_REWRITE_TAC thl = CONV_TAC(PURE_ONCE_REWRITE_CONV thl)
/// Rewrites a goal only once with basic_rewrites and the supplied list of theorems.
let ONCE_REWRITE_TAC thl = CONV_TAC(ONCE_REWRITE_CONV thl)
/// Rewrites a goal including the goal's assumptions as rewrites.
let (PURE_ASM_REWRITE_TAC : thm list -> tactic) = ASM PURE_REWRITE_TAC
/// Rewrites a goal including built-in rewrites and the goal's assumptions.
let (ASM_REWRITE_TAC : thm list -> tactic) = ASM REWRITE_TAC
/// Rewrites a goal once, including the goal's assumptions as rewrites.
let (PURE_ONCE_ASM_REWRITE_TAC : thm list -> tactic) = ASM PURE_ONCE_REWRITE_TAC
/// Rewrites a goal once including built-in rewrites and the goal's assumptions.
let (ONCE_ASM_REWRITE_TAC : thm list -> tactic) = ASM ONCE_REWRITE_TAC

(* ------------------------------------------------------------------------- *)
(* Simplification functions.                                                 *)
(* ------------------------------------------------------------------------- *)
/// General simplification with given strategy and simpset and theorems.
let GEN_SIMPLIFY_CONV (strat : strategy) ss lev thl = 
    let ss' = itlist AUGMENT_SIMPSET thl ss
    TRY_CONV(strat ss' lev)

/// General top-level simplification with arbitrary simpset.
let ONCE_SIMPLIFY_CONV ss = GEN_SIMPLIFY_CONV ONCE_DEPTH_SQCONV ss 1
/// General simplification at depth with arbitrary simpset.
let SIMPLIFY_CONV ss = GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV ss 3

(* ------------------------------------------------------------------------- *)
(* Simple but useful default version.                                        *)
(* ------------------------------------------------------------------------- *)
/// Simpset consisting of only the default rewrites and conversions.
let empty_ss = Simpset(empty_net, basic_prover, [], mk_rewrites true)

/// Construct a straightforward simpset from a list of theorems.
let basic_ss = 
    let rewmaker = mk_rewrites true
    fun thl -> 
        let cthms = itlist rewmaker thl []
        let net' = itlist (net_of_thm true) cthms (basic_net())
        let net'' = itlist net_of_cong (basic_congs()) net'
        Simpset(net'', basic_prover, [], rewmaker)

/// Simplify a term repeatedly by conditional contextual rewriting.
let SIMP_CONV thl = SIMPLIFY_CONV (basic_ss []) thl
/// Simplify a term repeatedly by conditional contextual rewriting, not using default simplications.
let PURE_SIMP_CONV thl = SIMPLIFY_CONV empty_ss thl
/// Simplify a term once by conditional contextual rewriting.
let ONCE_SIMP_CONV thl = ONCE_SIMPLIFY_CONV (basic_ss []) thl
/// Simplify conclusion of a theorem repeatedly by conditional contextual rewriting.
let SIMP_RULE thl = CONV_RULE(SIMP_CONV thl)
/// Simplify conclusion of a theorem repeatedly by conditional contextual rewriting, not using default simplifications.
let PURE_SIMP_RULE thl = CONV_RULE(PURE_SIMP_CONV thl)
/// Simplify conclusion of a theorem once by conditional contextual rewriting.
let ONCE_SIMP_RULE thl = CONV_RULE(ONCE_SIMP_CONV thl)
/// Simplify a goal repeatedly by conditional contextual rewriting.
let SIMP_TAC thl = CONV_TAC(SIMP_CONV thl)
/// Simplify a goal repeatedly by conditional contextual rewriting without default simplifications.
let PURE_SIMP_TAC thl = CONV_TAC(PURE_SIMP_CONV thl)
/// Simplify conclusion of goal once by conditional contextual rewriting.
let ONCE_SIMP_TAC thl = CONV_TAC(ONCE_SIMP_CONV thl)
/// Perform simplification of goal by conditional contextual rewriting using assumptions and
/// built-in simplifications.
let ASM_SIMP_TAC = ASM SIMP_TAC
/// Perform simplification of goal by conditional contextual rewriting using assumptions.
let PURE_ASM_SIMP_TAC = ASM PURE_SIMP_TAC
/// Simplify toplevel applicable terms in goal using assumptions and context.
let ONCE_ASM_SIMP_TAC = ASM ONCE_SIMP_TAC

(* ------------------------------------------------------------------------- *)
(* Abbreviation tactics.                                                     *)
(* ------------------------------------------------------------------------- *)
/// Tactic to introduce an abbreviation.
let ABBREV_TAC tm = 
    let cvs, t = Choice.get <| dest_eq tm
    let v, vs = strip_comb cvs
    let rs = list_mk_abs(vs, t)
    let eq = Choice.get <| mk_eq(rs, v)
    let th1 = 
        itlist (fun v th -> CONV_RULE (LAND_CONV BETA_CONV) (AP_THM th v)) 
            (rev vs) (ASSUME eq)
    let th2 = SIMPLE_CHOOSE v (SIMPLE_EXISTS v (GENL vs th1))
    let th3 = PROVE_HYP (EXISTS (mk_exists(v, eq), rs) (REFL rs)) th2
    fun (asl, w as gl) -> 
            let avoids = itlist (union << frees << concl << snd) asl (frees w)
            if mem v avoids
            then failwith "ABBREV_TAC: variable already used"
            else 
                CHOOSE_THEN (fun th -> 
                        RULE_ASSUM_TAC(PURE_ONCE_REWRITE_RULE [th])
                        |> THEN <| PURE_ONCE_REWRITE_TAC [th]
                        |> THEN <| ASSUME_TAC th) th3 gl

/// Expand an abbreviation in the hypotheses.
let EXPAND_TAC s = FIRST_ASSUM
                       (SUBST1_TAC << SYM 
                        << check((=) s << fst << Choice.get << dest_var << rhs << concl))
                   |> THEN <| BETA_TAC
