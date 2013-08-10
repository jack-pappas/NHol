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
/// Basic rewriting and simplification tools.
module NHol.simp

open System

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
#endif

logger.Trace("Entering simp.fs")

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
let IMP_REWR_CONV = PART_MATCH (Choice.bind lhs << Choice.map snd << dest_imp)

(* ------------------------------------------------------------------------- *)
(* Versions with ordered rewriting. We must have l' > r' for the rewrite     *)
(* |- l = r (or |- c ==> (l = r)) to apply.                                  *)
(* ------------------------------------------------------------------------- *)

/// Basic rewriting conversion restricted by term order.
let ORDERED_REWR_CONV ord th : term -> Protected<_> = 
    let basic_conv = REWR_CONV th
    fun tm -> 
        choice {
            let thm = basic_conv tm
            let! l, r = Choice.bind (dest_eq << concl) thm
            if ord l r then 
                return! thm
            else 
                return! Choice.failwith "ORDERED_REWR_CONV: wrong orientation"
        }

/// Basic conditional rewriting conversion restricted by term order.
let ORDERED_IMP_REWR_CONV ord th : term -> Protected<_> = 
    let basic_conv = IMP_REWR_CONV th
    fun tm -> 
        choice {
            let thm = basic_conv tm
            let! l, r = Choice.bind (Choice.bind dest_eq << rand << concl) thm
            if ord l r then 
                return! thm
            else 
                return! Choice.failwith "ORDERED_IMP_REWR_CONV: wrong orientation"
        }

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
        if l1 = [] then false
        elif l2 = [] then true
        else 
            let h1 = hd l1
            let h2 = hd l2
            ord h1 h2 || (h1 = h2 && lexify ord (tl l1) (tl l2))
    let rec dyn_order top tm1 tm2 = 
        let f1, args1 = strip_comb tm1
        let f2, args2 = strip_comb tm2
        if f1 = f2 then lexify (dyn_order f1) args1 args2
        elif f2 = top then false
        elif f1 = top then true
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
let net_of_thm rep (th : Protected<thm0>) (net : net<int * (term -> Protected<_>)>) : Protected<net<int * (term -> Protected<_>)>> =
    choice {
        let! tm = Choice.map concl th
        let! lconsts = Choice.map (freesl << hyp) th
        let matchable x y = Choice.isResult <| term_match lconsts x y
        match tm with
        | Comb(Comb(Const("=", _), (Abs(x, Comb(Var(s, ty) as v, x')) as l)), v') when x' = x && v' = v && not (x = v) ->
            let conv tm =
                choice {
                    match tm with
                    | Abs(y, Comb(t, y')) when y = y' && not(free_in y t) ->
                        let! inst = term_match [] v t
                        return! INSTANTIATE inst th
                    | _ ->
                        return! Choice.failwith "REWR_CONV (ETA_AX special case)"
                }
            return! enter lconsts (l, (1, conv)) net
        | Comb(Comb(Const("=", _), l), r) ->
            if rep && free_in l r then
                let! th' = EQT_INTRO th
                return! enter lconsts (l, (1, REWR_CONV (Choice.result th'))) net
            elif rep && matchable l r && matchable r l then
                return! enter lconsts (l, (1, ORDERED_REWR_CONV term_order th)) net
            else 
                return! enter lconsts (l, (1, REWR_CONV th)) net
        | Comb(Comb(_, t), Comb(Comb(Const("=", _), l), r)) -> 
            if rep && free_in l r then
                let th' = DISCH t (EQT_INTRO(UNDISCH th))
                return! enter lconsts (l, (3, IMP_REWR_CONV th')) net
            elif rep && matchable l r && matchable r l then
                return! enter lconsts (l, (3, ORDERED_IMP_REWR_CONV term_order th)) net
            else
                return! enter lconsts (l, (3, IMP_REWR_CONV th)) net
        | _ ->
            return! Choice.failwith "net_of_thm: Unhandled case."
    }

(* ------------------------------------------------------------------------- *)
(* Create a gconv net for a conversion with a term index.                    *)
(* ------------------------------------------------------------------------- *)

// TODO : Add brief synopsis from hol-light reference manual.
let net_of_conv tm conv sofar = enter [] (tm, (2, conv)) sofar

(* ------------------------------------------------------------------------- *)
(* Create a gconv net for a congruence rule (in canonical form!)             *)
(* ------------------------------------------------------------------------- *)

/// Add a congruence rule to a net.
let net_of_cong (th : Protected<thm0>) sofar : Protected<_> =
    choice {
        let! tm = Choice.map concl th
        let conc, n = repeat (fun (tm, m) -> 
                        match dest_imp tm with
                        | Success (_, tm') -> Some (tm', m + 1)
                        | Error _ -> None) (tm, 0)
        if n = 0 then 
            return! Choice.failwith "net_of_cong: Non-implicational congruence"
        else 
            let! pat = lhs conc
            let conv = GEN_PART_MATCH (Choice.bind lhand << Choice.funpow n rand) th
            return! enter [] (pat, (4, conv)) sofar
    }

(* ------------------------------------------------------------------------- *)
(* Rewrite maker for ordinary and conditional rewrites (via "cf" flag).      *)
(*                                                                           *)
(* We follow Don in going from ~(s = t) to (s = t) = F *and* (t = s) = F.    *)
(* Well, why not? However, we don't abandon s = t where FV(t) is not a       *)
(* subset of FV(s) in favour of (s = t) = T, as he does.                     *)
(* Note: looping rewrites are not discarded here, only when netted.          *)
(* ------------------------------------------------------------------------- *)

/// Turn theorem into list of (conditional) rewrites.
let mk_rewrites : _ -> _ -> _ -> Protected<_> = 
    let IMP_CONJ_CONV = 
        REWR_CONV(ITAUT(parse_term @"p ==> q ==> r <=> p /\ q ==> r"))
    let IMP_EXISTS_RULE = 
        let cnv = 
            REWR_CONV(ITAUT(parse_term @"(!x. P x ==> Q) <=> (?x. P x) ==> Q"))
        fun v th -> CONV_RULE cnv (GEN v th)

    let collect_condition oldhyps (th : Protected<_>) : Protected<_> =
        choice {
        let! th = th
        let tms = hyp th
        let conds = subtract tms oldhyps
        if List.isEmpty conds then 
            return th
        else 
            let jth = itlist DISCH conds (Choice.result th)
            let! kth = CONV_RULE (REPEATC IMP_CONJ_CONV) jth
            let tms' = concl kth
            let! cond, eqn = dest_imp tms'
            let fvs = subtract (subtract (frees cond) (frees eqn)) (freesl oldhyps)
            return!
                let kth = Choice.result kth in
                itlist IMP_EXISTS_RULE fvs kth
        }

    let rec split_rewrites oldhyps cf th sofar : Protected<Protected<thm0> list> = 
        choice {
            let tm = concl th
            if is_forall tm then
                let! th' = SPEC_ALL (Choice.result th)
                return! split_rewrites oldhyps cf th' sofar
            elif is_conj tm then
                let! th' = CONJUNCT2 (Choice.result th)
                let! right = split_rewrites oldhyps cf th' sofar
                let! th'' = CONJUNCT1 (Choice.result th)
                return! split_rewrites oldhyps cf th'' right
            elif is_imp tm && cf then
                let! th' = UNDISCH (Choice.result th)
                return! split_rewrites oldhyps cf th' sofar
            elif is_eq tm then
                let! v =
                    choice {
                    if cf then
                        return! collect_condition oldhyps (Choice.result th)
                    else return th }
                return (Choice.result v) :: sofar
            elif is_neg tm then
                let! th' = EQF_INTRO (Choice.result th)
                let! ths = split_rewrites oldhyps cf th' sofar
                let! tm1 = rand tm
                if is_eq tm1 then
                    let! th' = EQF_INTRO(GSYM (Choice.result th))
                    return! split_rewrites oldhyps cf th' ths
                else
                    return ths
            else
                let! th' = EQT_INTRO (Choice.result th)
                return! split_rewrites oldhyps cf th' sofar
        }

    fun cf (th : Protected<thm0>) (sofar : Protected<thm0> list) ->
        choice {
        let! th = th
        let ts = hyp th
        return! split_rewrites ts cf th sofar
        }

(* ------------------------------------------------------------------------- *)
(* Rewriting (and application of other conversions) based on a convnet.      *)
(* ------------------------------------------------------------------------- *)

/// Apply a prioritized conversion net to the term at the top level.
let REWRITES_CONV (net : net<int * (term -> Choice<'T, exn>)>) tm =
    choice {
        let! pconvs = lookup tm net
        match tryfind (fun (_, cnv) -> Choice.toOption <| cnv tm) pconvs with
        | Some result ->
            return result
        | None ->
            return!
                Choice.failwith "tryfind"
                |> Choice.mapError (fun e ->
                    nestedFailure e "REWRITES_CONV")
    }

(* ------------------------------------------------------------------------- *)
(* Decision procedures may accumulate their state in different ways (e.g.    *)
(* term nets and predicate-indexed lists of Horn clauses). To allow mixing   *)
(* of arbitrary types for state storage, we use a trick due to RJB via DRS.  *)
(* ------------------------------------------------------------------------- *)

type prover = 
    | Prover of conv * (Protected<thm0> list -> prover)

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
    | Simpset of gconv net * (strategy -> strategy) * prover list * (Protected<thm0> -> Protected<thm0> list -> Protected<Protected<thm0> list>)

(* Rewrites & congruences *)
(* Prover for conditions  *)
(* Subprovers for prover  *)
(* Rewrite maker          *)
and strategy = simpset -> int -> term -> Protected<thm0>

(* ------------------------------------------------------------------------- *)
(* Very simple prover: recursively simplify then try provers.                *)
(* ------------------------------------------------------------------------- *)

/// The basic prover use function used in the simplifier.
let basic_prover (strat : strategy) (Simpset(net, prover, provers, rewmaker) as ss) lev tm : Protected<thm0> = 
    let sth = 
        strat ss lev tm
        |> Choice.bindError (function Failure _ -> REFL tm | e -> Choice.error e)
    EQT_ELIM sth
    |> Choice.bindError (function
        | Failure _ ->
            choice {
                let! tm = Choice.bind (rand << concl)  sth
                let tth = 
                    tryfind (fun pr -> Choice.toOption <| apply_prover pr tm) provers
                    |> Option.toChoiceWithError "tryfind"
                return! EQ_MP (SYM sth) tth
                }
        | e -> Choice.error e)

(* ------------------------------------------------------------------------- *)
(* Functions for changing or augmenting components of simpsets.              *)
(* ------------------------------------------------------------------------- *)

/// Add theorems to a simpset.
let ss_of_thms thms (Simpset(net, prover, provers, rewmaker)) = 
    choice {
        let! cthms = Choice.List.fold (fun acc x -> rewmaker x acc) [] thms
        let! net' = Choice.List.fold (fun acc x -> net_of_thm true x acc) net cthms
        return Simpset(net', prover, provers, rewmaker)
    }

/// Add a new conversion to a simpset.
let ss_of_conv keytm conv (Simpset(net, prover, provers, rewmaker)) = 
    choice {
        let! net' = net_of_conv keytm conv net
        return Simpset(net', prover, provers, rewmaker)
    }

/// Add congruence rules to a simpset.
let ss_of_congs thms (Simpset(net, prover, provers, rewmaker)) = 
    choice {
        let! net' = Choice.List.fold (fun acc x -> net_of_cong x acc) net thms
        return Simpset(net', prover, provers, rewmaker)
    }

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
let AUGMENT_SIMPSET (cth : Protected<thm0>) (Simpset(net, prover, provers, rewmaker)) = 
    choice {
        let provers' = map (C augment [cth]) provers
        let! cthms = rewmaker cth []
        let! net' = Choice.List.fold (fun acc x -> net_of_thm true x acc) net cthms
        return Simpset(net', prover, provers', rewmaker)
    }

(* ------------------------------------------------------------------------- *)
(* Depth conversions.                                                        *)
(* ------------------------------------------------------------------------- *)

// ONCE_DEPTH_SQCONV: Applies simplification to the first suitable sub-term(s) encountered in top-down order.
// DEPTH_SQCONV: Applies simplification repeatedly to all the sub-terms of a term, in bottom-up order.
// REDEPTH_SQCONV: Applies simplification bottom-up to all subterms, retraversing changed ones.
// TOP_DEPTH_SQCONV: Applies simplification top-down to all subterms, retraversing changed ones.
// TOP_SWEEP_SQCONV: Applies simplification top-down at all levels, but after descending to subterms, does not return to higher ones.
let ONCE_DEPTH_SQCONV, DEPTH_SQCONV, REDEPTH_SQCONV, TOP_DEPTH_SQCONV, TOP_SWEEP_SQCONV = 
    let IMP_REWRITES_CONV strat (Simpset(net, prover, provers, rewmaker) as ss) lev pconvs tm = 
        pconvs
        |> tryfind (fun (n, cnv) -> 
                if n >= 4 then 
                    None
                else 
                    let th = cnv tm
                    match Choice.map concl th with
                    | Success etm ->
                        if is_eq etm then 
                            Choice.toOption th
                        elif lev <= 0 then 
                            None
                        else
                            match lhand etm with
                            | Success tm' ->
                                let cth = prover strat ss (lev - 1) tm'
                                Choice.toOption <| MP th cth
                            | Error _ -> None
                    | Error _ -> None)
        |> Option.toChoiceWithError "IMP_REWRITES_CONV: Too deep"

    let rec RUN_SUB_CONV strat ss lev triv th = 
        choice {
            let! th = th
            let tm = concl th
            if is_imp tm then 
                let! subtm = lhand tm
                let avs, bod = strip_forall subtm
                let! (t, t'), ss', mk_fun =
                    choice {
                    match dest_eq bod with
                    | Success t_pair ->
                        return t_pair, ss, I
                    | Error _ ->
                        match dest_imp bod with
                        | Success (cxt, deq) ->
                            let! tm' = dest_eq deq
                            let! cth = ASSUME cxt
                            let! ss' = AUGMENT_SIMPSET (Choice.result cth) ss
                            return tm', ss', DISCH cxt
                        | Error ex ->
                            return! Choice.error ex
                    }
                
                let! eth, triv' =
                    choice {
                    match strat ss' lev t with
                    | Success st ->
                        return Choice.result st, false
                    | Error _ -> 
                        return REFL t, triv
                    }
                let! eth = eth
                let! eth' = GENL avs (mk_fun (Choice.result eth))
                
                let! th' =
                    choice {
                    if is_var t' then
                        let! tm1 = rand <| concl eth
                        return! INST [tm1, t'] (Choice.result th)
                    else
                        let tm2 = concl eth'
                        return! GEN_PART_MATCH lhand (Choice.result th) tm2
                    }
                let th'' = MP (Choice.result th') (Choice.result eth')
                return! RUN_SUB_CONV strat ss lev triv' th''
            elif triv then
                return! Choice.fail()
            else 
                return th
        }

    let GEN_SUB_CONV strat ss lev pconvs tm = 
        tryfind (fun (n, cnv) -> 
            if n < 4 then None
            else 
                let th = cnv tm
                Choice.toOption <| RUN_SUB_CONV strat ss lev true th) pconvs
        |> Option.toChoiceWithError "tryfind"
        |> Choice.bindError (fun _ ->
            choice {
                if is_comb tm then 
                    let! l, r = dest_comb tm
                    let v = 
                        let th1 = strat ss lev l
                        let v' = 
                            let th2 = strat ss lev r
                            MK_COMB(th1, th2)
                        v' |> Choice.bindError (fun _ -> AP_THM th1 r)
                    return! v |> Choice.bindError (fun _ -> AP_TERM l (strat ss lev r))
                elif is_abs tm then 
                    let! v, bod = dest_abs tm
                    let th = strat ss lev bod
                    let v' = ABS v th
                    return! v' |> Choice.bindError (fun _ ->
                                    choice {
                                        let! ty = type_of v
                                        let gv = genvar ty
                                        let! gbod = vsubst [gv, v] bod
                                        let gth = ABS gv (strat ss lev gbod)
                                        let! gtm = Choice.map concl gth
                                        let! l, r = dest_eq gtm
                                        let! v' = variant (frees gtm) v
                                        let! l' = alpha v' l
                                        let! r' = alpha v' r
                                        let! tm' = mk_eq(l', r')
                                        return! EQ_MP (ALPHA gtm tm') gth
                                    })
                else 
                    return! Choice.failwith "GEN_SUB_CONV"
            })

    let rec ONCE_DEPTH_SQCONV (Simpset(net, prover, provers, rewmaker) as ss) lev tm : Protected<thm0> = 
        choice {
            let! pconvs = lookup tm net
            return! IMP_REWRITES_CONV ONCE_DEPTH_SQCONV ss lev pconvs tm
                    |> Choice.bindError (fun _ -> GEN_SUB_CONV ONCE_DEPTH_SQCONV ss lev pconvs tm)
        }

    let rec DEPTH_SQCONV (Simpset(net, prover, provers, rewmaker) as ss) lev tm : Protected<thm0> = 
        choice {
            let! pconvs = lookup tm net
            let v = 
                choice {
                    let th1 = GEN_SUB_CONV DEPTH_SQCONV ss lev pconvs tm
                    let! tm1 = Choice.bind (rand << concl) th1
                    let! pconvs1 = lookup tm1 net
                    return! TRANS th1 (IMP_REWRITES_CONV DEPTH_SQCONV ss lev pconvs1 tm1)
                            |> Choice.bindError (fun _ -> th1)
                }
            return! v |> Choice.bindError (fun _ -> IMP_REWRITES_CONV DEPTH_SQCONV ss lev pconvs tm)
        }

    let rec REDEPTH_SQCONV (Simpset(net, prover, provers, rewmaker) as ss) lev tm : Protected<thm0> = 
        choice {
            let! pconvs = lookup tm net
            let th = 
                choice { 
                    let th1 = GEN_SUB_CONV REDEPTH_SQCONV ss lev pconvs tm
                    let! tm1 = Choice.bind (rand << concl) th1
                    let! pconvs1 = lookup tm1 net
                    return! TRANS th1 (IMP_REWRITES_CONV REDEPTH_SQCONV ss lev pconvs1 tm1)
                            |> Choice.bindError (fun _ -> th1)
                }
                |> Choice.bindError (fun _ -> IMP_REWRITES_CONV REDEPTH_SQCONV ss lev pconvs tm)

            let v = 
                choice {
                    let! tm' = Choice.bind (rand << concl) th
                    let th' = REDEPTH_SQCONV ss lev tm'
                    return! TRANS th th'
                }
            return! v |> Choice.bindError (fun _ -> th)
        }

    let rec TOP_DEPTH_SQCONV (Simpset(net, prover, provers, rewmaker) as ss) lev tm : Protected<thm0> = 
        choice {
            let! pconvs = lookup tm net
            let th1 = 
                IMP_REWRITES_CONV TOP_DEPTH_SQCONV ss lev pconvs tm
                |> Choice.bindError (fun _ -> GEN_SUB_CONV TOP_DEPTH_SQCONV ss lev pconvs tm)
            let v = 
                choice {
                    let! tm1 = Choice.bind (rand << concl) th1
                    let th2 = TOP_DEPTH_SQCONV ss lev tm1
                    return! TRANS th1 th2
                }
            return! v |> Choice.bindError (fun _ -> th1)
        }

    let rec TOP_SWEEP_SQCONV (Simpset(net, prover, provers, rewmaker) as ss) lev tm : Protected<thm0> = 
        choice {
            let! pconvs = lookup tm net
            let v = 
                choice {
                    let th1 = IMP_REWRITES_CONV TOP_SWEEP_SQCONV ss lev pconvs tm
                    let v' = 
                        choice {
                            let! tm1 = Choice.bind (rand << concl) th1
                            let th2 = TOP_SWEEP_SQCONV ss lev tm1
                            return! TRANS th1 th2
                        }
                    return! v' |> Choice.bindError (fun _ -> th1)
                }
            return! v |> Choice.bindError (fun _ -> GEN_SUB_CONV TOP_SWEEP_SQCONV ss lev pconvs tm)
        }

    ONCE_DEPTH_SQCONV, DEPTH_SQCONV, REDEPTH_SQCONV, TOP_DEPTH_SQCONV, TOP_SWEEP_SQCONV

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
    let rewrites : Protected<thm0> list ref = ref []
    let conversions : ((string * (term * conv)) list) ref = ref []
    let conv_net : net<gconv> ref = ref empty_net

    let rehash_convnet() =
        choice {
            let! nets = Choice.List.fold (fun acc (_, (pat,cnv)) -> net_of_conv pat cnv acc) empty_net !conversions
            let! nets2 = Choice.List.fold (fun acc x -> net_of_thm true x acc) nets !rewrites
            return conv_net := nets2
        }

    let set_basic_rewrites thl =
        choice {
            let! canon_thl = Choice.List.fold (fun acc x -> mk_rewrites false x acc) [] thl
            rewrites := canon_thl
            do! rehash_convnet()
        }

    let extend_basic_rewrites thl =
        choice {
            let! canon_thl = Choice.List.fold (fun acc x -> mk_rewrites false x acc) [] thl
            rewrites := canon_thl @ !rewrites
            do! rehash_convnet()
        }

    let basic_rewrites() = !rewrites

    let set_basic_convs cnvs =
        conversions := cnvs
        rehash_convnet()

    let extend_basic_convs(name, patcong) =
        conversions := (name, patcong) :: filter (fun (name', _) -> name <> name') !conversions
        rehash_convnet()

    let basic_convs() = !conversions
    let basic_net() = !conv_net

    set_basic_rewrites, extend_basic_rewrites, basic_rewrites, set_basic_convs, extend_basic_convs, basic_convs, basic_net

(* ------------------------------------------------------------------------- *)
(* Same thing for the default congruences.                                   *)
(* ------------------------------------------------------------------------- *)

// set_basic_congs: Change the set of basic congruences used by the simplifier.
// extend_basic_congs: Extends the set of congruence rules used by the simplifier.
// basic_congs: Lists the congruence rules used by the simplifier.
let set_basic_congs, extend_basic_congs, basic_congs =
    let congs = ref([] : thm0 list)
    (fun thl -> congs := thl),
    (fun (thl : Protected<_> list) ->
        choice {
        let! thl = Choice.List.map id thl
        let equals_thm x y =
            equals_thm (Choice.result x) (Choice.result y)
        return congs := union' equals_thm thl !congs
        }),
    (fun () -> !congs)

(* ------------------------------------------------------------------------- *)
(* Main rewriting conversions.                                               *)
(* ------------------------------------------------------------------------- *)

/// Rewrite with theorems as well as an existing net.
let GENERAL_REWRITE_CONV rep (cnvl : conv -> conv) (builtin_net : gconv net) (thl : Protected<thm0> list) : conv = 
    fun tm ->
        choice {
        let! thl_canon = Choice.List.fold (fun acc x -> mk_rewrites false x acc) [] thl
        let! final_net = Choice.List.fold (fun acc x -> net_of_thm rep x acc) builtin_net thl_canon
        let conv = REWRITES_CONV final_net
        return! cnvl conv tm
        }

/// Rewrites a term, selecting terms according to a user-specified strategy.
let GEN_REWRITE_CONV (cnvl : conv -> conv) thl : conv = 
    GENERAL_REWRITE_CONV false cnvl empty_net thl

/// Rewrites a term with only the given list of rewrites.
let PURE_REWRITE_CONV thl : conv = 
    GENERAL_REWRITE_CONV true TOP_DEPTH_CONV empty_net thl

/// Rewrites a term including built-in tautologies in the list of rewrites.
let REWRITE_CONV thl : conv = 
    GENERAL_REWRITE_CONV true TOP_DEPTH_CONV (basic_net()) thl

/// Rewrites a term once with only the given list of rewrites.
let PURE_ONCE_REWRITE_CONV thl : conv = 
    GENERAL_REWRITE_CONV false ONCE_DEPTH_CONV empty_net thl

/// Rewrites a term, including built-in tautologies in the list of rewrites.
let ONCE_REWRITE_CONV thl : conv = 
    GENERAL_REWRITE_CONV false ONCE_DEPTH_CONV (basic_net()) thl

(* ------------------------------------------------------------------------- *)
(* Rewriting rules and tactics.                                              *)
(* ------------------------------------------------------------------------- *)

/// Rewrites a theorem, selecting terms according to a user-specified strategy.
let GEN_REWRITE_RULE cnvl thl = 
    CONV_RULE (GEN_REWRITE_CONV cnvl thl)

/// Rewrites a theorem with only the given list of rewrites.
let PURE_REWRITE_RULE thl =
    CONV_RULE (PURE_REWRITE_CONV thl)

/// Rewrites a theorem including built-in tautologies in the list of rewrites.
let REWRITE_RULE thl =
    CONV_RULE (REWRITE_CONV thl)

/// Rewrites a theorem once with only the given list of rewrites.
let PURE_ONCE_REWRITE_RULE thl =
    CONV_RULE (PURE_ONCE_REWRITE_CONV thl)

/// Rewrites a theorem, including built-in tautologies in the list of rewrites.
let ONCE_REWRITE_RULE thl =
    CONV_RULE (ONCE_REWRITE_CONV thl)

/// Rewrites a theorem including the theorem's assumptions as rewrites.
let PURE_ASM_REWRITE_RULE thl (th : Protected<thm0>) =
    choice {
    let! th = th
    let tms = hyp th
    let! assumptions = Choice.List.map ASSUME tms
    let assumptions = List.map Choice.result assumptions
    return! PURE_REWRITE_RULE (assumptions @ thl) (Choice.result th)
    }

/// Rewrites a theorem including built-in rewrites and the theorem's assumptions.
let ASM_REWRITE_RULE thl (th : Protected<thm0>) = 
    choice {
    let! th = th
    let tms = hyp th
    let! assumptions = Choice.List.map ASSUME tms
    let assumptions = List.map Choice.result assumptions
    return! REWRITE_RULE (assumptions @ thl) (Choice.result th)
    }

/// Rewrites a theorem once, including the theorem's assumptions as rewrites.
let PURE_ONCE_ASM_REWRITE_RULE thl (th : Protected<thm0>) =
    choice {
    let! th = th
    let tms = hyp th
    let! assumptions = Choice.List.map ASSUME tms
    let assumptions = List.map Choice.result assumptions
    return! PURE_ONCE_REWRITE_RULE (assumptions @ thl) (Choice.result th)
    }

let ONCE_ASM_REWRITE_RULE thl (th : Protected<thm0>) = 
    choice {
    let! th = th
    let tms = hyp th
    let! assumptions = Choice.List.map ASSUME tms
    let assumptions = List.map Choice.result assumptions
    return! ONCE_REWRITE_RULE (assumptions @ thl) (Choice.result th)
    }

/// Rewrites a goal, selecting terms according to a user-specified strategy.
let GEN_REWRITE_TAC cnvl thl = 
    CONV_TAC (GEN_REWRITE_CONV cnvl thl)

/// Rewrites a goal with only the given list of rewrites.
let PURE_REWRITE_TAC thl = 
    CONV_TAC (PURE_REWRITE_CONV thl)

/// Rewrites a goal including built-in tautologies in the list of rewrites.
let REWRITE_TAC thl = 
    CONV_TAC (REWRITE_CONV thl)

/// Rewrites a goal using a supplied list of theorems, making one rewriting pass over the goal.
let PURE_ONCE_REWRITE_TAC thl = 
    CONV_TAC (PURE_ONCE_REWRITE_CONV thl)

/// Rewrites a goal only once with basic_rewrites and the supplied list of theorems.
let ONCE_REWRITE_TAC thl = 
    CONV_TAC (ONCE_REWRITE_CONV thl)

/// Rewrites a goal including the goal's assumptions as rewrites.
let (PURE_ASM_REWRITE_TAC : Protected<thm0> list -> tactic) = 
    ASM PURE_REWRITE_TAC

/// Rewrites a goal including built-in rewrites and the goal's assumptions.
let (ASM_REWRITE_TAC : Protected<thm0> list -> tactic) = 
    ASM REWRITE_TAC

/// Rewrites a goal once, including the goal's assumptions as rewrites.
let (PURE_ONCE_ASM_REWRITE_TAC : Protected<thm0> list -> tactic) = 
    ASM PURE_ONCE_REWRITE_TAC

/// Rewrites a goal once including built-in rewrites and the goal's assumptions.
let (ONCE_ASM_REWRITE_TAC : Protected<thm0> list -> tactic) = 
    ASM ONCE_REWRITE_TAC

(* ------------------------------------------------------------------------- *)
(* Simplification functions.                                                 *)
(* ------------------------------------------------------------------------- *)

/// General simplification with given strategy and simpset and theorems.
let GEN_SIMPLIFY_CONV (strat : strategy) ss lev thl =
    fun tm ->
        choice {
        let! ss' = Choice.List.fold (flip AUGMENT_SIMPSET) ss thl
        return! TRY_CONV (strat ss' lev) tm
        }

/// General top-level simplification with arbitrary simpset.
let ONCE_SIMPLIFY_CONV ss = 
    GEN_SIMPLIFY_CONV ONCE_DEPTH_SQCONV ss 1

/// General simplification at depth with arbitrary simpset.
let SIMPLIFY_CONV ss = 
    GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV ss 3

(* ------------------------------------------------------------------------- *)
(* Simple but useful default version.                                        *)
(* ------------------------------------------------------------------------- *)

/// Simpset consisting of only the default rewrites and conversions.
let empty_ss =
    Simpset(empty_net, basic_prover, [], mk_rewrites true)

/// Construct a straightforward simpset from a list of theorems.
let basic_ss = 
    let rewmaker = mk_rewrites true
    fun thl -> 
        choice {
        let! cthms = Choice.List.fold (fun acc x -> rewmaker x acc) [] thl
        let! net' = Choice.List.fold (fun acc x -> net_of_thm true x acc) (basic_net()) cthms
        let! net'' = Choice.List.fold (fun acc x -> net_of_cong x acc) net' (List.map Choice.result <| basic_congs()) 
        return Simpset(net'', basic_prover, [], rewmaker)
        }

/// Simplify a term repeatedly by conditional contextual rewriting.
let SIMP_CONV thl : conv = 
    fun tm ->
        choice {
            let! ss = basic_ss []
            return! SIMPLIFY_CONV ss thl tm
        }

/// Simplify a term repeatedly by conditional contextual rewriting, not using default simplications.
let PURE_SIMP_CONV thl = 
    SIMPLIFY_CONV empty_ss thl

/// Simplify a term once by conditional contextual rewriting.
let ONCE_SIMP_CONV thl : conv = 
    fun tm ->
        choice {
            let! ss = basic_ss []
            return! ONCE_SIMPLIFY_CONV ss thl tm
        }

/// Simplify conclusion of a theorem repeatedly by conditional contextual rewriting.
let SIMP_RULE thl = 
    CONV_RULE (SIMP_CONV thl)

/// Simplify conclusion of a theorem repeatedly by conditional contextual rewriting, not using default simplifications.
let PURE_SIMP_RULE thl = 
    CONV_RULE (PURE_SIMP_CONV thl)

/// Simplify conclusion of a theorem once by conditional contextual rewriting.
let ONCE_SIMP_RULE thl = 
    CONV_RULE (ONCE_SIMP_CONV thl)

/// Simplify a goal repeatedly by conditional contextual rewriting.
let SIMP_TAC thl = 
    CONV_TAC (SIMP_CONV thl)

/// Simplify a goal repeatedly by conditional contextual rewriting without default simplifications.
let PURE_SIMP_TAC thl = 
    CONV_TAC (PURE_SIMP_CONV thl)

/// Simplify conclusion of goal once by conditional contextual rewriting.
let ONCE_SIMP_TAC thl = 
    CONV_TAC (ONCE_SIMP_CONV thl)

/// Perform simplification of goal by conditional contextual rewriting using assumptions and
/// built-in simplifications.
let ASM_SIMP_TAC = 
    ASM SIMP_TAC

/// Perform simplification of goal by conditional contextual rewriting using assumptions.
let PURE_ASM_SIMP_TAC = 
    ASM PURE_SIMP_TAC

/// Simplify toplevel applicable terms in goal using assumptions and context.
let ONCE_ASM_SIMP_TAC = 
    ASM ONCE_SIMP_TAC

(* ------------------------------------------------------------------------- *)
(* Abbreviation tactics.                                                     *)
(* ------------------------------------------------------------------------- *)

/// Tactic to introduce an abbreviation.
let ABBREV_TAC tm : tactic =
    let v_th3 = 
        choice {
            let! cvs, t = dest_eq tm
            let v, vs = strip_comb cvs
            let! rs = list_mk_abs (vs, t)
            let! eq = mk_eq(rs, v)
            let th1 =  itlist (fun v th -> CONV_RULE (LAND_CONV BETA_CONV) (AP_THM th v)) (rev vs) (ASSUME eq)
            let th2 = SIMPLE_CHOOSE v (SIMPLE_EXISTS v (GENL vs th1))
            let! tm = mk_exists(v, eq)
            let th3 = PROVE_HYP (EXISTS (tm, rs) (REFL rs)) th2
            return (v, th3)
        }
    fun (asl, w as gl) -> 
        choice {
            let! (v, th3) = v_th3 
            let! asl' = Choice.List.map snd asl
            let avoids = itlist (union << frees << concl) asl' (frees w)
            if mem v avoids then 
                return! Choice.failwith "ABBREV_TAC: variable already used"
            else 
                return!
                    CHOOSE_THEN (fun th ->
                    RULE_ASSUM_TAC(PURE_ONCE_REWRITE_RULE [th])
                    |> THEN <| PURE_ONCE_REWRITE_TAC [th]
                    |> THEN <| ASSUME_TAC th) th3 gl
        }

/// Expand an abbreviation in the hypotheses.
let EXPAND_TAC s = 
    // NOTE: recheck this
    let f thm =
        match check ((=) (Choice.result s) << Choice.map fst << Choice.bind dest_var << Choice.bind rhs << Choice.map concl) thm with
        | Success th -> th
        | Error ex -> Choice.error ex
    FIRST_ASSUM (SUBST1_TAC << SYM << f)
    |> THEN <| BETA_TAC
