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
/// More sophisticated derived rules including definitions and rewriting.
module NHol.drule

open System

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

open ExtCore.Control
open ExtCore.Control.Collections

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
#endif

(* ------------------------------------------------------------------------- *)
(* Type of instantiations, with terms, types and higher-order data.          *)
(* ------------------------------------------------------------------------- *)

type instantiation = (int * term) list * (term * term) list * (hol_type * hol_type) list

(* ------------------------------------------------------------------------- *)
(* The last recourse when all else fails!                                    *)
(* ------------------------------------------------------------------------- *)

/// Creates an arbitrary theorem as an axiom (dangerous!)
let mk_thm(asl, c) = 
    let ax = new_axiom(itlist (curry (Choice.get << mk_imp)) (rev asl) c)
    rev_itlist (fun t th -> MP th (ASSUME t)) (rev asl) ax

(* ------------------------------------------------------------------------- *)
(* Derived congruence rules; very useful things!                             *)
(* ------------------------------------------------------------------------- *)

/// Conjoin both sides of two equational theorems.
let MK_CONJ = 
    let andtm = parse_term @"(/\)"
    fun eq1 eq2 ->
        MK_COMB(AP_TERM andtm eq1, eq2)

/// Disjoin both sides of two equational theorems.
let MK_DISJ = 
    let ortm = parse_term @"(\/)"
    fun eq1 eq2 ->
        MK_COMB(AP_TERM ortm eq1, eq2)

/// Universally quantifies both sides of equational theorem.
let MK_FORALL = 
    let atm = mk_const("!", [])
    fun v (th : Protected<thm0>) -> 
        choice {
            let! tm = atm
            let! ty = type_of v
            let! tm' = inst [ty, aty] tm
            return! AP_TERM tm' (ABS v th)
        } : Protected<thm0>

/// Existentially quantifies both sides of equational theorem.
let MK_EXISTS = 
    let atm = mk_const("?", [])
    fun v (th : Protected<thm0>) -> 
        choice {
            let! tm = atm
            let! ty = type_of v
            let! tm' = inst [ty, aty] tm
            return! AP_TERM tm' (ABS v th)
        } : Protected<thm0>

(* ------------------------------------------------------------------------- *)
(* Eliminate the antecedent of a theorem using a conversion/proof rule.      *)
(* ------------------------------------------------------------------------- *)

/// Removes antecedent of implication theorem by solving it with a conversion.
let MP_CONV (cnv : conv) (th : Protected<thm0>) : Protected<thm0> = 
    choice {
    let! th = th
    let! l, r = dest_imp <| concl th
    let ath = cnv l
    return!
        let th = Choice.result th in
        MP th (EQT_ELIM ath)
        |> Choice.bindError (fun _ -> MP th ath)
    }    

(* ------------------------------------------------------------------------- *)
(* Multiple beta-reduction (we use a slight variant below).                  *)
(* ------------------------------------------------------------------------- *)
/// Beta conversion over multiple arguments.
let rec BETAS_CONV tm : Protected<thm0> =
    match tm with
    | Comb(Abs(_, _), _) ->
        BETA_CONV tm
    | Comb(Comb(_, _), _) ->
        (RATOR_CONV(THENC BETAS_CONV BETA_CONV)) tm
    | _ ->
        Choice.failwith "BETAS_CONV"

(* ------------------------------------------------------------------------- *)
(* Instantiators.                                                            *)
(* ------------------------------------------------------------------------- *)

/// Apply a higher-order instantiation to a term.
let instantiate : instantiation -> term -> Protected<term> = 
    let betas n tm =
        choice {
        let! (tms1, tm2) =
            ([], tm)
            |> Choice.funpow n (fun (l, t) ->
                choice {
                let! rand_t = rand t
                let! rator_t = rator t
                return rand_t :: l, rator_t
                })
        
        return!
            // TODO : This one is originally rev_itlist. 
            // We should validate the order of arguments.
            (tm2, tms1)
            ||> Choice.List.fold (fun l a ->
                choice {
                let! v, b = dest_abs l
                return! vsubst [a, v] b
                })
        }

    let rec ho_betas bcs pat tm =
        if is_var pat || is_const pat then
            Choice.fail ()
        else
            choice {
            let! bv, bod = dest_abs tm
            let! body_pat = body pat
            // CLEAN : Rename this value to something sensible.
            let! foo1 = ho_betas bcs body_pat bod
            return! mk_abs(bv, foo1)
            }
            |> Choice.bindError (fun _ ->
                let hop, args = strip_comb pat
                match rev_assoc hop bcs with
                | Some n when length args = n ->
                    betas n tm
                | _ ->
                    // CLEAN : This should be reworked to simplify the code.
                    match dest_comb pat with
                    | Error error ->
                        Choice.error error
                    | Success (lpat, rpat) ->
                        match dest_comb tm with
                        | Error error ->
                            Choice.error error
                        | Success (ltm, rtm) ->
                            match ho_betas bcs lpat ltm with
                            | Success lth ->
                                match ho_betas bcs rpat rtm with
                                | Success rth ->
                                    mk_comb(lth, rth)
                                | Error _ ->
                                    mk_comb(lth, rtm)
                            | Error _ ->
                                match ho_betas bcs rpat rtm with
                                | Success rth ->
                                    mk_comb(ltm, rth)
                                | Error error ->
                                    Choice.error error)

    fun (bcs, tmin, tyin) tm ->
        choice {
        let! itm =
            choice {
            if List.isEmpty tyin then
                return tm
            else
                return! inst tyin tm }

        if List.isEmpty tmin then
            return itm
        else
            let! ttm = vsubst tmin itm
            if List.isEmpty bcs then
                return ttm
            else
                return!
                    ho_betas bcs itm ttm
                    |> Choice.bindError (fun _ ->
                        Choice.result ttm)
        }

/// Apply a higher-order instantiation to conclusion of a theorem.
let INSTANTIATE : instantiation -> Protected<thm0> -> Protected<thm0> = 
    let rec BETAS_CONV n tm = 
        if n = 1 then
            TRY_CONV BETA_CONV tm
        else
            THENC (RATOR_CONV(BETAS_CONV(n - 1))) (TRY_CONV BETA_CONV) tm

    let rec HO_BETAS bcs pat tm =
        if is_var pat || is_const pat then
            Choice.fail ()
        else 
            choice {
                let! bv, bod = dest_abs tm
                let! tm' = body pat
                return! ABS bv (HO_BETAS bcs tm' bod)
            }
            |> Choice.bindError (fun _ ->
                let hop, args = strip_comb pat
                rev_assoc hop bcs
                |> Option.toChoiceWithError "find"
                |> Choice.bind (fun n ->
                    if length args = n then
                        BETAS_CONV n tm
                    else
                        Choice.fail ())
                |> Choice.bindError (fun _ ->
                    choice {
                        let! lpat, rpat = dest_comb pat
                        let! ltm, rtm = dest_comb tm
                        
                        let! lth = HO_BETAS bcs lpat ltm
                        let! rth = HO_BETAS bcs rpat rtm
                        return!
                            let lth = Choice.result lth in
                            let rth = Choice.result rth in
                            MK_COMB(lth, rth)
                            |> Choice.bindError (fun _ ->
                                AP_THM lth rtm)
                            |> Choice.bindError (fun _ ->
                                choice {
                                let! rth = HO_BETAS bcs rpat rtm
                                return! AP_TERM ltm (Choice.result rth)
                                })
                    }))

    fun (bcs, tmin, tyin) th ->
        choice {
        let! th = th
        let! ith =
            choice {
            if List.isEmpty tyin then
                return th
            else
                return! INST_TYPE tyin (Choice.result th) }

        if List.isEmpty tmin then
            return ith
        else
            let! tth = INST tmin (Choice.result ith)
            let tl1 = hyp tth
            let tl2 = hyp th

            if tl1 = tl2 then
                if List.isEmpty bcs then
                    return tth
                else
                    let itm = concl ith
                    let ttm = concl tth
                    let! eth = HO_BETAS bcs itm ttm
                    return!
                        let eth = Choice.result eth in
                        let tth = Choice.result tth in
                        EQ_MP eth tth
                        |> Choice.bindError (fun _ -> tth)
            else 
                return! Choice.failwith "INSTANTIATE: term or type var free in assumptions"
        }

/// Apply a higher-order instantiation to assumptions and conclusion of a theorem.
let INSTANTIATE_ALL : instantiation -> Protected<thm0> -> Protected<thm0> =
    let inst ((_, tmin, tyin) as i) th =
        choice {
        let! th = th
        if List.isEmpty tmin && List.isEmpty tyin then
            return th
        else
            let hyps = hyp th
            if List.isEmpty hyps then
                return! INSTANTIATE i (Choice.result th)
            else
                let! tyrel, tyiirel =
                    if List.isEmpty tyin then
                        Choice.result ([], hyps)
                    else
                        let tvs = itlist (union << tyvars << snd) tyin []
                        hyps
                        |> Choice.List.partition (fun tm ->
                            choice {
                            let! tvs' = type_vars_in_term tm
                            return not(intersect tvs tvs' = [])
                            })
                
                let tmrel, tmirrel =
                    if List.isEmpty tmin then
                        [], tyiirel
                    else
                        let vs = itlist (union << frees << snd) tmin []
                        tyiirel
                        |> partition (fun tm ->
                            let vs' = frees tm
                            not(intersect vs vs' = []))
                
                let rhyps = union tyrel tmrel
                let! th1 =
                    // TODO : Modify this to use Choice.List.fold/foldBack.
                    rev_itlist DISCH rhyps (Choice.result th)
                let! th2 = INSTANTIATE i (Choice.result th1)
                return! funpow (length rhyps) UNDISCH (Choice.result th2)
        }
    
    inst

(* ------------------------------------------------------------------------- *)
(* Higher order matching of terms.                                           *)
(*                                                                           *)
(* Note: in the event of spillover patterns, this may return false results;  *)
(* but there's usually an implicit check outside that the match worked       *)
(* anyway. A test could be put in (see if any "env" variables are left in    *)
(* the term after abstracting out the pattern instances) but it'd be slower. *)
(* ------------------------------------------------------------------------- *)

/// Match one term against another.
let term_match : term list -> term -> term -> Protected<_> = 
    let safe_inserta ((y : term, x : 'a) as n) (l : (term * 'a) list) = 
        choice {
            match rev_assoc x l with
            | Some z ->
                if aconv y z then 
                    return l
                else 
                    return! Choice.failwith "safe_inserta"
            | None ->
                return n :: l
        }

    let safe_insert ((y, x) as n) l =
        choice {
            match rev_assoc x l with
            | Some z ->
                if compare y z = 0 then 
                    return l
                else 
                    return! Choice.failwith "safe_insert"
            | None ->
                return n :: l
        }

    let mk_dummy = 
        let name = Choice.map fst (dest_var(genvar aty))
        fun ty -> 
            choice {
                let! name = name
                return mk_var(name, ty)
            }

    let rec term_pmatch lconsts env vtm ctm ((insts, homs) as sofar) = 
        choice {
            match (vtm, ctm) with
            | Var(_, _), _ ->
                match rev_assoc vtm env with
                | Some ctm' ->
                    if compare ctm' ctm = 0 then 
                        return sofar
                    else 
                        return! Choice.failwith "term_pmatch"
                | None ->
                    if mem vtm lconsts then
                        if compare ctm vtm = 0 then 
                            return sofar
                        else
                            return! Choice.failwith "term_pmatch: can't instantiate local constant"
                    else
                        let! insts' = safe_inserta (ctm, vtm) insts
                        return insts', homs

            | Const(vname, vty), Const(cname, cty) -> 
                if compare vname cname = 0 then 
                    if compare vty cty = 0 then 
                        return sofar
                    else 
                        let! cty' = mk_dummy cty
                        let! vty' = mk_dummy vty
                        let! inst' = safe_insert (cty', vty') insts
                        return inst', homs
                else
                    return! Choice.failwith "term_pmatch"

            | Abs(vv, vbod), Abs(cv, cbod) -> 
                let! sofar' =
                    choice {
                        // CLEAN : Rename this value to something reasonable.
                        let! dest_var_cv = dest_var cv
                        let! dest_var_vv = dest_var vv
                        let! tm1 = mk_dummy(snd dest_var_cv)
                        let! tm2 = mk_dummy(snd dest_var_vv)
                        let! foo1 = safe_insert (tm1, tm2) insts
                        return foo1, homs
                    }
                return! term_pmatch lconsts ((cv, vv) :: env) vbod cbod sofar'

            | _ -> 
                let vhop = repeat (Choice.toOption << rator) vtm
                if is_var vhop && not(mem vhop lconsts) && (Option.isNone <| rev_assoc vhop env) then
                    let! vty = type_of vtm
                    let! cty = type_of ctm
                    let! insts' = 
                        choice {
                            if compare vty cty = 0 then 
                                return insts
                            else 
                                let! tm1 = mk_dummy cty
                                let! tm2 = mk_dummy vty
                                return! safe_insert (tm1, tm2) insts
                        }

                    return insts', (env, ctm, vtm) :: homs
                else 
                    let! lv, rv = dest_comb vtm
                    let! lc, rc = dest_comb ctm
                    let! sofar' = term_pmatch lconsts env lv lc sofar
                    return! term_pmatch lconsts env rv rc sofar'
        }

    let get_type_insts insts acc =
        insts
        |> Choice.List.fold (fun sofar (t, x) ->
            choice {
            let! dest_var_x = dest_var x
            let! type_of_t = type_of t
            return! type_match (snd dest_var_x) type_of_t sofar
            }) acc

    let separate_insts (insts : (term * term) list) = 
        choice {
            let realinsts, patterns = partition (is_var << snd) insts
            let betacounts = 
                if patterns = [] then []
                else
                    (patterns, [])
                    ||> itlist (fun (_, p) sof -> 
                        let hop, args = strip_comb p
                        safe_insert (length args, hop) sof
                        |> Choice.fill( 
                            warn true "Inconsistent patterning in higher order match"
                            sof))

            let! tyins = get_type_insts realinsts []
            // CLEAN : Rename this value to something sensible.
            let! foo1 =
                realinsts
                |> Choice.List.choose (fun (t, x) -> 
                    choice {
                    let! x' =
                        choice {
                        let! xn, xty = dest_var x
                        return mk_var(xn, type_subst tyins xty)
                        }
                    if compare t x' = 0 then 
                        return None
                    else 
                        return Some(t, x')
                    })
            return betacounts, foo1, tyins
        }

    let rec term_homatch lconsts tyins (insts, homs) = 
        choice {
        if homs = [] then 
            return insts
        else 
            let (env, ctm, vtm) = hd homs
            if is_var vtm then
                if compare ctm vtm = 0 then
                    return! term_homatch lconsts tyins (insts, tl homs)
                else 
                    let! newtyins =
                        choice {
                        let! type_of_ctm = type_of ctm
                        let! dest_var_vtm = dest_var vtm
                        return! safe_insert (type_of_ctm, snd dest_var_vtm) tyins
                        }
                    let newinsts = (ctm, vtm) :: insts
                    return! term_homatch lconsts newtyins (newinsts, tl homs)
            else 
                let vhop, vargs = strip_comb vtm
                let afvs = freesl vargs
                let inst_fn = inst tyins
                return!
                    choice { 
                        let! tmins = 
                            Choice.List.map (fun a ->
                                choice {
                                    match rev_assoc a env with
                                    | Some x -> 
                                        let! a' = inst_fn a
                                        return x, a'
                                    | None ->
                                        match rev_assoc a insts with
                                        | Some x -> 
                                            let! a' = inst_fn a
                                            return x, a'
                                        | None -> 
                                             if mem a lconsts then 
                                                let! a' = inst_fn a
                                                return a, a'
                                             else 
                                                return! Choice.fail()
                               }) afvs

                        let! pats0 = Choice.List.map inst_fn vargs
                        let! pats = Choice.List.map (vsubst tmins) pats0
                        let! vhop' = inst_fn vhop
                        let! ni = 
                            choice {
                            let chop, cargs = strip_comb ctm
                            if compare cargs pats = 0 then 
                                if compare chop vhop = 0 then 
                                    return insts
                                else 
                                    return! safe_inserta (chop, vhop) insts
                            else 
                                let! ginsts = 
                                    Choice.List.map (fun p -> 
                                        choice {
                                            if is_var p then 
                                                return p, p
                                            else 
                                                let! p' = Choice.map genvar (type_of p)
                                                return p', p
                                        }) pats

                                let! ctm' = subst ginsts ctm
                                let gvs = map fst ginsts
                                let abstm = list_mk_abs(gvs, ctm')
                                let! vinsts = safe_inserta (abstm, vhop) insts
                                let icpair = ctm', list_mk_comb(vhop', gvs)
                                return icpair :: vinsts
                            }
                        return! term_homatch lconsts tyins (ni, tl homs)
                    }
                    |> Choice.bindError (function 
                            | Failure _ -> 
                                choice {
                                    let! lc, rc = dest_comb ctm
                                    let! lv, rv = dest_comb vtm
                                    let! pinsts_homs' = 
                                        term_pmatch lconsts env rv rc 
                                            (insts, (env, lc, lv) :: (tl homs))
                                    let! tyins' = get_type_insts (fst pinsts_homs') []
                                    return! term_homatch lconsts tyins' pinsts_homs'
                                }
                            | e -> Choice.error e)
        }

    fun lconsts vtm ctm ->
        choice {
            let! pinsts_homs = term_pmatch lconsts [] vtm ctm ([], [])
            let! tyins = get_type_insts (fst pinsts_homs) []
            let! insts = term_homatch lconsts tyins pinsts_homs
            return! separate_insts insts
        }

(* ------------------------------------------------------------------------- *)
(* First order unification (no type instantiation -- yet).                   *)
(* ------------------------------------------------------------------------- *)

/// Unify two terms.
let term_unify : term list -> term -> term -> Protected<_> = 
    let augment1 sofar (s, x) = 
        let s' = Choice.get <| subst sofar s
        if vfree_in x s && not(s = x) then
            failwith "augment_insts"
        else (s', x)

    let raw_augment_insts p insts =
        p :: (map (augment1 [p]) insts)

    let augment_insts (t, v) insts =
        let t' = Choice.get <| vsubst insts t
        if t' = v then insts
        elif vfree_in v t' then
            failwith "augment_insts"
        else raw_augment_insts (t', v) insts

    let rec unify vars tm1 tm2 sofar = 
        if tm1 = tm2 then sofar
        elif is_var tm1 && mem tm1 vars then
            match rev_assoc tm1 sofar with
            | Some tm1' ->
                unify vars tm1' tm2 sofar
            | None ->
                augment_insts (tm2, tm1) sofar
        elif is_var tm2 && mem tm2 vars then
            match rev_assoc tm2 sofar with
            | Some tm2' ->
                unify vars tm1 tm2' sofar
            | None ->
                augment_insts (tm1, tm2) sofar
        elif is_abs tm1 then 
            let tm1' = Choice.get <| body tm1
            let tm2' = Choice.get <| subst [Choice.get <| bndvar tm1, Choice.get <| bndvar tm2] (Choice.get <| body tm2)
            unify vars tm1' tm2' sofar
        else 
            let l1, r1 = Choice.get <| dest_comb tm1
            let l2, r2 = Choice.get <| dest_comb tm2
            unify vars l1 l2 (unify vars r1 r2 sofar)

    fun vars tm1 tm2 -> 
        Choice.attempt <| fun () ->
            [], unify vars tm1 tm2 [], []

(* ------------------------------------------------------------------------- *)
(* Modify bound variable names at depth. (Not very efficient...)             *)
(* ------------------------------------------------------------------------- *)

/// Modify bound variable according to renaming scheme.
let deep_alpha : (string * string) list -> term -> Protected<term> = 
    let tryalpha v tm =
        match alpha v tm with
        | Success x -> x
        | Error _ ->
            match variant (frees tm) v with
            | Error _ -> tm
            | Success v' ->
                match alpha v' tm with
                | Success x -> x
                | Error _ -> tm

    let rec deep_alpha env tm =
        choice {
        if env = [] then
            return tm
        else
            let! v, bod = dest_abs tm
            let! vn, vty = dest_var v

            return!
                choice {
                let! (vn', _), newenv =
                    remove (fun (_, x) -> x = vn) env
                    |> Option.toChoiceWithError "remove"
                let v' = mk_var(vn', vty)
                let tm' = tryalpha v' tm
                let! iv, ib = dest_abs tm'
                let! deep_alpha_ib = deep_alpha newenv ib
                return! mk_abs(iv, deep_alpha_ib)
                }
                |> Choice.bindError (fun _ ->
                    choice {
                    let! deep_alpha_bod = deep_alpha env bod
                    return! mk_abs(v, deep_alpha_bod)
                    })
        }
        |> Choice.bindError (fun _ ->
            choice {
            let! l, r = dest_comb tm
            let! deep_alpha_l = deep_alpha env l
            let! deep_alpha_r = deep_alpha env r
            return! mk_comb(deep_alpha_l, deep_alpha_r)
            }
            |> Choice.bindError (fun _ ->
                Choice.result tm))
    
    deep_alpha

(* ------------------------------------------------------------------------- *)
(* Instantiate theorem by matching part of it to a term.                     *)
(* The GEN_PART_MATCH version renames free vars to avoid clashes.            *)
(* ------------------------------------------------------------------------- *)

// PART_MATCH: Instantiates a theorem by matching part of it to a term.
// GEN_PART_MATCH: Instantiates a theorem by matching part of it to a term.
let (PART_MATCH : (term -> Protected<_>) -> _ -> _ -> Protected<_>), (GEN_PART_MATCH : (term -> Protected<_>) -> _ -> _ -> Protected<_>) = 
    let rec match_bvs t1 t2 acc = 
        choice { 
            let! v1, b1 = dest_abs t1
            let! v2, b2 = dest_abs t2
            let! (n1, _) = dest_var v1
            let! (n2, _) = dest_var v2
            let newacc = 
                if n1 = n2 then acc
                else insert (n1, n2) acc
            return match_bvs b1 b2 newacc
        }
        |> Choice.fill(
                choice { 
                    let! l1, r1 = dest_comb t1
                    let! l2, r2 = dest_comb t2
                    return match_bvs l1 l2 (match_bvs r1 r2 acc)
                }
                |> Choice.fill acc)

    let PART_MATCH partfn (th : Protected<thm0>) =
        let v = 
            choice {
                let sth = SPEC_ALL th
                let! bod = Choice.map concl sth
                let! pbod = partfn bod
                let! tm0 = Choice.map concl th
                let! tl = Choice.map hyp th
                let lconsts = intersect (frees tm0) (freesl tl)
                return (sth, bod, pbod, lconsts)
                }

        fun tm ->
            choice {      
                let! (sth, bod, pbod, lconsts) = v
                let bvms = match_bvs tm pbod []
                let! abod = deep_alpha bvms bod
                let ath = EQ_MP (ALPHA bod abod) sth
                let! tm1 = partfn abod
                let! insts = term_match lconsts tm1 tm
                let fth = INSTANTIATE insts ath
                let! fth' = fth
                let! ath' = ath
                if hyp fth' <> hyp ath' then 
                    return! Choice.failwith "PART_MATCH: instantiated hyps"
                else 
                    let! tm' = Choice.bind (partfn << concl) fth
                    if compare tm' tm = 0 then 
                        return! fth
                    else 
                        return!
                            SUBS [ALPHA tm' tm] fth
                            |> Choice.mapError (fun e -> nestedFailure e "PART_MATCH: Sanity check failure")
            }

    let GEN_PART_MATCH partfn (th : Protected<thm0>) = 
        let v =
            choice {
            let sth = SPEC_ALL th
            let! bod = Choice.map concl sth
            let! pbod = partfn bod
            let! tm0 = Choice.map concl th
            let! tl = Choice.map hyp th
            let lconsts = intersect (frees tm0) (freesl tl)
            let fvs = subtract (subtract (frees bod) (frees pbod)) lconsts
            return (sth, bod, pbod, lconsts, fvs)
            }
        fun tm ->
            choice {
            let! (sth, bod, pbod, lconsts, fvs) = v
            let bvms = match_bvs tm pbod []
            let! abod = deep_alpha bvms bod
            let! ath = EQ_MP (ALPHA bod abod) sth
            let! tm1 = partfn abod
            let! insts = term_match lconsts tm1 tm
            let! eth = INSTANTIATE insts (GENL fvs (Choice.result ath))
            let fth =
                (fvs, eth)
                ||> itlist (fun v th ->
                    choice {
                    let th = Choice.result th
                    let! result = SPEC_VAR th
                    return snd result
                    } |> Choice.get)
            if hyp fth <> hyp ath then
                return! Choice.failwith "PART_MATCH: instantiated hyps"
            else 
                let! tm' = partfn <| concl fth
                if compare tm' tm = 0 then 
                    return fth
                else 
                    return!
                        let fth = Choice.result fth in
                        SUBS [ALPHA tm' tm] fth
                        |> Choice.mapError (fun e -> nestedFailure e "PART_MATCH: Sanity check failure")
            }
    PART_MATCH, GEN_PART_MATCH

(* ------------------------------------------------------------------------- *)
(* Matching modus ponens.                                                    *)
(* ------------------------------------------------------------------------- *)

/// Modus Ponens inference rule with automatic matching.
let MATCH_MP (ith : Protected<thm0>) : Protected<thm0> -> Protected<thm0> = 
    let sth = 
        choice {
            let! tm = Choice.map concl ith
            let avs, bod = strip_forall tm
            let! ant, con = dest_imp bod
            let svs, pvs = partition (C vfree_in ant) avs
            if pvs = [] then 
                return! ith
            else 
                let th1 = SPECL avs (ASSUME tm)
                let th2 = GENL svs (DISCH ant (GENL pvs (UNDISCH th1)))
                return! MP (DISCH tm th2) ith
        }
        |> Choice.mapError (fun e -> nestedFailure e "MATCH_MP: Not an implication")

    let match_fun : term -> Protected<thm0> =
        PART_MATCH (Choice.map fst << dest_imp) sth

    fun (th : Protected<thm0>) ->
        choice {
        let! th' = th
        // CLEAN : Rename this value to something reasonable.
        let! foo1 = match_fun <| concl th'
        return! MP (Choice.result foo1) th
        }
        |> Choice.mapError (fun e -> nestedFailure e "MATCH_MP: No match")

(* ------------------------------------------------------------------------- *)
(* Useful instance of more general higher order matching.                    *)
(* ------------------------------------------------------------------------- *)

/// Rewrite once using more general higher order matching.
let HIGHER_REWRITE_CONV = 
    let BETA_VAR = 
        let rec BETA_CONVS n = 
            if n = 1 then TRY_CONV BETA_CONV
            else THENC (RATOR_CONV(BETA_CONVS(n - 1))) (TRY_CONV BETA_CONV)

        let rec free_beta v tm = 
            if is_abs tm then 
                let bv, bod = Choice.get <| dest_abs tm
                if v = bv then
                    failwith "unchanged"
                else
                    ABS_CONV(free_beta v bod)
            else
                let op, args = strip_comb tm
                if args = [] then
                    failwith "unchanged"
                elif op = v then
                    BETA_CONVS(length args)
                else
                    let l, r = Choice.get <| dest_comb tm
                    try 
                        let lconv = free_beta v l
                        try 
                             let rconv = free_beta v r
                             COMB2_CONV lconv rconv
                        with Failure _ ->
                            RATOR_CONV lconv
                    with Failure _ ->
                        RAND_CONV(free_beta v r)
        free_beta

    let GINST (th : Protected<thm0>) =
        let fvs =
            let th' = Choice.get th
            subtract (frees <| concl th') (freesl <| hyp th')
        let gvs = map (genvar << Choice.get << type_of) fvs
        INST (zip gvs fvs) th

    let higher_rewrite_conv ths =
        let thl = map (GINST << SPEC_ALL) ths
        let concs = map (concl << Choice.get) thl
        let lefts = map (Choice.get << lhs) concs
        let preds, pats = unzip(map (Choice.get << dest_comb) lefts)
        let beta_fns = map2 BETA_VAR preds concs
        let ass_list = zip pats (zip preds (zip thl beta_fns))
        let mnet = itlist (fun p n -> Choice.get <| enter [] (p, p) n) pats empty_net
        let look_fn t =
            // CLEAN : Rename this value to something reasonable.
            let foo1 = Choice.get <| lookup t mnet
            foo1
            |> mapfilter (fun p ->
                if Choice.isResult <| term_match [] p t then
                    Some p
                else None) 

        fun top tm -> 
            let pred t = not(look_fn t = []) && free_in t tm
            let stm = 
                if top then
                    Choice.get <| find_term pred tm
                else
                    hd(sort free_in (Choice.get <| find_terms pred tm))
            let pat = hd(look_fn stm)
            let _, tmin, tyin = Choice.get <| term_match [] pat stm
            let pred, (th, beta_fn) =
                assoc pat ass_list
                |> Option.getOrFailWith "find"
            let gv = genvar(Choice.get <| type_of stm)
            let abs = Choice.get <| mk_abs(gv, Choice.get <| subst [gv, stm] tm)
            let _, tmin0, tyin0 = Choice.get <| term_match [] pred abs
            CONV_RULE beta_fn (INST tmin (INST tmin0 (INST_TYPE tyin0 th)))

    fun ths top tm ->
        (Choice.attemptNested <| fun () ->
            higher_rewrite_conv ths top tm) : Protected<thm0>

(* ------------------------------------------------------------------------- *)
(* Derived principle of definition justifying |- c x1 .. xn = t[x1,..,xn]    *)
(* ------------------------------------------------------------------------- *)

/// Declare a new constant and a definitional axiom.
let new_definition tm : Protected<thm0> = 
    choice { 
        let avs, bod = strip_forall tm
        let! l, r = 
            dest_eq bod
            |> Choice.mapError (fun e -> nestedFailure e "new_definition: Not an equation")
        let lv, largs = strip_comb l
        let! rtm = 
            // NOTE: list_mk_abs isn't converted yet, so exceptions can leak out
            Choice.attempt (fun () -> list_mk_abs(largs, r))
            |> Choice.mapError (fun e -> nestedFailure e "new_definition: Non-variable in LHS pattern")

        let! def = mk_eq(lv, rtm)
        let th1 = new_basic_definition def
        let! th2 = 
            Choice.List.foldBack (fun tm acc -> 
                choice {
                    let ith = AP_THM acc tm
                    let! tm1 = Choice.bind (rand << concl) ith
                    return TRANS ith (BETA_CONV tm1)
                }) largs th1

        let rvs = filter (not << C mem avs) largs
        return! itlist GEN rvs (itlist GEN avs th2)
    }
