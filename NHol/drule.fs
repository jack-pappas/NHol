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
open FSharp.Compatibility.OCaml.Format

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
#endif

logger.Trace("Entering drule.fs")

(* ------------------------------------------------------------------------- *)
(* Type of instantiations, with terms, types and higher-order data.          *)
(* ------------------------------------------------------------------------- *)

type instantiation = (int * term) list * (term * term) list * (hol_type * hol_type) list

/// Prints a instantiation to formatter.
let pp_print_instantiation fmt inst =
    let (al,bl,cl) = inst
    let rec pp_print_al fmt al =
        match al with
        | (n,trm) :: tl ->
            pp_print_string fmt (string_of_int n)
            pp_print_string fmt ", "
            pp_print_term fmt trm
            pp_print_break fmt 0 0
            pp_print_al fmt tl
        | [] -> ()
    pp_print_al fmt al
    let rec pp_print_bl fmt al =
        match al with
        | (trma,trmb) :: tl ->
            pp_print_term fmt trma
            pp_print_string fmt ", "
            pp_print_term fmt trmb
            pp_print_break fmt 0 0
            pp_print_bl fmt tl
        | [] -> ()
    pp_print_bl fmt bl
    let rec pp_print_cl fmt al =
        match al with
        | (typa,typb) :: tl ->
            pp_print_term fmt typa
            pp_print_string fmt ", "
            pp_print_term fmt typb
            pp_print_break fmt 0 0
            pp_print_cl fmt tl
        | [] -> ()
    pp_print_cl fmt cl

/// Prints a instantiation (without quotes) to the standard output.
let print_instantiation = pp_print_instantiation std_formatter

/// Converts a instantiation to a string representation.
let string_of_instantiation = print_to_string pp_print_instantiation

#if INTERACTIVE
fsi.AddPrinter string_of_instantiation
#endif

/// Prints a ((int * term) list) to formatter.
let pp_print_list_inttrm fmt (al : (int * term) list) =
    let rec pp_print_list_inttrmInner fmt al =
        match al with
        | (inta,trmb) :: tl ->
            pp_print_int fmt inta
            pp_print_string fmt ", "
            pp_print_term fmt trmb
            pp_print_break fmt 0 0
            pp_print_list_inttrmInner fmt tl
        | [] -> ()
    if al.Length = 0 then 
        pp_print_string fmt "No items"
    else 
        pp_open_hvbox fmt 0
        pp_print_list_inttrmInner fmt al
        pp_close_box fmt ()

/// Prints a ((int * term) list) to the standard output.
let print_list_inttrm = pp_print_list_inttrm std_formatter

/// Converts a ((int * term) list) to a string representation.
let string_of_list_inttrm = print_to_string pp_print_list_inttrm

/// Prints a ((term * term) list) to formatter.
let pp_print_list_trmtrm fmt (al : (term * term) list) =
    let rec pp_print_list_trmtrmInner fmt al =
        match al with
        | (trma,trmb) :: tl ->
            pp_print_term fmt trma
            pp_print_string fmt ", "
            pp_print_term fmt trmb
            pp_print_break fmt 0 0
            pp_print_list_trmtrmInner fmt tl
        | [] -> ()
    if al.Length = 0 then 
        pp_print_string fmt "No items"
    else 
        pp_open_hvbox fmt 0
        pp_print_list_trmtrmInner fmt al
        pp_close_box fmt ()

/// Prints a ((term * term) list) to the standard output.
let print_list_trmtrm = pp_print_list_trmtrm std_formatter

/// Converts a ((term * term) list) to a string representation.
let string_of_list_trmtrm = print_to_string pp_print_list_trmtrm

(* ------------------------------------------------------------------------- *)
(* The last recourse when all else fails!                                    *)
(* ------------------------------------------------------------------------- *)

/// Creates an arbitrary theorem as an axiom (dangerous!)
let mk_thm(asl, c) : Protected<thm0> = 
    choice {
        let! tm = Choice.List.foldBack (curry mk_imp) (rev asl) c
        let! ax = new_axiom tm
        return! Choice.List.fold (fun th t -> MP (Choice.result th) (ASSUME t)) ax (rev asl)
    }

(* ------------------------------------------------------------------------- *)
(* Derived congruence rules; very useful things!                             *)
(* ------------------------------------------------------------------------- *)

/// Conjoin both sides of two equational theorems.
let MK_CONJ = 
    let andtm = parse_term @"(/\)"
    fun eq1 eq2 ->
        choice {
            let! eq1 = eq1
            let! eq2 = eq2
            let! th1 = AP_TERM andtm (Choice.result eq1)
            return! MK_COMB(Choice.result th1, Choice.result eq2)
        }

/// Disjoin both sides of two equational theorems.
let MK_DISJ = 
    let ortm = parse_term @"(\/)"
    fun eq1 eq2 ->
        choice {
            let! eq1 = eq1
            let! eq2 = eq2
            let! th1 = AP_TERM ortm (Choice.result eq1)
            return! MK_COMB(Choice.result th1, Choice.result eq2)
        }

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
            let! th1 = ABS v th
            return! AP_TERM tm' (Choice.result th1)
        } : Protected<thm0>

(* ------------------------------------------------------------------------- *)
(* Eliminate the antecedent of a theorem using a conversion/proof rule.      *)
(* ------------------------------------------------------------------------- *)

/// Removes antecedent of implication theorem by solving it with a conversion.
let MP_CONV (cnv : conv) (th : Protected<thm0>) : Protected<thm0> = 
    choice {
    let! th = th
    let! l, _ = dest_imp <| concl th
    let! ath = cnv l
    let! th1 = EQT_ELIM (Choice.result ath)
    return!
        MP (Choice.result th) (Choice.result th1)
        |> Choice.bindError (function Failure _ -> MP (Choice.result th) (Choice.result ath) | e -> Choice.error e)
    }    

(* ------------------------------------------------------------------------- *)
(* Multiple beta-reduction (we use a slight variant below).                  *)
(* ------------------------------------------------------------------------- *)

/// Beta conversion over multiple arguments.
let rec BETAS_CONV tm : Protected<thm0> =
    choice {
        match tm with
        | Comb(Abs(_, _), _) ->
            return! BETA_CONV tm
        | Comb(Comb(_, _), _) ->
            return! (RATOR_CONV BETAS_CONV |> THENC <| BETA_CONV) tm
        | _ ->
            return! Choice.failwith "BETAS_CONV"
    }

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
            |> Choice.bindError (function
                | Failure _ ->
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
                                        Choice.error error
                | e -> Choice.error e)

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
                    |> Choice.bindError (function Failure _ -> Choice.result ttm | e -> Choice.error e)
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
                let! th1 = HO_BETAS bcs tm' bod
                return! ABS bv (Choice.result th1)
            }
            |> Choice.bindError (function
                | Failure _ ->
                choice {
                    let hop, args = strip_comb pat
                    let! n = rev_assoc hop bcs
                             |> Option.toChoiceWithError "find"
                
                    if length args = n then
                        return! BETAS_CONV n tm
                    else
                        return! Choice.fail ()
                }
                |> Choice.bindError (function
                    | Failure _ ->
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
                        }
                        | e -> Choice.error e)
                 | e -> Choice.error e)

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
                        |> Choice.bindError (function Failure _ -> tth | e -> Choice.error e)
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
                
                let tmrel, _ =
                    if List.isEmpty tmin then
                        [], tyiirel
                    else
                        let vs = itlist (union << frees << snd) tmin []
                        tyiirel
                        |> partition (fun tm ->
                            let vs' = frees tm
                            not(intersect vs vs' = []))
                
                let rhyps = union tyrel tmrel
                let! th1 = Choice.List.fold (fun acc x -> DISCH x (Choice.result acc)) th rhyps
                let! th2 = INSTANTIATE i (Choice.result th1)
                return! Choice.funpow (length rhyps) (UNDISCH << Choice.result) th2
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
        (insts, acc)
        ||> Choice.List.foldBack (fun (t, x) sofar ->
            choice {
            let! dest_var_x = dest_var x
            let! type_of_t = type_of t
            return! type_match (snd dest_var_x) type_of_t sofar
            })

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
                                let! abstm = list_mk_abs(gvs, ctm')
                                let! vinsts = safe_inserta (abstm, vhop) insts
                                let! ctm'' = list_mk_comb(vhop', gvs)
                                let icpair = ctm', ctm''
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
        choice {
            let! s' = subst sofar s
            if vfree_in x s && not(s = x) then
                return! Choice.failwith "augment_insts"
            else 
                return (s', x)
        }

    let raw_augment_insts p insts : Protected<_> =
        choice {
            let! ps = Choice.List.map (augment1 [p]) insts
            return p :: ps
        }

    let augment_insts (t, v) insts =
        choice {
            let! t' = vsubst insts t
            if t' = v then 
                return insts
            elif vfree_in v t' then
                return! Choice.failwith "augment_insts"
            else 
                return! raw_augment_insts (t', v) insts
        }

    let rec unify vars tm1 tm2 sofar = 
        choice {
            if tm1 = tm2 then 
                return sofar
            elif is_var tm1 && mem tm1 vars then
                match rev_assoc tm1 sofar with
                | Some tm1' ->
                    return! unify vars tm1' tm2 sofar
                | None ->
                    return! augment_insts (tm2, tm1) sofar
            elif is_var tm2 && mem tm2 vars then
                match rev_assoc tm2 sofar with
                | Some tm2' ->
                    return! unify vars tm1 tm2' sofar
                | None ->
                    return! augment_insts (tm1, tm2) sofar
            elif is_abs tm1 then 
                let! tm1' = body tm1
                let! tm4 = bndvar tm1
                let! tm5 = bndvar tm2
                let! tm6 = body tm2
                let! tm2' = subst [tm4, tm5] tm6
                return! unify vars tm1' tm2' sofar
            else 
                let! l1, r1 = dest_comb tm1
                let! l2, r2 = dest_comb tm2
                let! tm3 = unify vars r1 r2 sofar
                return! unify vars l1 l2 tm3
        }

    fun vars tm1 tm2 -> 
        choice {
            let! tms = unify vars tm1 tm2 []
            return [], tms, []
        }

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
                |> Choice.bindError (function
                    | Failure _ ->
                        choice {
                        let! deep_alpha_bod = deep_alpha env bod
                        return! mk_abs(v, deep_alpha_bod)
                        }
                    | e -> Choice.error e)
        }
        |> Choice.bindError (function 
            | Failure _ ->
                choice {
                let! l, r = dest_comb tm
                let! deep_alpha_l = deep_alpha env l
                let! deep_alpha_r = deep_alpha env r
                return! mk_comb(deep_alpha_l, deep_alpha_r)
                }
                |> Choice.bindError (function Failure _ -> Choice.result tm | e -> Choice.error e)
            | e -> Choice.error e)
    
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
                let! ath = EQ_MP (ALPHA bod abod) sth
                let! tm1 = partfn abod
                let! insts = term_match lconsts tm1 tm
                let! fth = INSTANTIATE insts (Choice.result ath)
                if hyp fth <> hyp ath then 
                    return! Choice.failwith "PART_MATCH: instantiated hyps"
                else 
                    let! tm' = partfn <| concl fth
                    if compare tm' tm = 0 then 
                        return fth
                    else 
                        return!
                            SUBS [ALPHA tm' tm] (Choice.result fth)
                            |> Choice.mapError (fun e -> nestedFailure e "PART_MATCH: Sanity check failure")
            }

    let GEN_PART_MATCH partfn (th : Protected<thm0>) = 
        let v =
            choice {
            let! sth = SPEC_ALL th
            let bod = concl sth
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
            let! th1 = ALPHA bod abod
            let! ath = EQ_MP (Choice.result th1) (Choice.result sth)
            let! tm1 = partfn abod
            let! insts = term_match lconsts tm1 tm
            let! th2 = GENL fvs (Choice.result ath)
            let! eth = INSTANTIATE insts (Choice.result th2)
            let! fth =
                (fvs, eth)
                ||> Choice.List.foldBack (fun v th ->
                    choice {
                    let! result = SPEC_VAR (Choice.result th)
                    return snd result
                    })
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
                // Choice.get is safe to use here
                let bv, bod = Choice.get <| dest_abs tm
                if v = bv then
                    fun _ -> Choice.failwith "unchanged"
                else
                    ABS_CONV(free_beta v bod)
            else
                let op, args = strip_comb tm
                if args = [] then
                    fun _ -> Choice.failwith "unchanged"
                elif op = v then
                    BETA_CONVS(length args)
                else
                    let lr = dest_comb tm
                    // NOTE: 
                    // The original version raises an exception in initialization
                    // We have to evaluate the function with some input in order to determine errors
                    fun tm ->
                        choice {
                        let! (l, r) = lr
                        return!
                            choice { 
                                let lconv = free_beta v l
                                // Evaluate with tm to spot errors
                                let! _ = lconv tm
                                return!
                                    choice { 
                                        let rconv = free_beta v r
                                        // Evaluate with tm to spot errors
                                        let! _ = rconv tm
                                        return! COMB2_CONV lconv rconv tm
                                    }
                                    |> Choice.bindError (function
                                        | Failure _ ->
                                            RATOR_CONV lconv tm
                                        | e -> Choice.error e)
                            }
                            |> Choice.bindError (function
                                | Failure _ ->
                                    choice {
                                        let conv = free_beta v r
                                        // Evaluate with tm to spot errors
                                        let! _ = conv tm
                                        return! RAND_CONV conv tm
                                    }
                                | e -> Choice.error e)
                        }
        free_beta

    let GINST (th : Protected<thm0>) =
        choice {
            let! th = th
            let fvs = subtract (frees <| concl th) (freesl <| hyp th)
            let! gvs = Choice.List.map (Choice.map genvar << type_of) fvs
            return! INST (zip gvs fvs) (Choice.result th)
        }

    let higher_rewrite_conv ths =
        let v = 
            choice {
                let! thl = Choice.List.map (GINST << SPEC_ALL) ths
                let concs = map concl thl
                let! lefts = Choice.List.map lhs concs
                let! lefts' = Choice.List.map dest_comb lefts
                let preds, pats = unzip lefts'
                let beta_fns = map2 BETA_VAR preds concs
                let ass_list = zip pats (zip preds (zip thl beta_fns))
                let! mnet = Choice.List.foldBack (fun p n -> enter [] (p, p) n) pats empty_net
                return (thl, ass_list, mnet)
            }

        let look_fn t =
            choice {
                // CLEAN : Rename this value to something reasonable.
                let! (_, _, mnet) = v
                let! foo1 = lookup t mnet
                return
                    foo1
                    |> mapfilter (fun p ->
                        if Choice.isResult <| term_match [] p t then
                            Some p
                        else None) 
            }

        fun top tm -> 
            choice {
                let pred t = 
                    choice {
                        let! tms = look_fn t
                        if List.isEmpty tms then
                            return false
                        else
                            let! b = free_in t tm
                            return b
                    }

                let! (_, ass_list, _) = v

                let! stm = 
                    choice {
                    if top then
                        return! find_term pred tm
                    else
                        let! tms = find_terms pred tm
                        return hd(sort (fun x y -> free_in x y |> Choice.get) tms)
                    }
                let! stm' = look_fn stm
                let pat = hd stm'
                let! _, tmin, _ = term_match [] pat stm
                let! pred, (th, beta_fn) =
                    assoc pat ass_list
                    |> Option.toChoiceWithError "find"
                let! ty1 = type_of stm
                let gv = genvar ty1
                let! tm1 = subst [gv, stm] tm
                let! abs = mk_abs(gv, tm1)
                let! _, tmin0, tyin0 = term_match [] pred abs
                let! th1 = INST_TYPE tyin0 (Choice.result th)
                let! th2 = INST tmin0 (Choice.result th1)
                let! th3 = INST tmin (Choice.result th2)
                return! CONV_RULE beta_fn (Choice.result th3)
            }

    fun ths top tm ->
        higher_rewrite_conv ths top tm : Protected<thm0>

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
            list_mk_abs(largs, r)
            |> Choice.mapError (fun e -> nestedFailure e "new_definition: Non-variable in LHS pattern")

        let! def = mk_eq(lv, rtm)
        let! th1 = new_basic_definition def
        let! th2 = 
            // NOTE: this is rewritten from rev_itlist
            Choice.List.fold (fun acc tm -> 
                choice {
                    let! ith = AP_THM acc tm
                    let! tm1 = rand <| concl ith
                    let! th2 = BETA_CONV tm1
                    return TRANS (Choice.result ith) (Choice.result th2)
                }) (Choice.result th1) largs

        let rvs = filter (not << C mem avs) largs
        return! itlist GEN rvs (itlist GEN avs th2)
    }
    |> Choice.mapError (fun e ->
        logger.Error(Printf.sprintf "new_definition of '%s' returns %O" (string_of_term tm) e)
        e)
