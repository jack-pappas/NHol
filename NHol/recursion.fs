(*

Copyright 1998 University of Cambridge
Copyright 1998-2007 John Harrison
Copyright 2013 Jack Pappas, Eric Taucher, Domenico Masini

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
/// Tools for primitive recursion on inductive types.
module NHol.recursion

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
#endif

logger.Trace("Entering recursion.fs")

(* ------------------------------------------------------------------------- *)
(* Prove existence of recursive function. The inner "raw" version requires   *)
(* exact correspondence with recursion theorem; "canon" requires the         *)
(* PR argument to come first in the arg list; the outer one is more general. *)
(* ------------------------------------------------------------------------- *)

/// Prove existence of recursive function over inductive type.
let prove_recursive_functions_exist = 
    let prove_raw_recursive_functions_exist ax tm = 
        choice {
            let rawcls = conjuncts tm
            let spcls = map (snd << strip_forall) rawcls
            let! lpats = Choice.List.map (Choice.map strip_comb << lhand) spcls
            let ufns = itlist (insert << fst) lpats []
            let axth = SPEC_ALL ax
            let! exvs, axbody = Choice.map (strip_exists << concl) axth
            let axcls = conjuncts axbody
            let f = 
                Choice.map fst << Choice.bind dest_const 
                << repeat (Choice.toOption << Choice.map Choice.result << Choice.bind rator) 
                << Choice.bind rand << lhand << snd << strip_forall

            let findax s =
                choice {
                    let! tms = Choice.List.map (fun t -> f t |> Choice.map (fun ft -> ft, t)) axcls
                    return! assoc s tms
                            |> Option.toChoiceWithError "find"
                }

            let! raxs = 
                Choice.List.map (Choice.bind findax << Choice.map fst << dest_const << repeat (Choice.toOption << rator) << hd << snd) lpats

            let! axfns = Choice.List.map (Choice.map (repeat (Choice.toOption << rator)) << lhand << snd << strip_forall) raxs

            let urfns = map (fun v -> assocd v (setify(zip axfns (map fst lpats))) v) exvs

            let! tm1 = list_mk_conj raxs
            let! axtm = list_mk_exists(exvs, tm1)
            let! urtm = list_mk_exists(urfns, tm)

            let! insts = term_match [] axtm urtm
            let ixth = INSTANTIATE insts axth
            let! ixvs, ixbody = Choice.map (strip_exists << concl) ixth
            let! ixtm = subst (zip urfns ixvs) ixbody
            let ixths = CONJUNCTS(ASSUME ixtm)

            let! rixths = Choice.List.map (fun t -> 
                                Choice.List.tryFind (fun th ->
                                    choice {
                                        let! th = th
                                        let tm1 = concl th
                                        return aconv t tm1
                                    }) ixths
                                    |> Choice.bind (Option.toChoiceWithError "find")) rawcls

            let rixth = itlist SIMPLE_EXISTS ufns (end_itlist CONJ rixths)
            return! PROVE_HYP ixth (itlist SIMPLE_CHOOSE urfns rixth)
        }

    let canonize t = 
        choice {
            let avs, bod = strip_forall t
            let! l, r =dest_eq bod
            let fn, args = strip_comb l
            let rarg = hd args
            let vargs = tl args
            let! l' = mk_comb(fn, rarg)
            let! r' = list_mk_abs(vargs, r)
            let fvs = frees rarg
            let! tm1 = mk_eq(l', r')
            let! tm2 = list_mk_forall(fvs, tm1)
            let def = ASSUME(tm2)
            return! GENL avs (RIGHT_BETAS vargs (SPECL fvs def))
        }

    let prove_canon_recursive_functions_exist ax tm = 
        choice {
            let ths = map canonize (conjuncts tm)
            let! atm = list_mk_conj(map (hd << hyp << Choice.get) ths)
            let aths = CONJUNCTS(ASSUME atm)
            let rth = end_itlist CONJ (map2 PROVE_HYP aths ths)
            let eth = prove_raw_recursive_functions_exist ax atm
            let! (evs, _) = Choice.map (strip_exists << concl) eth
            return! PROVE_HYP eth (itlist SIMPLE_CHOOSE evs (itlist SIMPLE_EXISTS evs rth))
        }

    let reshuffle fn args acc = 
        choice {
            let args' = uncurry (C (@)) (partition is_var args)
            if args = args' then 
                return acc
            else 
                let! gvs = Choice.List.map (Choice.map genvar << type_of) args
                let! gvs' = Choice.List.map (fun x -> assoc x (zip args gvs) |> Option.toChoiceWithError "find") args'
                let! ty1 = type_of fn
                let! tms = Choice.funpow (length gvs) (Choice.map (hd << tl << snd) << dest_type) ty1
                let lty = itlist ((fun ty -> Choice.get << mk_fun_ty ty) << Choice.get << type_of) gvs' tms
                let fn' = genvar lty
                let! tm0 = list_mk_comb(fn', gvs')
                let! tm1 = list_mk_abs(gvs, tm0)
                let! def = mk_eq(fn, tm1)
                return (ASSUME def) :: acc
        }

    let scrub_def t th = 
        choice {
            let! l, r = dest_eq t
            return! MP (INST [r, l] (DISCH t th)) (REFL r)
        }

    fun ax tm -> 
        choice {
            let rawcls = conjuncts tm
            let spcls = map (snd << strip_forall) rawcls
            let! lpats = Choice.List.map (Choice.map strip_comb << lhand) spcls
            let ufns = itlist (insert << fst) lpats []
            let! uxargs = Choice.List.map (fun x -> assoc x lpats |> Option.toChoiceWithError "find") ufns
            let! trths = Choice.List.fold2 (fun acc x y -> reshuffle x y acc) [] ufns uxargs 
            let tth = GEN_REWRITE_CONV REDEPTH_CONV (BETA_THM :: trths) tm
            let! tm1 = Choice.bind (rand << concl) tth
            let eth = prove_canon_recursive_functions_exist ax tm1
            let! evs, ebod = Choice.map (strip_exists << concl) eth
            let fth = itlist SIMPLE_EXISTS ufns (EQ_MP (SYM tth) (ASSUME ebod))
            let! tms1 = Choice.List.map (Choice.map concl) trths
            let gth = itlist scrub_def tms1 fth
            return! PROVE_HYP eth (itlist SIMPLE_CHOOSE evs gth)
        }

(* ------------------------------------------------------------------------- *)
(* Version that defines function(s).                                         *)
(* ------------------------------------------------------------------------- *)

/// Define recursive function over inductive type.
let new_recursive_definition = 
    let the_recursive_definitions = ref []

    let find_redefinition tm th = 
        choice {
            let th' = PART_MATCH Choice.result th tm
            let! th1 = th
            ignore (PART_MATCH Choice.result th' (concl th1))
            return! th'
        }

    fun ax tm -> 
        choice { 
            let th = tryfind (Choice.toOption << find_redefinition tm) (!the_recursive_definitions)
                     |> Option.toChoiceWithError "tryfind"
            warn true "Benign redefinition of recursive function"
            return! th
        }
        |> Choice.bindError (fun _ ->
            choice {
                let rawcls = conjuncts tm
                let spcls = map (snd << strip_forall) rawcls
                let! lpats = Choice.List.map (Choice.map strip_comb << lhand) spcls
                let ufns = itlist (insert << fst) lpats []
                let fvs = map (fun t -> subtract (frees t) ufns) rawcls
                let! gcls = Choice.List.map2 (curry list_mk_forall) fvs rawcls
                let! tm1 = list_mk_conj gcls
                let eth = prove_recursive_functions_exist ax tm1
                let! evs, bod = Choice.map (strip_exists << concl) eth
                let! tms = Choice.List.map (Choice.map fst << dest_var) evs
                let dth = new_specification tms eth
                let dths = map2 SPECL fvs (CONJUNCTS dth)
                let th = end_itlist CONJ dths
                the_recursive_definitions := th :: (!the_recursive_definitions)
                return! th
            })
        |> Choice.mapError (fun e ->
            logger.Error(Printf.sprintf "%O" e)
            e)
