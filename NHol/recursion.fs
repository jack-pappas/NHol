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

#if INTERACTIVE
#else
/// Tools for primitive recursion on inductive types.
module NHol.recursion

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
open simp
open theorems
open ind_defs
open ``class``
open trivia
open canon
open meson
open quot
//open pair
open nums
#endif

(* ------------------------------------------------------------------------- *)
(* Prove existence of recursive function. The inner "raw" version requires   *)
(* exact correspondence with recursion theorem; "canon" requires the         *)
(* PR argument to come first in the arg list; the outer one is more general. *)
(* ------------------------------------------------------------------------- *)
/// Prove existence of recursive function over inductive type.
let prove_recursive_functions_exist = 
    let prove_raw_recursive_functions_exist ax tm = 
        let rawcls = conjuncts tm
        let spcls = map (snd << strip_forall) rawcls
        let lpats = map (strip_comb << lhand) spcls
        let ufns = itlist (insert << fst) lpats []
        let axth = SPEC_ALL ax
        let exvs, axbody = strip_exists(concl axth)
        let axcls = conjuncts axbody
        let f = 
            fst << Choice.get << dest_const << repeat rator << rand << lhand << snd 
            << strip_forall
        let findax s =
            assoc s (map (fun t -> f t, t) axcls)
            |> Option.getOrFailWith "find"
        let raxs = 
            map (findax << fst << Choice.get << dest_const << repeat rator << hd << snd) lpats
        let axfns = map (repeat rator << lhand << snd << strip_forall) raxs
        let urfns = 
            map (fun v -> assocd v (setify(zip axfns (map fst lpats))) v) exvs
        let axtm = list_mk_exists(exvs, list_mk_conj raxs)
        let urtm = list_mk_exists(urfns, tm)
        let insts = term_match [] axtm urtm
        let ixth = INSTANTIATE insts axth
        let ixvs, ixbody = strip_exists(concl ixth)
        let ixtm = subst (zip urfns ixvs) ixbody
        let ixths = CONJUNCTS(ASSUME ixtm)
        let rixths = map (fun t -> find (aconv t << concl) ixths) rawcls
        let rixth = itlist SIMPLE_EXISTS ufns (end_itlist CONJ rixths)
        PROVE_HYP ixth (itlist SIMPLE_CHOOSE urfns rixth)
    let canonize t = 
        let avs, bod = strip_forall t
        let l, r = dest_eq bod
        let fn, args = strip_comb l
        let rarg = hd args
        let vargs = tl args
        let l' = Choice.get <| mk_comb(fn, rarg)
        let r' = list_mk_abs(vargs, r)
        let fvs = frees rarg
        let def = ASSUME(list_mk_forall(fvs, mk_eq(l', r')))
        GENL avs (RIGHT_BETAS vargs (SPECL fvs def))
    let prove_canon_recursive_functions_exist ax tm = 
        let ths = map canonize (conjuncts tm)
        let atm = list_mk_conj(map (hd << hyp) ths)
        let aths = CONJUNCTS(ASSUME atm)
        let rth = end_itlist CONJ (map2 PROVE_HYP aths ths)
        let eth = prove_raw_recursive_functions_exist ax atm
        let evs = fst(strip_exists(concl eth))
        PROVE_HYP eth (itlist SIMPLE_CHOOSE evs (itlist SIMPLE_EXISTS evs rth))
    let reshuffle fn args acc = 
        let args' = uncurry (C (@)) (partition is_var args)
        if args = args'
        then acc
        else 
            let gvs = map (genvar << Choice.get << type_of) args
            let gvs' =
                args'
                |> map (fun x ->
                    assoc x (zip args gvs)
                    |> Option.getOrFailWith "find")
            let lty = 
                itlist (mk_fun_ty << Choice.get << type_of) gvs' (funpow (length gvs) (hd << tl << snd << Choice.get << dest_type) (Choice.get <| type_of fn))
            let fn' = genvar lty
            let def = mk_eq(fn, list_mk_abs(gvs, list_mk_comb(fn', gvs')))
            (ASSUME def) :: acc
    let scrub_def t th = 
        let l, r = dest_eq t
        MP (INST [r, l] (DISCH t th)) (REFL r)
    fun ax tm -> 
        let rawcls = conjuncts tm
        let spcls = map (snd << strip_forall) rawcls
        let lpats = map (strip_comb << lhand) spcls
        let ufns = itlist (insert << fst) lpats []
        let uxargs = map (fun x -> assoc x lpats |> Option.getOrFailWith "find") ufns
        let trths = itlist2 reshuffle ufns uxargs []
        let tth = GEN_REWRITE_CONV REDEPTH_CONV (BETA_THM :: trths) tm
        let eth = prove_canon_recursive_functions_exist ax (rand(concl tth))
        let evs, ebod = strip_exists(concl eth)
        let fth = itlist SIMPLE_EXISTS ufns (EQ_MP (SYM tth) (ASSUME ebod))
        let gth = itlist scrub_def (map concl trths) fth
        PROVE_HYP eth (itlist SIMPLE_CHOOSE evs gth)

(* ------------------------------------------------------------------------- *)
(* Version that defines function(s).                                         *)
(* ------------------------------------------------------------------------- *)
/// Define recursive function over inductive type.
let new_recursive_definition = 
    let the_recursive_definitions = ref []
    let find_redefinition tm th = 
        let th' = PART_MATCH I th tm
        ignore(PART_MATCH I th' (concl th))
        th'
    fun ax tm -> 
        try 
            let th = tryfind (find_redefinition tm) (!the_recursive_definitions)
            warn true "Benign redefinition of recursive function"
            th
        with
        | Failure _ -> 
            let rawcls = conjuncts tm
            let spcls = map (snd << strip_forall) rawcls
            let lpats = map (strip_comb << lhand) spcls
            let ufns = itlist (insert << fst) lpats []
            let fvs = map (fun t -> subtract (frees t) ufns) rawcls
            let gcls = map2 (curry list_mk_forall) fvs rawcls
            let eth = prove_recursive_functions_exist ax (list_mk_conj gcls)
            let evs, bod = strip_exists(concl eth)
            let dth = new_specification (map (fst << Choice.get << dest_var) evs) eth
            let dths = map2 SPECL fvs (CONJUNCTS dth)
            let th = end_itlist CONJ dths
            the_recursive_definitions := th :: (!the_recursive_definitions)
            th
