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
/// Derived rules for defining quotient types.
module NHol.quot

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
#endif

(* ------------------------------------------------------------------------- *)
(* Given a type name "ty" and a curried binary relation R, this defines      *)
(* a new type "ty" of R-equivalence classes. The abstraction and             *)
(* representation functions for the new type are called "mk_ty" and          *)
(* "dest_ty". The type bijections (after beta-conversion) are returned:      *)
(*                                                                           *)
(*             |- mk_ty (dest_ty a) = a                                      *)
(*                                                                           *)
(*             |- (?x. r = R x) <=> (dest_ty (mk_ty r) = r)                  *)
(* ------------------------------------------------------------------------- *)
/// Defines a quotient type based on given equivalence relation.
let define_quotient_type = 
    fun tyname (absname, repname) eqv -> 
        let ty = hd(snd(Choice.get <| dest_type(Choice.get <| type_of eqv)))
        let pty = Choice.get <| mk_fun_ty ty bool_ty
        let s = mk_var("s", pty)
        let x = mk_var("x", ty)
        let eqvx = Choice.get <| mk_comb(eqv, x)
        let pred = Choice.get <| mk_abs(s, Choice.get <| mk_exists(x, Choice.get <| mk_eq(s, eqvx)))
        let th0 = BETA_CONV(Choice.get <| mk_comb(pred, eqvx))
        let th1 = EXISTS (Choice.get <| rand(concl <| Choice.get th0), x) (REFL eqvx)
        let th2 = EQ_MP (SYM th0) th1
        let abs, rep = new_basic_type_definition tyname (absname, repname) th2
        abs, CONV_RULE (LAND_CONV BETA_CONV) rep

(* ------------------------------------------------------------------------- *)
(* Given a welldefinedness theorem for a curried function f, of the form:    *)
(*                                                                           *)
(* |- !x1 x1' .. xn xn'. (x1 == x1') /\ ... /\ (xn == xn')                   *)
(*                       ==> (f x1 .. xn == f x1' .. f nx')                  *)
(*                                                                           *)
(* where each "==" is either equality or some fixed binary relation R, a     *)
(* new operator called "opname" is introduced which lifts "f" up to the      *)
(* R-equivalence classes. Two theorems are returned: the actual definition   *)
(* and a useful consequence for lifting theorems.                            *)
(*                                                                           *)
(* The function also needs the second (more complicated) type bijection, and *)
(* the reflexivity and transitivity (not symmetry!) of the equivalence       *)
(* relation. The use also gives a name for the new function.                 *)
(* ------------------------------------------------------------------------- *)
/// Lift a function on representing type to quotient type of equivalence classes.
let lift_function = 
    let SELECT_LEMMA = 
        prove
            ((parse_term @"!x:A. (@y. x = y) = x"), 
             GEN_TAC
             |> THEN <| GEN_REWRITE_TAC (LAND_CONV << BINDER_CONV) [EQ_SYM_EQ]
             |> THEN <| MATCH_ACCEPT_TAC SELECT_REFL)
    fun tybij2 -> 
        let tybl, tybr = Choice.get <| dest_comb(concl <| Choice.get tybij2)
        let eqvx = Choice.get <| rand(Choice.get <| body(Choice.get <| rand(Choice.get <| rand tybl)))
        let eqv, xtm = Choice.get <| dest_comb eqvx
        let dmr, rtm = Choice.get <| dest_eq tybr
        let dest, mrt = Choice.get <| dest_comb dmr
        let mk = Choice.get <| rator mrt
        let ety = Choice.get <| type_of mrt
        fun (refl_th, trans_th) fname wth -> 
            let wtm = repeat (Choice.toOption << Choice.map snd << dest_forall) (concl <| Choice.get wth)
            let wfvs = frees wtm
            let hyps, con = 
                try 
                    (conjuncts ||>> I)(Choice.get <| dest_imp wtm)
                with
                | Failure _ -> [], wtm
            let eqs, rels = partition is_eq hyps
            let rvs = map (Choice.get << lhand) rels
            let qvs = map (Choice.get << lhs) eqs
            let evs = 
                Choice.get <| variants wfvs (map (fun v -> mk_var(fst(Choice.get <| dest_var v), ety)) rvs)
            let mems = 
                map2 (fun rv ev -> Choice.get <| mk_comb(Choice.get <| mk_comb(dest, ev), rv)) rvs evs
            let lcon, rcon = Choice.get <| dest_comb con
            let u = Choice.get <| variant (evs @ wfvs) (mk_var("u", Choice.get <| type_of rcon))
            let ucon = Choice.get <| mk_comb(lcon, u)
            let dbod = list_mk_conj(ucon :: mems)
            let detm = list_mk_exists(rvs, dbod)
            let datm = Choice.get <| mk_abs(u, detm)
            let def = 
                if is_eq con
                then Choice.get <| list_mk_icomb "@" [datm]
                else Choice.get <| mk_comb(mk, datm)
            let newargs = 
                map (fun e -> 
                        try 
                            Choice.get <| lhs e
                        with
                        | Failure _ as ex ->
                            match assoc (Choice.get <| lhand e) (zip rvs evs) with
                            | Some x -> x
                            | None ->
                                nestedFailwith ex "find") hyps
            let rdef = list_mk_abs(newargs, def)
            let ldef = mk_var(fname, Choice.get <| type_of rdef)
            let dth = new_definition(Choice.get <| mk_eq(ldef, rdef))
            let eth = 
                rev_itlist 
                    (fun v th -> CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th v)) 
                    newargs dth
            let targs = map (fun v -> Choice.get <| mk_comb(mk, Choice.get <| mk_comb(eqv, v))) rvs
            let dme_th = 
                let th = INST [eqvx, rtm] tybij2
                EQ_MP th (EXISTS (Choice.get <| lhs(concl <| Choice.get th), xtm) (REFL eqvx))
            let ith = INST (zip targs evs) eth
            let jth = SUBS (map (fun v -> INST [v, xtm] dme_th) rvs) ith
            let apop, uxtm = Choice.get <| dest_comb(Choice.get <| rand(concl <| Choice.get jth))
            let extm = Choice.get <| body uxtm
            let evs, bod = strip_exists extm
            let th1 = ASSUME bod
            let th2 = 
                if evs = []
                then th1
                else 
                    let th2a, th2b = CONJ_PAIR th1
                    let ethlist = CONJUNCTS th2b @ map REFL qvs
                    let th2c = 
                        end_itlist CONJ 
                            (map 
                                 (fun v -> 
                                     Option.get <| find ((=)(Choice.get <| lhand v) << Choice.get << lhand << concl << Choice.get) 
                                         ethlist) hyps)
                    let th2d = MATCH_MP wth th2c
                    let th2e = 
                        try 
                            TRANS th2d th2a
                        with
                        | Failure _ -> MATCH_MP trans_th (CONJ th2d th2a)
                    itlist SIMPLE_CHOOSE evs th2e
            let th3 = ASSUME(concl <| Choice.get th2)
            let th4 = end_itlist CONJ (th3 :: (map (C SPEC refl_th) rvs))
            let th5 = itlist SIMPLE_EXISTS evs (ASSUME bod)
            let th6 = MATCH_MP (DISCH_ALL th5) th4
            let th7 = IMP_ANTISYM_RULE (DISCH_ALL th2) (DISCH_ALL th6)
            let th8 = TRANS jth (AP_TERM apop (ABS u th7))
            let fconv = 
                if is_eq con
                then REWR_CONV SELECT_LEMMA
                else RAND_CONV ETA_CONV
            let th9 = CONV_RULE (RAND_CONV fconv) th8
            eth, GSYM th9

(* ------------------------------------------------------------------------- *)
(* Lifts a theorem. This can be done by higher order rewriting alone.        *)
(*                                                                           *)
(* NB! All and only the first order Choice.get <| variables must be bound by quantifiers.  *)
(* ------------------------------------------------------------------------- *)
/// Lifts a theorem to quotient type from representing type.
let lift_theorem = 
    let pth = 
        prove
            ((parse_term @"(!x:Repty. R x x) /\ (!x y. R x y <=> R y x) /\ (!x y z. R x y /\ R y z ==> R x z) /\ (!a. mk(dest a) = a) /\ (!r. (?x. r = R x) <=> (dest(mk r) = r)) ==> (!x y. R x y <=> (mk(R x) = mk(R y))) /\ (!P. (!x. P(mk(R x))) <=> (!x. P x)) /\ (!P. (?x. P(mk(R x))) <=> (?x. P x)) /\ (!x:Absty. mk(R((@)(dest x))) = x)"), 
             STRIP_TAC
             |> THEN 
             <| SUBGOAL_THEN 
                    (parse_term @"!x y. (mk((R:Repty->Repty->bool) x):Absty = mk(R y)) <=> (R x = R y)") 
                    ASSUME_TAC
             |> THENL <| [ASM_MESON_TAC []
                          ALL_TAC]
             |> THEN 
             <| MATCH_MP_TAC
                    (TAUT
                         (parse_term @"(a /\ b /\ c) /\ (b ==> a ==> d) ==> a /\ b /\ c /\ d"))
             |> THEN <| CONJ_TAC
             |> THENL <| [ASM_REWRITE_TAC []
                          |> THEN <| REWRITE_TAC [FUN_EQ_THM]
                          |> THEN <| ASM_MESON_TAC []
                          ALL_TAC]
             |> THEN <| REPEAT(DISCH_THEN(fun th -> REWRITE_TAC [GSYM th]))
             |> THEN <| X_GEN_TAC(parse_term @"x:Repty")
             |> THEN 
             <| SUBGOAL_THEN 
                    (parse_term @"dest(mk((R:Repty->Repty->bool) x):Absty) = R x") 
                    SUBST1_TAC
             |> THENL <| [ASM_MESON_TAC []
                          ALL_TAC]
             |> THEN <| GEN_REWRITE_TAC (LAND_CONV << RAND_CONV) [GSYM ETA_AX]
             |> THEN <| FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [th])
             |> THEN <| CONV_TAC SELECT_CONV
             |> THEN <| ASM_MESON_TAC [])
    fun tybij (refl_th, sym_th, trans_th) -> 
        let tybij1 = GEN_ALL(fst tybij)
        let tybij2 = GEN_ALL(snd tybij)
        let cth = end_itlist CONJ [refl_th; sym_th; trans_th; tybij1; tybij2]
        let ith = MATCH_MP pth cth
        fun trths -> REWRITE_RULE(ith :: trths)
