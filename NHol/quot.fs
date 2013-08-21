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
#endif

infof "Entering quot.fs"

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
        choice {
            let! ty1 = type_of eqv
            let! (_, tms) = dest_type ty1
            let ty = hd tms
            let! pty = mk_fun_ty ty bool_ty
            let s = mk_var("s", pty)
            let x = mk_var("x", ty)
            let! eqvx = mk_comb(eqv, x)
            let! tm1 = mk_eq(s, eqvx)
            let! tm2 = mk_exists(x, tm1)
            let! pred = mk_abs(s, tm2)
            let! tm2' = mk_comb(pred, eqvx)
            let! th0 = BETA_CONV tm2'
            let! tm3 = rand <| concl th0
            let! th1 = EXISTS (tm3, x) (REFL eqvx)
            let! th2 = EQ_MP (SYM (Choice.result th0)) (Choice.result th1)
            let abs, rep = new_basic_type_definition tyname (absname, repname) (Choice.result th2)
            return abs, CONV_RULE (LAND_CONV BETA_CONV) rep
        }
        |> Choice.getOrFailure2 "define_quotient_type"

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

    fun (tybij2 : Protected<thm0>) -> 
        let v =
            choice {
                let! tybij2 = tybij2
                let! tybl, tybr = dest_comb <| concl tybij2
                let! tm1 = rand tybl
                let! tm2 = rand tm1
                let! tm3 = body tm2
                let! eqvx = rand tm3
                let! eqv, xtm = dest_comb eqvx
                let! dmr, rtm = dest_eq tybr
                let! dest, mrt = dest_comb dmr
                let! mk = rator mrt
                let! ety = type_of mrt
                return (eqvx, eqv, xtm, rtm, dest, mk, ety)
            }

        fun (refl_th, trans_th) fname wth -> 
            choice {
                let! (eqvx, eqv, xtm, rtm, dest, mk, ety) = v

                let! refl_th = refl_th
                let! trans_th = trans_th
                let! wth = wth

                let tm1 = concl wth
                let wtm = repeat (Choice.toOption << Choice.map snd << dest_forall) tm1
                let wfvs = frees wtm
                let! hyps, con = 
                    Choice.map (conjuncts ||>> I) (dest_imp wtm)
                    |> Choice.bindError (function Failure _ -> Choice.result ([], wtm) | e -> Choice.error e)

                let eqs, rels = partition is_eq hyps
                let! rvs = Choice.List.map lhand rels
                let! qvs = Choice.List.map lhs eqs
                let! tms1 = Choice.List.map (fun v -> dest_var v |> Choice.map (fun (tm1, _) -> mk_var(tm1, ety))) rvs
                let! evs = variants wfvs tms1
                let! mems = Choice.List.map2 (fun rv ev -> mk_comb(dest, ev) |> Choice.bind (fun tm1 -> mk_comb(tm1, rv))) rvs evs

                let! lcon, rcon = dest_comb con
                let! ty1 = type_of rcon
                let! u = variant (evs @ wfvs) (mk_var("u", ty1))
                let! ucon = mk_comb(lcon, u)
                let! dbod = list_mk_conj(ucon :: mems)
                let! detm = list_mk_exists(rvs, dbod)
                let! datm = mk_abs(u, detm)
                let! def = 
                    if is_eq con then list_mk_icomb "@" [datm]
                    else mk_comb(mk, datm)

                let! newargs = 
                    Choice.List.map (fun e -> 
                        lhs e                            
                        |> Choice.bindError (fun _ ->
                            choice {
                                let! tm1 = lhand e
                                return! assoc tm1 (zip rvs evs)
                                        |> Option.toChoiceWithError "find"
                            })) hyps

                let! rdef = list_mk_abs(newargs, def)
                let! ty2 = type_of rdef
                let ldef = mk_var(fname, ty2)
                let! dth = Choice.bind new_definition (mk_eq(ldef, rdef))
                let! eth = 
                    Choice.List.fold 
                        (fun th v -> CONV_RULE (RAND_CONV BETA_CONV) (AP_THM (Choice.result th) v)) dth newargs

                let! targs = Choice.List.map (fun v -> mk_comb(eqv, v) |> Choice.bind (fun tm1 -> mk_comb(mk, tm1))) rvs
                let! dme_th = 
                    choice {
                        let! th = INST [eqvx, rtm] tybij2
                        let! tm1 = lhs <| concl th
                        return! EQ_MP (Choice.result th) (EXISTS (tm1, xtm) (REFL eqvx))
                    }

                let! ith = INST (zip targs evs) (Choice.result eth)
                let! jth = SUBS (map (fun v -> INST [v, xtm] (Choice.result dme_th)) rvs) (Choice.result ith)
                let! tm2 = rand <| concl jth
                let! apop, uxtm = dest_comb tm2
                let! extm = body uxtm
                let evs, bod = strip_exists extm
                let! th1 = ASSUME bod
                let! th2 = 
                    choice {
                        if evs = [] then 
                            return th1
                        else 
                            let th2a, th2b = CONJ_PAIR (Choice.result th1)
                            let ethlist = CONJUNCTS th2b @ map REFL qvs
                            let! tms2 = Choice.List.map 
                                         (fun v -> 
                                            Choice.List.tryFind (fun th -> 
                                                choice {
                                                    let! th = th
                                                    let tm1 = concl th
                                                    let! tm2 = lhand tm1
                                                    let! tm3 = lhand v
                                                    return tm2 = tm3
                                                }) ethlist
                                            |> Choice.bind (Option.toChoiceWithError "find")) hyps

                            let! th2c = end_itlist CONJ tms2
                            let! th2d = MATCH_MP (Choice.result wth) (Choice.result th2c)
                            let! th2e = 
                                TRANS (Choice.result th2d) th2a
                                |> Choice.bindError (fun _ -> MATCH_MP (Choice.result trans_th) (CONJ (Choice.result th2d) th2a))
                            return! itlist SIMPLE_CHOOSE evs (Choice.result th2e)
                    }

                let! th3 = ASSUME <| concl th2
                let! th4 = end_itlist CONJ (Choice.result th3 :: (map (C SPEC (Choice.result refl_th)) rvs))
                let! th5 = itlist SIMPLE_EXISTS evs (ASSUME bod)
                let! th6 = MATCH_MP (DISCH_ALL (Choice.result th5)) (Choice.result th4)
                let! th7 = IMP_ANTISYM_RULE (DISCH_ALL (Choice.result th2)) (DISCH_ALL (Choice.result th6))
                let! th8 = TRANS (Choice.result jth) (AP_TERM apop (ABS u (Choice.result th7)))
                let fconv = 
                    if is_eq con then REWR_CONV SELECT_LEMMA
                    else RAND_CONV ETA_CONV
                let! th9 = CONV_RULE (RAND_CONV fconv) (Choice.result th8)
                return Choice.result eth, GSYM (Choice.result th9)
            }
            |> Choice.getOrFailure2 "lift_function"

(* ------------------------------------------------------------------------- *)
(* Lifts a theorem. This can be done by higher order rewriting alone.        *)
(*                                                                           *)
(* NB! All and only the first order variables must be bound by quantifiers.  *)
(* ------------------------------------------------------------------------- *)

/// Lifts a theorem to quotient type from representing type.
let lift_theorem = 
    let pth = 
        // NOTE: investigate this soon
        assumeProof
            prove
            ((parse_term @"(!x:Repty. R x x) /\ (!x y. R x y <=> R y x) /\ (!x y z. R x y /\ R y z ==> R x z) /\ (!a. mk(dest a) = a) /\ (!r. (?x. r = R x) <=> (dest(mk r) = r)) ==> (!x y. R x y <=> (mk(R x) = mk(R y))) /\ (!P. (!x. P(mk(R x))) <=> (!x. P x)) /\ (!P. (?x. P(mk(R x))) <=> (?x. P x)) /\ (!x:Absty. mk(R((@)(dest x))) = x)"), 
             STRIP_TAC
             |> THEN <| SUBGOAL_THEN 
                            (parse_term @"!x y. (mk((R:Repty->Repty->bool) x):Absty = mk(R y)) <=> (R x = R y)") 
                            ASSUME_TAC
             |> THENL <| [ASM_MESON_TAC [];
                          ALL_TAC]
             |> THEN <| MATCH_MP_TAC
                            (TAUT (parse_term @"(a /\ b /\ c) /\ (b ==> a ==> d) ==> a /\ b /\ c /\ d"))
             |> THEN <| CONJ_TAC
             |> THENL <| [ASM_REWRITE_TAC []
                          |> THEN <| REWRITE_TAC [FUN_EQ_THM]
                          |> THEN <| ASM_MESON_TAC []
                          ALL_TAC]
             |> THEN <| REPEAT(DISCH_THEN(fun th -> REWRITE_TAC [GSYM th]))
             |> THEN <| X_GEN_TAC(parse_term @"x:Repty")
             |> THEN  <| SUBGOAL_THEN 
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
        fun trths -> 
            fun th ->
                choice {
                    let! _ = refl_th
                    let! _ = sym_th
                    let! _ = trans_th
                    let! _ = ith
                    let! _ = th
                    let! _ = Choice.List.map id trths
                    return! REWRITE_RULE(ith :: trths) th
                }
