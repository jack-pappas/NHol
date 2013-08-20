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
/// Derived rules for inductive definitions.
module NHol.ind_defs

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
open simp
open theorems
#endif

infof "Entering ind_defs.fs"

(* ------------------------------------------------------------------------- *)
(* Strip off exactly n arguments from combination.                           *)
(* ------------------------------------------------------------------------- *)

/// Strip away a given number of arguments from a combination.
let strip_ncomb : _ -> _ -> Protected<_> = 
    let rec strip(n, tm, acc) = 
        choice {
            if n < 1 then 
                return tm, acc
            else 
                let! l, r = dest_comb tm
                return! strip(n - 1, l, r :: acc)
        }
    fun n tm -> strip(n, tm, [])

(* ------------------------------------------------------------------------- *)
(* Expand lambda-term function definition with its arguments.                *)
(* ------------------------------------------------------------------------- *)

/// Apply and beta-reduce equational theorem with abstraction on RHS.
let RIGHT_BETAS = 
    fun tms th ->
        choice {
            let! th = th
            return! Choice.List.fold (fun th tm -> 
                        (CONV_RULE(RAND_CONV BETA_CONV) << C AP_THM tm) (Choice.result th)) th tms
        }

(* ------------------------------------------------------------------------- *)
(*      A, x = t |- P[x]                                                     *)
(*     ------------------ EXISTS_EQUATION                                    *)
(*        A |- ?x. P[x]                                                      *)
(* ------------------------------------------------------------------------- *)

/// Derives existence from explicit equational constraint.
let EXISTS_EQUATION = 
    let pth = 
        prove
            ((parse_term @"!P t. (!x:A. (x = t) ==> P x) ==> (?) P"), 
             REWRITE_TAC [EXISTS_DEF]
             |> THEN <| BETA_TAC
             |> THEN <| REPEAT STRIP_TAC
             |> THEN <| FIRST_ASSUM MATCH_MP_TAC
             |> THEN <| EXISTS_TAC(parse_term @"t:A")
             |> THEN <| FIRST_ASSUM MATCH_MP_TAC
             |> THEN <| REFL_TAC)
    fun tm (th : Protected<thm0>) -> 
        choice {
            let! th = th
            let! pth = pth
            let! l, r = dest_eq tm
            let tm' = concl th
            let! P = mk_abs(l, tm')
            let! tm1 = mk_comb(P, l)
            let! th1 = BETA_CONV tm1
            let! th2 = ISPECL [P; r] (Choice.result pth)
            let! th2' = SYM (Choice.result th1)
            let! th3 = EQ_MP (Choice.result th2') (Choice.result th)
            let! th3' = DISCH tm (Choice.result th3)
            let! th4 = GEN l (Choice.result th3')
            return! MP (Choice.result th2) (Choice.result th4)
        } : Protected<thm0>

(* ========================================================================= *)
(* Part 1: The main part of the inductive definitions package.               *)
(* This proves that a certain definition yields the requires theorems.       *)
(* ========================================================================= *)

/// Deduce inductive definitions properties from an explicit assignment.
let derive_nonschematic_inductive_relations : conv = 
    let getconcl tm = 
        let bod = repeat (Choice.toOption << Choice.map snd << dest_forall) tm
        choice {
            let! (_, bod') = dest_imp bod
            return bod'
        }
        |> Choice.fill bod

    let CONJ_ACI_RULE = AC CONJ_ACI

    let SIMPLE_DISJ_PAIR th = 
        choice {
            let! th = th
            let tms = hyp th
            let! l, r = dest_disj <| hd tms
            let! th1 = ASSUME l
            let! th2 = DISJ1 (Choice.result th1) r
            let! th3 = PROVE_HYP (Choice.result th2) (Choice.result th)
            let! th4 = ASSUME r
            let! th5 = DISJ2 l (Choice.result th4)
            let! th6 = PROVE_HYP (Choice.result th5) (Choice.result th)
            return Choice.result th3, Choice.result th6
        }

    let HALF_BETA_EXPAND args th = 
        choice {
            let! th = th
            let! th1 = RIGHT_BETAS args (Choice.result th)
            return! GENL args (Choice.result th1)
        }

    let AND_IMPS_CONV tm = 
        choice {
            let ths = CONJUNCTS(ASSUME tm)
            let! th' = hd ths
            let tm' = concl th'
            let avs = fst(strip_forall tm')
            let thl = map (DISCH tm << UNDISCH << SPEC_ALL) ths
            let! th1 = end_itlist SIMPLE_DISJ_CASES thl
            let tm1 = hd <| hyp th1
            let! th1' = UNDISCH (Choice.result th1)
            let! th1'' = DISCH tm1 (Choice.result th1')
            let! th2 = GENL avs (Choice.result th1'')
            let tm2 = concl th2
            let! th3 = DISCH tm2 (UNDISCH(SPEC_ALL(ASSUME tm2)))
            let! thts, tht = Choice.List.nsplit SIMPLE_DISJ_PAIR (tl ths) (Choice.result th3)
            let proc_fn th = 
                choice {
                    let! th = th
                    let t = hd <| hyp th
                    return! GENL avs (DISCH t (UNDISCH (Choice.result th)))
                }

            let! th4 = itlist (CONJ << proc_fn) thts (proc_fn tht)
            return! IMP_ANTISYM_RULE (DISCH_ALL (Choice.result th2)) (DISCH_ALL (Choice.result th4))
        }

    let t_tm = (parse_term @"T")

    let calculate_simp_sequence = 
        let rec getequs(avs, plis) = 
            if plis = [] then []
            else 
                match plis with
                | h :: t ->
                    let r = snd h
                    if mem r avs then 
                        h :: (getequs(avs, filter ((<>) r << snd) t))
                    else getequs(avs, t)
                | [] -> failwith "getequs: Empty list."
        fun avs plis -> 
            let oks = getequs(avs, plis)
            oks, subtract plis oks

    let FORALL_IMPS_CONV tm = 
        choice {
            let avs, bod = strip_forall tm
            let! th1 = DISCH tm (UNDISCH(SPEC_ALL(ASSUME tm)))
            let! th2 = itlist SIMPLE_CHOOSE avs (Choice.result th1)
            let tm2 = hd <| hyp th2
            let! th3 = DISCH tm2 (UNDISCH (Choice.result th2))
            let! th4 = ASSUME <| concl th3
            let! ant = lhand bod
            let! th5 = itlist SIMPLE_EXISTS avs (ASSUME ant)
            let! th6 = GENL avs (DISCH ant (MP (Choice.result th4) (Choice.result th5)))
            return! IMP_ANTISYM_RULE (DISCH_ALL (Choice.result th3)) (DISCH_ALL (Choice.result th6))
        }

    let canonicalize_clause cls args = 
        choice {
            let avs, bimp = strip_forall cls
            let! ant, con = 
                dest_imp bimp
                |> Choice.bindError (function Failure _ -> Choice.result (t_tm, bimp) | e -> Choice.error e)

            let rel, xargs = strip_comb con
            let plis = zip args xargs
            let yes, no = calculate_simp_sequence avs plis
            let nvs = filter (not << C mem (map snd yes)) avs
            let! eth = 
                choice {
                    if is_imp bimp then 
                        let atm = itlist (curry (Choice.get << mk_conj) << Choice.get << mk_eq) (yes @ no) ant
                        let ths, tth = nsplit CONJ_PAIR plis (ASSUME atm)
                        let! thl = Choice.List.map (fun t -> 
                                        Choice.List.tryFind (fun th -> 
                                            choice {
                                                let! th = th
                                                let tm1 = concl th
                                                let! tm2 = lhs tm1
                                                return tm2 = t
                                            }) ths
                                        |> Choice.bind (Option.toChoiceWithError "find")
                                            ) args

                        let! th0 = MP (SPECL avs (ASSUME cls)) tth
                        let! th1' = REFL rel
                        // NOTE: revise order of arguments
                        let! th1 = Choice.List.fold (fun acc x -> MK_COMB(Choice.result acc, x)) th1' thl
                        let! th2 = EQ_MP (SYM (Choice.result th1)) (Choice.result th0)
                        let! th3 = INST yes (DISCH atm (Choice.result th2))
                        let! tm3 = lhand <| concl th3
                        let! tm4 = Choice.funpow (length yes) rand tm3
                        let! th4 = itlist (CONJ << REFL << fst) yes (ASSUME tm4)
                        let! th5 = GENL args (GENL nvs (DISCH tm4 (MP (Choice.result th3) (Choice.result th4))))
                        let tm5 = concl th5
                        let! th6 = SPECL nvs (SPECL (map snd plis) (ASSUME tm5))
                        let! th7 = itlist (CONJ << REFL << snd) no (ASSUME ant)
                        let! th8 = GENL avs (DISCH ant (MP (Choice.result th6) (Choice.result th7)))
                        return! IMP_ANTISYM_RULE (DISCH_ALL (Choice.result th5)) (DISCH_ALL (Choice.result th8))
                    else
                        let! tms = Choice.List.map mk_eq (yes @ no)
                        let! atm = list_mk_conj tms
                        let ths = CONJUNCTS(ASSUME atm)
                        let! thl = Choice.List.map (fun t -> 
                                        Choice.List.tryFind (fun th -> 
                                            choice {
                                                let! th = th
                                                let tm1 = concl th
                                                let! tm2 = lhs tm1
                                                return tm2 = t
                                            }) ths
                                        |> Choice.bind (Option.toChoiceWithError "find")) args
                        let! th0 = SPECL avs (ASSUME cls)
                        let! th1' = REFL rel
                        let! th1 = Choice.List.fold (fun acc x -> MK_COMB(Choice.result acc, x)) th1' thl
                        let! th2 = EQ_MP (SYM (Choice.result th1)) (Choice.result th0)
                        let! th3 = INST yes (DISCH atm (Choice.result th2))
                        let! tm3 = lhand <| concl th3
                        let! tm4 = Choice.funpow (length yes) rand tm3
                        let! th4 = itlist (CONJ << REFL << fst) yes (ASSUME tm4)
                        let! th5 = GENL args (GENL nvs (DISCH tm4 (MP (Choice.result th3) (Choice.result th4))))
                        let tm5 = concl th5
                        let! th6 = SPECL nvs (SPECL (map snd plis) (ASSUME tm5))
                        let! th7 = end_itlist CONJ (map (REFL << snd) no)
                        let! th8 = GENL avs (MP (Choice.result th6) (Choice.result th7))
                        return! IMP_ANTISYM_RULE (DISCH_ALL (Choice.result th5)) (DISCH_ALL (Choice.result th8))
                }

            let! tm1 = rand <| concl eth
            let! ftm = Choice.funpow (length args) (Choice.bind body << rand) tm1
            return! TRANS (Choice.result eth) (itlist MK_FORALL args (FORALL_IMPS_CONV ftm))
        }

    let canonicalize_clauses clauses = 
        choice {
            let concls = map getconcl clauses
            let uncs = map strip_comb concls
            let rels = itlist (insert << fst) uncs []
            let! xargs = rels |> Choice.List.map (fun x -> assoc x uncs |> Option.toChoiceWithError "find")
            let! closed = list_mk_conj clauses
            let! avoids = variables closed
            let! tys = Choice.List.map type_of (end_itlist (@) xargs)
            let! flargs = make_args "a" avoids tys
            let zargs = zip rels (shareout xargs flargs)
            let! cargs = uncs |> Choice.List.map (fun (r, a) -> assoc r zargs |> Option.toChoiceWithError "find")
            let! cthms = Choice.List.map2 canonicalize_clause clauses cargs
            let! pclauses = Choice.List.map (rand << concl) cthms
            let collectclauses tm = 
                mapfilter (fun t -> 
                    if fst t = tm then Some (snd t) else None) (zip (map fst uncs) pclauses)
            let clausell = map collectclauses rels
            let! cclausel = Choice.List.map list_mk_conj clausell
            let! cclauses = list_mk_conj cclausel
            let! oclauses = list_mk_conj pclauses
            let! tm' = mk_eq (oclauses, cclauses)
            let! eth = CONJ_ACI_RULE tm'
            let! pth = TRANS (Choice.List.reduceBack (fun x acc -> MK_CONJ (Choice.result x) (Choice.result acc)) cthms) (Choice.result eth)
            return! TRANS (Choice.result pth) (end_itlist MK_CONJ (map AND_IMPS_CONV cclausel))
        }

    let derive_canon_inductive_relations clauses = 
        choice {
            let! closed = list_mk_conj clauses
            let clauses = conjuncts closed
            let vargs, bodies = unzip (map strip_forall clauses)
            let! tms = Choice.List.map dest_imp bodies
            let ants, concs = unzip tms
            let rels = map (repeat (Choice.toOption << rator)) concs
            let! avoids = variables closed
            let! rels' = variants avoids rels
            let crels = zip rels' rels
            let prime_fn = subst crels
            let! closed' = prime_fn closed
            let mk_def arg con = 
                choice {
                    let! tm = prime_fn con
                    let! tm' = mk_imp(closed', tm)
                    let! tm0 = list_mk_forall(rels', tm')
                    let! tm1 = list_mk_abs (arg, tm0)
                    return! mk_eq(repeat (Choice.toOption << rator) con, tm1)
                }

            let! deftms = Choice.List.map2 mk_def vargs concs
            let defthms = map2 HALF_BETA_EXPAND vargs (map ASSUME deftms)

            let mk_ind args th = 
                choice {
                    let th1 = fst(EQ_IMP_RULE(SPEC_ALL th))
                    let! ant = Choice.bind (lhand << concl) th1
                    let th2 = SPECL rels' (UNDISCH th1)
                    return! GENL args (DISCH ant (UNDISCH th2))
                }

            let indthms = map2 mk_ind vargs defthms
            let! indthmr = end_itlist CONJ indthms
            let! indthm = GENL rels' (DISCH closed' (Choice.result indthmr))
            let! mconcs = Choice.List.map2 (fun a t -> 
                            choice {
                                let! tm1 = prime_fn t
                                let! tm2 = mk_imp(t, tm1)
                                return! list_mk_forall(a, tm2)
                            }) vargs ants
            let tmr = concl indthmr
            let! tm2 = list_mk_conj mconcs
            let! monotm = mk_imp(tmr, tm2)
            let! tm3 = list_mk_forall(rels', monotm)
            let! tm4 = list_mk_forall(rels, tm3)
            let! monothm = ASSUME tm4
            let! closthm = ASSUME closed'
            let monothms = CONJUNCTS(MP (SPEC_ALL (Choice.result monothm)) (MP (SPECL rels' (Choice.result indthm)) (Choice.result closthm)))
            let closthms = CONJUNCTS (Choice.result closthm)

            let prove_rule mth (cth, dth) = 
                choice {
                    let! mth = mth
                    let! cth = cth
                    let! dth = dth
                    let avs, bod = strip_forall <| concl mth
                    let! th1 = IMP_TRANS (SPECL avs (Choice.result mth)) (SPECL avs (Choice.result cth))
                    let! th2 = GENL rels' (DISCH closed' (UNDISCH (Choice.result th1)))
                    let! th3 = EQ_MP (SYM(SPECL avs (Choice.result dth))) (Choice.result th2)
                    let! tm = lhand bod
                    return! GENL avs (DISCH tm (Choice.result th3))
                }

            let rulethms = map2 prove_rule monothms (zip closthms defthms)
            let! rulethm = end_itlist CONJ rulethms
            let! dtms = Choice.List.map2 (curry list_mk_abs) vargs ants
            let double_fn = subst (zip dtms rels)

            let mk_unbetas tm dtm = 
                choice {
                    let avs, bod = strip_forall tm
                    let! il, r = dest_comb bod
                    let! i, l = dest_comb il
                    let bth = RIGHT_BETAS avs (REFL dtm)
                    let munb = AP_THM (AP_TERM i bth) r
                    let! tm1 = double_fn l
                    let! tm2 = mk_comb(i, tm1)
                    let iunb = AP_TERM tm2 bth
                    let! tm3 = mk_comb(i, r)
                    let junb = AP_TERM tm3 bth
                    let quantify = itlist MK_FORALL avs
                    return (quantify munb, (quantify iunb, quantify junb))
                }

            let! unths = Choice.List.map2 mk_unbetas clauses dtms
            let! irthm = EQ_MP (SYM(end_itlist MK_CONJ (map fst unths))) (Choice.result rulethm)
            let! mrthm = MP (SPECL rels (SPECL dtms (Choice.result monothm))) (Choice.result irthm)
            let! imrth = EQ_MP (SYM(end_itlist MK_CONJ (map (fst << snd) unths))) (Choice.result mrthm)
            let! ifthm = MP (SPECL dtms (Choice.result indthm)) (Choice.result imrth)
            let! fthm = EQ_MP (end_itlist MK_CONJ (map (snd << snd) unths)) (Choice.result ifthm)

            let mk_case th1 th2 = 
                choice {
                    let! th1 = th1
                    let! th2 = th2
                    let avs = (fst << strip_forall << concl) th1
                    return! GENL avs (IMP_ANTISYM_RULE (SPEC_ALL (Choice.result th1)) (SPEC_ALL (Choice.result th2)))
                }

            let! casethm = end_itlist CONJ (map2 mk_case (CONJUNCTS (Choice.result fthm)) (CONJUNCTS (Choice.result rulethm)))
            return! CONJ (Choice.result rulethm) (CONJ (Choice.result indthm) (Choice.result casethm))
        }

    fun tm -> 
        choice {
            let clauses = conjuncts tm
            let! canonthm = canonicalize_clauses clauses
            let! canonthm' = SYM (Choice.result canonthm)
            let! pclosed = rand <| concl canonthm
            let pclauses = conjuncts pclosed
            let! rawthm = derive_canon_inductive_relations pclauses

            let rulethm, otherthms = CONJ_PAIR (Choice.result rawthm)
            let! rulethm = rulethm
            let! otherthms = otherthms

            let indthm, casethm = CONJ_PAIR (Choice.result otherthms)
            let! indthm = indthm
            let! casethm = casethm

            let! rulethm' = EQ_MP (Choice.result canonthm') (Choice.result rulethm)
            let! indthm' = CONV_RULE (ONCE_DEPTH_CONV(REWR_CONV (Choice.result canonthm'))) (Choice.result indthm)
            return! CONJ (Choice.result rulethm') (CONJ (Choice.result indthm') (Choice.result casethm))
        }

(* ========================================================================= *)
(* Part 2: Tactic-integrated tools for proving monotonicity automatically.   *)
(* ========================================================================= *)

let MONO_AND = 
    ITAUT(parse_term @"(A ==> B) /\ (C ==> D) ==> (A /\ C ==> B /\ D)")

let MONO_OR = ITAUT(parse_term @"(A ==> B) /\ (C ==> D) ==> (A \/ C ==> B \/ D)")

let MONO_IMP = 
    ITAUT(parse_term @"(B ==> A) /\ (C ==> D) ==> ((A ==> C) ==> (B ==> D))")

let MONO_NOT = ITAUT(parse_term @"(B ==> A) ==> (~A ==> ~B)")

let MONO_FORALL = 
    prove
        ((parse_term @"(!x:A. P x ==> Q x) ==> ((!x. P x) ==> (!x. Q x))"), 
         REPEAT STRIP_TAC
         |> THEN <| FIRST_ASSUM MATCH_MP_TAC
         |> THEN <| ASM_REWRITE_TAC [])

let MONO_EXISTS = 
    prove
        ((parse_term @"(!x:A. P x ==> Q x) ==> ((?x. P x) ==> (?x. Q x))"), 
         DISCH_TAC
         |> THEN <| DISCH_THEN(X_CHOOSE_TAC(parse_term @"x:A"))
         |> THEN <| EXISTS_TAC(parse_term @"x:A")
         |> THEN <| FIRST_ASSUM MATCH_MP_TAC
         |> THEN <| ASM_REWRITE_TAC [])

(* ------------------------------------------------------------------------- *)
(* Assignable list of monotonicity theorems, so users can add their own.     *)
(* ------------------------------------------------------------------------- *)

/// List of monotonicity theorems for inductive definitions package.
let monotonicity_theorems = 
    ref [MONO_AND; MONO_OR; MONO_IMP; MONO_NOT; MONO_EXISTS; MONO_FORALL]

(* ------------------------------------------------------------------------- *)
(* Attempt to backchain through the monotonicity theorems.                   *)
(* ------------------------------------------------------------------------- *)

/// Attempt to prove monotonicity theorem automatically.
let MONO_TAC : goal -> Protected<goalstate0> = 
    let imp = (parse_term @"(==>)")
    let IMP_REFL = ITAUT(parse_term @"!p. p ==> p")
    let BACKCHAIN_TAC th = 
        let match_fn = PART_MATCH (Choice.map snd << dest_imp) th
        fun (asl, w) -> 
            choice {
                let! th1 = match_fn w
                let! ant, con = dest_imp <| concl th1
                let fun1 l =
                    match l with
                    | [a] -> Choice.result a
                    | _ -> Choice.failwith "MONO_TAC.fun1: Unhandled case."
                let just =        
                    fun i tl -> MATCH_MP (INSTANTIATE i (Choice.result th1)) (fun1 tl)
                return (null_meta, [asl, ant], just)
            }

    let MONO_ABS_TAC(asl, w) = 
        choice {
            let! ant, con = dest_imp w
            let vars = snd(strip_comb con)
            let rnum = length vars - 1
            let! hd1, args1 = strip_ncomb rnum ant
            let! hd2, args2 = strip_ncomb rnum con
            let! hd1' = BETA_CONV hd1
            let! th1 = Choice.List.fold (fun acc x -> AP_THM (Choice.result acc) x) hd1' args1
            let! hd2' = BETA_CONV hd2
            let! th2 = Choice.List.fold (fun acc x -> AP_THM (Choice.result acc) x) hd2' args1
            let! th3 = MK_COMB(AP_TERM imp (Choice.result th1), Choice.result th2)
            let! _ = Choice.List.map snd asl
            return! CONV_TAC (REWR_CONV (Choice.result th3)) (asl, w)
        }

    let APPLY_MONOTAC tacs (asl, w) = 
        choice {
            let! a, c = dest_imp w
            if aconv a c then 
                let! _ = Choice.List.map snd asl
                return! ACCEPT_TAC (SPEC a IMP_REFL) (asl, w)
            else 
                let cn = 
                    choice {
                        let! (s, _) = dest_const(repeat (Choice.toOption << rator) c)
                        return s
                    }
                    |> Choice.fill ""

                return! 
                    tryfind (fun (k, t) -> 
                        if k = cn then Choice.toOption <| t(asl, w)
                        else None) tacs
                    |> Option.toChoiceWithError "tryfind"
        }

    fun gl -> 
        choice {
            let! tacs = 
                Choice.List.foldBack (fun th acc -> 
                        choice {
                            let! th = th
                            let! tm = Choice.funpow 2 rand (concl th)
                            let ft = repeat (Choice.toOption << rator) tm
                            let c = 
                                choice {
                                    let! (s, _) = dest_const ft
                                    return s
                                }
                                |> Choice.fill ""

                            return (c, BACKCHAIN_TAC (Choice.result th) |> THEN <| REPEAT CONJ_TAC) :: acc
                        }) (!monotonicity_theorems) ["", MONO_ABS_TAC]
            let MONO_STEP_TAC = REPEAT GEN_TAC
                                |> THEN <| APPLY_MONOTAC tacs
            return! (REPEAT MONO_STEP_TAC
                     |> THEN <| ASM_REWRITE_TAC []) gl
         }

(* ------------------------------------------------------------------------- *)
(* Attempt to dispose of the non-equational assumption(s) of a theorem.      *)
(* ------------------------------------------------------------------------- *)

/// Attempt to prove monotonicity hypotheses of theorem automatically.
let prove_monotonicity_hyps = 
    let tac = 
        REPEAT GEN_TAC
        |> THEN <| DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)
        |> THEN <| REPEAT CONJ_TAC
        |> THEN <| MONO_TAC
    let prove_mth t = prove(t, tac)
    fun (th : Protected<thm0>) -> 
        choice {
            let! th = th
            let tms = hyp th
            let mths = mapfilter (Choice.toOption << Choice.map Choice.result << prove_mth) (filter (not << is_eq) tms)
            return! itlist PROVE_HYP mths (Choice.result th)
        } : Protected<thm0>

(* ========================================================================= *)
(* Part 3: The final user wrapper, with schematic variables added.           *)
(* ========================================================================= *)

/// List of all definitions introduced so far.
let the_inductive_definitions : (Protected<thm0> * Protected<thm0> * Protected<thm0>) list ref = ref []

// prove_inductive_relations_exist: Prove existence of inductively defined relations without defining them.
// new_inductive_definition: Attempt to prove monotonicity hypotheses of theorem automatically.
let prove_inductive_relations_exist, new_inductive_definition = 
    let rec pare_comb qvs tm = 
        choice {
            if intersect (frees tm) qvs = [] && forall is_var (snd(strip_comb tm)) then 
                return tm
            else
                let! tm1 = rator tm
                return! pare_comb qvs tm1
        }
    let generalize_schematic_variables gflag vs = 
        let generalize_def tm th = 
            choice {
                let! th = th
                let! l, r = dest_eq tm
                let! lname, lty = dest_var l
                // TODO: revise due to massive changes
                let! tm1 = Choice.List.foldBack (fun x acc -> type_of x |> Choice.bind (fun y -> mk_fun_ty y acc)) vs lty
                let l' = mk_var(lname, tm1)
                let! r' = list_mk_abs(vs, r)
                let! tm2 = mk_eq(l', r')
                let! th0 = RIGHT_BETAS vs (ASSUME tm2)
                let! tm3 = lhs <| concl th0
                let! th1 = INST [tm3, l] (DISCH tm (Choice.result th))
                return! MP (Choice.result th1) (Choice.result th0)
            }

        fun (th : Protected<thm0>) -> 
            choice {
                let! th = th
                let tms = hyp th
                let defs, others = partition is_eq tms
                let! th1 = itlist generalize_def defs (Choice.result th)
                if gflag then 
                    let! others' = 
                        Choice.List.map (fun t -> 
                            choice {
                                let fvs = frees t
                                let! tm1 = list_mk_forall(fvs, t)
                                return SPECL fvs (ASSUME(tm1))
                            }) others
                    return! GENL vs (itlist PROVE_HYP others' (Choice.result th1))
                else 
                    return th1
            }

    let derive_existence (th : Protected<thm0>) = 
        choice {
            let! th = th
            let tms = hyp th
            let defs = filter is_eq tms
            return! itlist EXISTS_EQUATION defs (Choice.result th)
        }

    let make_definitions (th : Protected<thm0>) = 
        choice {
            let! th = th
            let tms = hyp th
            let defs = filter is_eq tms
            let! dths = Choice.List.map new_definition defs
            let! tms1 = Choice.List.map (lhs << concl) dths
            let! tms2 = Choice.List.map lhs defs
            let insts = zip tms1 tms2
            let! th1 = INST insts (itlist DISCH defs (Choice.result th))
            return! Choice.List.fold (fun acc x -> MP (Choice.result acc) (Choice.result x)) th1 dths
        }

    let unschematize_clauses clauses = 
        choice {
            let! schem = 
                Choice.List.map (fun cls -> 
                        let avs, bod = strip_forall cls
                        pare_comb avs (match dest_imp bod with
                                       | Success(_, bod') -> bod'
                                       | Error _ -> bod)) clauses
            let schems = setify schem
            if is_var(hd schem) then 
                return (clauses, [])
            elif not(length(setify(map (snd << strip_comb) schems)) = 1) then 
                return! Choice.failwith "Schematic variables not used consistently"
            else 
                let! tm0 = list_mk_conj clauses
                let! avoids = variables tm0
                let hack_fn tm = 
                    choice {
                        let! (tm1, _) = dest_var(repeat (Choice.toOption << rator) tm)
                        let! ty = type_of tm
                        return mk_var(tm1, ty)
                    }
                let! tms = Choice.List.map hack_fn schems
                let! grels = variants avoids tms
                let crels = zip grels schems
                let! clauses' = Choice.List.map (subst crels) clauses
                return clauses', snd(strip_comb(hd schems))
        }

    let find_redefinition tm (rth, ith, cth as trip) = 
        choice {
            let! rth = rth
            let tm1 = concl rth
            if aconv tm tm1 then 
                return trip
            else 
                return! Choice.failwith "find_redefinition"
        }

    let prove_inductive_properties tm = 
        choice {
            let clauses = conjuncts tm
            let! clauses', fvs = unschematize_clauses clauses
            let! tm1 = list_mk_conj clauses'
            let! th = derive_nonschematic_inductive_relations tm1
            return fvs, prove_monotonicity_hyps (Choice.result th)
        }

    let prove_inductive_relations_exist tm = 
        choice {
            let! fvs, th1 = prove_inductive_properties tm
            let! th1 = th1
            let! th2 = generalize_schematic_variables true fvs (Choice.result th1)
            return! derive_existence (Choice.result th2)
        } : Protected<thm0>

    let new_inductive_definition tm : Protected<thm0> * Protected<thm0> * Protected<thm0> =          
        let th = tryfind (Choice.toOption << find_redefinition tm) (!the_inductive_definitions)
                 |> Option.toChoiceWithError "tryfind"
        warn true "Benign redefinition of inductive predicate"
        match th with
        | Success th -> th
        | Error _ ->
            choice {
                let! fvs, th1 = prove_inductive_properties tm
                let! th1 = th1
                let! th2 = generalize_schematic_variables true fvs (Choice.result th1)
                let! th3 = make_definitions (Choice.result th2)
                let (avs, _) = strip_forall <| concl th3
                
                let r, ic = CONJ_PAIR(SPECL avs (Choice.result th3))
                let! r = r
                let! ic = ic

                let i, c = CONJ_PAIR (Choice.result ic)
                let! i = i
                let! c = c

                let! th1' = GENL avs (Choice.result r)
                let! th2' = GENL avs (Choice.result i)
                let! th3' = GENL avs (Choice.result c)
                let thtr = Choice.result th1', Choice.result th2', Choice.result th3' 
                the_inductive_definitions := thtr :: (!the_inductive_definitions)
                return thtr
            }
            |> Choice.mapError (fun e ->
                    logger.Error(Printf.sprintf "new_inductive_definition of '%s' returns %O" (string_of_term tm) e)
                    e)
            // We return three exceptions in case of errors. It's still better than raising exceptions directly.
            |> Choice.getOrFailure3 "new_inductive_definition"

    prove_inductive_relations_exist, new_inductive_definition

(* ------------------------------------------------------------------------- *)
(* Derivation of "strong induction".                                         *)
(* ------------------------------------------------------------------------- *)

/// Derive stronger induction theorem from inductive definition.
let derive_strong_induction : Protected<thm0> * Protected<thm0> -> Protected<thm0> = 
    let dest_ibod tm = 
        choice {
            let avs, ibod = strip_forall tm
            let n = length avs
            let prator = Choice.funpow n rator
            let! ant, con = dest_imp ibod
            let! ant' = prator ant
            let! con' = prator con
            return n, (ant', con')
        }

    let rec prove_triv tm = 
        choice {
            if is_conj tm then
                let! ltm = lhand tm
                let! rtm = rand tm
                return! CONJ (prove_triv ltm) (prove_triv rtm)
            else 
                let avs, bod = strip_forall tm
                let! a, c = dest_imp bod
                let ths = CONJUNCTS(ASSUME a)
                let! th = 
                    Choice.List.tryFind (fun th -> 
                        choice {
                            let! th = th
                            return aconv c (concl th)
                        }) ths
                    |> Choice.bind (Option.toChoiceWithError "find")
                let! th = th
                return! GENL avs (DISCH a (Choice.result th))
        }

    let rec weaken_triv th = 
        choice {
            let! th = th
            let tm1 = concl th
            if is_conj tm1 then 
                return! CONJ (weaken_triv(CONJUNCT1 (Choice.result th))) (weaken_triv(CONJUNCT2 (Choice.result th)))
            else 
                let avs, bod = strip_forall <| concl th
                let! th1 = SPECL avs (Choice.result th)
                let! (a, _) = dest_imp <| concl th1
                return! GENL avs (DISCH a (CONJUNCT2(UNDISCH (Choice.result th1))))
        }

    let MATCH_IMPS = MATCH_MP MONO_AND

    fun (rth, ith) -> 
        choice {
            let! rth = rth
            let! ith = ith
            let ovs, ibod = strip_forall <| concl ith
            let! iant, icon = dest_imp ibod
            let! tms = Choice.List.map dest_ibod (conjuncts icon)
            let ns, prrs = unzip tms
            let rs, ps = unzip prrs
            let! bods = variables ibod
            let! gs = variants bods ps
            let svs, tvs = chop_list (length ovs - length ns) ovs
            let! sth = SPECL svs (Choice.result rth)
            let! jth = SPECL svs (Choice.result ith)
            let! gimps = subst (zip gs rs) icon
            let! prs = 
                Choice.List.map2 
                    (fun n (r, p) -> 
                        choice {
                            let! tyr = type_of r
                            let! tys, ty = Choice.List.nsplit dest_fun_ty (1 -- n) tyr
                            let gvs = map genvar tys
                            let! tm1 = list_mk_comb(r, gvs)
                            let! tm2 = list_mk_comb(p, gvs)
                            let! conj = mk_conj(tm1, tm2)
                            return! list_mk_abs(gvs, conj)
                        }) ns prrs

            let modify_rule rcl itm = 
                choice {
                    let! rcl = rcl
                    let avs, bod = strip_forall itm
                    if is_imp bod then 
                        let! a, c = dest_imp bod
                        let! tm1 = vsubst (zip gs ps) a
                        let! tm2 = mk_imp(tm1, a)
                        let! mgoal = mk_imp(gimps, tm2)
                        let! tm2' = list_mk_forall(gs @ ps @ avs, mgoal)
                        let! mth = ASSUME tm2'
                        let! ith_r = BETA_RULE(SPECL (prs @ rs @ avs) (Choice.result mth))
                        let! tm3 = lhand <| concl ith_r
                        let! jth_r = MP (Choice.result ith_r) (prove_triv tm3)

                        let! t = lhand <| concl jth_r
                        let! kth_r = UNDISCH (Choice.result jth_r)
                        let! tm4 = mk_imp(t, c)
                        let! ntm = list_mk_forall(avs, tm4)
                        let! lth_r = MP (SPECL avs (Choice.result rcl)) (Choice.result kth_r)
                        let! lth_p = UNDISCH(SPECL avs (ASSUME ntm))
                        return! DISCH ntm (GENL avs (DISCH t (CONJ (Choice.result lth_r) (Choice.result lth_p))))
                    else 
                        return! DISCH itm (GENL avs (CONJ (SPECL avs (Choice.result rcl)) (SPECL avs (ASSUME itm))))
                }

            let! mimps = Choice.List.map2 modify_rule (CONJUNCTS (Choice.result sth)) (conjuncts iant)
            let! th1 = Choice.List.reduceBack (fun th th' -> MATCH_IMPS(CONJ (Choice.result th) (Choice.result th'))) mimps
            let! th2 = BETA_RULE(SPECL prs (Choice.result jth))
            let! th3 = IMP_TRANS (Choice.result th1) (Choice.result th2)
            let! nasm = lhand <| concl th3
            let! th4 = GENL ps (DISCH nasm (weaken_triv(UNDISCH (Choice.result th3))))
            return! GENL svs (prove_monotonicity_hyps (Choice.result th4))
        }
