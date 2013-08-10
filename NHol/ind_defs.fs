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

logger.Trace("Entering ind_defs.fs")

(* ------------------------------------------------------------------------- *)
(* Strip off exactly n arguments from combination.                           *)
(* ------------------------------------------------------------------------- *)

/// Strip away a given number of arguments from a combination.
let strip_ncomb = 
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
    rev_itlist (fun a -> CONV_RULE(RAND_CONV BETA_CONV) << C AP_THM a)

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
            let! l, r = dest_eq tm
            let! tm' = Choice.map concl th
            let! P = mk_abs(l, tm')
            let th1 = Choice.bind BETA_CONV (mk_comb(P, l))
            let th2 = ISPECL [P; r] pth
            let th3 = EQ_MP (SYM th1) th
            let th4 = GEN l (DISCH tm th3)
            return! MP th2 th4
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
            let! l, r = Choice.bind (dest_disj << hd << hyp) th
            return PROVE_HYP (DISJ1 (ASSUME l) r) th, PROVE_HYP (DISJ2 l (ASSUME r)) th
        }

    let HALF_BETA_EXPAND args th = GENL args (RIGHT_BETAS args th)

    let AND_IMPS_CONV tm = 
        choice {
            let ths = CONJUNCTS(ASSUME tm)
            let! tm' = Choice.map concl (hd ths)
            let avs = fst(strip_forall tm')
            let thl = map (DISCH tm << UNDISCH << SPEC_ALL) ths
            let th1 = end_itlist SIMPLE_DISJ_CASES thl
            let! tm1 = Choice.map (hd << hyp) th1
            let th2 = GENL avs (DISCH tm1 (UNDISCH th1))
            let! tm2 = Choice.map concl th2
            let th3 = DISCH tm2 (UNDISCH(SPEC_ALL(ASSUME tm2)))
            let! thts, tht = Choice.List.nsplit SIMPLE_DISJ_PAIR (tl ths) th3
            let proc_fn th = 
                choice {
                    let! t = Choice.map (hd << hyp) th
                    return! GENL avs (DISCH t (UNDISCH th))
                }

            let th4 = itlist (CONJ << proc_fn) thts (proc_fn tht)
            return! IMP_ANTISYM_RULE (DISCH_ALL th2) (DISCH_ALL th4)
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
            let th1 = DISCH tm (UNDISCH(SPEC_ALL(ASSUME tm)))
            let th2 = itlist SIMPLE_CHOOSE avs th1
            let! tm2 = Choice.map (hd << hyp) th2
            let th3 = DISCH tm2 (UNDISCH th2)
            let th4 = Choice.bind (ASSUME << concl) th3
            let! ant = lhand bod
            let th5 = itlist SIMPLE_EXISTS avs (ASSUME ant)
            let th6 = GENL avs (DISCH ant (MP th4 th5))
            return! IMP_ANTISYM_RULE (DISCH_ALL th3) (DISCH_ALL th6)
        }

    let canonicalize_clause cls args = 
        choice {
            let avs, bimp = strip_forall cls
            let! ant, con = 
                dest_imp bimp
                |> Choice.bindError (fun _ -> Choice.result (t_tm, bimp))

            let rel, xargs = strip_comb con
            let plis = zip args xargs
            let yes, no = calculate_simp_sequence avs plis
            let nvs = filter (not << C mem (map snd yes)) avs
            let eth = 
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

                        let th0 = MP (SPECL avs (ASSUME cls)) tth
                        let th1 = rev_itlist (C(curry MK_COMB)) thl (REFL rel)
                        let th2 = EQ_MP (SYM th1) th0
                        let th3 = INST yes (DISCH atm th2)
                        let! tm3 = Choice.bind (lhand << concl) th3
                        let! tm4 = Choice.funpow (length yes) rand tm3
                        let th4 = itlist (CONJ << REFL << fst) yes (ASSUME tm4)
                        let th5 = GENL args (GENL nvs (DISCH tm4 (MP th3 th4)))
                        let! tm5 = Choice.map concl th5
                        let th6 = SPECL nvs (SPECL (map snd plis) (ASSUME tm5))
                        let th7 = itlist (CONJ << REFL << snd) no (ASSUME ant)
                        let th8 = GENL avs (DISCH ant (MP th6 th7))
                        return! IMP_ANTISYM_RULE (DISCH_ALL th5) (DISCH_ALL th8)
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
                        let th0 = SPECL avs (ASSUME cls)
                        let th1 = rev_itlist (C(curry MK_COMB)) thl (REFL rel)
                        let th2 = EQ_MP (SYM th1) th0
                        let th3 = INST yes (DISCH atm th2)
                        let! tm3 = Choice.bind (lhand << concl) th3
                        let! tm4 = Choice.funpow (length yes) rand tm3
                        let th4 = itlist (CONJ << REFL << fst) yes (ASSUME tm4)
                        let th5 = GENL args (GENL nvs (DISCH tm4 (MP th3 th4)))
                        let! tm5 = Choice.map concl th5
                        let th6 = SPECL nvs (SPECL (map snd plis) (ASSUME tm5))
                        let th7 = end_itlist CONJ (map (REFL << snd) no)
                        let th8 = GENL avs (MP th6 th7)
                        return! IMP_ANTISYM_RULE (DISCH_ALL th5) (DISCH_ALL th8)
                }

            let! tm1 = Choice.bind (rand << concl) eth
            let! ftm = Choice.funpow (length args) (Choice.bind body << rand) tm1
            return! TRANS eth (itlist MK_FORALL args (FORALL_IMPS_CONV ftm))
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
            let cthms = map2 canonicalize_clause clauses cargs
            let! pclauses = Choice.List.map (Choice.bind rand << Choice.map concl) cthms
            let collectclauses tm = 
                mapfilter (fun t -> 
                    if fst t = tm then Some (snd t) else None) (zip (map fst uncs) pclauses)
            let clausell = map collectclauses rels
            let! cclausel = Choice.List.map list_mk_conj clausell
            let! cclauses = list_mk_conj cclausel
            let! oclauses = list_mk_conj pclauses
            let! tm' = mk_eq (oclauses, cclauses)
            let eth = CONJ_ACI_RULE tm'
            let pth = TRANS (end_itlist MK_CONJ cthms) eth
            return! TRANS pth (end_itlist MK_CONJ (map AND_IMPS_CONV cclausel))
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
            let indthmr = end_itlist CONJ indthms
            let indthm = GENL rels' (DISCH closed' indthmr)
            let! mconcs = Choice.List.map2 (fun a t -> 
                            choice {
                                let! tm1 = prime_fn t
                                let! tm2 = mk_imp(t, tm1)
                                return! list_mk_forall(a, tm2)
                            }) vargs ants
            let! tmr = Choice.map concl indthmr
            let! tm2 = list_mk_conj mconcs
            let! monotm = mk_imp(tmr, tm2)
            let! tm3 = list_mk_forall(rels', monotm)
            let! tm4 = list_mk_forall(rels, tm3)
            let monothm = ASSUME(tm4)
            let closthm = ASSUME closed'
            let monothms = CONJUNCTS(MP (SPEC_ALL monothm) (MP (SPECL rels' indthm) closthm))
            let closthms = CONJUNCTS closthm

            let prove_rule mth (cth, dth) = 
                choice {
                    let! avs, bod = Choice.map (strip_forall << concl) mth
                    let th1 = IMP_TRANS (SPECL avs mth) (SPECL avs cth)
                    let th2 = GENL rels' (DISCH closed' (UNDISCH th1))
                    let th3 = EQ_MP (SYM(SPECL avs dth)) th2
                    let! tm = lhand bod
                    return! GENL avs (DISCH tm th3)
                }

            let rulethms = map2 prove_rule monothms (zip closthms defthms)
            let rulethm = end_itlist CONJ rulethms
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
            let irthm = EQ_MP (SYM(end_itlist MK_CONJ (map fst unths))) rulethm
            let mrthm = MP (SPECL rels (SPECL dtms monothm)) irthm
            let imrth = EQ_MP (SYM(end_itlist MK_CONJ (map (fst << snd) unths))) mrthm
            let ifthm = MP (SPECL dtms indthm) imrth
            let fthm = EQ_MP (end_itlist MK_CONJ (map (snd << snd) unths)) ifthm

            let mk_case th1 th2 = 
                choice {
                    let! avs = Choice.map (fst << strip_forall << concl) th1
                    return! GENL avs (IMP_ANTISYM_RULE (SPEC_ALL th1) (SPEC_ALL th2))
                }

            let casethm = end_itlist CONJ (map2 mk_case (CONJUNCTS fthm) (CONJUNCTS rulethm))
            return! CONJ rulethm (CONJ indthm casethm)
        }

    fun tm -> 
        choice {
            let clauses = conjuncts tm
            let canonthm = canonicalize_clauses clauses
            let canonthm' = SYM canonthm
            let! pclosed = Choice.bind (rand << concl) canonthm
            let pclauses = conjuncts pclosed
            let rawthm = derive_canon_inductive_relations pclauses
            let rulethm, otherthms = CONJ_PAIR rawthm
            let indthm, casethm = CONJ_PAIR otherthms
            let rulethm' = EQ_MP canonthm' rulethm
            let indthm' = CONV_RULE (ONCE_DEPTH_CONV(REWR_CONV canonthm')) indthm
            return! CONJ rulethm' (CONJ indthm' casethm)
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
let MONO_TAC = 
    let imp = (parse_term @"(==>)")
    let IMP_REFL = ITAUT(parse_term @"!p. p ==> p")
    let BACKCHAIN_TAC th = 
        let match_fn = PART_MATCH (Choice.map snd << dest_imp) th
        fun (asl, w) -> 
            choice {
                let th1 = match_fn w
                let! ant, con = Choice.bind (dest_imp << concl) th1
                let fun1 l =
                    match l with
                    | [a] -> a
                    | _ -> Choice.failwith "MONO_TAC.fun1: Unhandled case."       
                return (null_meta, [asl, ant], fun i tl -> MATCH_MP (INSTANTIATE i th1) (fun1 tl))
            }

    let MONO_ABS_TAC(asl, w) = 
        choice {
            let! ant, con = dest_imp w
            let vars = snd(strip_comb con)
            let rnum = length vars - 1
            let! hd1, args1 = strip_ncomb rnum ant
            let! hd2, args2 = strip_ncomb rnum con
            let th1 = rev_itlist (C AP_THM) args1 (BETA_CONV hd1)
            let th2 = rev_itlist (C AP_THM) args1 (BETA_CONV hd2)
            let th3 = MK_COMB(AP_TERM imp th1, th2)
            return! CONV_TAC (REWR_CONV th3) (asl, w)
        }

    let APPLY_MONOTAC tacs (asl, w) = 
        choice {
            let! a, c = dest_imp w
            if aconv a c then 
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
                Choice.List.fold (fun acc th -> 
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
                        }) ["", MONO_ABS_TAC] (!monotonicity_theorems) 

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
            let! tms = Choice.map hyp th
            let mths = mapfilter (Choice.toOption << Choice.map Choice.result << prove_mth) (filter (not << is_eq) tms)
            return! itlist PROVE_HYP mths th
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
                let! l, r = dest_eq tm
                let! lname, lty = dest_var l
                // TODO: revise due to massive changes
                let! tm1 = Choice.List.fold (fun acc x -> type_of x |> Choice.bind (fun y -> mk_fun_ty y acc)) lty vs
                let l' = mk_var(lname, tm1)
                let! r' = list_mk_abs(vs, r)
                let! tm2 = mk_eq(l', r')
                let th0 = RIGHT_BETAS vs (ASSUME tm2)
                let! tm3 = Choice.bind (lhs << concl) th0
                let th1 = INST [tm3, l] (DISCH tm th)
                return! MP th1 th0
            }

        fun (th : Protected<thm0>) -> 
            choice {
                let! tms = Choice.map hyp th
                let defs, others = partition is_eq tms
                let th1 = itlist generalize_def defs th
                if gflag then 
                    let! others' = 
                        Choice.List.map (fun t -> 
                            choice {
                                let fvs = frees t
                                let! tm1 = list_mk_forall(fvs, t)
                                return SPECL fvs (ASSUME(tm1))
                            }) others
                    return! GENL vs (itlist PROVE_HYP others' th1)
                else 
                    return! th1
            }

    let derive_existence (th : Protected<thm0>) = 
        choice {
            let! tms = Choice.map hyp th
            let defs = filter is_eq tms
            return! itlist EXISTS_EQUATION defs th
        }

    let make_definitions (th : Protected<thm0>) = 
        choice {
            let! tms = Choice.map hyp th
            let defs = filter is_eq tms
            let dths = map new_definition defs
            let! tms1 = Choice.List.map (Choice.bind lhs << Choice.map concl) dths
            let! tms2 = Choice.List.map lhs defs
            let insts = zip tms1 tms2
            return! rev_itlist (C MP) dths (INST insts (itlist DISCH defs th))
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
            let! tm1 = Choice.map concl rth
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
            let th = derive_nonschematic_inductive_relations tm1
            return fvs, prove_monotonicity_hyps th
        }

    let prove_inductive_relations_exist tm = 
        choice {
            let! fvs, th1 = prove_inductive_properties tm
            let th2 = generalize_schematic_variables true fvs th1
            return! derive_existence th2
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
                let th2 = generalize_schematic_variables true fvs th1
                let th3 = make_definitions th2
                let! (avs, _) = Choice.map (strip_forall << concl) th3
                let r, ic = CONJ_PAIR(SPECL avs th3)
                let i, c = CONJ_PAIR ic
                let thtr = GENL avs r, GENL avs i, GENL avs c
                the_inductive_definitions := thtr :: (!the_inductive_definitions)
                return thtr
            }
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
                return! GENL avs (DISCH a th)
        }

    let rec weaken_triv th = 
        choice {
            let! tm1 = Choice.map concl th
            if is_conj tm1 then 
                return! CONJ (weaken_triv(CONJUNCT1 th)) (weaken_triv(CONJUNCT2 th))
            else 
                let! avs, bod = Choice.map (strip_forall << concl) th
                let th1 = SPECL avs th
                let! (a, _) = Choice.bind (dest_imp << concl) th1
                return! GENL avs (DISCH a (CONJUNCT2(UNDISCH th1)))
        }

    let MATCH_IMPS = MATCH_MP MONO_AND

    fun (rth, ith) -> 
        choice {
            let! ovs, ibod = Choice.map (strip_forall << concl) ith
            let! iant, icon = dest_imp ibod
            let! tms = Choice.List.map dest_ibod (conjuncts icon)
            let ns, prrs = unzip tms
            let rs, ps = unzip prrs
            let! bods = variables ibod
            let! gs = variants bods ps
            let svs, tvs = chop_list (length ovs - length ns) ovs
            let sth = SPECL svs rth
            let jth = SPECL svs ith
            let! gimps = subst (zip gs rs) icon
            let! prs = 
                Choice.List.map2 
                    (fun n (r, p) -> 
                        choice {
                            let! tyr = type_of r
                            let! tys, ty = Choice.List.nsplit dest_fun_ty (1 -- n) tyr
                            let gvs = map genvar tys
                            let! conj = mk_conj(list_mk_comb(r, gvs), list_mk_comb(p, gvs))
                            return! list_mk_abs(gvs, conj)
                        }) ns prrs

            let modify_rule rcl itm = 
                choice {
                    let avs, bod = strip_forall itm
                    if is_imp bod then 
                        let! a, c = dest_imp bod
                        let! tm1 = vsubst (zip gs ps) a
                        let! tm2 = mk_imp(tm1, a)
                        let! mgoal = mk_imp(gimps, tm2)
                        let! tm2' = list_mk_forall(gs @ ps @ avs, mgoal)
                        let mth = ASSUME(tm2')
                        let ith_r = BETA_RULE(SPECL (prs @ rs @ avs) mth)
                        let! tm3 = Choice.bind (lhand << concl) ith_r
                        let jth_r = MP ith_r (prove_triv tm3)

                        let! t = Choice.bind (lhand << concl) jth_r
                        let kth_r = UNDISCH jth_r
                        let! tm4 = mk_imp(t, c)
                        let! ntm = list_mk_forall(avs, tm4)
                        let lth_r = MP (SPECL avs rcl) kth_r
                        let lth_p = UNDISCH(SPECL avs (ASSUME ntm))
                        return! DISCH ntm (GENL avs (DISCH t (CONJ lth_r lth_p)))
                    else 
                        return! DISCH itm (GENL avs (CONJ (SPECL avs rcl) (SPECL avs (ASSUME itm))))
                }

            let mimps = map2 modify_rule (CONJUNCTS sth) (conjuncts iant)
            let th1 = end_itlist (fun th th' -> MATCH_IMPS(CONJ th th')) mimps
            let th2 = BETA_RULE(SPECL prs jth)
            let th3 = IMP_TRANS th1 th2
            let! nasm = Choice.bind (lhand << concl) th3
            let th4 = GENL ps (DISCH nasm (weaken_triv(UNDISCH th3)))
            return! GENL svs (prove_monotonicity_hyps th4)
        }
