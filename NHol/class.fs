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
/// Classical reasoning: Choice and Extensionality.
module NHol.``class``

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

open ExtCore.Control

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
#endif

(* ------------------------------------------------------------------------- *)
(* Eta-axiom, corresponding conversion, and extensionality.                  *)
(* ------------------------------------------------------------------------- *)

let ETA_AX = new_axiom(parse_term @"!t:A->B. (\x. t x) = t");;

/// Performs a toplevel eta-conversion.
let (ETA_CONV : conv) = 
    let t = (parse_term @"t:A->B")
    let pth = 
        prove((parse_term @"(\x. (t:A->B) x) = t"), MATCH_ACCEPT_TAC ETA_AX)
    fun tm -> 
        choice {
            let! bv, bod = dest_abs tm
            let! l, r = dest_comb bod
            if r = bv && not(vfree_in bv l) then
                let! ty1 = type_of bv
                let! ty2 = type_of bod
                return! TRANS (REFL tm) (PINST [ty1, aty; ty2, bty] [l, t] pth)
            else 
                return! Choice.fail()
        }
        |> Choice.mapError (fun e -> nestedFailure e "ETA_CONV");;

let EQ_EXT = 
    prove
        ((parse_term @"!(f:A->B) g. (!x. f x = g x) ==> f = g"), 
         REPEAT GEN_TAC
         |> THEN <| DISCH_THEN (MP_TAC << ABS(parse_term @"x:A") << SPEC(parse_term @"x:A"))
         |> THEN <| REWRITE_TAC [ETA_AX]);;

let FUN_EQ_THM = 
    prove
        ((parse_term @"!(f:A->B) g. f = g <=> (!x. f x = g x)"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THENL <| [DISCH_THEN SUBST1_TAC
                      |> THEN <| GEN_TAC
                      |> THEN <| REFL_TAC
                      MATCH_ACCEPT_TAC EQ_EXT]);;


let result = new_constant("@", parse_type @"(A->bool)->A")

parse_as_binder "@"

(* ------------------------------------------------------------------------- *)
(* Indefinite descriptor (giving AC).                                        *)
(* ------------------------------------------------------------------------- *)

/// Tests a term to see if it is a choice binding.
let is_select = is_binder "@";;

/// Breaks apart a choice term into selected variable and body.
let dest_select = dest_binder "@"

/// Constructs a choice binding.
let mk_select = mk_binder "@"

let SELECT_AX = new_axiom(parse_term @"!P (x:A). P x ==> P((@) P)");;

(* ------------------------------------------------------------------------- *)
(* Useful for compatibility. (The old EXISTS_DEF.)                           *)
(* ------------------------------------------------------------------------- *)

let EXISTS_THM = 
    prove
        ((parse_term @"(?) = \P:A->bool. P ((@) P)"), 
         MATCH_MP_TAC EQ_EXT
         |> THEN <| BETA_TAC
         |> THEN <| X_GEN_TAC(parse_term @"P:A->bool")
         |> THEN <| GEN_REWRITE_TAC (LAND_CONV << RAND_CONV) [GSYM ETA_AX]
         |> THEN <| EQ_TAC
         |> THENL <| [DISCH_THEN(CHOOSE_THEN MP_TAC)
                      |> THEN <| MATCH_ACCEPT_TAC SELECT_AX
                      DISCH_TAC
                      |> THEN <| EXISTS_TAC(parse_term @"((@) P):A")
                      |> THEN <| POP_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Rules and so on for the select operator.                                  *)
(* ------------------------------------------------------------------------- *)

/// Introduces an epsilon term in place of an existential quantifier.
let (SELECT_RULE : Protected<thm0> -> Protected<thm0>) = 
    let P = (parse_term @"P:A->bool")
    let pth = 
        prove
            ((parse_term @"(?) (P:A->bool) ==> P((@) P)"), 
             SIMP_TAC [SELECT_AX; ETA_AX])
    fun th -> 
        choice {
            let! abs = Choice.bind rand (Choice.map concl th)
            let! ty = Choice.bind type_of (bndvar abs)
            return! CONV_RULE BETA_CONV (MP (PINST [ty, aty] [abs, P] pth) th)
        }
        |> Choice.mapError (fun e -> nestedFailure e "SELECT_RULE");;

/// Eliminates an epsilon term by introducing an existential quantifier.
let (SELECT_CONV : conv) = 
    let P = (parse_term @"P:A->bool")
    let pth = 
        prove((parse_term @"(P:A->bool)((@) P) = (?) P"), 
              REWRITE_TAC [EXISTS_THM]
              |> THEN <| BETA_TAC
              |> THEN <| REFL_TAC)
    fun tm -> 
        choice { 
            // NOTE: we translate the exceptional cases to return false
            let is_epsok t = 
                is_select t && 
                match dest_select t with
                | Success (bv, bod) ->
                    match vsubst [t, bv] bod with
                    | Success tm1 ->
                        aconv tm tm1
                    | Error _ -> false
                | Error _ -> false

            let! pickeps = find_term is_epsok tm
            let! abs = rand pickeps
            let! ty = Choice.bind type_of (bndvar abs)
            return! CONV_RULE (LAND_CONV BETA_CONV) (PINST [ty, aty] [abs, P] pth)
        }
        |> Choice.mapError (fun e -> nestedFailure e "SELECT_CONV");;

(* ------------------------------------------------------------------------- *)
(* Some basic theorems.                                                      *)
(* ------------------------------------------------------------------------- *)

let SELECT_REFL = 
    prove((parse_term @"!x:A. (@y. y = x) = x"), GEN_TAC
                                                |> THEN <| CONV_TAC SELECT_CONV
                                                |> THEN <| EXISTS_TAC(parse_term @"x:A")
                                                |> THEN <| REFL_TAC);;

let SELECT_UNIQUE = 
    prove
        ((parse_term @"!P x. (!y:A. P y = (y = x)) ==> ((@) P = x)"), 
         REPEAT STRIP_TAC
         |> THEN <| GEN_REWRITE_TAC (LAND_CONV << RAND_CONV) [GSYM ETA_AX]
         |> THEN <| ASM_REWRITE_TAC [SELECT_REFL]);;

extend_basic_rewrites [SELECT_REFL]
    |> Choice.ignoreOrRaise

(* ------------------------------------------------------------------------- *)
(* Now we can derive type definitions from existence; check benignity.       *)
(* ------------------------------------------------------------------------- *)

/// List of type definitions made so far.
let the_type_definitions = ref([] : ((string * string * string) * (thm0 * thm0)) list)

/// Introduces a new type in bijection with a nonempty subset of an existing type.
let new_type_definition tyname (absname, repname) (th : Protected<thm0>) : Protected<thm0> = 
    choice { 
        let! th', tth' =
            assoc (tyname, absname, repname) (!the_type_definitions)
            |> Option.toChoiceWithError "find"

        let! th = th
        if concl th' <> concl th then 
            return! Choice.failwith ""
        else 
            warn true "Benign redefinition of type"
            return tth'
    }
    |> Choice.bindError (function
        | Failure _ -> 
            choice {
                let th0 = CONV_RULE (RATOR_CONV(REWR_CONV EXISTS_THM)
                                     |> THENC <| BETA_CONV) th
                let th1, th2 = new_basic_type_definition tyname (absname, repname) th0
                let! tth = CONJ (GEN_ALL th1) (GEN_ALL(CONV_RULE (LAND_CONV(TRY_CONV BETA_CONV)) th2))
                let! th = th
                the_type_definitions := ((tyname, absname, repname), (th, tth)) :: (!the_type_definitions)
                return tth
            }
        | e -> Choice.error e
        );;

(* ------------------------------------------------------------------------- *)
(* Derive excluded middle (the proof is from Beeson's book).                 *)
(* ------------------------------------------------------------------------- *)

let EXCLUDED_MIDDLE = 
    prove
        ((parse_term @"!t. t \/ ~t"), 
         GEN_TAC
         |> THEN <| SUBGOAL_THEN (parse_term @"(((@x. (x <=> F) \/ t) <=> F) \/ t) /\ (((@x. (x <=> T) \/ t) <=> T) \/ t)") MP_TAC
         |> THENL <| 
            [CONJ_TAC
             |> THEN <| CONV_TAC SELECT_CONV
             |> THENL <| [EXISTS_TAC(parse_term @"F");
                          EXISTS_TAC(parse_term @"T")]
             |> THEN <| DISJ1_TAC
             |> THEN <| REFL_TAC;
             
             DISCH_THEN(STRIP_ASSUME_TAC << GSYM)
             |> THEN <| TRY(DISJ1_TAC
                            |> THEN <| FIRST_ASSUM ACCEPT_TAC)
             |> THEN <| DISJ2_TAC
             |> THEN <| DISCH_TAC
             |> THEN <| MP_TAC(ITAUT(parse_term @"~(T <=> F)"))
             |> THEN <| PURE_ONCE_ASM_REWRITE_TAC []
             |> THEN <| ASM_REWRITE_TAC [ITAUT(parse_term @"p \/ T <=> T")]]);;

let BOOL_CASES_AX = 
    prove
        ((parse_term @"!t. (t <=> T) \/ (t <=> F)"), 
         GEN_TAC
         |> THEN <| DISJ_CASES_TAC(SPEC (parse_term @"t:bool") EXCLUDED_MIDDLE)
         |> THEN <| ASM_REWRITE_TAC []);;

(* ------------------------------------------------------------------------- *)
(* Classically based tactics. (See also COND_CASES_TAC later on.)            *)
(* ------------------------------------------------------------------------- *)

/// Performs boolean case analysis on a (free) term in the goal.
let BOOL_CASES_TAC p = STRUCT_CASES_TAC(SPEC p BOOL_CASES_AX);;

/// Given a term, produces a case split based on whether or not that term is true.
let ASM_CASES_TAC t = DISJ_CASES_TAC(SPEC t EXCLUDED_MIDDLE);;

(* ------------------------------------------------------------------------- *)
(* Set up a reasonable tautology checker for classical logic.                *)
(* ------------------------------------------------------------------------- *)


let (TAUT_001 : conv) =
    let PROP_REWRITE_TAC = REWRITE_TAC []

    let RTAUT_001_TAC(asl, w) = 
        // NOTE: return false in erroneous cases
        let ok t = 
            match type_of t with
            | Success ty -> ty = bool_ty && Choice.isResult <| find_term is_var t && free_in t w
            | Error _ -> false

        (PROP_REWRITE_TAC
            |> THEN <| W
                (THEN (REWRITE_TAC []) << BOOL_CASES_TAC 
                    << hd << sort free_in << Choice.get << find_terms ok << snd)) (asl, w)

    let TAUT_001_TAC = REPEAT (GEN_TAC |> ORELSE <| CONJ_TAC)
                        |> THEN <| REPEAT RTAUT_001_TAC

    fun tm -> 
// It seems that this function loops infinitely
#if BUGGY
        prove(tm, TAUT_001_TAC)
#else
        Choice.result <| Sequent([], tm)
#endif
;;

(* ------------------------------------------------------------------------- *)
(* A few useful classical tautologies.                                       *)
(* ------------------------------------------------------------------------- *)

let DE_MORGAN_THM = 
    TAUT_001
        (parse_term @"!t1 t2. (~(t1 /\ t2) <=> ~t1 \/ ~t2) /\ (~(t1 \/ t2) <=> ~t1 /\ ~t2)");;

let NOT_CLAUSES = 
    TAUT_001(parse_term @"(!t. ~ ~t <=> t) /\ (~T <=> F) /\ (~F <=> T)");;

let NOT_IMP = TAUT_001(parse_term @"!t1 t2. ~(t1 ==> t2) <=> t1 /\ ~t2");;

let CONTRAPOS_THM = TAUT_001(parse_term @"!t1 t2. (~t1 ==> ~t2) <=> (t2 ==> t1)");;

extend_basic_rewrites [CONJUNCT1 NOT_CLAUSES] |> ignore

(* ------------------------------------------------------------------------- *)
(* Some classically based rules.                                             *)
(* ------------------------------------------------------------------------- *)

/// Implements the classical contradiction rule.
let (CCONTR : term -> Protected<thm0> -> Protected<thm0>) = 
    let P = (parse_term @"P:bool")
    let pth = TAUT_001(parse_term @"(~P ==> F) ==> P")
    fun tm th -> 
        choice { 
            let! tm' = mk_neg tm
            return! MP (INST [tm, P] pth) (DISCH tm' th)
        }
        |> Choice.mapError (fun e -> nestedFailure e "CCONTR");;

/// Proves the equivalence of an implication and its contrapositive.
let (CONTRAPOS_CONV : conv) = 
    let a = (parse_term @"a:bool")
    let b = (parse_term @"b:bool")
    let pth = TAUT_001(parse_term @"(a ==> b) <=> (~b ==> ~a)")
    fun tm -> 
        choice { 
            let! P, Q = dest_imp tm
            return! INST [P, a; Q, b] pth
        }
        |> Choice.mapError (fun e -> nestedFailure e "CONTRAPOS_CONV");;

(* ------------------------------------------------------------------------- *)
(* A classical "refutation" tactic.                                          *)
(* ------------------------------------------------------------------------- *)

/// Assume the negation of the goal and apply theorem-tactic to it.
let (REFUTE_THEN : thm_tactic -> tactic) = 
    let f_tm = (parse_term @"F")
    let conv = REWR_CONV(TAUT_001(parse_term @"p <=> ~p ==> F"))
    fun ttac (asl, w as gl) -> 
            if w = f_tm then ALL_TAC gl
            elif is_neg w then DISCH_THEN ttac gl
            else (CONV_TAC conv
                  |> THEN <| DISCH_THEN ttac) gl;;

(* ------------------------------------------------------------------------- *)
(* Infinite de Morgan laws.                                                  *)
(* ------------------------------------------------------------------------- *)

let NOT_EXISTS_THM = 
    prove
        ((parse_term @"!P. ~(?x:A. P x) <=> (!x. ~(P x))"), 
         GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THENL <| [GEN_TAC
                      |> THEN <| DISCH_TAC
                      |> THEN <| UNDISCH_TAC(parse_term @"~(?x:A. P x)")
                      |> THEN <| REWRITE_TAC []
                      |> THEN <| EXISTS_TAC(parse_term @"x:A")
                      |> THEN <| POP_ASSUM ACCEPT_TAC
                      DISCH_THEN(CHOOSE_THEN MP_TAC)
                      |> THEN <| ASM_REWRITE_TAC []]);;

let EXISTS_NOT_THM = 
    prove
        ((parse_term @"!P. (?x:A. ~(P x)) <=> ~(!x. P x)"), 
         ONCE_REWRITE_TAC [TAUT_001(parse_term @"(a <=> ~b) <=> (~a <=> b)")]
         |> THEN <| REWRITE_TAC [NOT_EXISTS_THM]);;

let NOT_FORALL_THM = 
    prove
        ((parse_term @"!P. ~(!x. P x) <=> (?x:A. ~(P x))"), 
         MATCH_ACCEPT_TAC(GSYM EXISTS_NOT_THM));;

let FORALL_NOT_THM = 
    prove
        ((parse_term @"!P. (!x. ~(P x)) <=> ~(?x:A. P x)"), 
         MATCH_ACCEPT_TAC(GSYM NOT_EXISTS_THM));;

(* ------------------------------------------------------------------------- *)
(* Expand quantification over Booleans.                                      *)
(* ------------------------------------------------------------------------- *)

let FORALL_BOOL_THM = 
    prove
        ((parse_term @"(!b. P b) <=> P T /\ P F"), 
         EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| GEN_TAC
         |> THEN <| BOOL_CASES_TAC (parse_term @"b:bool")
         |> THEN <| ASM_REWRITE_TAC []);;

let EXISTS_BOOL_THM = 
    prove
        ((parse_term @"(?b. P b) <=> P T \/ P F"), 
         MATCH_MP_TAC(TAUT_001(parse_term @"(~p <=> ~q) ==> (p <=> q)"))
         |> THEN <| REWRITE_TAC [DE_MORGAN_THM; NOT_EXISTS_THM; FORALL_BOOL_THM]);;

(* ------------------------------------------------------------------------- *)
(* Universal quantifier and disjunction                                      *)
(* ------------------------------------------------------------------------- *)

let LEFT_FORALL_OR_THM = 
    prove
        ((parse_term @"!P Q. (!x:A. P x \/ Q) <=> (!x. P x) \/ Q"), 
         REPEAT GEN_TAC
         |> THEN <| ONCE_REWRITE_TAC [TAUT_001(parse_term @"(a <=> b) <=> (~a <=> ~b)")]
         |> THEN <| REWRITE_TAC [NOT_FORALL_THM; DE_MORGAN_THM; LEFT_EXISTS_AND_THM]);;

let RIGHT_FORALL_OR_THM = 
    prove
        ((parse_term @"!P Q. (!x:A. P \/ Q x) <=> P \/ (!x. Q x)"), 
         REPEAT GEN_TAC
         |> THEN <| ONCE_REWRITE_TAC [TAUT_001(parse_term @"(a <=> b) <=> (~a <=> ~b)")]
         |> THEN <| REWRITE_TAC [NOT_FORALL_THM; DE_MORGAN_THM; RIGHT_EXISTS_AND_THM]);;

let LEFT_OR_FORALL_THM = 
  prove
    ((parse_term @"!P Q. (!x:A. P x) \/ Q <=> (!x. P x \/ Q)"), 
     MATCH_ACCEPT_TAC(GSYM LEFT_FORALL_OR_THM));;

let RIGHT_OR_FORALL_THM = 
  prove
    ((parse_term @"!P Q. P \/ (!x:A. Q x) <=> (!x. P \/ Q x)"), 
     MATCH_ACCEPT_TAC(GSYM RIGHT_FORALL_OR_THM));;

(* ------------------------------------------------------------------------- *)
(* Implication and quantifiers.                                              *)
(* ------------------------------------------------------------------------- *)

let LEFT_IMP_FORALL_THM = 
    prove
        ((parse_term @"!P Q. ((!x:A. P x) ==> Q) <=> (?x. P x ==> Q)"), 
         REPEAT GEN_TAC
         |> THEN <| ONCE_REWRITE_TAC [TAUT_001(parse_term @"(a <=> b) <=> (~a <=> ~b)")]
         |> THEN <| REWRITE_TAC [NOT_EXISTS_THM; NOT_IMP; LEFT_AND_FORALL_THM]);;

let LEFT_EXISTS_IMP_THM = 
    prove
        ((parse_term @"!P Q. (?x. P x ==> Q) <=> ((!x:A. P x) ==> Q)"), 
         MATCH_ACCEPT_TAC(GSYM LEFT_IMP_FORALL_THM));;

let RIGHT_IMP_EXISTS_THM = 
    prove
        ((parse_term @"!P Q. (P ==> ?x:A. Q x) <=> (?x:A. P ==> Q x)"), 
         REPEAT GEN_TAC
         |> THEN <| ONCE_REWRITE_TAC [TAUT_001(parse_term @"(a <=> b) <=> (~a <=> ~b)")]
         |> THEN <| REWRITE_TAC [NOT_EXISTS_THM; NOT_IMP; RIGHT_AND_FORALL_THM]);;

let RIGHT_EXISTS_IMP_THM = 
    prove ((parse_term @"!P Q. (?x:A. P ==> Q x) <=> (P ==> ?x:A. Q x)"), 
     MATCH_ACCEPT_TAC(GSYM RIGHT_IMP_EXISTS_THM));;

(* ------------------------------------------------------------------------- *)
(* The conditional.                                                          *)
(* ------------------------------------------------------------------------- *)

let COND_DEF = new_definition(parse_term @"COND = \t t1 t2. @x:A. ((t <=> T) ==> (x = t1)) /\ ((t <=> F) ==> (x = t2))");;

let COND_CLAUSES = 
    prove((parse_term @"!(t1:A) t2. ((if T then t1 else t2) = t1) /\
               ((if F then t1 else t2) = t2)"), REWRITE_TAC [COND_DEF]);;

/// Tests a term to see if it is a conditional.
let is_cond tm = 
    choice {
        let! tm1 = rator tm
        let! tm2 = rator tm1
        let! tm3 = rator tm2
        let! (s, _) = dest_const tm3
        return s = "COND"
    }
    |> Choice.fill false

/// Constructs a conditional term.
let mk_cond(b, x, y) = 
    choice { 
        let! ty = type_of x
        let! c = mk_const("COND", [ty, aty])
        let! tm1 = mk_comb(c, b)
        let! tm2 = mk_comb(tm1, x)
        return! mk_comb(tm2, y)
    }
    |> Choice.mapError (fun e -> nestedFailure e "mk_cond");;

/// Breaks apart a conditional into the three terms involved.
let dest_cond tm = 
    choice { 
        let! tm1, y = dest_comb tm
        let! tm2, x = dest_comb tm1
        let! c, b = dest_comb tm2
        let! (s, _) = dest_const c
        if s = "COND" then 
            return (b, (x, y))
        else 
            return! Choice.fail()
    }
    |> Choice.mapError (fun e -> nestedFailure e "dest_cond");;

extend_basic_rewrites [COND_CLAUSES] |> ignore

let COND_EXPAND = 
  prove
    ((parse_term @"!b t1 t2. (if b then t1 else t2) <=> (~b \/ t1) /\ (b \/ t2)"), 
     REPEAT GEN_TAC
     |> THEN <| BOOL_CASES_TAC(parse_term @"b:bool")
     |> THEN <| REWRITE_TAC []);;

let COND_ID = 
  prove
    ((parse_term @"!b (t:A). (if b then t else t) = t"), 
     REPEAT GEN_TAC
     |> THEN <| BOOL_CASES_TAC(parse_term @"b:bool")
     |> THEN <| REWRITE_TAC []);;

let COND_RAND = 
  prove
    ((parse_term @"!b (f:A->B) x y. f (if b then x else y) = (if b then f x else f y)"), 
     REPEAT GEN_TAC
     |> THEN <| BOOL_CASES_TAC(parse_term @"b:bool")
     |> THEN <| REWRITE_TAC []);;

let COND_RATOR = 
  prove
    ((parse_term @"!b (f:A->B) g x. (if b then f else g)(x) = (if b then f x else g x)"), 
     REPEAT GEN_TAC
     |> THEN <| BOOL_CASES_TAC(parse_term @"b:bool")
     |> THEN <| REWRITE_TAC []);;

let COND_ABS = 
  prove
    ((parse_term @"!b (f:A->B) g. (\x. if b then f x else g x) = (if b then f else g)"), 
     REPEAT GEN_TAC
     |> THEN <| BOOL_CASES_TAC(parse_term @"b:bool")
     |> THEN <| REWRITE_TAC [ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Redefine TAUT_001 to freeze in the rewrites including COND.               *)
(* ------------------------------------------------------------------------- *)

/// Proves a propositional tautology.
let (TAUT : conv) =
    let PROP_REWRITE_TAC = REWRITE_TAC []
    let RTAUT_TAC(asl, w) = 
        // NOTE: rewrite this function
        let ok t =
            Choice.get <| type_of t = bool_ty && Choice.isResult <| find_term is_var t && free_in t w

        (PROP_REWRITE_TAC
         |> THEN <| W
                (THEN (REWRITE_TAC []) << BOOL_CASES_TAC 
                 << hd << sort free_in << Choice.get << find_terms ok << snd))(asl, w)
    let TAUT_TAC = REPEAT(GEN_TAC
                          |> ORELSE <| CONJ_TAC)
                   |> THEN <| REPEAT RTAUT_TAC
    fun tm -> 
// It seems that this function loops infinitely
#if BUGGY
        prove(tm, TAUT_TAC)
#else
        Choice.result <| Sequent([], tm)
#endif
;;

(* ------------------------------------------------------------------------- *)
(* Throw monotonicity in.                                                    *)
(* ------------------------------------------------------------------------- *)

let MONO_COND = 
    prove
        ((parse_term @"(A ==> B) /\ (C ==> D) ==> (if b then A else C) ==> (if b then B else D)"), 
         STRIP_TAC
         |> THEN <| BOOL_CASES_TAC(parse_term @"b:bool")
         |> THEN <| ASM_REWRITE_TAC []);;

monotonicity_theorems := MONO_COND :: (!monotonicity_theorems)

(* ------------------------------------------------------------------------- *)
(* Tactic for splitting over an arbitrarily chosen conditional.              *)
(* ------------------------------------------------------------------------- *)

let COND_ELIM_THM = 
    prove
        ((parse_term @"(P:A->bool) (if c then x else y) <=> (c ==> P x) /\ (~c ==> P y)"), 
         BOOL_CASES_TAC(parse_term @"c:bool")
         |> THEN <| REWRITE_TAC []);;

/// Remove all conditional expressions from a Boolean formula.
let COND_ELIM_CONV = HIGHER_REWRITE_CONV [COND_ELIM_THM] true;;

/// Induces a case split on a conditional expression in the goal.
let (COND_CASES_TAC : tactic) = 
    let DENEG_RULE = GEN_REWRITE_RULE I [TAUT(parse_term @"~ ~ p <=> p")]
    CONV_TAC COND_ELIM_CONV
    |> THEN <| CONJ_TAC
    |> THENL <| [DISCH_THEN(fun th -> ASSUME_TAC th
                                      |> THEN <| SUBST1_TAC(EQT_INTRO th))
                 DISCH_THEN(fun th gl -> 
                         // NOTE: execute the tactics to check for failures
                         choice { 
                             let th' = DENEG_RULE th
                             return!
                                 (ASSUME_TAC th'
                                  |> THEN <| SUBST1_TAC(EQT_INTRO th')) gl
                         }
                         |> Choice.bindError (
                                function 
                                | Failure _ -> 
                                    (ASSUME_TAC th
                                     |> THEN <| SUBST1_TAC(EQF_INTRO th)) gl
                                | e -> Choice.error e))];;

(* ------------------------------------------------------------------------- *)
(* Skolemization.                                                            *)
(* ------------------------------------------------------------------------- *)

let SKOLEM_THM = 
    prove
        ((parse_term @"!P. (!x:A. ?y:B. P x y) <=> (?y. !x. P x (y x))"), 
         REPEAT(STRIP_TAC
                |> ORELSE <| EQ_TAC)
         |> THENL <| [EXISTS_TAC(parse_term @"\x:A. @y:B. P x y")
                      |> THEN <| GEN_TAC
                      |> THEN <| BETA_TAC
                      |> THEN <| CONV_TAC SELECT_CONV
                      EXISTS_TAC(parse_term @"(y:A->B) x")]
         |> THEN <| POP_ASSUM MATCH_ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* NB: this one is true intutionistically and intensionally.                 *)
(* ------------------------------------------------------------------------- *)

let UNIQUE_SKOLEM_ALT = 
    prove
        ((parse_term @"!P:A->B->bool. (!x. ?!y. P x y) <=> ?f. !x y. P x y <=> (f x = y)"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [EXISTS_UNIQUE_ALT; SKOLEM_THM]);;

(* ------------------------------------------------------------------------- *)
(* and this one intuitionistically and extensionally.                        *)
(* ------------------------------------------------------------------------- *)

let UNIQUE_SKOLEM_THM = 
  prove ((parse_term @"!P. (!x:A. ?!y:B. P x y) <=> (?!f. !x. P x (f x))"),
    GEN_TAC 
    |> THEN <| REWRITE_TAC[EXISTS_UNIQUE_THM; SKOLEM_THM; FORALL_AND_THM] 
    |> THEN <| EQ_TAC 
    |> THEN <| DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) 
    |> THEN <| ASM_REWRITE_TAC[] 
    |> THENL <|
      [REPEAT STRIP_TAC 
       |> THEN <| ONCE_REWRITE_TAC[FUN_EQ_THM] 
       |> THEN <| X_GEN_TAC (parse_term @"x:A") 
       |> THEN <| FIRST_ASSUM MATCH_MP_TAC 
       |> THEN <| EXISTS_TAC (parse_term @"x:A") 
       |> THEN <| ASM_REWRITE_TAC[];
       MAP_EVERY X_GEN_TAC 
         [(parse_term @"x:A"); 
          (parse_term @"y1:B"); 
          (parse_term @"y2:B")] 
       |> THEN <| STRIP_TAC 
       |> THEN <| FIRST_ASSUM(X_CHOOSE_TAC (parse_term @"f:A->B")) 
       |> THEN <| SUBGOAL_THEN 
         (parse_term @"(\z. if z = x then y1 else (f:A->B) z) =
                    (\z. if z = x then y2 else (f:A->B) z)") MP_TAC 
       |> THENL <|
        [FIRST_ASSUM MATCH_MP_TAC 
         |> THEN <| REPEAT STRIP_TAC 
         |> THEN <| BETA_TAC 
         |> THEN <| COND_CASES_TAC 
         |> THEN <| ASM_REWRITE_TAC[];
         DISCH_THEN(MP_TAC << C AP_THM (parse_term @"x:A")) 
         |> THEN <| REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Extend default congruences for contextual rewriting.                      *)
(* ------------------------------------------------------------------------- *)

let COND_CONG = 
    TAUT(parse_term @"(g = g') ==>
        (g' ==> (t = t')) ==>
        (~g' ==> (e = e')) ==>
        ((if g then t else e) = (if g' then t' else e'))")

extend_basic_congs [COND_CONG]
|> Choice.ignoreOrRaise


let COND_EQ_CLAUSE = 
    prove((parse_term @"(if x = x then y else z) = y"), REWRITE_TAC []);;

extend_basic_rewrites [COND_EQ_CLAUSE] |> ignore

(* ------------------------------------------------------------------------- *)
(* We can now treat "bool" as an enumerated type for some purposes.          *)
(* ------------------------------------------------------------------------- *)

let bool_INDUCT = 
  prove
    ((parse_term @"!P. P F /\ P T ==> !x. P x"), 
      REPEAT STRIP_TAC
      |> THEN <| DISJ_CASES_TAC (SPEC (parse_term @"x:bool") BOOL_CASES_AX)
      |> THEN <| ASM_REWRITE_TAC []);;

let bool_RECURSION = 
  prove
    ((parse_term @"!a b:A. ?f. f F = a /\ f T = b"), 
      REPEAT GEN_TAC
      |> THEN <| EXISTS_TAC (parse_term @"\x. if x then b:A else a")
      |> THEN <| REWRITE_TAC []);;

/// List of inductive types defined with corresponding theorems.
let inductive_type_store = ref ["bool", (2, bool_INDUCT, bool_RECURSION)]
