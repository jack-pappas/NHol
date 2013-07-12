(*

Copyright 1998 University of Cambridge
Copyright 1998-2007 John Harrison
Copyright 2012 Marco Maggesi
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

#if INTERACTIVE
#else
/// System of tactics (slightly different from any traditional LCF method).
module NHol.tactics

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
#endif

(* ------------------------------------------------------------------------- *)
(* The common case of trivial instantiations.                                *)
(* ------------------------------------------------------------------------- *)

let null_inst = ([], [], [] : instantiation)

let null_meta = (([] : term list), null_inst)

(* ------------------------------------------------------------------------- *)
(* A goal has labelled assumptions, and the hyps are now thms.               *)
(* ------------------------------------------------------------------------- *)

type goal = (string * thm) list * term

let equals_goal ((a, w) : goal) ((a', w') : goal) = 
    forall2 (fun (s, th) (s', th') -> s = s' && equals_thm th th') a a' 
    && w = w'

(* ------------------------------------------------------------------------- *)
(* A justification function for a goalstate [A1 ?- g1; ...; An ?- gn],       *)
(* starting from an initial goal A ?- g, is a function f such that for any   *)
(* instantiation @:                                                          *)
(*                                                                           *)
(*   f(@) [A1@ |- g1@; ...; An@ |- gn@] = A@ |- g@                           *)
(* ------------------------------------------------------------------------- *)

type justification = instantiation -> thm list -> thm

(* ------------------------------------------------------------------------- *)
(* The goalstate stores the subgoals, justification, current instantiation,  *)
(* and a list of metavariables.                                              *)
(* ------------------------------------------------------------------------- *)

type goalstate = (term list * instantiation) * goal list * justification

(* ------------------------------------------------------------------------- *)
(* A goalstack is just a list of goalstates. Could go for more...            *)
(* ------------------------------------------------------------------------- *)

type goalstack = goalstate list

(* ------------------------------------------------------------------------- *)
(* A refinement, applied to a goalstate [A1 ?- g1; ...; An ?- gn]            *)
(* yields a new goalstate with updated justification function, to            *)
(* give a possibly-more-instantiated version of the initial goal.            *)
(* ------------------------------------------------------------------------- *)

type refinement = goalstate -> goalstate

(* ------------------------------------------------------------------------- *)
(* A tactic, applied to a goal A ?- g, returns:                              *)
(*                                                                           *)
(*  o A list of new metavariables introduced                                 *)
(*  o An instantiation (%)                                                   *)
(*  o A list of subgoals                                                     *)
(*  o A justification f such that for any instantiation @ we have            *)
(*    f(@) [A1@  |- g1@; ...; An@ |- gn@] = A(%;@) |- g(%;@)                 *)
(* ------------------------------------------------------------------------- *)

type tactic = goal -> goalstate

type thm_tactic = thm -> tactic

type thm_tactical = thm_tactic -> thm_tactic

(* ------------------------------------------------------------------------- *)
(* Apply instantiation to a goal.                                            *)
(* ------------------------------------------------------------------------- *)

/// Apply higher-order instantiation to a goal.
let inst_goal : instantiation -> goal -> goal = 
    fun p (thms, w) -> map (I ||>> INSTANTIATE_ALL p) thms, instantiate p w

(* ------------------------------------------------------------------------- *)
(* Perform a sequential composition (left first) of instantiations.          *)
(* ------------------------------------------------------------------------- *)

/// Compose two instantiations.
let compose_insts : instantiation -> instantiation -> instantiation = 
    fun (pats1, tmin1, tyin1) ((pats2, tmin2, tyin2) as i2) -> 
        let tmin = map (instantiate i2 ||>> inst tyin2) tmin1
        let tyin = map (type_subst tyin2 ||>> I) tyin1
        let tmin' = filter (fun (_, x) -> not(can (rev_assoc x) tmin)) tmin2
        let tyin' = filter (fun (_, a) -> not(can (rev_assoc a) tyin)) tyin2
        pats1 @ pats2, tmin @ tmin', tyin @ tyin'

(* ------------------------------------------------------------------------- *)
(* Construct A,_FALSITY_ |- p; contortion so falsity is the last element.    *)
(* ------------------------------------------------------------------------- *)

let _FALSITY_ = new_definition(parse_term @"_FALSITY_ = F")

let mk_fthm = 
    let pth() = UNDISCH(fst(EQ_IMP_RULE _FALSITY_))
    let qth = ASSUME(parse_term @"_FALSITY_")
    fun (asl, c) -> PROVE_HYP qth (itlist ADD_ASSUM (rev asl) (CONTR c <| pth()))

(* ------------------------------------------------------------------------- *)
(* Validity checking of tactics. This cannot be 100% accurate without making *)
(* arbitrary theorems, but "mk_fthm" brings us quite close.                  *)
(* ------------------------------------------------------------------------- *)

let (VALID : tactic -> tactic) = 
    let fake_thm(asl, w) = 
        let asms = itlist (union << hyp << snd) asl []
        mk_fthm(asms, w)
    let false_tm = parse_term @"_FALSITY_"
    fun tac (asl, w) -> 
        let ((mvs, i), gls, just as res) = tac(asl, w)
        let ths = map fake_thm gls
        let asl', w' = dest_thm(just null_inst ths)
        let asl'', w'' = inst_goal i (asl, w)
        let maxasms = 
            itlist (fun (_, th) -> union(insert (concl th) (hyp th))) asl'' []
        if aconv w' w'' 
           && forall (fun t -> exists (aconv t) maxasms) 
                  (subtract asl' [false_tm])
        then res
        else failwith "VALID: Invalid tactic"

(* ------------------------------------------------------------------------- *)
(* Various simple combinators for tactics, identity tactic etc.              *)
(* ------------------------------------------------------------------------- *)

let (THEN), (THENL) = 
    let propagate_empty i x =
        match x with
        | [] -> []
        | _ -> failwith "propagate_empty: Unhandled case."
    let propagate_thm th i l =
        match l with
        | [] -> INSTANTIATE_ALL i th
        | _ -> failwith "propagate_thm: Unhandled case."
    let compose_justs n just1 just2 i ths = 
        let ths1, ths2 = chop_list n ths
        (just1 i ths1) :: (just2 i ths2)
    let rec seqapply l1 l2 = 
        match (l1, l2) with
        | ([], []) -> null_meta, [], propagate_empty
        | ((tac : tactic) :: tacs), ((goal : goal) :: goals) -> 
            let ((mvs1, insts1), gls1, just1) = tac goal
            let goals' = map (inst_goal insts1) goals
            let ((mvs2, insts2), gls2, just2) = seqapply tacs goals'
            ((union mvs1 mvs2, compose_insts insts1 insts2), gls1 @ gls2, 
             compose_justs (length gls1) just1 just2)
        | _, _ -> failwith "seqapply: Length mismatch"
    let justsequence just1 just2 insts2 i ths = 
        just1 (compose_insts insts2 i) (just2 i ths)
    let tacsequence ((mvs1, insts1), gls1, just1) tacl = 
        let ((mvs2, insts2), gls2, just2) = seqapply tacl gls1
        let jst = justsequence just1 just2 insts2
        let just = 
            if gls2 = []
            then propagate_thm(jst null_inst [])
            else jst
        ((union mvs1 mvs2, compose_insts insts1 insts2), gls2, just)
    let (then_ : tactic -> tactic -> tactic) = 
        fun tac1 tac2 g -> 
            let _, gls, _ as gstate = tac1 g
            tacsequence gstate (replicate tac2 (length gls))
    let (thenl_ : tactic -> tactic list -> tactic) = 
        fun tac1 tac2l g -> 
            let _, gls, _ as gstate = tac1 g
            if gls = []
            then tacsequence gstate []
            else tacsequence gstate tac2l
    then_, thenl_

let ((ORELSE) : tactic -> tactic -> tactic) = 
    fun tac1 tac2 g -> 
        try 
            tac1 g
        with
        | Failure _ -> tac2 g

let (FAIL_TAC : string -> tactic) = fun tok g -> failwith tok
let (NO_TAC : tactic) = FAIL_TAC "NO_TAC"

let (ALL_TAC : tactic) = 
  let fun1 x y =
      match (x,y) with
      | (_, [th]) -> th
      | _ -> failwith "ALL_TAC.fun1: Unhandled case."
  fun g -> null_meta, [g], fun1

let TRY tac = ORELSE tac ALL_TAC

// CAUTION: Change this to delay StackOverflowException
let rec REPEAT(tac : tactic) : tactic =
    fun g -> (ORELSE (THEN tac (REPEAT tac)) ALL_TAC) g

let EVERY tacl = itlist (fun t1 t2 -> THEN t1 t2) tacl ALL_TAC
let (FIRST : tactic list -> tactic) = 
    fun tacl g -> end_itlist (fun t1 t2 -> ORELSE t1 t2) tacl g
let MAP_EVERY (tacf : 'a -> tactic) (lst : 'a list) : tactic = 
    EVERY(map tacf lst)
let MAP_FIRST tacf lst = FIRST(map tacf lst)

let (CHANGED_TAC : tactic -> tactic) = 
    fun tac g -> 
        let (meta, gl, _ as gstate) = tac g
        if meta = null_meta && length gl = 1 && equals_goal (hd gl) g
        then failwith "CHANGED_TAC"
        else gstate

let rec REPLICATE_TAC n tac = 
    if n <= 0
    then ALL_TAC
    else THEN tac (REPLICATE_TAC (n - 1) tac)

(* ------------------------------------------------------------------------- *)
(* Combinators for theorem continuations / "theorem tacticals".              *)
(* ------------------------------------------------------------------------- *)

let ((THEN_TCL) : thm_tactical -> thm_tactical -> thm_tactical) = 
    fun ttcl1 ttcl2 ttac -> ttcl1(ttcl2 ttac)

let ((ORELSE_TCL) : thm_tactical -> thm_tactical -> thm_tactical) = 
    fun ttcl1 ttcl2 ttac th -> 
        try 
            ttcl1 ttac th
        with
        | Failure _ -> ttcl2 ttac th

// CAUTION: Change REPEAT_TCL to delay StackOverflowException
let rec REPEAT_TCL ttcl = 
    fun ttac -> (ORELSE_TCL (THEN_TCL ttcl (REPEAT_TCL ttcl)) I) ttac

let (REPEAT_GTCL : thm_tactical -> thm_tactical) = 
    let rec REPEAT_GTCL ttcl ttac th g = 
        try 
            ttcl (REPEAT_GTCL ttcl ttac) th g
        with
        | Failure _ -> ttac th g
    REPEAT_GTCL

let (ALL_THEN : thm_tactical) = I
let (NO_THEN : thm_tactical) = fun ttac th -> failwith "NO_THEN"
let EVERY_TCL ttcll = itlist (fun t1 t2 -> THEN_TCL t1 t2) ttcll ALL_THEN
let FIRST_TCL ttcll = end_itlist (fun t1 t2 -> ORELSE_TCL t1 t2) ttcll

(* ------------------------------------------------------------------------- *)
(* Tactics to augment assumption list. Note that to allow "ASSUME p" for     *)
(* any assumption "p", these add a PROVE_HYP in the justification function,  *)
(* just in case.                                                             *)
(* ------------------------------------------------------------------------- *)
    
let (LABEL_TAC : string -> thm_tactic) = 
    let fun1 l =
        match l with
        | [a] -> a
        | _ -> failwith "LABEL_TAC.fun1: Unhandled case."
    fun s thm  ((asl : (string * thm) list), (w : term)) ->
      null_meta, [(s, thm) :: asl, w], fun i thml -> PROVE_HYP (INSTANTIATE_ALL i thm) (fun1 thml)  

let ASSUME_TAC = LABEL_TAC ""

(* ------------------------------------------------------------------------- *)
(* Manipulation of assumption list.                                          *)
(* ------------------------------------------------------------------------- *)

let (FIND_ASSUM : thm_tactic -> term -> tactic) = 
    fun ttac t ((asl, w) as g) -> ttac (snd(find (fun (_, th) -> concl th = t) asl)) g

let (POP_ASSUM : thm_tactic -> tactic) = 
    fun ttac -> 
        function 
        | (((_, th) :: asl), w) -> ttac th (asl, w)
        | _ -> failwith "POP_ASSUM: No assumption to pop"

/// Applies a tactic generated from the goal's assumption list.
let ASSUM_LIST : (thm list -> tactic) -> tactic = 
    fun aslfun (asl, w) -> aslfun (map snd asl) (asl, w)
/// 
let (POP_ASSUM_LIST : (thm list -> tactic) -> tactic) = 
    fun asltac (asl, w) -> asltac (map snd asl) ([], w)
let (EVERY_ASSUM : thm_tactic -> tactic) = 
    fun ttac -> ASSUM_LIST(MAP_EVERY ttac)

let (FIRST_ASSUM : thm_tactic -> tactic) = 
    fun ttac (asl, w as g) -> tryfind (fun (_, th) -> ttac th g) asl

let (RULE_ASSUM_TAC : (thm -> thm) -> tactic) = 
    fun rule (asl, w) -> 
        (THEN (POP_ASSUM_LIST(K ALL_TAC)) 
             (MAP_EVERY (fun (s, th) -> LABEL_TAC s (rule th)) (rev asl)))
            (asl, w)

(* ------------------------------------------------------------------------- *)
(* Operate on assumption identified by a label.                              *)
(* ------------------------------------------------------------------------- *)

let (USE_THEN : string -> thm_tactic -> tactic) = 
    fun s ttac (asl, w as gl) -> 
        let th = 
            try 
                assoc s asl
            with
            | Failure _ -> failwith("USE_TAC: didn't find assumption " + s)
        ttac th gl

let (REMOVE_THEN : string -> thm_tactic -> tactic) = 
    fun s ttac (asl, w) -> 
        let th = 
            try 
                assoc s asl
            with
            | Failure _ -> failwith("USE_TAC: didn't find assumption " + s)
        let asl1, asl2 = chop_list (index s (map fst asl)) asl
        let asl' = asl1 @ tl asl2
        ttac th (asl', w)

(* ------------------------------------------------------------------------- *)
(* General tools to augment a required set of theorems with assumptions.     *)
(* Here ASM uses all current hypotheses of the goal, while HYP uses only     *)
(* those whose labels are given in the string argument.                      *)
(* ------------------------------------------------------------------------- *)

let (ASM : (thm list -> tactic) -> thm list -> tactic) = 
    fun tltac ths (asl, w as g) -> tltac (map snd asl @ ths) g

let HYP = 
    let ident = 
        function 
        | Ident s :: rest when isalnum s -> s, rest
        | _ -> raise Noparse
    let parse_using = many ident
    let HYP_LIST tac l = 
        rev_itlist (fun s k l -> USE_THEN s (fun th -> k(th :: l))) l tac
    fun tac s -> 
        let l, rest = (fix "Using pattern" parse_using << lex << explode) s
        if rest = []
        then HYP_LIST tac l
        else failwith "Invalid using pattern"

(* ------------------------------------------------------------------------- *)
(* Basic tactic to use a theorem equal to the goal. Does *no* matching.      *)
(* ------------------------------------------------------------------------- *)

let (ACCEPT_TAC : thm_tactic) = 
    let propagate_thm th i x =
        match x with
        | [] -> INSTANTIATE_ALL i th
        | _ -> failwith "propagate_thm: Unhandled case."
    fun th (asl, w) -> 
        if aconv (concl th) w
        then null_meta, [], propagate_thm th
        else failwith "ACCEPT_TAC"

(* ------------------------------------------------------------------------- *)
(* Create tactic from a conversion. This allows the conversion to return     *)
(* |- p rather than |- p = T on a term "p". It also eliminates any goals of  *)
(* the form "T" automatically.                                               *)
(* ------------------------------------------------------------------------- *)

let (CONV_TAC : conv -> tactic) = 
    let t_tm = parse_term @"T"
    fun conv ((asl, w) as g) -> 
        let th = conv w
        let tm = concl th
        if aconv tm w then ACCEPT_TAC th g
        else 
            let l, r = dest_eq tm
            if not(aconv l w) then failwith "CONV_TAC: bad equation"
            elif r = t_tm then ACCEPT_TAC (EQT_ELIM th) g
            else 
                let fun1 l =
                    match l with
                    | [a] -> a
                    | _ -> failwith "CONV_TAC.fun1: Unhandled case."
                let th' = SYM th
                null_meta, [asl, r], fun i thml -> EQ_MP (INSTANTIATE_ALL i th') (fun1 thml)

(* ------------------------------------------------------------------------- *)
(* Tactics for equality reasoning.                                           *)
(* ------------------------------------------------------------------------- *)

let (REFL_TAC : tactic) = 
    fun ((asl, w) as g) -> 
        try 
            ACCEPT_TAC (REFL(rand w)) g
        with
        | Failure _ -> failwith "REFL_TAC"

let (ABS_TAC : tactic) = 
    fun (asl, w) -> 
        try 
            let l, r = dest_eq w
            let lv, lb = dest_abs l
            let rv, rb = dest_abs r
            let avoids = itlist (union << thm_frees << snd) asl (frees w)
            let v = mk_primed_var avoids lv
            null_meta, [asl, mk_eq(vsubst [v, lv] lb, vsubst [v, rv] rb)], 
            fun i tl -> 
                let fun1 l =
                    match l with
                    | [a] -> a
                    | _ -> failwith "ABS_TAC.fun1: Unhandled case."
                let ath = ABS v (fun1 tl)
                EQ_MP (ALPHA (concl ath) (instantiate i w)) ath
        with
        | Failure _ -> failwith "ABS_TAC: Failure."

let (MK_COMB_TAC : tactic) = 
    fun (asl, gl) -> 
        try 
            let fun1 l =
                match l with
                | [a1; a2] -> (a1, a2)
                | _ -> failwith "MK_COMB_TAC.fun1: Unhandled case."
            let l, r = dest_eq gl
            let f, x = dest_comb l
            let g, y = dest_comb r
            null_meta, 
            [asl, mk_eq(f, g);
             asl, mk_eq(x, y)], fun _ tl -> MK_COMB (fun1 tl)
        with
        | Failure _ -> failwith "MK_COMB_TAC: Failure."

let (AP_TERM_TAC : tactic) = 
    let tac = THENL MK_COMB_TAC [REFL_TAC; ALL_TAC]
    fun gl -> 
        try 
            tac gl
        with
        | Failure _ -> failwith "AP_TERM_TAC"

let (AP_THM_TAC : tactic) = 
    let tac = THENL MK_COMB_TAC [ALL_TAC; REFL_TAC]
    fun gl -> 
        try 
            tac gl
        with
        | Failure _ -> failwith "AP_THM_TAC"

let (BINOP_TAC : tactic) = 
    let tac = THENL MK_COMB_TAC [AP_TERM_TAC; ALL_TAC]
    fun gl -> 
        try 
            tac gl
        with
        | Failure _ -> failwith "AP_THM_TAC"

let (SUBST1_TAC : thm_tactic) = fun th -> CONV_TAC(SUBS_CONV [th])
let SUBST_ALL_TAC rth = THEN (SUBST1_TAC rth) (RULE_ASSUM_TAC(SUBS [rth]))
let BETA_TAC = CONV_TAC(REDEPTH_CONV BETA_CONV)

(* ------------------------------------------------------------------------- *)
(* Just use an equation to substitute if possible and uninstantiable.        *)
(* ------------------------------------------------------------------------- *)

let SUBST_VAR_TAC th = 
    try 
        let asm, eq = dest_thm th
        let l, r = dest_eq eq
        if aconv l r
        then ALL_TAC
        elif not(subset (frees eq) (freesl asm))
        then fail()
        elif (is_const l || is_var l) && not(free_in l r)
        then SUBST_ALL_TAC th
        elif (is_const r || is_var r) && not(free_in r l)
        then SUBST_ALL_TAC(SYM th)
        else fail()
    with
    | Failure _ -> failwith "SUBST_VAR_TAC"

(* ------------------------------------------------------------------------- *)
(* Basic logical tactics.                                                    *)
(* ------------------------------------------------------------------------- *)

let (DISCH_TAC : tactic) = 
    let f_tm = parse_term @"F"
    fun (asl, w) -> 
        try 
            let ant, c = dest_imp w
            let th1 = ASSUME ant
            let fun1 l =
                match l with
                | [a] -> a
                | _ -> failwith "DISCH_TAC.fun1: Unhandled case."
            null_meta, [("", th1) :: asl, c], fun i thl -> DISCH (instantiate i ant) (fun1 thl)
        with
        | Failure _ -> 
            try 
                let fun2 l =
                    match l with
                    | [a] -> a
                    | _ -> failwith "DISCH_TAC.fun2: Unhandled case."
                let ant = dest_neg w
                let th1 = ASSUME ant
                null_meta, [("", th1) :: asl, f_tm], fun i thl -> NOT_INTRO(DISCH (instantiate i ant) (fun2 thl))
            with
            | Failure _ -> failwith "DISCH_TAC"

let (MP_TAC : thm_tactic) = 
    let fun1 l =
        match l with
        | [a] -> a
        | _ -> failwith "MP_TAC.fun1: Unhandled case."
    fun thm (asl, w) -> null_meta, [asl, mk_imp(concl thm, w)], fun i thl -> MP (fun1 thl) (INSTANTIATE_ALL i thm)

let (EQ_TAC : tactic) = 
    fun (asl, w) -> 
        try 
            let fun1 l =
                match l with
                | [th1; th2] -> IMP_ANTISYM_RULE th1 th2
                | _ -> failwith "EQ_TAC.fun1: Unhandled case."
            let l, r = dest_eq w
            null_meta, 
            [asl, mk_imp(l, r);
             asl, mk_imp(r, l)], fun _ tml -> fun1 tml
        with
        | Failure _ -> failwith "EQ_TAC: Failure."

let (UNDISCH_TAC : term -> tactic) = 
    fun tm (asl, w) -> 
        try 
            let fun1 l =
                match l with
                | [a] -> a
                | _ -> failwith "UNDISCH_TAC.fun1: Unhandled case."
            let sthm, asl' = remove (fun (_, asm) -> aconv (concl asm) tm) asl
            let thm = snd sthm
            null_meta, [asl', mk_imp(tm, w)], fun i tl -> MP (fun1 tl) (INSTANTIATE_ALL i thm)
        with
        | Failure _ -> failwith "UNDISCH_TAC: Failure."

let (SPEC_TAC : term * term -> tactic) = 
    fun (t, x) (asl, w) -> 
        try 
            let fun1 l =
                match l with
                | [a] -> a
                | _ -> failwith "LABEL_TAC.fun1: Unhandled case."
            null_meta, [asl, mk_forall(x, subst [x, t] w)], fun i tl -> SPEC (instantiate i t) (fun1 tl)
        with
        | Failure _ -> failwith "SPEC_TAC: Failure."

let private tactic_type_compatibility_check pfx e g = 
    let et = type_of e
    let gt = type_of g
    if et = gt
    then ()
    else 
        let msg = 
            (pfx + ": expected type :" + string_of_type et + " but got :" 
             + string_of_type gt)
        failwith msg

let X_GEN_TAC x' = 
    if not(is_var x')
    then failwith "X_GEN_TAC: not a variable"
    else 
        fun (asl, w) -> 
            let x, bod = 
                try 
                    dest_forall w
                with
                | Failure _ -> failwith "X_GEN_TAC: Not universally quantified"
            let _ = tactic_type_compatibility_check "X_GEN_TAC" x x'
            let avoids = itlist (union << thm_frees << snd) asl (frees w)
            if mem x' avoids
            then failwith "X_GEN_TAC: invalid variable"
            else 
                let afn = CONV_RULE(GEN_ALPHA_CONV x)
                let fun1 l =
                    match l with
                    | [a] -> a
                    | _ -> failwith "X_GEN_TAC.fun1: Unhandled case."
                null_meta, [asl, vsubst [x', x] bod], fun i tl -> afn(GEN x' (fun1 tl))

let X_CHOOSE_TAC x' xth = 
    let xtm = concl xth
    let x, bod = 
        try 
            dest_exists xtm
        with
        | Failure _ -> failwith "X_CHOOSE_TAC: not existential"
    let _ = tactic_type_compatibility_check "X_CHOOSE_TAC" x x'
    let pat = vsubst [x', x] bod
    let xth' = ASSUME pat
    fun (asl, w) -> 
        let avoids = 
            itlist (union << frees << concl << snd) asl 
                (union (frees w) (thm_frees xth))
        if mem x' avoids
        then failwith "X_CHOOSE_TAC: invalid variable"
        else 
            let fun1 l =
                match l with
                | [a] -> a
                | _ -> failwith "X_CHOOSE_TAC.fun1: Unhandled case."
            null_meta, [("", xth') :: asl, w], fun i tl -> CHOOSE (x', INSTANTIATE_ALL i xth) (fun1 tl)

let EXISTS_TAC t (asl, w) = 
    let v, bod = 
        try 
            dest_exists w
        with
        | Failure _ -> failwith "EXISTS_TAC: Goal not existentially quantified"
    let _ = tactic_type_compatibility_check "EXISTS_TAC" v t
    let fun1 l =
        match l with
        | [a] -> a
        | _ -> failwith "EXISTS_TAC.fun1: Unhandled case."
    null_meta, [asl, vsubst [t, v] bod], fun i tl -> EXISTS (instantiate i w, instantiate i t) (fun1 tl)

let (GEN_TAC : tactic) = 
    fun (asl, w) -> 
        try 
            let x = fst(dest_forall w)
            let avoids = itlist (union << thm_frees << snd) asl (frees w)
            let x' = mk_primed_var avoids x
            X_GEN_TAC x' (asl, w)
        with
        | Failure _ -> failwith "GEN_TAC"

let (CHOOSE_TAC : thm_tactic) = 
    fun xth -> 
        try 
            let x = fst(dest_exists(concl xth))
            fun (asl, w) -> 
                let avoids = 
                    itlist (union << thm_frees << snd) asl 
                        (union (frees w) (thm_frees xth))
                let x' = mk_primed_var avoids x
                X_CHOOSE_TAC x' xth (asl, w)
        with
        | Failure _ -> failwith "CHOOSE_TAC"

let (CONJ_TAC : tactic) = 
    fun (asl, w) -> 
        try 
            let fun1 l =
                match l with
                | [th1; th2] -> CONJ th1 th2
                | _ -> failwith "CONJ_TAC.fun1: Unhandled case."
            let l, r = dest_conj w
            null_meta, [asl, l
                        asl, r], fun _ tl -> fun1 tl
        with
        | Failure _ -> failwith "CONJ_TAC: Failure."

let (DISJ1_TAC : tactic) = 
    fun (asl, w) -> 
        try 
            let fun1 l =
                match l with
                | [a] -> a
                | _ -> failwith "DISJ1_TAC.fun1: Unhandled case."
            let l, r = dest_disj w
            null_meta, [asl, l], fun i tl -> DISJ1 (fun1 tl) (instantiate i r)
        with
        | Failure _ -> failwith "DISJ1_TAC: Failure."

let (DISJ2_TAC : tactic) = 
    fun (asl, w) -> 
        try 
            let fun1 l =
                match l with
                | [a] -> a
                | _ -> failwith "DISJ2_TAC.fun1: Unhandled case."
            let l, r = dest_disj w
            null_meta, [asl, r], fun i tl -> DISJ2 (instantiate i l) (fun1 tl)
        with
        | Failure _ -> failwith "DISJ2_TAC: Failure."

let (DISJ_CASES_TAC : thm_tactic) = 
    fun dth -> 
        try 
            let fun1 l i =
                match l with
                | [th1; th2] -> DISJ_CASES (INSTANTIATE_ALL i dth) th1 th2
                | _ -> failwith "DISJ_CASES_TAC.fun1: Unhandled case."
            let dtm = concl dth
            let l, r = dest_disj dtm
            let thl = ASSUME l
            let thr = ASSUME r
            fun (asl, w) -> 
                null_meta, [("", thl) :: asl, w
                            ("", thr) :: asl, w], fun i tl -> fun1 tl i
        with
        | Failure _ -> failwith "DISJ_CASES_TAC: Failure."

let (CONTR_TAC : thm_tactic) = 
    let propagate_thm th i l =
        match l with
        | [] -> INSTANTIATE_ALL i th
        | _ -> failwith "CONTR_TAC.propagate_thm: Unhandled case."
    fun cth (asl, w) -> 
        try 
            let th = CONTR w cth
            null_meta, [], propagate_thm th
        with
        | Failure _ -> failwith "CONTR_TAC: Failure."

let (MATCH_ACCEPT_TAC : thm_tactic) = 
    let propagate_thm th i l =
        match l with
        | [] -> INSTANTIATE_ALL i th
        | _ -> failwith "CONTR_TAC.propagate_thm: Unhandled case."
    let rawtac th (asl, w) = 
        try 
            let ith = PART_MATCH I th w
            null_meta, [], propagate_thm ith
        with
        | Failure _ -> failwith "ACCEPT_TAC: Failure."
    fun th -> THEN (REPEAT GEN_TAC) (rawtac th)

let (MATCH_MP_TAC : thm_tactic) = 
    fun th -> 
        let sth = 
            try 
                let tm = concl th
                let avs, bod = strip_forall tm
                let ant, con = dest_imp bod
                let th1 = SPECL avs (ASSUME tm)
                let th2 = UNDISCH th1
                let evs = 
                    filter (fun v -> vfree_in v ant && not(vfree_in v con)) avs
                let th3 = itlist SIMPLE_CHOOSE evs (DISCH tm th2)
                let tm3 = hd(hyp th3)
                MP (DISCH tm (GEN_ALL(DISCH tm3 (UNDISCH th3)))) th
            with
            | Failure _ -> failwith "MATCH_MP_TAC: Bad theorem"
        let match_fun = PART_MATCH (snd << dest_imp) sth
        fun (asl, w) -> 
            try 
                let fun1 l =
                    match l with
                    | [a] -> a
                    | _ -> failwith "MATCH_MP_TAC.fun1: Unhandled case."
                let xth = match_fun w
                let lant = fst(dest_imp(concl xth))
                null_meta, [asl, lant], fun i tl -> MP (INSTANTIATE_ALL i xth) (fun1 tl)
            with
            | Failure _ -> failwith "MATCH_MP_TAC: No match"

(* ------------------------------------------------------------------------- *)
(* Theorem continuations.                                                    *)
(* ------------------------------------------------------------------------- *)

let (CONJUNCTS_THEN2 : thm_tactic -> thm_tactic -> thm_tactic) = 
    fun ttac1 ttac2 cth -> 
        let c1, c2 = dest_conj(concl cth)
        fun gl -> 
            let ti, gls, jfn = (THEN (ttac1(ASSUME c1)) (ttac2(ASSUME c2))) gl
            let jfn' i ths = 
                let th1, th2 = CONJ_PAIR(INSTANTIATE_ALL i cth)
                PROVE_HYP th1 (PROVE_HYP th2 (jfn i ths))
            ti, gls, jfn'

let (CONJUNCTS_THEN : thm_tactical) = W CONJUNCTS_THEN2

let (DISJ_CASES_THEN2 : thm_tactic -> thm_tactic -> thm_tactic) = 
    fun ttac1 ttac2 cth -> 
        THENL (DISJ_CASES_TAC cth) [POP_ASSUM ttac1
                                    POP_ASSUM ttac2]

let (DISJ_CASES_THEN : thm_tactical) = W DISJ_CASES_THEN2
let (DISCH_THEN : thm_tactic -> tactic) = 
    fun ttac -> THEN DISCH_TAC (POP_ASSUM ttac)
let (X_CHOOSE_THEN : term -> thm_tactical) = 
    fun x ttac th -> THEN (X_CHOOSE_TAC x th) (POP_ASSUM ttac)
let (CHOOSE_THEN : thm_tactical) = 
    fun ttac th -> THEN (CHOOSE_TAC th) (POP_ASSUM ttac)

(* ------------------------------------------------------------------------- *)
(* Various derived tactics and theorem continuations.                        *)
(* ------------------------------------------------------------------------- *)

let STRIP_THM_THEN = FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN; CHOOSE_THEN]

let (ANTE_RES_THEN : thm_tactical) = 
    fun ttac ante -> 
        ASSUM_LIST(fun asl -> 
                let tacs = mapfilter (fun imp -> ttac(MATCH_MP imp ante)) asl
                match tacs with
                | [] -> failwith "IMP_RES_THEN"
                | _ -> EVERY tacs)

let (IMP_RES_THEN : thm_tactical) = 
    fun ttac imp -> 
        ASSUM_LIST(fun asl -> 
                let tacs = mapfilter (fun ante -> ttac(MATCH_MP imp ante)) asl
                match tacs with
                | [] -> failwith "IMP_RES_THEN"
                | _ -> EVERY tacs)

let STRIP_ASSUME_TAC = 
    let DISCARD_TAC th = 
        let tm = concl th
        fun (asl, w as g) -> 
                if exists (fun a -> aconv tm (concl(snd a))) asl
                then ALL_TAC g
                else failwith "DISCARD_TAC: not already present"
    
    (REPEAT_TCL STRIP_THM_THEN)(fun gth -> 
        FIRST [CONTR_TAC gth
               ACCEPT_TAC gth
               DISCARD_TAC gth
               ASSUME_TAC gth])

let STRUCT_CASES_THEN ttac = REPEAT_TCL STRIP_THM_THEN ttac
let STRUCT_CASES_TAC = 
    STRUCT_CASES_THEN(fun th -> ORELSE (SUBST1_TAC th) (ASSUME_TAC th))

let STRIP_GOAL_THEN ttac = 
    FIRST [GEN_TAC
           CONJ_TAC
           DISCH_THEN ttac]

let (STRIP_TAC : tactic) = 
    fun g -> 
        try 
            STRIP_GOAL_THEN STRIP_ASSUME_TAC g
        with
        | Failure _ -> failwith "STRIP_TAC"

let (UNDISCH_THEN : term -> thm_tactic -> tactic) = 
    fun tm ttac (asl, w) -> 
        let thp, asl' = remove (fun (_, th) -> aconv (concl th) tm) asl
        ttac (snd thp) (asl', w)

let FIRST_X_ASSUM ttac = FIRST_ASSUM(fun th -> UNDISCH_THEN (concl th) ttac)

(* ------------------------------------------------------------------------- *)
(* Subgoaling and freezing variables (latter is especially useful now).      *)
(* ------------------------------------------------------------------------- *)

let (SUBGOAL_THEN : term -> thm_tactic -> tactic) = 
    fun wa ttac (asl, w) -> 
        let meta, gl, just = ttac (ASSUME wa) (asl, w)
        meta, (asl, wa) :: gl, fun i l -> PROVE_HYP (hd l) (just i (tl l))

let SUBGOAL_TAC s tm prfs = 
    match prfs with
    | p :: ps -> 
        warn (ps.Length > 0) "SUBGOAL_TAC: additional subproofs ignored"
        THENL (SUBGOAL_THEN tm (LABEL_TAC s)) [p; ALL_TAC]
    | [] -> failwith "SUBGOAL_TAC: no subproof given"

let (FREEZE_THEN : thm_tactical) = 
    fun ttac th (asl, w) -> 
        let meta, gl, just = ttac (ASSUME(concl th)) (asl, w)
        meta, gl, fun i l -> PROVE_HYP th (just i l)

(* ------------------------------------------------------------------------- *)
(* Metavariable tactics.                                                     *)
(* ------------------------------------------------------------------------- *)

let (X_META_EXISTS_TAC : term -> tactic) = 
    fun t (asl, w) -> 
        try 
            if not(is_var t)
            then fail()
            else 
                let fun1 l =
                    match l with
                    | [a] -> a
                    | _ -> failwith "X_META_EXISTS_TAC.fun1: Unhandled case."
                let v, bod = dest_exists w
                ([t], null_inst), [asl, vsubst [t, v] bod], fun i tl -> EXISTS (instantiate i w, instantiate i t) (fun1 tl)
        with
        | Failure _ -> failwith "X_META_EXISTS_TAC: Failure."

let META_EXISTS_TAC((asl, w) as gl) = 
    let v = fst(dest_exists w)
    let avoids = itlist (union << frees << concl << snd) asl (frees w)
    let v' = mk_primed_var avoids v
    X_META_EXISTS_TAC v' gl

let (META_SPEC_TAC : term -> thm -> tactic) = 
    fun t thm (asl, w) -> 
        let fun1 l =
            match l with
            | [a] -> a
            | _ -> failwith "MATCH_MP_TAC.fun1: Unhandled case."
        let sth = SPEC t thm
        ([t], null_inst), [(("", sth) :: asl), w], fun i tl -> PROVE_HYP (SPEC (instantiate i t) thm) (fun1 tl)

(* ------------------------------------------------------------------------- *)
(* If all else fails!                                                        *)
(* ------------------------------------------------------------------------- *)

let (CHEAT_TAC : tactic) = fun (asl, w) -> ACCEPT_TAC (mk_thm([], w)) (asl, w)

(* ------------------------------------------------------------------------- *)
(* Intended for time-consuming rules; delays evaluation till it sees goal.   *)
(* ------------------------------------------------------------------------- *)

let RECALL_ACCEPT_TAC r a g = ACCEPT_TAC (time r a) g

(* ------------------------------------------------------------------------- *)
(* Split off antecedent of antecedent as a subgoal.                          *)
(* ------------------------------------------------------------------------- *)

let ANTS_TAC = 
    let tm1 = parse_term @"p /\ (q ==> r)"
    let tm2 = parse_term @"p ==> q"
    let th1, th2 = CONJ_PAIR(ASSUME tm1)
    let th = itlist DISCH [tm1; tm2] (MP th2 (MP (ASSUME tm2) th1))
    THEN (MATCH_MP_TAC th) CONJ_TAC

(* ------------------------------------------------------------------------- *)
(* A printer for goals etc.                                                  *)
(* ------------------------------------------------------------------------- *)

let (print_goal : goal -> unit) = 
    let string3 n = 
        if n < 10
        then "  " + string n
        elif n < 100
        then " " + string n
        else string n
    let print_hyp n (s, th) = 
        Format.open_hbox()
        Format.print_string(string3 n)
        Format.print_string " ["
        Format.open_hvbox 0
        print_qterm(concl th)
        Format.close_box()
        Format.print_string "]"
        (if not(s = "")
         then (Format.print_string(" (" + s + ")"))
         else ())
        Format.close_box()
        Format.print_newline()
    let rec print_hyps n asl = 
        if asl = []
        then ()
        else 
            (print_hyp n (hd asl)
             print_hyps (n + 1) (tl asl))
    fun (asl, w) -> 
        Format.print_newline()
        if asl <> []
        then 
            (print_hyps 0 (rev asl)
             Format.print_newline())
        else ()
        print_qterm w
        Format.print_newline()

let (print_goalstack : goalstack -> unit) = 
    let print_goalstate k gs = 
        let (_, gl, _) = gs
        let n = length gl
        let s = 
            if n = 0
            then "No subgoals"
            else 
                (string k) + " subgoal" + (if k > 1
                                                  then "s"
                                                  else "") + " (" 
                + (string n) + " total)"
        Format.print_string s
        Format.print_newline()
        if gl = []
        then ()
        else do_list (print_goal << C el gl) (rev(0 -- (k - 1)))
    fun l -> 
        match l.Length with
        | 0 -> Format.print_string "Empty goalstack"
        | 1 -> 
            let (_, gl, _ as gs) = hd l
            print_goalstate 1 gs
        | _ -> 
            let (_, gl, _ as gs) = hd l
            let (_, gl0, _) = hd(tl l)
            let p = length gl - length gl0
            let p' = 
                if p < 1
                then 1
                else p + 1
            print_goalstate p' gs

(* ------------------------------------------------------------------------- *)
(* Convert a tactic into a refinement on head subgoal in current state.      *)
(* ------------------------------------------------------------------------- *)

let (by : tactic -> refinement) = 
    fun tac ((mvs, inst), gls, just) -> 
        if gls = [] then failwith "No goal set"
        else 
            let g = hd gls
            let ogls = tl gls
            let ((newmvs, newinst), subgls, subjust) = tac g
            let n = length subgls
            let mvs' = union newmvs mvs
            let inst' = compose_insts inst newinst
            let gls' = subgls @ map (inst_goal newinst) ogls
            let just' i ths = 
                let i' = compose_insts inst' i
                let cths, oths = chop_list n ths
                let sths = (subjust i cths) :: oths
                just i' sths
            (mvs', inst'), gls', just'

(* ------------------------------------------------------------------------- *)
(* Rotate the goalstate either way.                                          *)
(* ------------------------------------------------------------------------- *)

let (rotate : int -> refinement) = 
    let rotate_p(meta, sgs, just) = 
        let sgs' = (tl sgs) @ [hd sgs]
        let just' i ths = 
            let ths' = (last ths) :: (butlast ths)
            just i ths'
        (meta, sgs', just')
    let rotate_n(meta, sgs, just) = 
        let sgs' = (last sgs) :: (butlast sgs)
        let just' i ths = 
            let ths' = (tl ths) @ [hd ths]
            just i ths'
        (meta, sgs', just')
    fun n -> 
        if n > 0
        then funpow n rotate_p
        else funpow (-n) rotate_n

(* ------------------------------------------------------------------------- *)
(* Perform refinement proof, tactic proof etc.                               *)
(* ------------------------------------------------------------------------- *)

let (mk_goalstate : goal -> goalstate) = 
    fun (asl, w) -> 
        if type_of w = bool_ty
        then 
            let fun1 l =
                match l with
                | [a] -> a
                | _ -> failwith "mk_goalstate.fun1: Unhandled case."
            null_meta, [asl, w], (fun inst tl -> INSTANTIATE_ALL inst (fun1 tl))
        else failwith "mk_goalstate: Non-boolean goal"

let (TAC_PROOF : goal * tactic -> thm) = 
    fun (g, tac) -> 
        let gstate = mk_goalstate g
        let _, sgs, just = by tac gstate
        match sgs with
        | [] ->
            just null_inst []
        | _ ->
            let ex =
                let msg =
                    let goalOrGoals = if List.length sgs = 1 then "goal" else "goals"
                    sprintf "TAC_PROOF: %i unsolved %s" (List.length sgs) goalOrGoals
                exn msg
            if not <| isNull ex.Data then
                ex.Data.["UnsolvedGoals"] <- sgs
            raise ex

let prove(t, tac) = 
    let th = TAC_PROOF(([], t), tac)
    let t' = concl th
    if t' = t
    then th
    else 
        try 
            EQ_MP (ALPHA t' t) th
        with
        | Failure _ -> failwith "prove: justification generated wrong theorem"

(* ------------------------------------------------------------------------- *)
(* Interactive "subgoal package" stuff.                                      *)
(* ------------------------------------------------------------------------- *)

let current_goalstack = ref([] : goalstack)

let (refine : refinement -> goalstack) = 
    fun r -> 
        let l = !current_goalstack
        if l.IsEmpty
        then failwith "No current goal"
        else 
            let h = hd l
            let res = r h :: l
            current_goalstack := res
            !current_goalstack

let flush_goalstack() = 
    let l = !current_goalstack
    current_goalstack := [hd l]

let e tac = refine(by(VALID tac))
let r n = refine(rotate n)

let set_goal(asl, w) = 
    current_goalstack := [mk_goalstate(map (fun t -> "", ASSUME t) asl, w)]
    !current_goalstack

let g t = 
    let fvs = sort (<) (map (fst << dest_var) (frees t))
    (if fvs <> []
     then 
         let errmsg = end_itlist (fun s t -> s + ", " + t) fvs
         warn true ("Free variables in goal: " + errmsg)
     else ())
    set_goal([], t)

let b() = 
    let l = !current_goalstack
    if List.length l = 1
    then failwith "Can't back up any more"
    else 
        current_goalstack := tl l
        !current_goalstack

let p() = !current_goalstack

let top_realgoal() = 
    match !current_goalstack with
    | (_, ((asl, w) :: _), _) :: _ -> asl, w
    | _ -> failwith "top_realgoal: Unhandled case."

let top_goal() = 
    let asl, w = top_realgoal()
    map (concl << snd) asl, w

let top_thm() = 
    match !current_goalstack with
    | (_, [], f) :: _ -> f null_inst []
    | _ -> failwith "top_thm: Unhandled case."