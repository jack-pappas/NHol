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

#if USE
#else
/// System of tactics (slightly different from any traditional LCF method).
module NHol.tactics

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
open drule
#endif

logger.Trace("Entering tactics.fs")

(* ------------------------------------------------------------------------- *)
(* The common case of trivial instantiations.                                *)
(* ------------------------------------------------------------------------- *)

/// Empty instantiation.
let null_inst = ([], [], [] : instantiation)

/// Empty metavariable information.
let null_meta = (([] : term list), null_inst)

(* ------------------------------------------------------------------------- *)
(* A goal has labelled assumptions, and the hyps are now thms.               *)
(* ------------------------------------------------------------------------- *)

type goal = (string * Protected<thm0>) list * term

/// NOTE: Redefined version of equals_thm
let equals_thm (th : Protected<thm0>) (th' : Protected<thm0>) =
    choice {
        let! th = th
        let! th' = th'
        return equals_thm th th'
    }
    |> Choice.fill false

/// Equality test on goals.
let equals_goal ((a, w) : goal) ((a', w') : goal) = 
    forall2 (fun (s, th) (s', th') -> 
                s = s' && equals_thm th th') a a' 
    && w = w'

(* ------------------------------------------------------------------------- *)
(* A justification function for a goalstate [A1 ?- g1; ...; An ?- gn],       *)
(* starting from an initial goal A ?- g, is a function f such that for any   *)
(* instantiation @:                                                          *)
(*                                                                           *)
(*   f(@) [A1@ |- g1@; ...; An@ |- gn@] = A@ |- g@                           *)
(* ------------------------------------------------------------------------- *)

type justification = instantiation -> thm0 list -> Protected<thm0>

/// Prints a justification signature to formatter.
let pp_print_justification fmt (just : justification) =
    pp_print_string fmt "instantiation -> thm list -> thm = <fun>" 

/// Prints a justification signature to the standard output.
let print_justification = pp_print_justification std_formatter

/// Converts a justification signature to a string representation.
let string_of_justification = print_to_string pp_print_justification

#if INTERACTIVE
fsi.AddPrinter string_of_justification
#endif

(* ------------------------------------------------------------------------- *)
(* The goalstate stores the subgoals, justification, current instantiation,  *)
(* and a list of metavariables.                                              *)
(* ------------------------------------------------------------------------- *)

type goalstate0 = (term list * instantiation) * goal list * justification
type goalstate = Protected<goalstate0>

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

/// Prints a refinement signature to formatter.
let pp_print_refinement fmt (r : refinement) =
    pp_print_string fmt "goalstate -> goalstate = <fun>"

/// Prints a refinement signature to the standard output.
let print_refinement = pp_print_refinement std_formatter

/// Converts a refinement signature to a string representation.
let string_of_refinement = print_to_string pp_print_refinement

#if INTERACTIVE
fsi.AddPrinter string_of_refinement
#endif

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

/// Prints a tactic signature to formatter.
let pp_print_tactic fmt (t : tactic) =
    pp_print_string fmt "goal -> goalstate = <fun>"

/// Prints a tactic signature to the standard output.
let print_tactic = pp_print_tactic std_formatter

/// Converts a tactic signature to a string representation.
let string_of_tactic = print_to_string pp_print_tactic

#if INTERACTIVE
fsi.AddPrinter string_of_tactic
#endif

type thm_tactic = Protected<thm0> -> tactic

/// Prints a thm_tactic signature to formatter.
let pp_print_thm_tactic fmt (tt : tactic) =
    pp_print_string fmt "thm -> tactic = <fun>"

/// Prints a thm_tactic signature to the standard output.
let print_thm_tactic = pp_print_thm_tactic std_formatter

/// Converts a thm_tactic signature to a string representation.
let string_of_thm_tactic = print_to_string pp_print_thm_tactic

#if INTERACTIVE
fsi.AddPrinter string_of_thm_tactic
#endif

type thm_tactical = thm_tactic -> thm_tactic

/// Prints a thm_tactical signature to formatter.
let pp_print_thm_tactical fmt (tt : thm_tactical) =
    pp_print_string fmt "thm_tactic -> thm_tactic = <fun>"

/// Prints a thm_tactical signature to the standard output.
let print_thm_tactical = pp_print_thm_tactical std_formatter

/// Converts a thm_tactical signature to a string representation.
let string_of_thm_tactical = print_to_string pp_print_thm_tactical

#if INTERACTIVE
fsi.AddPrinter string_of_thm_tactical
#endif

(* ------------------------------------------------------------------------- *)
(* Apply instantiation to a goal.                                            *)
(* ------------------------------------------------------------------------- *)

/// Apply higher-order instantiation to a goal.
let inst_goal : instantiation -> goal -> goal = 
    // TODO: to get rid of Choice.get, we have to lift from term to Choice<term, exn> in declaration of goal
    fun p (thms, w) -> map (I ||>> INSTANTIATE_ALL p) thms, Choice.get <| instantiate p w

(* ------------------------------------------------------------------------- *)
(* Perform a sequential composition (left first) of instantiations.          *)
(* ------------------------------------------------------------------------- *)

/// Compose two instantiations.
let compose_insts : instantiation -> instantiation -> instantiation = 
    fun (pats1, tmin1, tyin1) ((pats2, tmin2, tyin2) as i2) -> 
        let tmin = map ((Choice.get << instantiate i2) ||>> (Choice.get << inst tyin2)) tmin1
        let tyin = map (type_subst tyin2 ||>> I) tyin1
        let tmin' = filter (fun (_, x) -> Option.isNone <| rev_assoc x tmin) tmin2
        let tyin' = filter (fun (_, a) -> Option.isNone <| rev_assoc a tyin) tyin2
        pats1 @ pats2, tmin @ tmin', tyin @ tyin'

(* ------------------------------------------------------------------------- *)
(* Construct A,_FALSITY_ |- p; contortion so falsity is the last element.    *)
(* ------------------------------------------------------------------------- *)

let _FALSITY_ = new_definition(parse_term @"_FALSITY_ = F")

/// Create arbitrary theorem by adding additional `false' assumption.
let mk_fthm = 
    let pth = UNDISCH(fst(EQ_IMP_RULE _FALSITY_))
    let qth = ASSUME(parse_term @"_FALSITY_")
    fun (asl, c) -> 
        choice {
            let! pth = pth
            let! qth = qth
            let! th1 = CONTR c (Choice.result pth)
            let! th2 = itlist ADD_ASSUM (rev asl) (Choice.result th1)
            return! PROVE_HYP (Choice.result qth) (Choice.result th2)
        }

(* ------------------------------------------------------------------------- *)
(* Validity checking of tactics. This cannot be 100% accurate without making *)
(* arbitrary theorems, but "mk_fthm" brings us quite close.                  *)
(* ------------------------------------------------------------------------- *)

/// Tries to ensure that a tactic is valid.
let (VALID : tactic -> tactic) = 
    let fake_thm ((asl, w) : goal) = 
        choice {
            let! asl = Choice.List.map snd asl
            let asms = itlist (union << hyp) asl []
            return! mk_fthm(asms, w)
        }
    let false_tm = parse_term @"_FALSITY_"
    fun tac (asl, w) -> 
        choice {
            let! ((mvs, i), gls, just as res) = tac(asl, w)
            let! ths = Choice.List.map fake_thm gls
            let! thm = just null_inst ths
            let asl', w' = dest_thm thm
            let asl'', w'' = inst_goal i (asl, w)
            let! asl'' = Choice.List.map snd asl''
            let maxasms = itlist (fun th -> union (insert (concl th) (hyp th))) asl'' []
            if aconv w' w'' && forall (fun t -> exists (aconv t) maxasms) (subtract asl' [false_tm]) then 
                return res
            else 
                return! Choice.failwith "VALID: Invalid tactic"
        }

(* ------------------------------------------------------------------------- *)
(* Various simple combinators for tactics, identity tactic etc.              *)
(* ------------------------------------------------------------------------- *)

// THEN: Applies two tactics in sequence.
// THENL: Applies a list of tactics to the corresponding subgoals generated by a tactic.
let THEN, THENL = 
    let propagate_empty i x =
        match x with
        | [] -> []
        | _ -> failwith "propagate_empty: Unhandled case."

    let propagate_thm th i l =
        match l with
        | [] -> INSTANTIATE_ALL i th
        | _ -> Choice.failwith "propagate_thm: Unhandled case."

    let compose_justs n just1 just2 i ths = 
        // NOTE: Normalize list length to avoid exceptions
        // Beware that this change could lead to subtle bugs
        let n = 
            let len = List.length ths
            if n > len then len
            elif n < 0 then 0
            else n
        let ths1, ths2 = chop_list n ths
        (just1 i ths1) :: (just2 i ths2)

    let rec seqapply l1 l2 = 
        choice {
            match (l1, l2) with
            | ([], []) -> 
                return (null_meta, [], propagate_empty)
            | ((tac : tactic) :: tacs), ((goal : goal) :: goals) ->
                let! ((mvs1, insts1), gls1, just1) = tac goal
                let goals' = map (inst_goal insts1) goals
                let! ((mvs2, insts2), gls2, just2) = seqapply tacs goals'
                return ((union mvs1 mvs2, compose_insts insts1 insts2), gls1 @ gls2, 
                        compose_justs (length gls1) just1 just2)
            | _, _ -> return! Choice.failwith "seqapply: Length mismatch"
        }

    let justsequence just1 just2 insts2 i ths =
        choice { 
            let! ths = Choice.List.map id (just2 i ths)
            return! just1 (compose_insts insts2 i) ths
        }

    let tacsequence ((mvs1, insts1), gls1, just1 : justification) tacl : goalstate = 
        choice {
            let! ((mvs2, insts2), gls2, just2) = seqapply tacl gls1
            let jst = justsequence just1 just2 insts2
            let! just = 
                choice {
                    if gls2 = [] then 
                        // If th is an error, the goalstate is erroneous
                        let! th = jst null_inst []
                        return propagate_thm(Choice.result th)
                    else 
                        return jst
                }
            return ((union mvs1 mvs2, compose_insts insts1 insts2), gls2, just)
        }

    let then_ : tactic -> tactic -> tactic = 
        fun tac1 tac2 g -> 
            choice {
                let! (_, gls, _ as gstate) = tac1 g
                return! tacsequence gstate (replicate tac2 (length gls))
            }

    let thenl_ : tactic -> tactic list -> tactic = 
        fun tac1 tac2l g -> 
            choice {
                let! (_, gls, _ as gstate) = tac1 g
                if gls = [] then 
                    return! tacsequence gstate []
                else 
                    return! tacsequence gstate tac2l
            }
    then_, thenl_

/// Applies first tactic, and iff it fails, applies the second instead.
let (ORELSE : tactic -> tactic -> tactic) = 
    fun tac1 tac2 g -> 
        choice {
            let! (_, gls, just as gstate) = tac1 g
            return gstate
        }
        |> Choice.bindError (function
                | Failure _ -> tac2 g
                | e -> Choice.error e)

/// Tactic that always fails, with the supplied string.
let (FAIL_TAC : string -> tactic) = 
    fun tok g -> Choice.failwith tok

/// Tactic that always fails.
let (NO_TAC : tactic) = FAIL_TAC "NO_TAC"

/// Passes on a goal unchanged.
let (ALL_TAC : tactic) = 
    let fun1 x y =
        match (x, y) with
        | (_, [th]) -> Choice.result th
        | _ -> Choice.failwith "ALL_TAC.fun1: Unhandled case."
    fun g -> 
        choice {
            let just = fun1
            return (null_meta, [g], just)
        }

/// Makes a tactic have no effect rather than fail.
let TRY tac =
    tac |> ORELSE <| ALL_TAC;;

/// Repeatedly applies a tactic until it fails.
// CAUTION: Change this to delay StackOverflowException
let rec REPEAT tac g =
    ((tac |> THEN <| REPEAT tac) |> ORELSE <| ALL_TAC) g;;

/// Sequentially applies all the tactics in a given list of tactics.
let EVERY tacl =
    itlist THEN tacl ALL_TAC

/// Applies the first tactic in a tactic list that succeeds.
let FIRST : tactic list -> tactic =
    fun tacl g -> end_itlist ORELSE tacl g

/// Sequentially applies all tactics given by mapping a function over a list.
let MAP_EVERY (tacf : 'T -> tactic) (lst : 'T list) : tactic = 
    EVERY(map tacf lst)

/// Applies first tactic that succeeds in a list given by mapping a function over a list.
let MAP_FIRST tacf lst = FIRST(map tacf lst)

/// Makes a tactic fail if it has no effect.
let (CHANGED_TAC : tactic -> tactic) = 
    fun tac g -> 
        choice {
            let! (meta, gl, just as gstate) = tac g
            if meta = null_meta && length gl = 1 && equals_goal (hd gl) g then 
                return! Choice.failwith "CHANGED_TAC"
            else
                return gstate
        }

/// Apply a tactic a specific number of times.
let rec REPLICATE_TAC n tac =
    if n <= 0 then 
        ALL_TAC
    else
        tac |> THEN <|
        (REPLICATE_TAC (n - 1) tac)

(* ------------------------------------------------------------------------- *)
(* Combinators for theorem continuations / "theorem tacticals".              *)
(* ------------------------------------------------------------------------- *)

/// Composes two theorem-tacticals.
let (THEN_TCL : thm_tactical -> thm_tactical -> thm_tactical) = 
    fun ttcl1 ttcl2 ttac -> ttcl1(ttcl2 ttac)

/// Applies a theorem-tactical, and if it fails, tries a second.
let (ORELSE_TCL : thm_tactical -> thm_tactical -> thm_tactical) = 
    fun ttcl1 ttcl2 ttac th g -> 
        choice {
            let! (_, gls, just as gstate) = ttcl1 ttac th g
            return gstate
        }
        |> Choice.bindError (function
                | Failure _ -> ttcl2 ttac th g
                | e -> Choice.error e)

/// Repeatedly applies a theorem-tactical until it fails when applied to the theorem.
// CAUTION: Change REPEAT_TCL to delay StackOverflowException
let rec REPEAT_TCL ttcl ttac th =
    ((ttcl |> THEN_TCL <| (REPEAT_TCL ttcl)) |> ORELSE_TCL <| I) ttac th;;

/// Applies a theorem-tactical until it fails when applied to a goal.
let (REPEAT_GTCL : thm_tactical -> thm_tactical) = 
    let rec REPEAT_GTCL ttcl ttac th g = 
        choice {
            let! th = th
            let! (_, gls, just as gstate) = ttcl (REPEAT_GTCL ttcl ttac) (Choice.result th) g
            return gstate
        }
        |> Choice.bindError (function
                | Failure _ -> ttac th g
                | e -> Choice.error e)
    REPEAT_GTCL

/// Passes a theorem unchanged to a theorem-tactic.
let (ALL_THEN : thm_tactical) = I

/// Theorem-tactical which always fails.
let (NO_THEN : thm_tactical) = 
    fun ttac th g -> Choice.failwith "NO_THEN"

/// Composes a list of theorem-tacticals.
let EVERY_TCL ttcll =
    itlist THEN_TCL ttcll ALL_THEN

/// Applies the first theorem-tactical in a list that succeeds.
let FIRST_TCL ttcll =
    end_itlist ORELSE_TCL ttcll

(* ------------------------------------------------------------------------- *)
(* Tactics to augment assumption list. Note that to allow "ASSUME p" for     *)
(* any assumption "p", these add a PROVE_HYP in the justification function,  *)
(* just in case.                                                             *)
(* ------------------------------------------------------------------------- *)
    
/// Add an assumption with a named label to a goal.
let (LABEL_TAC : string -> thm_tactic) = 
    let fun1 l =
        match l with
        | [a] -> Choice.result a
        | _ -> Choice.failwith "LABEL_TAC.fun1: Unhandled case."
    fun s thm ((asl : (string * Protected<thm0>) list), (w : term)) ->
        choice {
            let just =
                fun i thml -> 
                    choice {
                        let! th1 = INSTANTIATE_ALL i thm
                        let! th2 = fun1 thml
                        return! PROVE_HYP (Choice.result th1) (Choice.result th2)
                    }
            let! thm = thm
            let! _ = Choice.List.map snd asl
            return (null_meta, [(s, Choice.result thm) :: asl, w], just)
        }

/// Adds an assumption to a goal.
let ASSUME_TAC = LABEL_TAC ""

(* ------------------------------------------------------------------------- *)
(* Manipulation of assumption list.                                          *)
(* ------------------------------------------------------------------------- *)

/// Apply a theorem-tactic to the the first assumption equal to given term.
let (FIND_ASSUM : thm_tactic -> term -> tactic) = 
    fun ttac t ((asl, w) as g) -> 
        choice {
            let! asl = Choice.List.map snd asl
            let! th1 = find (fun th -> concl th = t) asl
                       |> Option.toChoiceWithError "find"
            let! (_, gls, just as gstate) = ttac (Choice.result th1) g
            return gstate
        }

/// Applies tactic generated from the first element of a goal's assumption list.
let (POP_ASSUM : thm_tactic -> tactic) = 
    fun ttac -> 
        fun gl ->
            choice {
            match gl with 
            | (((_, th) :: asl), w) -> 
                let! th = th
                let! _ = Choice.List.map snd asl
                return! ttac (Choice.result th) (asl, w)
            | _ -> 
                return! Choice.failwith "POP_ASSUM: No assumption to pop"
            }

/// Applies a tactic generated from the goal's assumption list.
let (ASSUM_LIST : (Protected<thm0> list -> tactic) -> tactic) = 
    fun aslfun (asl, w) -> 
        choice {
            let asl0 = map snd asl
            let! _ = Choice.List.map id asl0
            return! aslfun asl0 (asl, w)
        }

/// Generates a tactic from the assumptions, discards the assumptions and applies the tactic.
let (POP_ASSUM_LIST : (Protected<thm0> list -> tactic) -> tactic) = 
    fun asltac (asl, w) -> 
        choice {
            let asl0 = map snd asl
            let! _ = Choice.List.map id asl0
            return! asltac asl0 ([], w)
        }

/// Sequentially applies all tactics given by mapping a function over the assumptions of a goal.
let (EVERY_ASSUM : thm_tactic -> tactic) = 
    fun ttac -> ASSUM_LIST(MAP_EVERY ttac)

/// Applied theorem-tactic to rst assumption possible.
let (FIRST_ASSUM : thm_tactic -> tactic) = 
    fun ttac (asl, w as g) -> 
        tryfind (fun (_, th) -> Choice.toOption <| ttac th g) asl 
        |> Option.toChoiceWithError "tryfind"

/// Maps an inference rule over the assumptions of a goal.
let (RULE_ASSUM_TAC : (Protected<thm0> -> Protected<thm0>) -> tactic) = 
    fun rule (asl,w) ->
        (POP_ASSUM_LIST(K ALL_TAC) 
         |> THEN <| MAP_EVERY (fun (s,th) -> LABEL_TAC s (rule th)) (rev asl)) (asl, w)

(* ------------------------------------------------------------------------- *)
(* Operate on assumption identified by a label.                              *)
(* ------------------------------------------------------------------------- *)

/// Apply a theorem tactic to named assumption.
let (USE_THEN : string -> thm_tactic -> tactic) = 
    fun s ttac (asl, w as gl) -> 
        choice {
            let! th =            
                match assoc s asl with
                | Some thm -> thm
                | None -> Choice.failwith ("USE_TAC: didn't find assumption " + s)

            let! (_, gls, just as gstate) = ttac (Choice.result th) gl
            return gstate
        }

/// Apply a theorem tactic to named assumption, removing the assumption.
let (REMOVE_THEN : string -> thm_tactic -> tactic) = 
    fun s ttac (asl, w) -> 
        choice {
        let! th =
            match assoc s asl with
            | Some thm -> thm
            | None -> Choice.failwith ("USE_TAC: didn't find assumption " + s)
        let asl1, asl2 = chop_list (index s (map fst asl)) asl
        let asl' = asl1 @ tl asl2
        let! _ = Choice.List.map snd asl'
        let! (_, gls, just as gstate) = ttac (Choice.result th) (asl', w)
        return gstate
        }

(* ------------------------------------------------------------------------- *)
(* General tools to augment a required set of theorems with assumptions.     *)
(* Here ASM uses all current hypotheses of the goal, while HYP uses only     *)
(* those whose labels are given in the string argument.                      *)
(* ------------------------------------------------------------------------- *)

/// Augments a tactic's theorem list with the assumptions.
let ASM : (Protected<thm0> list -> tactic) -> Protected<thm0> list -> tactic = 
    fun tltac ths (asl, w as g) ->
        choice {
            let asl0 = map snd asl @ ths
            let! _ = Choice.List.map id asl0
            return! tltac asl0 g
        }

/// Augments a tactic's theorem list with named assumptions.
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
        if rest = [] then 
            HYP_LIST tac l
        else 
            failwith "Invalid using pattern"

(* ------------------------------------------------------------------------- *)
(* Basic tactic to use a theorem equal to the goal. Does *no* matching.      *)
(* ------------------------------------------------------------------------- *)

/// Solves a goal if supplied with the desired theorem (up to alpha-conversion).
let (ACCEPT_TAC : thm_tactic) = 
    let propagate_thm th i x =
        match x with
        | [] -> INSTANTIATE_ALL i th
        | _ -> Choice.failwith  "propagate_thm: Unhandled case."
    fun th (asl, w) -> 
        choice {
            let! th = th
            let tm = concl th
            if aconv tm w then 
                let just = propagate_thm (Choice.result th)
                return (null_meta, [], just)
            else 
                return! Choice.failwith "ACCEPT_TAC"
        }

(* ------------------------------------------------------------------------- *)
(* Create tactic from a conversion. This allows the conversion to return     *)
(* |- p rather than |- p = T on a term "p". It also eliminates any goals of  *)
(* the form "T" automatically.                                               *)
(* ------------------------------------------------------------------------- *)

/// Makes a tactic from a conversion.
let (CONV_TAC : conv -> tactic) = 
    let t_tm = parse_term @"T"
    fun conv ((asl, w) as g) ->
        choice {
        let! th = conv w
        let tm = concl th
        if aconv tm w then
            return! ACCEPT_TAC (Choice.result th) g
        else 
            let! l, r = dest_eq tm
            if not(aconv l w) then
                return! Choice.failwith "CONV_TAC: bad equation"
            elif r = t_tm then
                let! th1 = EQT_ELIM (Choice.result th)
                return! ACCEPT_TAC (Choice.result th1) g
            else 
                let fun1 l =
                    match l with
                    | [a] -> Choice.result a
                    | _ -> Choice.failwith "CONV_TAC.fun1: Unhandled case."
                let! th' = SYM (Choice.result th)
                let just = 
                    fun i thml -> 
                        choice {
                            let! th1 = INSTANTIATE_ALL i (Choice.result th')
                            let! th2 = fun1 thml
                            return! EQ_MP (Choice.result th1) (Choice.result th2)
                        }
                let _ = Choice.List.map snd asl
                return (null_meta, [asl, r], just)
        }

(* ------------------------------------------------------------------------- *)
(* Tactics for equality reasoning.                                           *)
(* ------------------------------------------------------------------------- *)

/// Solves a goal that is an equation between alpha-equivalent terms.
let (REFL_TAC : tactic) = 
    fun ((asl, w) as g) -> 
        choice {
            let! tm = rand w
            let! th1 = REFL tm
            let! (_, gls, just as gstate) = ACCEPT_TAC (Choice.result th1) g
            return gstate
        }
        |> Choice.mapError (fun e -> nestedFailure e "REFL_TAC")

/// Strips an abstraction from each side of an equational goal.
let (ABS_TAC : tactic) = 
    fun (asl, w) -> 
        choice { 
            let! l, r = dest_eq w
            let! lv, lb = dest_abs l
            let! rv, rb = dest_abs r
            let! asl' = Choice.List.map snd asl
            let avoids = itlist (union << thm_frees) asl' (frees w)
            let! v = mk_primed_var avoids lv
            let! tm1 = vsubst [v, lv] lb
            let! tm2 = vsubst [v, rv] rb
            let! tm3 = mk_eq(tm1, tm2)
            let just = 
                fun i tl -> 
                    let fun1 l =
                        match l with
                        | [a] -> Choice.result a
                        | _ -> Choice.failwith "ABS_TAC.fun1: Unhandled case."
                    choice {
                        let! ath = ABS v (fun1 tl)
                        let tm = concl ath
                        let! tm1 = instantiate i w
                        let! th1 = ALPHA tm tm1
                        return! EQ_MP (Choice.result th1) (Choice.result ath)
                    }
            return (null_meta, [asl, tm3], just)            
        }
        |> Choice.mapError (fun e -> nestedFailure e "ABS_TAC: Failure.")

/// Breaks down a goal between function applications into equality of functions and arguments.
let (MK_COMB_TAC : tactic) = 
    fun (asl, gl) -> 
        choice { 
            let fun1 l =
                choice {
                    match l with
                    | [a1; a2] -> 
                        return (a1, a2)
                    | _ -> 
                        return! Choice.failwith "MK_COMB_TAC.fun1: Unhandled case."
                }

            let! l, r = dest_eq gl
            let! f, x = dest_comb l
            let! g, y = dest_comb r
            let! tm1 = mk_eq(f, g)
            let! tm2 = mk_eq(x, y)

            let just =
                fun _ tl -> 
                        choice {
                            let! (th1, th2) = fun1 tl
                            return! MK_COMB (Choice.result th1, Choice.result th2)
                        }
            let! _ = Choice.List.map snd asl
            return (null_meta, [asl, tm1; asl, tm2], just)            
        } 
        |> Choice.mapError (fun e -> nestedFailure e "MK_COMB_TAC: Failure.")

/// Strips a function application from both sides of an equational goal.
let (AP_TERM_TAC : tactic) =
     let tac = MK_COMB_TAC |> THENL <| [REFL_TAC; ALL_TAC]
     fun gl ->
        tac gl
        |> Choice.mapError (fun e -> nestedFailure e "AP_TERM_TAC")

/// Strips identical operands from functions on both sides of an equation.
let (AP_THM_TAC : tactic) =
    let tac = MK_COMB_TAC |> THENL <| [ALL_TAC; REFL_TAC]
    fun gl -> 
        tac gl
        |> Choice.mapError (fun e -> nestedFailure e "AP_THM_TAC")

/// Breaks apart equation between binary operator applications into equality between their arguments.
let (BINOP_TAC : tactic) =
    let tac = MK_COMB_TAC |> THENL <| [AP_TERM_TAC; ALL_TAC]
    fun gl -> 
        tac gl
        |> Choice.mapError (fun e -> nestedFailure e "AP_THM_TAC")

/// Makes a simple term substitution in a goal using a single equational theorem.
let (SUBST1_TAC : thm_tactic) = 
    fun th -> CONV_TAC (SUBS_CONV [th])

/// Substitutes using a single equation in both the assumptions and conclusion of a goal.
let SUBST_ALL_TAC rth =
    SUBST1_TAC rth |> THEN <| RULE_ASSUM_TAC (SUBS [rth])

/// Beta-reduces all the beta-redexes in the conclusion of a goal.
let BETA_TAC = 
    CONV_TAC (REDEPTH_CONV BETA_CONV)

(* ------------------------------------------------------------------------- *)
(* Just use an equation to substitute if possible and uninstantiable.        *)
(* ------------------------------------------------------------------------- *)

/// Use an equation to substitute "safely" in goal.
let SUBST_VAR_TAC (th : Protected<thm0>) g : goalstate = 
    choice { 
        let! th = th
        let asm, eq = dest_thm th
        let! l, r = dest_eq eq
        if aconv l r then 
            return! ALL_TAC g
        elif not(subset (frees eq) (freesl asm)) then 
            return! Choice.failwith ""
        elif (is_const l || is_var l) && not(Choice.get <| free_in l r) then 
            return! SUBST_ALL_TAC (Choice.result th) g
        elif (is_const r || is_var r) && not(Choice.get <| free_in r l) then
            return! SUBST_ALL_TAC (SYM (Choice.result th)) g
        else 
            return! Choice.failwith ""
    } 
    |> Choice.mapError (fun e -> nestedFailure e "SUBST_VAR_TAC")

(* ------------------------------------------------------------------------- *)
(* Basic logical tactics.                                                    *)
(* ------------------------------------------------------------------------- *)

/// Moves the antecedent of an implicative goal into the assumptions.
let (DISCH_TAC : tactic) = 
    let f_tm = parse_term @"F"
    fun (asl, w) ->
        choice {
            let! ant, c = dest_imp w
            let! th1 = ASSUME ant
            let fun1 l =
                match l with
                | [a] -> Choice.result a
                | _ -> Choice.failwith "DISCH_TAC.fun1: Unhandled case."
            let just i thl = 
                choice {
                    let! tm1 = instantiate i ant
                    let! th1 = fun1 thl
                    return! DISCH tm1 (Choice.result th1)
                }
            let! _ = Choice.List.map snd asl
            return (null_meta, [("", Choice.result th1) :: asl, c], just)
        }
        |> Choice.bindError (function
            | Failure _ ->
                choice { 
                    let fun2 l =
                        match l with
                        | [a] -> Choice.result a
                        | _ -> Choice.failwith "DISCH_TAC.fun2: Unhandled case."
                    let! ant = dest_neg w
                    let! th1 = ASSUME ant
                    let just =
                        fun i thl -> 
                            choice {
                                let! tm1 = instantiate i ant
                                let! th2 = fun2 thl
                                let! th3 = DISCH tm1 (Choice.result th2)
                                return! NOT_INTRO(Choice.result th3)
                            }
                    let! _ = Choice.List.map snd asl
                    return (null_meta, [("", Choice.result th1) :: asl, f_tm], just)
                }
                |> Choice.mapError (fun e -> nestedFailure e "DISCH_TAC")
            | e -> Choice.error e)

/// Adds a theorem as an antecedent to the conclusion of the goal.
let (MP_TAC : thm_tactic) = 
    let fun1 l =
        match l with
        | [a] -> Choice.result a
        | _ -> Choice.failwith "MP_TAC.fun1: Unhandled case."
    fun thm (asl, w) -> 
        choice {
            let! thm = thm
            let tm = concl thm
            let! tm' = mk_imp(tm, w)
            let just =
                fun i thl -> 
                    choice {
                        let! th1 = fun1 thl
                        let! th2 = INSTANTIATE_ALL i (Choice.result thm)
                        return! MP (Choice.result th1) (Choice.result th2)
                    }
            let! _ = Choice.List.map snd asl
            return (null_meta, [asl, tm'], just)        
        }

/// Reduces goal of equality of boolean terms to forward and backward implication.
let (EQ_TAC : tactic) = 
    fun (asl, w) ->
        choice {
            let fun1 l =
                match l with
                | [th1; th2] -> IMP_ANTISYM_RULE (Choice.result th1) (Choice.result th2)
                | _ -> Choice.failwith "EQ_TAC.fun1: Unhandled case."
            let! l, r = dest_eq w
            let! tm1 = mk_imp(l, r)
            let! tm2 = mk_imp(r, l)
            let just =
                fun _ tml -> fun1 tml
            let! _ = Choice.List.map snd asl
            return (null_meta, [asl, tm1; asl, tm2], just)
        }
        |> Choice.mapError (fun e -> nestedFailure e "EQ_TAC: Failure.")

/// Undischarges an assumption.
let (UNDISCH_TAC : term -> tactic) = 
    fun tm (asl, w) -> 
        choice {
            let fun1 l =
                match l with
                | [a] -> Choice.result a
                | _ -> Choice.failwith "UNDISCH_TAC.fun1: Unhandled case."
            let! sthm, asl' = 
                remove (fun (_, asm) -> 
                    match asm with
                    | Success asm -> aconv (concl asm) tm
                    | Error _ -> false) asl
                |> Option.toChoiceWithError "remove"
            let! thm = snd sthm
            let! tm' = mk_imp(tm, w)
            let just =
                fun i tl -> 
                    choice {
                        let! th1 = fun1 tl
                        let! th2 = INSTANTIATE_ALL i (Choice.result thm)
                        return! MP (Choice.result th1) (Choice.result th2)
                    }
            let! _ = Choice.List.map snd asl'
            return (null_meta, [asl', tm'], just)
        }
        |> Choice.mapError (fun e -> nestedFailure e "UNDISCH_TAC: Failure.")

/// Generalizes a goal.
let (SPEC_TAC : term * term -> tactic) = 
    fun (t, x) (asl, w) ->
        choice {
            let fun1 l =
                match l with
                | [a] -> Choice.result a
                | _ -> Choice.failwith "LABEL_TAC.fun1: Unhandled case."
            let! tm1 = subst [x, t] w
            let! tm2 = mk_forall(x, tm1)
            let just =
                fun i tl -> 
                    choice {
                        let! tm1 = instantiate i t
                        let! th2 = fun1 tl
                        return! SPEC tm1 (Choice.result th2)
                    }
            let! _ = Choice.List.map snd asl
            return (null_meta, [asl, tm2], just)
        }
        |> Choice.mapError (fun e -> nestedFailure e "SPEC_TAC: Failure.")

let private tactic_type_compatibility_check pfx e g : Protected<_> =
    choice {
    let! et = type_of e
    let! gt = type_of g
    if et = gt then
        return ()
    else 
        let msg = pfx + ": expected type :" + string_of_type et + " but got :" + string_of_type gt
        return! Choice.failwith msg
    }

/// Specializes a goal with the given variable.
let X_GEN_TAC x' : tactic = 
    if not(is_var x') then
        fun _ -> Choice.failwith "X_GEN_TAC: not a variable"
    else 
        fun (asl, w) ->
            choice {
                let! x, bod =
                    dest_forall w
                    |> Choice.mapError (fun e -> nestedFailure e "X_GEN_TAC: Not universally quantified")

                do! tactic_type_compatibility_check "X_GEN_TAC" x x'
                let! asl' = Choice.List.map snd asl
                let avoids = itlist (union << thm_frees) asl' (frees w)
                if mem x' avoids then
                    return! Choice.failwith "X_GEN_TAC: invalid variable"
                else 
                    let afn = CONV_RULE (GEN_ALPHA_CONV x)
                    let fun1 l =
                        match l with
                        | [a] -> Choice.result a
                        | _ -> Choice.failwith "X_GEN_TAC.fun1: Unhandled case."
                    let! tm = vsubst [x', x] bod
                    let just =
                        fun i tl -> 
                            choice {
                            let! th1 = fun1 tl
                            let! th2 = GEN x' (Choice.result th1)
                            return! afn (Choice.result th2)
                            }
                    return (null_meta, [asl, tm], just)
            }

/// Assumes a theorem, with existentially quantified variable replaced by a given witness.
let X_CHOOSE_TAC x' (xth : Protected<thm0>) : tactic =
    let xth' =
        choice {
            let! xth = xth
            let xtm = concl xth
            let! x, bod = 
                dest_exists xtm
                |> Choice.mapError (fun e -> nestedFailure e "X_CHOOSE_TAC: not existential") 

            do! tactic_type_compatibility_check "X_CHOOSE_TAC" x x'

            let! pat = vsubst [x', x] bod
            return! ASSUME pat
        }
    fun (asl, w) -> 
        choice {
            let! xth = xth
            let! xth' = xth'
            let! asl' = Choice.List.map snd asl
            let tms = thm_frees xth
            let avoids = itlist (union << frees << concl) asl' (union (frees w) tms)
            if mem x' avoids then
                return! Choice.failwith "X_CHOOSE_TAC: invalid variable"
            else 
                let fun1 l =
                    match l with
                    | [a] -> Choice.result a
                    | _ -> Choice.failwith "X_CHOOSE_TAC.fun1: Unhandled case."
                let just =
                    fun i tl -> 
                        choice {
                            let! th1 = INSTANTIATE_ALL i (Choice.result xth)
                            let! th2 = fun1 tl
                            return! CHOOSE (x', Choice.result th1) (Choice.result th2)
                        }
                return (null_meta, [("", Choice.result xth') :: asl, w], just)                
        }

/// Reduces existentially quantified goal to one involving a specific witness.
let EXISTS_TAC t : tactic =
    fun (asl, w) ->
        choice {
            let! v, bod = 
                dest_exists w
                |> Choice.mapError (fun e -> nestedFailure e "EXISTS_TAC: Goal not existentially quantified")
            do! tactic_type_compatibility_check "EXISTS_TAC" v t
            let fun1 l =
                match l with
                | [a] -> Choice.result a
                | _ -> Choice.failwith "EXISTS_TAC.fun1: Unhandled case."
            let! tm = vsubst [t, v] bod
            let just =
                fun i tl -> 
                    choice {
                        let! tm1 = instantiate i w
                        let! tm2 = instantiate i t
                        let! th1 = fun1 tl
                        return! EXISTS (tm1, tm2) (Choice.result th1)
                    }
            let! _ = Choice.List.map snd asl
            return (null_meta, [asl, tm], just)
        }

/// Strips the outermost universal quantifier from the conclusion of a goal.
let (GEN_TAC : tactic) = 
    fun (asl, w) -> 
        choice { 
            let! (x, _) = dest_forall w
            let! asl' = Choice.List.map snd asl
            let avoids = itlist (union << thm_frees) asl' (frees w)
            let! x' = mk_primed_var avoids x
            return! X_GEN_TAC x' (asl, w)
        }
        |> Choice.mapError (fun e -> nestedFailure e "GEN_TAC")

/// Adds the body of an existentially quantified theorem to the assumptions of a goal.
let (CHOOSE_TAC : thm_tactic) = 
    fun xth -> 
        fun (asl, w) -> 
            choice {
                let! xth = xth
                let! (x, _) = dest_exists <| concl xth
                let! asl' = Choice.List.map snd asl
                let tms = thm_frees xth
                let avoids = itlist (union << thm_frees) asl' (union (frees w) tms)
                let! x' = mk_primed_var avoids x
                return! X_CHOOSE_TAC x' (Choice.result xth) (asl, w)
            }
            |> Choice.mapError (fun e -> nestedFailure e "CHOOSE_TAC")            

/// Reduces a conjunctive goal to two separate subgoals.
let (CONJ_TAC : tactic) = 
    fun (asl, w) -> 
        choice {
        let fun1 l =
            match l with
            | [th1; th2] -> CONJ (Choice.result th1) (Choice.result th2)
            | _ -> Choice.failwith "CONJ_TAC.fun1: Unhandled case."
        let! l, r = dest_conj w
        let just =
            fun _ tl -> fun1 tl
        let! _ = Choice.List.map snd asl
        return (null_meta, [asl, l; asl, r], just)
        }    
        |> Choice.mapError (fun e -> nestedFailure e "CONJ_TAC: Failure.")

/// Selects the left disjunct of a disjunctive goal.
let (DISJ1_TAC : tactic) = 
    fun (asl, w) ->
        choice {
        let fun1 l =
            match l with
            | [a] -> Choice.result a
            | _ -> Choice.failwith "DISJ1_TAC.fun1: Unhandled case."
        let! l, r = dest_disj w
        let just =
            fun i tl -> 
                choice {
                    let! tm1 = instantiate i r
                    let! th1 = fun1 tl
                    return! DISJ1 (Choice.result th1) tm1
                }
        let! _ = Choice.List.map snd asl
        return (null_meta, [asl, l], just)
        }
        |> Choice.mapError (fun e -> nestedFailure e "DISJ1_TAC: Failure.")

/// Selects the right disjunct of a disjunctive goal.
let (DISJ2_TAC : tactic) = 
    fun (asl, w) ->
        choice {
        let fun1 l =
            match l with
            | [a] -> Choice.result a
            | _ -> Choice.failwith "DISJ2_TAC.fun1: Unhandled case."
        let! l, r = dest_disj w
        let just =
            fun i tl -> 
                choice {
                    let! tm1 = instantiate i l
                    let! th1 = fun1 tl
                    return! DISJ2 tm1 (Choice.result th1)
                }
        let! _ = Choice.List.map snd asl
        return (null_meta, [asl, r], just)
        }
        |> Choice.mapError (fun e -> nestedFailure e "DISJ2_TAC: Failure.")

/// Produces a case split based on a disjunctive theorem.
let (DISJ_CASES_TAC : thm_tactic) = 
    fun dth ->         
        let fun1 l i =
            choice {
                match l with
                | [th1; th2] -> 
                    let! dth = dth
                    let! th = INSTANTIATE_ALL i (Choice.result dth)
                    return! DISJ_CASES (Choice.result th) (Choice.result th1) (Choice.result th2)
                | _ -> 
                    return! Choice.failwith "DISJ_CASES_TAC.fun1: Unhandled case."
            }
        let v = 
            choice {
                let! dth = dth
                let dtm = concl dth
                let! (l, r) = dest_disj dtm
                let! thl = ASSUME l
                let! thr = ASSUME r
                return (l, r, thl, thr)
            }
        fun (asl, w) -> 
            choice {
                let! l, r, thl, thr = v
                let just =
                    fun i tl -> fun1 tl i
                let! _ = Choice.List.map snd asl
                return (null_meta, [("", Choice.result thl) :: asl, w; ("", Choice.result thr) :: asl, w], just)            
            }
            |> Choice.mapError (fun e -> nestedFailure e "DISJ_CASES_TAC: Failure.")

/// Solves any goal from contradictory theorem.
let (CONTR_TAC : thm_tactic) = 
    let propagate_thm th i l =
        match l with
        | [] -> INSTANTIATE_ALL i th
        | _ -> Choice.failwith "CONTR_TAC.propagate_thm: Unhandled case."
    fun cth (asl, w) -> 
        choice { 
            let! cth = cth
            // CAUTION: it's extremely weird that when I return early in case th is an error, ITAUT function doesn't terminate
            let! th = CONTR w (Choice.result cth)
            let just = propagate_thm (Choice.result th)
            return (null_meta, [], just)
        }
        |> Choice.mapError (fun e -> nestedFailure e "CONTR_TAC: Failure.")

/// Solves a goal which is an instance of the supplied theorem.
let (MATCH_ACCEPT_TAC : thm_tactic) =
    let propagate_thm th i l =
        match l with
        | [] -> INSTANTIATE_ALL i th
        | _ -> Choice.failwith "MATCH_ACCEPT_TAC.propagate_thm: Unhandled case."
    let rawtac th (asl,w) =
        choice {
            let! th = th
            let! ith = PART_MATCH Choice.result (Choice.result th) w
            let just = propagate_thm (Choice.result ith)
            return (null_meta, [], just)
        }
        |> Choice.mapError (fun e -> nestedFailure e "ACCEPT_TAC")
    fun th -> REPEAT GEN_TAC |> THEN <| rawtac th

/// Reduces the goal using a supplied implication, with matching.
let (MATCH_MP_TAC : thm_tactic) = 
    fun th -> 
        let sth = 
            choice { 
                let! th = th
                let tm = concl th
                let avs, bod = strip_forall tm
                let! ant, con = dest_imp bod
                let! th1 = SPECL avs (ASSUME tm)
                let! th2 = UNDISCH (Choice.result th1)
                let evs = filter (fun v -> vfree_in v ant && not(vfree_in v con)) avs
                let! th2' = DISCH tm (Choice.result th2)
                let! th3 = itlist SIMPLE_CHOOSE evs (Choice.result th2')
                let! tm3 = Choice.map (hd << hyp) (Choice.result th3)
                let! th4 = UNDISCH (Choice.result th3)
                let! th5 = DISCH tm3 (Choice.result th4)
                let! th6 = GEN_ALL (Choice.result th5)
                let! th7 = DISCH tm (Choice.result th6)
                return! MP (Choice.result th7) (Choice.result th)
            }
            |> Choice.mapError (fun e -> nestedFailure e "MATCH_MP_TAC: Bad theorem")

        let match_fun = PART_MATCH (Choice.map snd << dest_imp) sth

        fun (asl, w) -> 
            choice { 
                let fun1 l =
                    match l with
                    | [a] -> Choice.result a
                    | _ -> Choice.failwith "MATCH_MP_TAC.fun1: Unhandled case."
                let! xth = match_fun w
                let tm1 = concl xth
                let! (lant, _) = dest_imp tm1
                let just =
                    fun i tl -> 
                        choice {
                            let! th1 = INSTANTIATE_ALL i (Choice.result xth)
                            let! th2 = fun1 tl
                            return! MP (Choice.result th1) (Choice.result th2)
                        }
                let! _ = Choice.List.map snd asl
                return (null_meta, [asl, lant], just)
            }
            |> Choice.mapError (fun e -> nestedFailure e "MATCH_MP_TAC: No match")

(* ------------------------------------------------------------------------- *)
(* Theorem continuations.                                                    *)
(* ------------------------------------------------------------------------- *)

/// Applies two theorem-tactics to the corresponding conjuncts of a theorem.
let (CONJUNCTS_THEN2 : thm_tactic -> thm_tactic -> thm_tactic) =
    fun ttac1 ttac2 cth ->
        let c12 = Choice.bind (dest_conj << concl) cth
        fun gl -> 
            choice {
                let! c1, c2 = c12
                let! (ti, gls, jfn) = (ttac1(ASSUME c1) |> THEN <| ttac2(ASSUME c2)) gl
                
                let jfn' i ths =
                    choice {
                        let th1, th2 = CONJ_PAIR(INSTANTIATE_ALL i cth)
                        let! th1 = th1
                        let! th2 = th2
                        let! th3 = jfn i ths
                        let! th4 = PROVE_HYP (Choice.result th2) (Choice.result th3)
                        return! PROVE_HYP (Choice.result th1) (Choice.result th4)
                    }
                let just = jfn'
                return (ti, gls, jfn')                
            }

/// Applies a theorem-tactic to each conjunct of a theorem.
let (CONJUNCTS_THEN : thm_tactical) = W CONJUNCTS_THEN2

/// Applies separate theorem-tactics to the two disjuncts of a theorem.
let (DISJ_CASES_THEN2 : thm_tactic -> thm_tactic -> thm_tactic) =
    fun ttac1 ttac2 cth ->
        DISJ_CASES_TAC cth |> THENL <| [POP_ASSUM ttac1; POP_ASSUM ttac2]

/// Applies a theorem-tactic to each disjunct of a disjunctive theorem.
let (DISJ_CASES_THEN : thm_tactical) = W DISJ_CASES_THEN2

/// Undischarges an antecedent of an implication and passes it to a theorem-tactic.
let (DISCH_THEN : thm_tactic -> tactic) =
    fun ttac -> DISCH_TAC |> THEN <| POP_ASSUM ttac

/// Replaces existentially quantified variable with given witness, and passes it to a theorem-tactic.
let (X_CHOOSE_THEN : term -> thm_tactical) =
    fun x ttac th -> X_CHOOSE_TAC x th |> THEN <| POP_ASSUM ttac

/// Applies a tactic generated from the body of existentially quantified theorem.
let (CHOOSE_THEN : thm_tactical) =
    fun ttac th -> CHOOSE_TAC th |> THEN <| POP_ASSUM ttac

(* ------------------------------------------------------------------------- *)
(* Various derived tactics and theorem continuations.                        *)
(* ------------------------------------------------------------------------- *)

/// Applies the given theorem-tactic using the result of stripping off one outer
/// connective from the given theorem.
let STRIP_THM_THEN = 
    FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN; CHOOSE_THEN]

/// Resolves implicative assumptions with an antecedent.
let (ANTE_RES_THEN : thm_tactical) = 
    fun ttac ante gl -> 
        ASSUM_LIST (fun asl -> 
            // NOTE: this mapfilter call can throw exception in the original version, but can't return Choice2Of2 case here
            // We need to execute the tactic to be able to determine its failure
            let tacs = mapfilter (fun imp -> 
                          let f = ttac (MATCH_MP imp ante)
                          if Choice.isResult <| f gl then Some f else None) asl
            match tacs with
            | [] -> fun tm -> Choice.failwith "IMP_RES_THEN"
            | _ -> EVERY tacs) gl

/// Resolves an implication with the assumptions of a goal.
let (IMP_RES_THEN : thm_tactical) = 
    fun ttac imp gl -> 
        ASSUM_LIST(fun asl -> 
            // NOTE: this mapfilter call can throw exception in the original version, but can't return Choice2Of2 case here
            // We need to execute the tactic to be able to determine its failure
            let tacs = mapfilter (fun ante ->
                           let f = ttac (MATCH_MP imp ante)
                           if Choice.isResult <| f gl then Some f else None) asl
            match tacs with
            | [] -> fun tm -> Choice.failwith "IMP_RES_THEN"
            | _ -> EVERY tacs) gl

/// Splits a theorem into a list of theorems and then adds them to the assumptions.
let STRIP_ASSUME_TAC = 
    let DISCARD_TAC th = 
        let tm = Choice.map concl th
        fun (asl, w as g) -> 
            choice {
                let! tm = tm
                let! asl' = Choice.List.map snd asl
                if exists (fun a -> aconv tm (concl a)) asl' then 
                    return! ALL_TAC g
                else 
                    return! Choice.failwith "DISCARD_TAC: not already present"
            }
    
    (REPEAT_TCL STRIP_THM_THEN)(fun gth -> 
        FIRST [CONTR_TAC gth;
               ACCEPT_TAC gth;
               DISCARD_TAC gth;
               ASSUME_TAC gth])

/// Performs structural case analysis, applying theorem-tactic to results.
let STRUCT_CASES_THEN ttac = 
    REPEAT_TCL STRIP_THM_THEN ttac

/// Performs very general structural case analysis.
let STRUCT_CASES_TAC = 
    STRUCT_CASES_THEN (fun th -> SUBST1_TAC th |> ORELSE <| ASSUME_TAC th)

/// Splits a goal by eliminating one outermost connective, applying the given theorem-tactic
/// to the antecedents of implications.
let STRIP_GOAL_THEN ttac = 
    FIRST [GEN_TAC;
           CONJ_TAC;
           DISCH_THEN ttac]

/// Splits a goal by eliminating one outermost connective.
let (STRIP_TAC : tactic) = 
    fun g -> 
        STRIP_GOAL_THEN STRIP_ASSUME_TAC g
        |> Choice.mapError (fun e -> nestedFailure e "STRIP_TAC")

/// Undischarges an assumption and applies theorem-tactic to it.
let (UNDISCH_THEN : term -> thm_tactic -> tactic) = 
    fun tm ttac (asl, w) -> 
        choice {            
            let! thp, asl' = 
                remove (fun (_, th) -> 
                    match th with
                    | Success th -> aconv (concl th) tm
                    | Error _ -> false) asl
                |> Option.toChoiceWithError "remove"

            let! th = snd thp
            let! _ = Choice.List.map snd asl'
            return! ttac (Choice.result th) (asl', w)
        }

/// Applies theorem-tactic to first assumption possible, extracting assumption.
let FIRST_X_ASSUM ttac = 
    FIRST_ASSUM (fun th g -> 
        choice {
            let! th = th
            let tm = concl th
            return! UNDISCH_THEN tm ttac g
        })

(* ------------------------------------------------------------------------- *)
(* Subgoaling and freezing variables (latter is especially useful now).      *)
(* ------------------------------------------------------------------------- *)

/// Introduces a lemma as a new subgoal.
let SUBGOAL_THEN : term -> thm_tactic -> tactic = 
    fun wa ttac (asl, w) -> 
        choice {
            let! _ = Choice.List.map snd asl
            let! (meta, gl, just) = ttac (ASSUME wa) (asl, w)
            let just =
                fun i l -> 
                    choice {
                        let th1 = hd l
                        let! th2 = just i (tl l)
                        return! PROVE_HYP (Choice.result th1) (Choice.result th2)
                    }
            
            return(meta, (asl, wa) :: gl, just)            
        }

/// Encloses the sub-proof of a named lemma.
let SUBGOAL_TAC s tm prfs =
    match prfs with
    | p::ps ->
        warn (ps.Length <> 0) "SUBGOAL_TAC: additional subproofs ignored"
        SUBGOAL_THEN tm (LABEL_TAC s) |> THENL <| [p; ALL_TAC]
    |  [] -> fun _ -> Choice.failwith "SUBGOAL_TAC: no subproof given"

/// 'Freezes' a theorem to prevent instantiation of its free variables.
let (FREEZE_THEN : thm_tactical) = 
    fun ttac th (asl, w) -> 
        choice {
            let! th = th
            let tm = concl th
            let! _ = Choice.List.map snd asl
            let! (meta, gl, just) = ttac (ASSUME tm) (asl, w)
            let just =
                fun i l -> 
                    choice {
                        let! th1 = just i l
                        return! PROVE_HYP (Choice.result th) (Choice.result th1)
                    }
            return(meta, gl, just)            
        }

(* ------------------------------------------------------------------------- *)
(* Metavariable tactics.                                                     *)
(* ------------------------------------------------------------------------- *)

/// Replaces existentially quantified variable with given metavariables.
let (X_META_EXISTS_TAC : term -> tactic) = 
    fun t (asl, w) -> 
        choice { 
            if not (is_var t) then 
                return! Choice.fail()
            else 
                let fun1 l =
                    match l with
                    | [a] -> Choice.result a
                    | _ -> Choice.failwith "X_META_EXISTS_TAC.fun1: Unhandled case."
                let! v, bod = dest_exists w
                let! tm = vsubst [t, v] bod
                let just =
                    fun i tl -> 
                        choice {
                            let! tm1 = instantiate i w
                            let! tm2 = instantiate i t
                            let! th1 = fun1 tl
                            return! EXISTS (tm1, tm2) (Choice.result th1)
                        }
                let! _ = Choice.List.map snd asl
                return (([t], null_inst), [asl, tm], just)                
        }
        |> Choice.mapError (fun e -> nestedFailure e "X_META_EXISTS_TAC: Failure.")

/// Changes existentially quantified variable to metavariable.
let META_EXISTS_TAC : tactic =
    fun ((asl, w) as gl) ->
        choice {
            let! (v, _) = dest_exists w
            let! asl' = Choice.List.map snd asl
            let avoids = itlist (union << frees << concl) asl' (frees w)
            let! v' = mk_primed_var avoids v
            return! X_META_EXISTS_TAC v' gl
        }

/// Replaces universally quantified variable in theorem with metavariable.
let META_SPEC_TAC : term -> Protected<thm0> -> tactic = 
    fun t thm (asl, w) -> 
        choice {
            let fun1 l =
                match l with
                | [a] -> Choice.result a
                | _ -> Choice.failwith "MATCH_MP_TAC.fun1: Unhandled case."
            let! sth = SPEC t thm
            let just =
                fun i tl -> 
                    choice {
                        let! tm1 = instantiate i t
                        let! th1 = SPEC tm1 thm
                        return! PROVE_HYP (Choice.result th1) (fun1 tl)
                    }
            let! _ = Choice.List.map snd asl
            return (([t], null_inst), [(("", Choice.result sth) :: asl), w], just)            
        }

(* ------------------------------------------------------------------------- *)
(* If all else fails!                                                        *)
(* ------------------------------------------------------------------------- *)

/// Proves goal by asserting it as an axiom.
let (CHEAT_TAC : tactic) = 
    fun (asl, w) -> 
        choice {
            let! th = mk_thm([], w)
            let! _ = Choice.List.map snd asl
            return! ACCEPT_TAC (Choice.result th) (asl, w)
        }

(* ------------------------------------------------------------------------- *)
(* Intended for time-consuming rules; delays evaluation till it sees goal.   *)
(* ------------------------------------------------------------------------- *)

/// Delay evaluation of theorem-producing function till needed.
let RECALL_ACCEPT_TAC r a g = 
    choice {
        let! th = time r a
        return! ACCEPT_TAC (Choice.result th) g
    }

(* ------------------------------------------------------------------------- *)
(* Split off antecedent of antecedent as a subgoal.                          *)
(* ------------------------------------------------------------------------- *)

/// Split off antecedent of antecedent of goal as a new subgoal.
let ANTS_TAC =
    let tm1 = (parse_term @"p /\ (q ==> r)")
    let tm2 = (parse_term @"p ==> q")
    let th1,th2 = CONJ_PAIR(ASSUME tm1)
    fun g ->
        choice {
            let! th1 = th1
            let! th2 = th2
            let! th3 = ASSUME tm2
            let! th4 = MP (Choice.result th3) (Choice.result th1)
            let! th5 = MP (Choice.result th2) (Choice.result th4)
            let! th = itlist DISCH [tm1;tm2] (Choice.result th5)
            return! (MATCH_MP_TAC (Choice.result th) |> THEN <| CONJ_TAC) g
        }

(* ------------------------------------------------------------------------- *)
(* A printer for goals etc.                                                  *)
(* ------------------------------------------------------------------------- *)

/// Prints a goal to formatter.
let pp_print_goal fmt (gl : goal) = 
    let string3 n = 
        if n < 10
        then "  " + string n
        elif n < 100
        then " " + string n
        else string n
    let pp_print_hyp fmt n (s, th : Protected<thm0>) =
        match th with
        | Success th ->
            Format.pp_open_hbox fmt ()
            Format.pp_print_string fmt (string3 n)
            Format.pp_print_string fmt  " ["
            Format.pp_open_hbox fmt ()
            pp_print_qterm fmt (concl th)
            Format.pp_close_box fmt ()
            Format.pp_print_string fmt  "]"
            (if not(s = "") then (Format.pp_print_string fmt (" (" + s + ")"))
             else ())
            Format.pp_close_box fmt ()
            Format.pp_print_newline fmt ()
        | Error e ->
            let msg = Printf.sprintf "Error in theorem: %O" e
            Format.pp_print_string fmt msg
    let rec pp_print_hyps fmt n asl = 
        if asl = [] then ()
        else 
            (pp_print_hyp fmt n (hd asl)
             pp_print_hyps fmt (n + 1) (tl asl))
    let pp_print_asl_term fmt (asl, w) =
            Format.pp_print_newline fmt ()
            if asl <> [] then 
                (pp_print_hyps fmt 0 (rev asl)
                 Format.pp_print_newline fmt ())
            else ()
            pp_print_qterm fmt w
            Format.pp_print_newline fmt ()
    pp_print_asl_term fmt gl

/// Print a goal to standard output, with no following newline.
let print_goal = pp_print_goal std_formatter

/// Converts a goal to a string representation.
let string_of_goal = print_to_string pp_print_goal

#if INTERACTIVE
fsi.AddPrinter string_of_goal
#endif

/// Prints a list of goals to formatter.
let pp_print_list_goal fmt (al : goal list) =
    let rec pp_print_list_goalInner fmt al =
        match al with
        | g :: tl ->
            pp_print_goal fmt g
            pp_print_break fmt 0 0
            pp_print_list_goalInner fmt tl
        | [] -> ()
    if al.Length = 0
    then pp_print_string fmt "No goals"
    else
        pp_open_hvbox fmt 0
        pp_print_list_goalInner fmt al
        pp_close_box fmt ()

/// Print a list of goals to standard output, with no following newline.
let print_list_goal = pp_print_list_goal std_formatter

/// Converts a list of goals to a string representation.
let string_of_list_goal = print_to_string pp_print_list_goal

/// Prints a list of (term * term) to formatter.
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
    if al.Length = 0
    then pp_print_string fmt "No items"
    else
        pp_open_hvbox fmt 0
        pp_print_list_trmtrmInner fmt al
        pp_close_box fmt ()

/// Prints a goalstack to formatter.
let pp_print_goalstack fmt gs =
    let pp_print_goalstate fmt k (gs : goalstate0) = 
        let (_, gl, _) = gs
        let n = length gl
        let s = 
            if n = 0 then "No subgoals"
            else
                (string k) + " subgoal" + (if k > 1 then "s" else "") + " (" + (string n) + " total)"
        Format.pp_print_string fmt s
        Format.pp_print_newline fmt ()
        if not <| List.isEmpty gl then
            do_list (pp_print_goal fmt << C el gl) (rev(0 -- (k - 1)))

    let pp_print_goalstates fmt (l : goalstate list) =
        match Choice.List.map id l with
        | Success l ->
            // OPTIMIZE : Use pattern-matching here -- it's faster than checking the length
            // of the list, since we don't need to traverse the entire list.
            match l with
            | [] ->
                Format.pp_print_string fmt "Empty goalstack"
            | [x] -> 
                let gs = x
                pp_print_goalstate fmt 1 gs
            | x :: y :: _ -> 
                let (_, gl, _ as gs) = x
                let (_, gl0, _) = y
                let p = length gl - length gl0
                let p' = 
                    if p < 1 then 1
                    else p + 1
                pp_print_goalstate fmt p' gs
        | Error e -> 
            let msg = Printf.sprintf "Error in goalstack: %O" e
            Format.pp_print_string fmt msg
    pp_print_goalstates fmt gs

/// Print a goalstack to standard output, with no following newline.
let print_goalstack = pp_print_goalstack std_formatter

/// Converts a goalstack to a string representation.
let string_of_goalstack = print_to_string pp_print_goalstack

#if INTERACTIVE
fsi.AddPrinter string_of_goalstack
#endif

/// Prints a goalstate to formatter.
let pp_print_goalstate fmt gs =
    let ((trml,inst),gl,j) = gs
    let rec pp_print_trml fmt trml =
        match trml with
        | trm :: tl ->
            pp_print_term fmt trm
            pp_print_break fmt 0 0
            pp_print_trml fmt tl
        | [] -> ()
    pp_print_trml fmt trml
    pp_print_instantiation fmt inst
    let rec pp_print_gl fmt gl =
        match gl with
        | g :: tl ->
            pp_print_goal fmt g
            pp_print_break fmt 0 0
            pp_print_gl fmt tl
        | [] -> ()
    pp_print_gl fmt gl
    pp_print_justification fmt j

/// Prints a goalstate (without quotes) to the standard output.
let print_goalstate = pp_print_goalstate std_formatter

/// Converts a goalstate to a string representation.
let string_of_goalstate = print_to_string pp_print_goalstate

#if INTERACTIVE
fsi.AddPrinter string_of_goalstate
#endif

(* ------------------------------------------------------------------------- *)
(* Convert a tactic into a refinement on head subgoal in current state.      *)
(* ------------------------------------------------------------------------- *)

/// Converts a tactic to a refinement.
let by : tactic -> refinement = 
    fun tac g ->
        choice {
        let! ((mvs, inst), gls, just) = g
        if gls = [] then 
            return! Choice.failwith "No goal set"
        else 
            let g = hd gls
            let ogls = tl gls
            let! ((newmvs, newinst), subgls, subjust) = tac g
            let n = length subgls
            let mvs' = union newmvs mvs
            let inst' = compose_insts inst newinst
            let gls' = subgls @ map (inst_goal newinst) ogls
            let just' i ths = 
                choice {
                let i' = compose_insts inst' i
                let cths, oths = chop_list n ths
                let! th = subjust i cths
                let sths = th :: oths
                return! just i' sths
                }
            return ((mvs', inst'), gls', just')
        }

(* ------------------------------------------------------------------------- *)
(* Rotate the goalstate either way.                                          *)
(* ------------------------------------------------------------------------- *)

/// Rotate a goalstate.
let rotate : int -> refinement = 
    let rotate_p p =
        choice {
            let! (meta, sgs, just) = p
            let sgs' = (tl sgs) @ [hd sgs]
            let just' i ths = 
                let ths' = (last ths) :: (butlast ths)
                just i ths'
            return (meta, sgs', just')
        }

    let rotate_n n =
        choice {
            let! (meta, sgs, just) = n
            let sgs' = (last sgs) :: (butlast sgs)
            let just' i ths = 
                let ths' = (tl ths) @ [hd ths]
                just i ths'
            return (meta, sgs', just')
        }

    fun n -> 
        if n > 0
        then funpow n rotate_p
        else funpow (-n) rotate_n

(* ------------------------------------------------------------------------- *)
(* Perform refinement proof, tactic proof etc.                               *)
(* ------------------------------------------------------------------------- *)

/// Converts a goal into a 1-element goalstate.
let (mk_goalstate : goal -> goalstate) = 
    fun (asl, w) -> 
        choice {
            let! ty = type_of w
            if ty = bool_ty then 
                let fun1 l =
                    match l with
                    | [a] -> Choice.result a
                    | _ -> Choice.failwith "mk_goalstate.fun1: Unhandled case."
                let just =
                    fun inst tl -> 
                        choice {
                            let! th1 = fun1 tl
                            return! INSTANTIATE_ALL inst (Choice.result th1)
                        }
                let! _ = Choice.List.map snd asl
                return (null_meta, [asl, w], just) 
            else 
                return! Choice.failwith "mk_goalstate: Non-boolean goal"
        }

/// Attempts to prove a goal using a given tactic.
let (TAC_PROOF : goal * tactic -> Protected<thm0>) = 
    fun (g, tac) -> 
        choice {
            let! gstate = mk_goalstate g
            let! (_, sgs, just) = by tac (Choice.result gstate)
            match sgs with
            | [] ->
                return! just null_inst []
            | _ ->
                let ex =
                    let msg =
                        let goalOrGoals = if List.length sgs = 1 then "goal" else "goals"
                        Printf.sprintf "TAC_PROOF: %i unsolved %s" (List.length sgs) goalOrGoals
                    exn msg
                if not <| isNull ex.Data then
                    ex.Data.["UnsolvedGoals"] <- sgs
                return! Choice.error ex
        }

/// Attempts to prove a boolean term using the supplied tactic.
let prove(t, tac) : Protected<thm0> =
    choice {
    let! th = TAC_PROOF(([], t), tac)
    let t' = concl th
    if t' = t then
        return th
    else
        // TODO : Rename these values to something sensible.
        let! th' = ALPHA t' t
        return!
            EQ_MP (Choice.result th') (Choice.result th)
            |> Choice.mapError (fun e -> nestedFailure e "prove: justification generated wrong theorem")
    }
    |> function
        | Success th ->
            logger.Info(Printf.sprintf "Proved \"%s\"" (string_of_term t))
            Choice.result th
        | Error e ->
            logger.Error(Printf.sprintf "Failed at proving \"%s\"" (string_of_term t))
            logger.Error(Printf.sprintf "Currently return %O" e)
            Choice.error e

(* ------------------------------------------------------------------------- *)
(* Interactive "subgoal package" stuff.                                      *)
(* ------------------------------------------------------------------------- *)

/// Reference variable holding current goalstack.
let current_goalstack = ref([] : goalstack)

/// Applies a refinement to the current goalstack.
let (refine : refinement -> goalstack) = 
    fun r -> 
        let l = !current_goalstack
        if l.IsEmpty then 
            failwith "No current goal"
        else 
            let h = hd l
            let res = r h :: l
            current_goalstack := res
            !current_goalstack

/// Eliminate all but the current goalstate from the current goalstack.
let flush_goalstack() = 
    let l = !current_goalstack
    current_goalstack := [hd l]

/// Applies a tactic to the current goal, stacking the resulting subgoals.
let e tac = refine(by(VALID tac))

/// Reorders the subgoals on top of the subgoal package goal stack.
let r n = refine(rotate n)

/// Initializes the subgoal package with a new goal.
let set_goal(asl, w) = 
    current_goalstack := [mk_goalstate(map (fun t -> "", ASSUME t) asl, w)]
    !current_goalstack

/// Initializes the subgoal package with a new goal which has no assumptions.
let g t = 
    let fvs = sort (<) (map (fst << Choice.get << dest_var) (frees t))
    (if fvs <> []
     then 
         let errmsg = end_itlist (fun s t -> s + ", " + t) fvs
         warn true ("Free variables in goal: " + errmsg)
     else ())
    set_goal([], t)

/// Restores the proof state, undoing the effects of a previous expansion.
let b() = 
    let l = !current_goalstack
    if List.length l = 1
    then failwith "Can't back up any more"
    else 
        current_goalstack := tl l
        !current_goalstack

/// Prints the top level of the subgoal package goal stack.
let p() = !current_goalstack

/// Returns the actual internal structure of the current goal.
let top_realgoal() = 
    choice {
        match !current_goalstack with
        | Success(_, ((asl, w) :: _), _) :: _ -> return asl, w
        | Error e :: _ -> return! Choice.error e
        | _ -> 
            return! Choice.failwith "top_realgoal: Unhandled case."
    }

/// Returns the current goal of the subgoal package.
let top_goal() = 
    choice {
        let! asl, w = top_realgoal()
        let! tms = Choice.List.map (Choice.map concl << snd) asl
        return tms, w
    }

/// Returns the theorem just proved using the subgoal package.
let top_thm() = 
    choice {
        match !current_goalstack with
        | Success(_, [], f) :: _ -> return! f null_inst []
        | Error e :: _ -> return! Choice.error e
        | _ -> 
            return! Choice.failwith "top_thm: Unhandled case."
    }
