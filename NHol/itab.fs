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
/// Intuitionistic theorem prover (complete for propositional fragment).
module NHol.itab

open System

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num
open ExtCore.Control

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
#endif

(* ------------------------------------------------------------------------- *)
(* Accept a theorem modulo unification.                                      *)
(* ------------------------------------------------------------------------- *)

/// Unify free variables in theorem and metavariables in goal to accept theorem.
let UNIFY_ACCEPT_TAC mvs (th : thm) : tactic =
    fun (asl, w) ->
        choice {
        let! th' = th
        let! insts = term_unify mvs (concl th') w
        let th'' = INSTANTIATE insts th
        return (([], insts), [], (fun i [] -> INSTANTIATE i th''))
        }

(* ------------------------------------------------------------------------- *)
(* The actual prover, as a tactic.                                           *)
(* ------------------------------------------------------------------------- *)

/// Simple intuitionistic logic prover.
let ITAUT_TAC = 
    let CONJUNCTS_THEN' ttac cth = 
        ttac(CONJUNCT1 cth)
        |> THEN <| ttac(CONJUNCT2 cth)

    let IMPLICATE t : thm =
        choice {
        let! t' = dest_neg t
        let th1 = AP_THM NOT_DEF t'
        return! CONV_RULE (RAND_CONV BETA_CONV) th1
        }

    let RIGHT_REVERSIBLE_TAC = 
        FIRST [ CONJ_TAC;                                                 (* and     *)
                GEN_TAC;                                                  (* forall  *)
                DISCH_TAC;                                                (* implies *)
                (fun gl -> CONV_TAC (K(IMPLICATE(snd gl))) gl);           (* not     *)
                EQ_TAC ]                                                  (* iff     *)

    let LEFT_REVERSIBLE_TAC th gl : goalstate = 
        tryfind (fun ttac -> Choice.toOption <| ttac th gl)        
            [ CONJUNCTS_THEN' ASSUME_TAC;                                 (* and    *)
              DISJ_CASES_TAC;                                             (* or     *)
              CHOOSE_TAC;                                                 (* exists *)
              (fun th gl -> 
                   choice { 
                       let! tm = Choice.map concl th
                       return! ASSUME_TAC(EQ_MP (IMPLICATE tm) th) gl 
                   });                                                    (* not    *)
              (CONJUNCTS_THEN' MP_TAC << uncurry CONJ << EQ_IMP_RULE) ]   (* iff    *)
        |> Option.toChoiceWithError "tryfind"

    let rec ITAUT_TAC mvs n gl : goalstate =
        let meta_spec_tac th : tactic =
            fun gl ->
                choice {
                    let! (tm, _) = Choice.bind (dest_forall << concl) th
                    let! ty = type_of tm
                    let gv = genvar ty
                    return! (META_SPEC_TAC gv th
                             |> THEN <| ITAUT_TAC (gv :: mvs) (n - 2)
                             |> THEN <| NO_TAC) gl
                }

        let x_meta_exists_tac : tactic =
            fun gl ->
                choice {
                     let! gv = (Choice.map genvar << Choice.bind type_of << Choice.map fst << dest_exists << snd) gl
                     return! (X_META_EXISTS_TAC gv
                              |> THEN <| ITAUT_TAC (gv :: mvs) (n - 2)
                              |> THEN <| NO_TAC) gl
                }

        let subgoal_then : thm_tactic = 
            fun th gl -> 
                choice {
                    let! (tm, _) = (Choice.bind dest_imp << Choice.map concl) th
                    return! (SUBGOAL_THEN tm (fun ath -> ASSUME_TAC(MP th ath))
                             |> THEN <| ITAUT_TAC mvs (n - 1)
                             |> THEN <| NO_TAC) gl
                }
                
        if n <= 0
        then Choice.failwith "ITAUT_TAC: Too deep"
        else 
            ((FIRST_ASSUM(UNIFY_ACCEPT_TAC mvs))
             |> ORELSE <| (ACCEPT_TAC TRUTH)
             |> ORELSE <| (FIRST_ASSUM CONTR_TAC)
             |> ORELSE <| (RIGHT_REVERSIBLE_TAC
                           |> THEN <| TRY(ITAUT_TAC mvs n))
             |> ORELSE <| (FIRST_X_ASSUM LEFT_REVERSIBLE_TAC
                           |> THEN <| TRY(ITAUT_TAC mvs n))
             |> ORELSE <| (FIRST_X_ASSUM(fun th -> 
                                   ASSUME_TAC th
                                   |> THEN <| meta_spec_tac th))
             |> ORELSE <| (DISJ1_TAC
                           |> THEN <| ITAUT_TAC mvs n
                           |> THEN <| NO_TAC)
             |> ORELSE <| (DISJ2_TAC
                           |> THEN <| ITAUT_TAC mvs n
                           |> THEN <| NO_TAC)
             |> ORELSE <| x_meta_exists_tac
             |> ORELSE <| (FIRST_ASSUM subgoal_then)) gl

    let rec ITAUT_ITERDEEP_TAC n gl = 
        remark("Searching with limit " + (string n))
        ((ITAUT_TAC [] n
          |> THEN <| NO_TAC)
         |> ORELSE <| ITAUT_ITERDEEP_TAC(n + 1)) gl
    ITAUT_ITERDEEP_TAC 0

(* ------------------------------------------------------------------------- *)
(* Alternative interface.                                                    *)
(* ------------------------------------------------------------------------- *)

/// Attempt to prove term using intuitionistic first-order logic.
let ITAUT tm = prove(tm, ITAUT_TAC)
