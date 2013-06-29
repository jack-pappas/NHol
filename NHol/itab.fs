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
/// Intuitionistic theorem prover (complete for propositional fragment).
module NHol.itab

open FSharp.Compatibility.OCaml
open lib
open fusion
open basics
open nets
open printer
open preterm
open parser
open equal
open bool
open drule
open tactics

(* ------------------------------------------------------------------------- *)
(* Accept a theorem modulo unification.                                      *)
(* ------------------------------------------------------------------------- *)
let UNIFY_ACCEPT_TAC mvs th (asl, w) = 
    let insts = term_unify mvs (concl th) w
    ([], insts), [], 
    let th' = INSTANTIATE insts th
    fun i [] -> INSTANTIATE i th'

(* ------------------------------------------------------------------------- *)
(* The actual prover, as a tactic.                                           *)
(* ------------------------------------------------------------------------- *)
let ITAUT_TAC = 
    let CONJUNCTS_THEN' ttac cth = ttac(CONJUNCT1 cth)
                                   |> THEN <| ttac(CONJUNCT2 cth)
    let IMPLICATE t = 
        let th1 = AP_THM NOT_DEF (dest_neg t)
        CONV_RULE (RAND_CONV BETA_CONV) th1
    let RIGHT_REVERSIBLE_TAC = 
        FIRST [CONJ_TAC                                                 (* and     *)
               GEN_TAC                                                  (* forall  *)
               DISCH_TAC                                                (* implies *)
               (fun gl -> CONV_TAC (K(IMPLICATE(snd gl))) gl)           (* not     *)
               EQ_TAC]                                                  (* iff     *)
    let LEFT_REVERSIBLE_TAC th gl = 
        tryfind (fun ttac -> ttac th gl)        
            [CONJUNCTS_THEN' ASSUME_TAC                                 (* and    *)
             DISJ_CASES_TAC                                             (* or     *)
             CHOOSE_TAC                                                 (* exists *)
             (fun th -> ASSUME_TAC(EQ_MP (IMPLICATE(concl th)) th))     (* not    *)
             (CONJUNCTS_THEN' MP_TAC << uncurry CONJ << EQ_IMP_RULE)]   (* iff    *)
    let rec ITAUT_TAC mvs n gl = 
        if n <= 0
        then failwith "ITAUT_TAC: Too deep"
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
                                   |> THEN <| (let gv = 
                                                   genvar
                                                       (type_of
                                                            (fst
                                                                 (dest_forall
                                                                      (concl th))))
                                               META_SPEC_TAC gv th
                                               |> THEN <| ITAUT_TAC (gv :: mvs) (n - 2)
                                               |> THEN <| NO_TAC)))
             |> ORELSE <| (DISJ1_TAC
                           |> THEN <| ITAUT_TAC mvs n
                           |> THEN <| NO_TAC)
             |> ORELSE <| (DISJ2_TAC
                           |> THEN <| ITAUT_TAC mvs n
                           |> THEN <| NO_TAC)
             |> ORELSE <| (fun gl -> 
                 let gv = genvar(type_of(fst(dest_exists(snd gl))))
                 (X_META_EXISTS_TAC gv
                  |> THEN <| ITAUT_TAC (gv :: mvs) (n - 2)
                  |> THEN <| NO_TAC) gl)
             |> ORELSE <| (FIRST_ASSUM(fun th -> 
                                   SUBGOAL_THEN (fst(dest_imp(concl th))) 
                                       (fun ath -> ASSUME_TAC(MP th ath))
                                   |> THEN <| ITAUT_TAC mvs (n - 1)
                                   |> THEN <| NO_TAC))) gl
    let rec ITAUT_ITERDEEP_TAC n gl = 
        remark("Searching with limit " + (string_of_int n))
        ((ITAUT_TAC [] n
          |> THEN <| NO_TAC)
         |> ORELSE <| ITAUT_ITERDEEP_TAC(n + 1)) gl
    ITAUT_ITERDEEP_TAC 0

(* ------------------------------------------------------------------------- *)
(* Alternative interface.                                                    *)
(* ------------------------------------------------------------------------- *)
let ITAUT tm = prove(tm, ITAUT_TAC)