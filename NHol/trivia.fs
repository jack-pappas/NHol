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

#if INTERACTIVE
#else
/// Some very basic theories, e.g. type ":1".
module NHol.trivia

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

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
#endif

parse_as_infix("o", (26, "right"))

(* ------------------------------------------------------------------------- *)
(* Combinators. We don't bother with S and K, which seem of little use.      *)
(* ------------------------------------------------------------------------- *)
let o_DEF = new_definition(parse_term @"(o) (f:B->C) g = \x:A. f(g(x))")

let I_DEF = new_definition(parse_term @"I = \x:A. x")

let o_THM = 
    prove
        ((parse_term @"!f:B->C. !g:A->B. !x:A. (f o g) x = f(g(x))"), 
         PURE_REWRITE_TAC [o_DEF]
         |> THEN <| CONV_TAC(DEPTH_CONV BETA_CONV)
         |> THEN <| REPEAT GEN_TAC
         |> THEN <| REFL_TAC)

let o_ASSOC = 
    prove
        ((parse_term @"!f:C->D. !g:B->C. !h:A->B. f o (g o h) = (f o g) o h"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [o_DEF]
         |> THEN <| CONV_TAC(REDEPTH_CONV BETA_CONV)
         |> THEN <| REFL_TAC)

let I_THM = prove((parse_term @"!x:A. I x = x"), REWRITE_TAC [I_DEF])
let I_O_ID = 
    prove
        ((parse_term @"!f:A->B. (I o f = f) /\ (f o I = f)"), 
         REPEAT STRIP_TAC
         |> THEN <| REWRITE_TAC [FUN_EQ_THM; o_DEF; I_THM])

(* ------------------------------------------------------------------------- *)
(* The theory "1" (a 1-element type).                                        *)
(* ------------------------------------------------------------------------- *)
let EXISTS_ONE_REP = 
    prove((parse_term @"?b:bool. b"), EXISTS_TAC(parse_term @"T")
                                     |> THEN <| BETA_TAC
                                     |> THEN <| ACCEPT_TAC TRUTH)

let one_tydef = new_type_definition "1" ("one_ABS", "one_REP") EXISTS_ONE_REP
let one_DEF = new_definition(parse_term @"one = @x:1. T")

let one = 
    prove((parse_term @"!v:1. v = one"), MP_TAC
                                            (GEN_ALL
                                                 (SPEC (parse_term @"one_REP a") 
                                                      (CONJUNCT2 one_tydef)))
                                        |> THEN 
                                        <| REWRITE_TAC [CONJUNCT1 one_tydef]
                                        |> THEN <| DISCH_TAC
                                        |> THEN 
                                        <| ONCE_REWRITE_TAC 
                                               [GSYM(CONJUNCT1 one_tydef)]
                                        |> THEN <| ASM_REWRITE_TAC [])

let one_axiom = 
    prove((parse_term @"!f g. f = (g:A->1)"), REPEAT GEN_TAC
                                             |> THEN 
                                             <| ONCE_REWRITE_TAC [FUN_EQ_THM]
                                             |> THEN <| GEN_TAC
                                             |> THEN <| ONCE_REWRITE_TAC [one]
                                             |> THEN <| REFL_TAC)

let one_INDUCT = 
    prove((parse_term @"!P. P one ==> !x. P x"), ONCE_REWRITE_TAC [one]
                                                |> THEN <| REWRITE_TAC [])

let one_RECURSION = 
    prove((parse_term @"!e:A. ?fn. fn one = e"), GEN_TAC
                                                |> THEN 
                                                <| EXISTS_TAC
                                                       (parse_term @"\x:1. e:A")
                                                |> THEN <| BETA_TAC
                                                |> THEN <| REFL_TAC)

let one_Axiom = 
    prove((parse_term @"!e:A. ?!fn. fn one = e"), GEN_TAC
                                                 |> THEN 
                                                 <| REWRITE_TAC 
                                                        [EXISTS_UNIQUE_THM; 
                                                         one_RECURSION]
                                                 |> THEN <| REPEAT STRIP_TAC
                                                 |> THEN 
                                                 <| ONCE_REWRITE_TAC 
                                                        [FUN_EQ_THM]
                                                 |> THEN 
                                                 <| ONCE_REWRITE_TAC [one]
                                                 |> THEN <| ASM_REWRITE_TAC [])

inductive_type_store := ("1", (1, one_INDUCT, one_RECURSION)) :: (!inductive_type_store)