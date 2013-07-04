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
/// Axiom of Infinity, definition of natural numbers.
module NHol.nums

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

open NHol
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
open itab
open simp
open theorems
open ind_defs
open ``class``
open trivia
open canon
open meson
open quot
open pair

new_type("ind", 0)

let ONE_ONE = 
    new_definition
        (parse_term @"ONE_ONE(f:A->B) = !x1 x2. (f x1 = f x2) ==> (x1 = x2)")
let ONTO = new_definition(parse_term @"ONTO(f:A->B) = !y. ?x. y = f x")
let INFINITY_AX = new_axiom(parse_term @"?f:ind->ind. ONE_ONE f /\ ~(ONTO f)")

let IND_SUC_0_EXISTS = 
    prove
        ((parse_term 
              "?(f:ind->ind) z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\ (!x. ~(f x = z))"), 
         X_CHOOSE_TAC (parse_term @"f:ind->ind") INFINITY_AX
         |> THEN <| EXISTS_TAC(parse_term @"f:ind->ind")
         |> THEN <| POP_ASSUM MP_TAC
         |> THEN <| REWRITE_TAC [ONE_ONE; ONTO]
         |> THEN <| MESON_TAC [])

let IND_SUC_SPEC = 
    let th1 = 
        new_definition
            (parse_term 
                 "IND_SUC = @f:ind->ind. ?z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\ (!x. ~(f x = z))")
    let th2 = REWRITE_RULE [GSYM th1] (SELECT_RULE IND_SUC_0_EXISTS)
    let th3 = new_definition(parse_term @"IND_0 = @z:ind. (!x1 x2. IND_SUC x1 = IND_SUC x2 <=> x1 = x2) /\
                    (!x. ~(IND_SUC x = z))")
    REWRITE_RULE [GSYM th3] (SELECT_RULE th2)

let IND_SUC_INJ, IND_SUC_0 = CONJ_PAIR IND_SUC_SPEC
let NUM_REP_RULES, NUM_REP_INDUCT, NUM_REP_CASES = new_inductive_definition(parse_term @"NUM_REP IND_0 /\
    (!i. NUM_REP i ==> NUM_REP (IND_SUC i))")
let num_tydef = 
    new_basic_type_definition "num" ("mk_num", "dest_num") 
        (CONJUNCT1 NUM_REP_RULES)
let ZERO_DEF = new_definition(parse_term @"_0 = mk_num IND_0")
let SUC_DEF = new_definition(parse_term @"SUC n = mk_num(IND_SUC(dest_num n))")

let NOT_SUC_001 = 
    prove((parse_term @"!n. ~(SUC n = _0)"), REWRITE_TAC [SUC_DEF; ZERO_DEF]
                                            |> THEN <| MESON_TAC [NUM_REP_RULES
                                                                  fst num_tydef
                                                                  snd num_tydef
                                                                  IND_SUC_0])

let SUC_INJ = 
    prove
        ((parse_term @"!m n. SUC m = SUC n <=> m = n"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [SUC_DEF]
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| POP_ASSUM(MP_TAC << AP_TERM(parse_term @"dest_num"))
         |> THEN 
         <| SUBGOAL_THEN (parse_term @"!p. NUM_REP (IND_SUC (dest_num p))") 
                MP_TAC
         |> THENL <| [GEN_TAC
                      |> THEN <| MATCH_MP_TAC(CONJUNCT2 NUM_REP_RULES)
                      ALL_TAC]
         |> THEN <| REWRITE_TAC [fst num_tydef
                                 snd num_tydef]
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC [IND_SUC_INJ]
         |> THEN <| DISCH_THEN(MP_TAC << AP_TERM(parse_term @"mk_num"))
         |> THEN <| REWRITE_TAC [fst num_tydef])

let num_INDUCTION_001 = 
    prove
        ((parse_term @"!P. P(_0) /\ (!n. P(n) ==> P(SUC n)) ==> !n. P n"), 
         REPEAT STRIP_TAC
         |> THEN 
         <| MP_TAC
                (SPEC (parse_term @"\i. NUM_REP i /\ P(mk_num i):bool") 
                     NUM_REP_INDUCT)
         |> THEN <| ASM_REWRITE_TAC [GSYM ZERO_DEF
                                     NUM_REP_RULES]
         |> THEN 
         <| W
                (C SUBGOAL_THEN (fun t -> REWRITE_TAC [t]) << funpow 2 lhand 
                 << snd)
         |> THENL <| [REPEAT STRIP_TAC
                      |> THENL 
                      <| [MATCH_MP_TAC(CONJUNCT2 NUM_REP_RULES)
                          |> THEN <| ASM_REWRITE_TAC []
                          SUBGOAL_THEN 
                              (parse_term @"mk_num(IND_SUC i) = SUC(mk_num i)") 
                              SUBST1_TAC
                          |> THENL <| [REWRITE_TAC [SUC_DEF]
                                       |> THEN <| REPEAT AP_TERM_TAC
                                       |> THEN <| CONV_TAC SYM_CONV
                                       |> THEN 
                                       <| REWRITE_TAC [GSYM(snd num_tydef)]
                                       |> THEN <| FIRST_ASSUM MATCH_ACCEPT_TAC
                                       FIRST_ASSUM MATCH_MP_TAC
                                       |> THEN <| FIRST_ASSUM MATCH_ACCEPT_TAC]]
                      DISCH_THEN(MP_TAC << SPEC(parse_term @"dest_num n"))
                      |> THEN <| REWRITE_TAC [fst num_tydef
                                              snd num_tydef]])

let num_Axiom_001 = 
    prove
        ((parse_term @"!(e:A) f. ?!fn. (fn _0 = e) /\
                    (!n. fn (SUC n) = f (fn n) n)"), 
         REPEAT GEN_TAC
         |> THEN <| ONCE_REWRITE_TAC [EXISTS_UNIQUE_THM]
         |> THEN <| CONJ_TAC
         |> THENL <| [(MP_TAC << prove_inductive_relations_exist)
                          (parse_term 
                               "PRG _0 e /\ (!b:A n:num. PRG n b ==> PRG (SUC n) (f b n))")
                      |> THEN 
                      <| DISCH_THEN
                             (CHOOSE_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))
                      |> THEN 
                      <| DISCH_THEN
                             (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC << GSYM))
                      |> THEN 
                      <| SUBGOAL_THEN (parse_term @"!n:num. ?!y:A. PRG n y") 
                             MP_TAC
                      |> THENL <| [MATCH_MP_TAC num_INDUCTION_001
                                   |> THEN <| REPEAT STRIP_TAC
                                   |> THEN 
                                   <| FIRST_ASSUM
                                          (fun th -> 
                                              GEN_REWRITE_TAC BINDER_CONV 
                                                  [GSYM th])
                                   |> THEN 
                                   <| REWRITE_TAC 
                                          [GSYM NOT_SUC_001
                                           NOT_SUC_001; SUC_INJ; 
                                           EXISTS_UNIQUE_REFL]
                                   |> THEN <| REWRITE_TAC [UNWIND_THM1]
                                   |> THEN 
                                   <| UNDISCH_TAC
                                          (parse_term @"?!y. PRG (n:num) (y:A)")
                                   |> THEN <| REWRITE_TAC [EXISTS_UNIQUE_THM]
                                   |> THEN 
                                   <| DISCH_THEN
                                          (CONJUNCTS_THEN2 
                                               (X_CHOOSE_TAC(parse_term @"y:A")) 
                                               ASSUME_TAC)
                                   |> THEN <| REPEAT STRIP_TAC
                                   |> THEN <| ASM_REWRITE_TAC []
                                   |> THENL 
                                   <| [MAP_EVERY EXISTS_TAC [(parse_term 
                                                                  "(f:A->num->A) y n")
                                                             (parse_term @"y:A")]
                                       AP_THM_TAC
                                       |> THEN <| AP_TERM_TAC
                                       |> THEN <| FIRST_ASSUM MATCH_MP_TAC]
                                   |> THEN <| ASM_REWRITE_TAC []
                                   REWRITE_TAC [UNIQUE_SKOLEM_ALT]
                                   |> THEN 
                                   <| DISCH_THEN
                                          (X_CHOOSE_THEN 
                                               (parse_term @"fn:num->A") 
                                               (ASSUME_TAC << GSYM))
                                   |> THEN <| EXISTS_TAC(parse_term @"fn:num->A")
                                   |> THEN <| ASM_REWRITE_TAC []
                                   |> THEN <| GEN_TAC
                                   |> THEN 
                                   <| FIRST_ASSUM(MATCH_MP_TAC << CONJUNCT2)
                                   |> THEN 
                                   <| FIRST_ASSUM
                                          (fun th -> GEN_REWRITE_TAC I [GSYM th])
                                   |> THEN <| REFL_TAC]
                      REPEAT STRIP_TAC
                      |> THEN <| ONCE_REWRITE_TAC [FUN_EQ_THM]
                      |> THEN <| MATCH_MP_TAC num_INDUCTION_001
                      |> THEN <| ASM_REWRITE_TAC []
                      |> THEN <| REPEAT STRIP_TAC
                      |> THEN <| ASM_REWRITE_TAC []])

let NUMERAL = new_definition(parse_term @"NUMERAL (n:num) = n")

let [NOT_SUC; num_INDUCTION; num_Axiom] = 
    let th = prove((parse_term @"_0 = 0"), REWRITE_TAC [NUMERAL])
    map (GEN_REWRITE_RULE DEPTH_CONV [th]) 
        [NOT_SUC_001; num_INDUCTION_001; num_Axiom_001]

let (INDUCT_TAC : tactic) = 
    MATCH_MP_TAC num_INDUCTION
    |> THEN <| CONJ_TAC
    |> THENL <| [ALL_TAC
                 GEN_TAC
                 |> THEN <| DISCH_TAC]

let num_RECURSION = 
    let avs = fst(strip_forall(concl num_Axiom))
    GENL avs (EXISTENCE(SPECL avs num_Axiom))

let num_CASES = 
    prove
        ((parse_term @"!m. (m = 0) \/ (?n. m = SUC n)"), INDUCT_TAC
                                                        |> THEN <| MESON_TAC [])

let num_RECURSION_STD = 
    prove
        ((parse_term @"!e:Z f. ?fn. (fn 0 = e) /\ (!n. fn (SUC n) = f n (fn n))"), 
         REPEAT GEN_TAC
         |> THEN 
         <| MP_TAC
                (ISPECL [(parse_term @"e:Z")
                         (parse_term @"(\z n. (f:num->Z->Z) n z)")] num_RECURSION)
         |> THEN <| REWRITE_TAC [])

inductive_type_store 
:= ("num", (2, num_INDUCTION, num_RECURSION_STD)) :: (!inductive_type_store)

let BIT0_DEF = 
    let def = 
        new_definition
            (parse_term 
                 "BIT0 = @fn. fn 0 = 0 /\ (!n. fn (SUC n) = SUC (SUC(fn n)))")
    let th = 
        BETA_RULE(ISPECL [(parse_term @"0")
                          (parse_term @"\m n:num. SUC(SUC m)")] num_RECURSION)
    REWRITE_RULE [GSYM def] (SELECT_RULE th)

let BIT1_DEF = new_definition(parse_term @"BIT1 n = SUC (BIT0 n)")

let mk_numeral = 
    let Z = mk_const("_0", [])
    let BIT0 = mk_const("BIT0", [])
    let BIT1 = mk_const("BIT1", [])
    let NUMERAL = mk_const("NUMERAL", [])
    let zero = num_0
    let rec mk_num n = 
        if n =/ num_0
        then Z
        else 
            mk_comb((if mod_num n num_2 =/ num_0
                     then BIT0
                     else BIT1), mk_num(quo_num n num_2))
    fun n -> 
        if n </ zero
        then failwith "mk_numeral: negative argument"
        else mk_comb(NUMERAL, mk_num n)

let mk_small_numeral n = mk_numeral(Int n)
let dest_small_numeral t = Num.int_of_num(dest_numeral t)
let is_numeral = can dest_numeral
let the_specifications = ref []

let new_specification = 
    let check_distinct l = 
        try 
            itlist (fun t res -> 
                    if mem t res
                    then fail()
                    else t :: res) l [] |> ignore
            true
        with
        | Failure _ -> false
    let specify n name th = 
        let ntm = mk_numeral n
        let gv = genvar(type_of ntm)
        let th0 = CONV_RULE (REWR_CONV SKOLEM_THM) (GEN gv th)
        let th1 = CONV_RULE (RATOR_CONV(REWR_CONV EXISTS_THM)
                             |> THENC <| BETA_CONV) th0
        let l, r = dest_comb(concl th1)
        let rn = mk_comb(r, ntm)
        let ty = type_of rn
        let th2 = new_definition(mk_eq(mk_var(name, ty), rn))
        GEN_REWRITE_RULE ONCE_DEPTH_CONV [GSYM th2] 
            (SPEC ntm (CONV_RULE BETA_CONV th1))
    let rec specifies n names th = 
        match names with
        | [] -> th
        | name :: onames -> 
            let th' = specify n name th
            specifies (n +/ Int 1) onames th'
    let specification_counter = ref(Int 0)
    fun names th -> 
        let asl, c = dest_thm th
        if not(asl = [])
        then failwith "new_specification: Assumptions not allowed in theorem"
        elif not(frees c = [])
        then failwith "new_specification: Free variables in predicate"
        else 
            let avs = fst(strip_exists c)
            if length names = 0 || length names > length avs
            then 
                failwith 
                    "new_specification: Unsuitable number of constant names"
            elif not(check_distinct names)
            then failwith "new_specification: Constant names not distinct"
            else 
                try 
                    let sth = 
                        snd
                            (find 
                                 (fun ((names', th'), sth') ->
                                         names' = names 
                                         && aconv (concl th') (concl th)) 
                                 (!the_specifications))
                    warn true ("Benign respecification")
                    sth
                with
                | Failure _ -> 
                    let sth = specifies (!specification_counter) names th
                    the_specifications 
                    := ((names, th), sth) :: (!the_specifications)
                    specification_counter 
                    := !specification_counter +/ Int(length names)
                    sth