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
//// Tools for defining inductive types.
module NHol.ind_types

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
open nums
open recursion
open arith
open wf
open calc_num
open normalizer

(* ------------------------------------------------------------------------- *)
(* Abstract left inverses for binary injections (we could construct them...) *)
(* ------------------------------------------------------------------------- *)
let INJ_INVERSE2 = 
  prove((parse_term @"!P:A->B->C.
    (!x1 y1 x2 y2. (P x1 y1 = P x2 y2) <=> (x1 = x2) /\ (y1 = y2))
    ==> ?X Y. !x y. (X(P x y) = x) /\ (Y(P x y) = y)"),
   GEN_TAC
   |> THEN <| DISCH_TAC
   |> THEN <| EXISTS_TAC(parse_term @"\z:C. @x:A. ?y:B. P x y = z")
   |> THEN <| EXISTS_TAC(parse_term @"\z:C. @y:B. ?x:A. P x y = z")
   |> THEN <| REPEAT GEN_TAC
   |> THEN <| ASM_REWRITE_TAC [BETA_THM]
   |> THEN <| CONJ_TAC
   |> THEN <| MATCH_MP_TAC SELECT_UNIQUE
   |> THEN <| GEN_TAC
   |> THEN <| BETA_TAC
   |> THEN <| EQ_TAC
   |> THEN <| STRIP_TAC
   |> THEN <| ASM_REWRITE_TAC []
   |> THEN <| W(EXISTS_TAC << rand << snd << dest_exists << snd)
   |> THEN <| REFL_TAC)

(* ------------------------------------------------------------------------- *)
(* Define an injective pairing function on ":num".                           *)
(* ------------------------------------------------------------------------- *)
let NUMPAIR = new_definition(parse_term @"NUMPAIR x y = (2 EXP x) * (2 * y + 1)")

let NUMPAIR_INJ_LEMMA = 
    prove
        ((parse_term 
              "!x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) ==> (x1 = x2)"), 
         REWRITE_TAC [NUMPAIR]
         |> THEN <| REPEAT(INDUCT_TAC
                           |> THEN <| GEN_TAC)
         |> THEN <| ASM_REWRITE_TAC [EXP
                                     GSYM MULT_ASSOC
                                     ARITH
                                     EQ_MULT_LCANCEL
                                     NOT_SUC
                                     GSYM NOT_SUC
                                     SUC_INJ]
         |> THEN <| DISCH_THEN(MP_TAC << AP_TERM(parse_term @"EVEN"))
         |> THEN <| REWRITE_TAC [EVEN_MULT; EVEN_ADD; ARITH])

let NUMPAIR_INJ = 
    prove
        ((parse_term 
              "!x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) <=> (x1 = x2) /\ (y1 = y2)"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| FIRST_ASSUM(SUBST_ALL_TAC << MATCH_MP NUMPAIR_INJ_LEMMA)
         |> THEN <| POP_ASSUM MP_TAC
         |> THEN <| REWRITE_TAC [NUMPAIR]
         |> THEN 
         <| REWRITE_TAC [EQ_MULT_LCANCEL; EQ_ADD_RCANCEL; EXP_EQ_0; ARITH])

let NUMPAIR_DEST = 
    new_specification ["NUMFST"
                       "NUMSND"] (MATCH_MP INJ_INVERSE2 NUMPAIR_INJ)

(* ------------------------------------------------------------------------- *)
(* Also, an injective map bool->num->num (even easier!)                      *)
(* ------------------------------------------------------------------------- *)
let NUMSUM = 
    new_definition(parse_term @"NUMSUM b x = if b then SUC(2 * x) else 2 * x")

let NUMSUM_INJ = 
    prove
        ((parse_term 
              "!b1 x1 b2 x2. (NUMSUM b1 x1 = NUMSUM b2 x2) <=> (b1 = b2) /\ (x1 = x2)"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| POP_ASSUM(MP_TAC << REWRITE_RULE [NUMSUM])
         |> THEN 
         <| DISCH_THEN
                (fun th -> MP_TAC th
                           |> THEN <| MP_TAC(AP_TERM (parse_term @"EVEN") th))
         |> THEN <| REPEAT COND_CASES_TAC
         |> THEN <| REWRITE_TAC [EVEN; EVEN_DOUBLE]
         |> THEN <| REWRITE_TAC [SUC_INJ; EQ_MULT_LCANCEL; ARITH])

let NUMSUM_DEST = 
    new_specification ["NUMLEFT"
                       "NUMRIGHT"] (MATCH_MP INJ_INVERSE2 NUMSUM_INJ)

(* ------------------------------------------------------------------------- *)
(* Injection num->Z, where Z == num->A->bool.                                *)
(* ------------------------------------------------------------------------- *)
let INJN = new_definition(parse_term @"INJN (m:num) = \(n:num) (a:A). n = m")

let INJN_INJ = 
    prove
        ((parse_term @"!n1 n2. (INJN n1 :num->A->bool = INJN n2) <=> (n1 = n2)"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN 
         <| POP_ASSUM
                (MP_TAC << C AP_THM (parse_term @"n1:num") << REWRITE_RULE [INJN])
         |> THEN <| DISCH_THEN(MP_TAC << C AP_THM (parse_term @"a:A"))
         |> THEN <| REWRITE_TAC [BETA_THM])

(* ------------------------------------------------------------------------- *)
(* Injection A->Z, where Z == num->A->bool.                                  *)
(* ------------------------------------------------------------------------- *)
let INJA = new_definition(parse_term @"INJA (a:A) = \(n:num) b. b = a")

let INJA_INJ = 
    prove
        ((parse_term @"!a1 a2. (INJA a1 = INJA a2) <=> (a1:A = a2)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [INJA; FUN_EQ_THM]
         |> THEN <| EQ_TAC
         |> THENL <| [DISCH_THEN(MP_TAC << SPEC(parse_term @"a1:A"))
                      |> THEN <| REWRITE_TAC []
                      DISCH_THEN SUBST1_TAC
                      |> THEN <| REWRITE_TAC []])

(* ------------------------------------------------------------------------- *)
(* Injection (num->Z)->Z, where Z == num->A->bool.                           *)
(* ------------------------------------------------------------------------- *)
let INJF = 
    new_definition
        (parse_term @"INJF (f:num->(num->A->bool)) = \n. f (NUMFST n) (NUMSND n)")

let INJF_INJ = 
    prove
        ((parse_term @"!f1 f2. (INJF f1 :num->A->bool = INJF f2) <=> (f1 = f2)"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| REWRITE_TAC [FUN_EQ_THM]
         |> THEN <| MAP_EVERY X_GEN_TAC [(parse_term @"n:num")
                                         (parse_term @"m:num")
                                         (parse_term @"a:A")]
         |> THEN <| POP_ASSUM(MP_TAC << REWRITE_RULE [INJF])
         |> THEN 
         <| DISCH_THEN
                (MP_TAC << C AP_THM (parse_term @"a:A") 
                 << C AP_THM (parse_term @"NUMPAIR n m"))
         |> THEN <| REWRITE_TAC [NUMPAIR_DEST])

(* ------------------------------------------------------------------------- *)
(* Injection Z->Z->Z, where Z == num->A->bool.                               *)
(* ------------------------------------------------------------------------- *)
let INJP = 
    new_definition
        (parse_term 
             "INJP f1 f2:num->A->bool = \n a. if NUMLEFT n then f1 (NUMRIGHT n) a else f2 (NUMRIGHT n) a")

let INJP_INJ = 
    prove((parse_term @"!(f1:num->A->bool) f1' f2 f2'.
        (INJP f1 f2 = INJP f1' f2') <=> (f1 = f1') /\ (f2 = f2')"),
       REPEAT GEN_TAC
       |> THEN <| EQ_TAC
       |> THEN <| DISCH_TAC
       |> THEN <| ASM_REWRITE_TAC []
       |> THEN <| ONCE_REWRITE_TAC [FUN_EQ_THM]
       |> THEN <| REWRITE_TAC [AND_FORALL_THM]
       |> THEN <| X_GEN_TAC(parse_term @"n:num")
       |> THEN <| POP_ASSUM(MP_TAC << REWRITE_RULE [INJP])
       |> THEN 
       <| DISCH_THEN
              (MP_TAC << GEN(parse_term @"b:bool") 
               << C AP_THM (parse_term @"NUMSUM b n"))
       |> THEN 
       <| DISCH_THEN(fun th -> MP_TAC(SPEC (parse_term @"T") th)
                               |> THEN <| MP_TAC(SPEC (parse_term @"F") th))
       |> THEN <| ASM_SIMP_TAC [NUMSUM_DEST; ETA_AX])

(* ------------------------------------------------------------------------- *)
(* Now, set up "constructor" and "bottom" element.                           *)
(* ------------------------------------------------------------------------- *)
let ZCONSTR = 
    new_definition
        (parse_term 
             "ZCONSTR c i r :num->A->bool = INJP (INJN (SUC c)) (INJP (INJA i) (INJF r))")

let ZBOT = 
    new_definition(parse_term @"ZBOT = INJP (INJN 0) (@z:num->A->bool. T)")
let ZCONSTR_ZBOT = 
    prove
        ((parse_term @"!c i r. ~(ZCONSTR c i r :num->A->bool = ZBOT)"), 
         REWRITE_TAC [ZCONSTR; ZBOT; INJP_INJ; INJN_INJ; NOT_SUC])

(* ------------------------------------------------------------------------- *)
(* Carve out an inductively defined set.                                     *)
(* ------------------------------------------------------------------------- *)
let ZRECSPACE_RULES, ZRECSPACE_INDUCT, ZRECSPACE_CASES = new_inductive_definition(parse_term @"ZRECSPACE (ZBOT:num->A->bool) /\
    (!c i r. (!n. ZRECSPACE (r n)) ==> ZRECSPACE (ZCONSTR c i r))")

let recspace_tydef = 
    new_basic_type_definition "recspace" ("_mk_rec", "_dest_rec") 
        (CONJUNCT1 ZRECSPACE_RULES)

(* ------------------------------------------------------------------------- *)
(* Define lifted constructors.                                               *)
(* ------------------------------------------------------------------------- *)
let BOTTOM = new_definition(parse_term @"BOTTOM = _mk_rec (ZBOT:num->A->bool)")

let CONSTR = 
    new_definition
        (parse_term 
             "CONSTR c i r :(A)recspace = _mk_rec (ZCONSTR c i (\n. _dest_rec(r n)))")

(* ------------------------------------------------------------------------- *)
(* Some lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)
let MK_REC_INJ = 
    prove((parse_term @"!x y. (_mk_rec x :(A)recspace = _mk_rec y)
         ==> (ZRECSPACE x /\ ZRECSPACE y ==> (x = y))"),
        REPEAT GEN_TAC
        |> THEN <| DISCH_TAC
        |> THEN <| REWRITE_TAC [snd recspace_tydef]
        |> THEN <| DISCH_THEN(fun th -> ONCE_REWRITE_TAC [GSYM th])
        |> THEN <| ASM_REWRITE_TAC [])

let DEST_REC_INJ = 
    prove
        ((parse_term @"!x y. (_dest_rec x = _dest_rec y) <=> (x:(A)recspace = y)"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN 
         <| POP_ASSUM
                (MP_TAC 
                 << AP_TERM(parse_term @"_mk_rec:(num->A->bool)->(A)recspace"))
         |> THEN <| REWRITE_TAC [fst recspace_tydef])

(* ------------------------------------------------------------------------- *)
(* Show that the set is freely inductively generated.                        *)
(* ------------------------------------------------------------------------- *)
let CONSTR_BOT = 
    prove
        ((parse_term @"!c i r. ~(CONSTR c i r :(A)recspace = BOTTOM)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [CONSTR; BOTTOM]
         |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP MK_REC_INJ)
         |> THEN <| REWRITE_TAC [ZCONSTR_ZBOT; ZRECSPACE_RULES]
         |> THEN <| MATCH_MP_TAC(CONJUNCT2 ZRECSPACE_RULES)
         |> THEN <| REWRITE_TAC [fst recspace_tydef
                                 snd recspace_tydef])

let CONSTR_INJ = 
    prove
        ((parse_term @"!c1 i1 r1 c2 i2 r2. (CONSTR c1 i1 r1 :(A)recspace = CONSTR c2 i2 r2) <=>
                       (c1 = c2) /\ (i1 = i2) /\ (r1 = r2)"),
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| POP_ASSUM(MP_TAC << REWRITE_RULE [CONSTR])
         |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP MK_REC_INJ)
         |> THEN <| W(C SUBGOAL_THEN ASSUME_TAC << funpow 2 lhand << snd)
         |> THENL <| [CONJ_TAC
                      |> THEN <| MATCH_MP_TAC(CONJUNCT2 ZRECSPACE_RULES)
                      |> THEN <| REWRITE_TAC [fst recspace_tydef
                                              snd recspace_tydef]
                      ASM_REWRITE_TAC []
                      |> THEN <| REWRITE_TAC [ZCONSTR]
                      |> THEN 
                      <| REWRITE_TAC [INJP_INJ; INJN_INJ; INJF_INJ; INJA_INJ]
                      |> THEN <| ONCE_REWRITE_TAC [FUN_EQ_THM]
                      |> THEN <| BETA_TAC
                      |> THEN <| REWRITE_TAC [SUC_INJ; DEST_REC_INJ]])

let CONSTR_IND = 
    prove((parse_term @"!P. P(BOTTOM) /\
       (!c i r. (!n. P(r n)) ==> P(CONSTR c i r))
       ==> !x:(A)recspace. P(x)"),
      REPEAT STRIP_TAC
      |> THEN 
      <| MP_TAC
             (SPEC (parse_term @"\z:num->A->bool. ZRECSPACE(z) /\ P(_mk_rec z)") 
                  ZRECSPACE_INDUCT)
      |> THEN <| BETA_TAC
      |> THEN <| ASM_REWRITE_TAC [ZRECSPACE_RULES
                                  GSYM BOTTOM]
      |> THEN <| W(C SUBGOAL_THEN ASSUME_TAC << funpow 2 lhand << snd)
      |> THENL <| [REPEAT GEN_TAC
                   |> THEN <| REWRITE_TAC [FORALL_AND_THM]
                   |> THEN <| REPEAT STRIP_TAC
                   |> THENL <| [MATCH_MP_TAC(CONJUNCT2 ZRECSPACE_RULES)
                                |> THEN <| ASM_REWRITE_TAC []
                                FIRST_ASSUM(ANTE_RES_THEN MP_TAC)
                                |> THEN <| REWRITE_TAC [CONSTR]
                                |> THEN 
                                <| RULE_ASSUM_TAC
                                       (REWRITE_RULE [snd recspace_tydef])
                                |> THEN <| ASM_SIMP_TAC [ETA_AX]]
                   ASM_REWRITE_TAC []
                   |> THEN 
                   <| DISCH_THEN
                          (MP_TAC 
                           << SPEC(parse_term @"_dest_rec (x:(A)recspace)"))
                   |> THEN <| REWRITE_TAC [fst recspace_tydef]
                   |> THEN 
                   <| REWRITE_TAC 
                          [ITAUT(parse_term @"(a ==> a /\ b) <=> (a ==> b)")]
                   |> THEN <| DISCH_THEN MATCH_MP_TAC
                   |> THEN <| REWRITE_TAC [fst recspace_tydef
                                           snd recspace_tydef]])

(* ------------------------------------------------------------------------- *)
(* Now prove the recursion theorem (this subcase is all we need).            *)
(* ------------------------------------------------------------------------- *)
let CONSTR_REC = 
  prove((parse_term @"!Fn:num->A->(num->(A)recspace)->(num->B)->B.
     ?f. (!c i r. f (CONSTR c i r) = Fn c i r (\n. f (r n)))"),
    REPEAT STRIP_TAC
    |> THEN <| (MP_TAC << prove_inductive_relations_exist)(parse_term @"(Z:(A)recspace->B->bool) BOTTOM b /\
     (!c i r y. (!n. Z (r n) (y n)) ==> Z (CONSTR c i r) (Fn c i r y))")
    |> THEN <| DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC))
    |> THEN <| DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC << GSYM))
    |> THEN 
    <| SUBGOAL_THEN (parse_term @"!x. ?!y. (Z:(A)recspace->B->bool) x y") MP_TAC
    |> THENL <| [W(MP_TAC << PART_MATCH rand CONSTR_IND << snd)
                 |> THEN <| DISCH_THEN MATCH_MP_TAC
                 |> THEN <| CONJ_TAC
                 |> THEN <| REPEAT GEN_TAC
                 |> THENL <| [FIRST_ASSUM
                                  (fun t -> GEN_REWRITE_TAC BINDER_CONV [GSYM t])
                              |> THEN <| REWRITE_TAC [GSYM CONSTR_BOT
                                                      EXISTS_UNIQUE_REFL]
                              DISCH_THEN
                                  (MP_TAC 
                                   << REWRITE_RULE 
                                          [EXISTS_UNIQUE_THM; FORALL_AND_THM])
                              |> THEN 
                              <| DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)
                              |> THEN 
                              <| DISCH_THEN(MP_TAC << REWRITE_RULE [SKOLEM_THM])
                              |> THEN 
                              <| DISCH_THEN
                                     (X_CHOOSE_THEN (parse_term @"y:num->B") 
                                          ASSUME_TAC)
                              |> THEN <| REWRITE_TAC [EXISTS_UNIQUE_THM]
                              |> THEN 
                              <| FIRST_ASSUM
                                     (fun th -> 
                                         CHANGED_TAC(ONCE_REWRITE_TAC [GSYM th]))
                              |> THEN <| CONJ_TAC
                              |> THENL <| [EXISTS_TAC
                                               (parse_term 
                                                    "(Fn:num->A->(num->(A)recspace)->(num->B)->B) c i r y")
                                           |> THEN 
                                           <| REWRITE_TAC [CONSTR_BOT
                                                           CONSTR_INJ
                                                           GSYM CONJ_ASSOC]
                                           |> THEN 
                                           <| REWRITE_TAC 
                                                  [UNWIND_THM1; 
                                                   RIGHT_EXISTS_AND_THM]
                                           |> THEN 
                                           <| EXISTS_TAC(parse_term @"y:num->B")
                                           |> THEN <| ASM_REWRITE_TAC []
                                           REWRITE_TAC [CONSTR_BOT
                                                        CONSTR_INJ
                                                        GSYM CONJ_ASSOC]
                                           |> THEN 
                                           <| REWRITE_TAC 
                                                  [UNWIND_THM1; 
                                                   RIGHT_EXISTS_AND_THM]
                                           |> THEN <| REPEAT STRIP_TAC
                                           |> THEN <| ASM_REWRITE_TAC []
                                           |> THEN <| REPEAT AP_TERM_TAC
                                           |> THEN 
                                           <| ONCE_REWRITE_TAC [FUN_EQ_THM]
                                           |> THEN 
                                           <| X_GEN_TAC(parse_term @"w:num")
                                           |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                                           |> THEN 
                                           <| EXISTS_TAC(parse_term @"w:num")
                                           |> THEN <| ASM_REWRITE_TAC []]]
                 REWRITE_TAC [UNIQUE_SKOLEM_ALT]
                 |> THEN 
                 <| DISCH_THEN
                        (X_CHOOSE_THEN (parse_term @"fn:(A)recspace->B") 
                             (ASSUME_TAC << GSYM))
                 |> THEN <| EXISTS_TAC(parse_term @"fn:(A)recspace->B")
                 |> THEN <| ASM_REWRITE_TAC []
                 |> THEN <| REPEAT GEN_TAC
                 |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                 |> THEN <| GEN_TAC
                 |> THEN <| FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th])
                 |> THEN <| REWRITE_TAC [BETA_THM]])

(* ------------------------------------------------------------------------- *)
(* The following is useful for coding up functions casewise.                 *)
(* ------------------------------------------------------------------------- *)
let FCONS = 
    new_recursive_definition num_RECURSION 
        (parse_term 
             "(!a f. FCONS (a:A) f 0 = a) /\ (!a f n. FCONS (a:A) f (SUC n) = f n)")

let FCONS_UNDO = 
    prove
        ((parse_term @"!f:num->A. f = FCONS (f 0) (f << SUC)"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [FUN_EQ_THM]
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [FCONS; o_THM])

let FNIL = new_definition(parse_term @"FNIL (n:num) = @x:A. T")

(* ------------------------------------------------------------------------- *)
(* The initial mutual type definition function, with a type-restricted       *)
(* recursion theorem.                                                        *)
(* ------------------------------------------------------------------------- *)
let define_type_raw_001 = 
    (* ----------------------------------------------------------------------- *)
    (* Handy utility to produce "SUC << SUC << SUC ..." form of numeral.         *)
    (* ----------------------------------------------------------------------- *)
    let sucivate = 
        let zero = (parse_term @"0")
        let suc = (parse_term @"SUC")
        fun n -> funpow n (curry mk_comb suc) zero
    (* ----------------------------------------------------------------------- *)
    (* Eliminate local "definitions" in hyps.                                  *)
    (* ----------------------------------------------------------------------- *)
    let SCRUB_EQUATION eq (th, insts) = 
        (*HA*)
        let eq' = itlist subst (map (fun t -> [t]) insts) eq
        let l, r = dest_eq eq'
        (MP (INST [r, l] (DISCH eq' th)) (REFL r), (r, l) :: insts)
    (* ----------------------------------------------------------------------- *)
    (* Proves existence of model (inductively); use pseudo-constructors.       *)
    (*                                                                         *)
    (* Returns suitable definitions of constructors in terms of CONSTR, and    *)
    (* the rule and induction theorems from the inductive relation package.    *)
    (* ----------------------------------------------------------------------- *)
    let justify_inductive_type_model = 
        let t_tm = (parse_term @"T")
        let n_tm = (parse_term @"n:num")
        let beps_tm = (parse_term @"@x:bool. T")
        let rec munion s1 s2 = 
            if s1 = []
            then s2
            else 
                let h1 = hd s1
                let s1' = tl s1
                try 
                    let _, s2' = remove (fun h2 -> h2 = h1) s2
                    h1 :: (munion s1' s2')
                with
                | Failure _ -> h1 :: (munion s1' s2)
        fun def -> 
            let newtys, rights = unzip def
            let tyargls = itlist ((@) << map snd) rights []
            let alltys = itlist (munion << C subtract newtys) tyargls []
            let epstms = map (fun ty -> mk_select(mk_var("v", ty), t_tm)) alltys
            let pty = 
                try 
                    end_itlist (fun ty1 ty2 -> mk_type("prod", [ty1; ty2])) 
                        alltys
                with
                | Failure _ -> bool_ty
            let recty = mk_type("recspace", [pty])
            let constr = mk_const("CONSTR", [pty, aty])
            let fcons = mk_const("FCONS", [recty, aty])
            let bot = mk_const("BOTTOM", [pty, aty])
            let bottail = mk_abs(n_tm, bot)
            let mk_constructor n (cname, cargs) = 
                let ttys = 
                    map (fun ty -> 
                            if mem ty newtys
                            then recty
                            else ty) cargs
                let args = make_args "a" [] ttys
                let rargs, iargs = partition (fun t -> type_of t = recty) args
                let rec mk_injector epstms alltys iargs = 
                    if alltys = []
                    then []
                    else 
                        let ty = hd alltys
                        try 
                            let a, iargs' = 
                                remove (fun t -> type_of t = ty) iargs
                            a :: (mk_injector (tl epstms) (tl alltys) iargs')
                        with
                        | Failure _ -> 
                            (hd epstms) 
                            :: (mk_injector (tl epstms) (tl alltys) iargs)
                let iarg = 
                    try 
                        end_itlist (curry mk_pair) 
                            (mk_injector epstms alltys iargs)
                    with
                    | Failure _ -> beps_tm
                let rarg = itlist (mk_binop fcons) rargs bottail
                let conty = itlist mk_fun_ty (map type_of args) recty
                let condef = 
                    list_mk_comb(constr, [sucivate n
                                          iarg; rarg])
                mk_eq(mk_var(cname, conty), list_mk_abs(args, condef))
            let rec mk_constructors n rights = 
                if rights = []
                then []
                else 
                    (mk_constructor n (hd rights)) 
                    :: (mk_constructors (n + 1) (tl rights))
            let condefs = mk_constructors 0 (itlist (@) rights [])
            let conths = map ASSUME condefs
            let predty = mk_fun_ty recty bool_ty
            let edefs = 
                itlist (fun (x, l) acc -> map (fun t -> x, t) l @ acc) def []
            let idefs = 
                map2 (fun (r, (_, atys)) def -> (r, atys), def) edefs condefs
            let mk_rule((r, a), condef) = 
                let left, right = dest_eq condef
                let args, bod = strip_abs right
                let lapp = list_mk_comb(left, args)
                let conds = 
                    itlist2 (fun arg argty sofar -> 
                            if mem argty newtys
                            then 
                                mk_comb(mk_var(dest_vartype argty, predty), arg) 
                                :: sofar
                            else sofar) args a []
                let conc = mk_comb(mk_var(dest_vartype r, predty), lapp)
                let rule = 
                    if conds = []
                    then conc
                    else mk_imp(list_mk_conj conds, conc)
                list_mk_forall(args, rule)
            let rules = list_mk_conj(map mk_rule idefs)
            let th0 = derive_nonschematic_inductive_relations rules
            let th1 = prove_monotonicity_hyps th0
            let th2a, th2bc = CONJ_PAIR th1
            let th2b = CONJUNCT1 th2bc
            conths, th2a, th2b
    (* ----------------------------------------------------------------------- *)
    (* Shows that the predicates defined by the rules are all nonempty.        *)
    (* (This could be done much more efficiently/cleverly, but it's OK.)       *)
    (* ----------------------------------------------------------------------- *)
    let prove_model_inhabitation rth = 
        let srules = map SPEC_ALL (CONJUNCTS rth)
        let imps, bases = partition (is_imp << concl) srules
        let concs = map concl bases @ map (rand << concl) imps
        let preds = setify(map (repeat rator) concs)
        let rec exhaust_inhabitations ths sofar = 
            let dunnit = setify(map (fst << strip_comb << concl) sofar)
            let useful = 
                filter 
                    (fun th -> not(mem (fst(strip_comb(rand(concl th)))) dunnit)) 
                    ths
            if useful = []
            then sofar
            else 
                let follow_horn thm = 
                    let preds = 
                        map (fst << strip_comb) (conjuncts(lhand(concl thm)))
                    let asms = 
                        map 
                            (fun p -> 
                                find (fun th -> fst(strip_comb(concl th)) = p) 
                                    sofar) preds
                    MATCH_MP thm (end_itlist CONJ asms)
                let newth = tryfind follow_horn useful
                exhaust_inhabitations ths (newth :: sofar)
        let ithms = exhaust_inhabitations imps bases
        let exths = 
            map (fun p -> find (fun th -> fst(strip_comb(concl th)) = p) ithms) 
                preds
        exths
    (* ----------------------------------------------------------------------- *)
    (* Makes a type definition for one of the defined subsets.                 *)
    (* ----------------------------------------------------------------------- *)
    let define_inductive_type cdefs exth = 
        let extm = concl exth
        let epred = fst(strip_comb extm)
        let ename = fst(dest_var epred)
        let th1 = ASSUME(find (fun eq -> lhand eq = epred) (hyp exth))
        let th2 = TRANS th1 (SUBS_CONV cdefs (rand(concl th1)))
        let th3 = EQ_MP (AP_THM th2 (rand extm)) exth
        let th4, _ = itlist SCRUB_EQUATION (hyp th3) (th3, [])
        let mkname = "_mk_" ^ ename
        let destname = "_dest_" ^ ename
        let bij1, bij2 = new_basic_type_definition ename (mkname, destname) th4
        let bij2a = AP_THM th2 (rand(rand(concl bij2)))
        let bij2b = TRANS bij2a bij2
        bij1, bij2b
    (* ----------------------------------------------------------------------- *)
    (* Defines a type constructor corresponding to current pseudo-constructor. *)
    (* ----------------------------------------------------------------------- *)
    let define_inductive_type_constructor defs consindex th = 
        let avs, bod = strip_forall(concl th)
        let asms, conc = 
            if is_imp bod
            then conjuncts(lhand bod), rand bod
            else [], bod
        let asmlist = map dest_comb asms
        let cpred, cterm = dest_comb conc
        let oldcon, oldargs = strip_comb cterm
        let modify_arg v = 
            try 
                let dest = snd(assoc (rev_assoc v asmlist) consindex)
                let ty' = hd(snd(dest_type(type_of dest)))
                let v' = mk_var(fst(dest_var v), ty')
                mk_comb(dest, v'), v'
            with
            | Failure _ -> v, v
        let newrights, newargs = unzip(map modify_arg oldargs)
        let retmk = fst(assoc cpred consindex)
        let defbod = mk_comb(retmk, list_mk_comb(oldcon, newrights))
        let defrt = list_mk_abs(newargs, defbod)
        let expth = find (fun th -> lhand(concl th) = oldcon) defs
        let rexpth = SUBS_CONV [expth] defrt
        let deflf = mk_var(fst(dest_var oldcon), type_of defrt)
        let defth = new_definition(mk_eq(deflf, rand(concl rexpth)))
        TRANS defth (SYM rexpth)
    (* ----------------------------------------------------------------------- *)
    (* Instantiate the induction theorem on the representatives to transfer    *)
    (* it to the new type(s). Uses "\x. rep-pred(x) /\ P(mk x)" for "P".       *)
    (* ----------------------------------------------------------------------- *)
    let instantiate_induction_theorem consindex ith = 
        let avs, bod = strip_forall(concl ith)
        let corlist = 
            map ((repeat rator ||>> repeat rator) << dest_imp << body << rand) 
                (conjuncts(rand bod))
        let consindex' = 
            map (fun v -> 
                    let w = rev_assoc v corlist
                    w, assoc w consindex) avs
        let recty = 
            (hd << snd << dest_type << type_of << fst << snd << hd) consindex
        let newtys = 
            map (hd << snd << dest_type << type_of << snd << snd) consindex'
        let ptypes = map (C mk_fun_ty bool_ty) newtys
        let preds = make_args "P" [] ptypes
        let args = make_args "x" [] (map (K recty) preds)
        let lambs = 
            map2 
                (fun (r, (m, d)) (p, a) ->
                        mk_abs
                            (a, 
                             mk_conj(mk_comb(r, a), mk_comb(p, mk_comb(m, a))))) 
                consindex' (zip preds args)
        SPECL lambs ith
    (* ----------------------------------------------------------------------- *)
    (* Reduce a single clause of the postulated induction theorem (old_ver) ba *)
    (* to the kind wanted for the new type (new_ver); |- new_ver ==> old_ver   *)
    (* ----------------------------------------------------------------------- *)
    let pullback_induction_clause tybijpairs conthms = 
        let PRERULE = GEN_REWRITE_RULE (funpow 3 RAND_CONV) (map SYM conthms)
        let IPRULE = SYM << GEN_REWRITE_RULE I (map snd tybijpairs)
        fun rthm tm -> 
            let avs, bimp = strip_forall tm
            if is_imp bimp
            then 
                let ant, con = dest_imp bimp
                let ths = map (CONV_RULE BETA_CONV) (CONJUNCTS(ASSUME ant))
                let tths, pths = unzip(map CONJ_PAIR ths)
                let tth = MATCH_MP (SPEC_ALL rthm) (end_itlist CONJ tths)
                let mths = map IPRULE (tth :: tths)
                let conth1 = BETA_CONV con
                let contm1 = rand(concl conth1)
                let conth2 = 
                    TRANS conth1 
                        (AP_TERM (rator contm1) 
                             (SUBS_CONV (tl mths) (rand contm1)))
                let conth3 = PRERULE conth2
                let lctms = map concl pths
                let asmin = mk_imp(list_mk_conj lctms, rand(rand(concl conth3)))
                let argsin = map rand (conjuncts(lhand asmin))
                let argsgen = 
                    map (fun tm -> mk_var(fst(dest_var(rand tm)), type_of tm)) 
                        argsin
                let asmgen = subst (zip argsgen argsin) asmin
                let asmquant = 
                    list_mk_forall(snd(strip_comb(rand(rand asmgen))), asmgen)
                let th1 = INST (zip argsin argsgen) (SPEC_ALL(ASSUME asmquant))
                let th2 = MP th1 (end_itlist CONJ pths)
                let th3 = EQ_MP (SYM conth3) (CONJ tth th2)
                DISCH asmquant (GENL avs (DISCH ant th3))
            else 
                let con = bimp
                let conth2 = BETA_CONV con
                let tth = PART_MATCH I rthm (lhand(rand(concl conth2)))
                let conth3 = PRERULE conth2
                let asmgen = rand(rand(concl conth3))
                let asmquant = 
                    list_mk_forall(snd(strip_comb(rand asmgen)), asmgen)
                let th2 = SPEC_ALL(ASSUME asmquant)
                let th3 = EQ_MP (SYM conth3) (CONJ tth th2)
                DISCH asmquant (GENL avs th3)
    (* ----------------------------------------------------------------------- *)
    (* Finish off a consequence of the induction theorem.                      *)
    (* ----------------------------------------------------------------------- *)
    let finish_induction_conclusion consindex tybijpairs = 
        let tybij1, tybij2 = unzip tybijpairs
        let PRERULE = 
            GEN_REWRITE_RULE (LAND_CONV << LAND_CONV << RAND_CONV) tybij1 
            << GEN_REWRITE_RULE LAND_CONV tybij2
        let FINRULE = GEN_REWRITE_RULE RAND_CONV tybij1
        fun th -> 
            let av, bimp = dest_forall(concl th)
            let pv = lhand(body(rator(rand bimp)))
            let p, v = dest_comb pv
            let mk, dest = assoc p consindex
            let ty = hd(snd(dest_type(type_of dest)))
            let v' = mk_var(fst(dest_var v), ty)
            let dv = mk_comb(dest, v')
            let th1 = PRERULE(SPEC dv th)
            let th2 = MP th1 (REFL(rand(lhand(concl th1))))
            let th3 = CONV_RULE BETA_CONV th2
            GEN v' (FINRULE(CONJUNCT2 th3))
    (* ----------------------------------------------------------------------- *)
    (* Derive the induction theorem.                                           *)
    (* ----------------------------------------------------------------------- *)
    let derive_induction_theorem consindex tybijpairs conthms iith rth = 
        let bths = 
            map2 (pullback_induction_clause tybijpairs conthms) (CONJUNCTS rth) 
                (conjuncts(lhand(concl iith)))
        let asm = list_mk_conj(map (lhand << concl) bths)
        let ths = map2 MP bths (CONJUNCTS(ASSUME asm))
        let th1 = MP iith (end_itlist CONJ ths)
        let th2 = 
            end_itlist CONJ 
                (map (finish_induction_conclusion consindex tybijpairs) 
                     (CONJUNCTS th1))
        let th3 = DISCH asm th2
        let preds = map (rator << body << rand) (conjuncts(rand(concl th3)))
        let th4 = GENL preds th3
        let pasms = filter (C mem (map fst consindex) << lhand) (hyp th4)
        let th5 = itlist DISCH pasms th4
        let th6, _ = itlist SCRUB_EQUATION (hyp th5) (th5, [])
        let th7 = UNDISCH_ALL th6
        fst(itlist SCRUB_EQUATION (hyp th7) (th7, []))
    (* ----------------------------------------------------------------------- *)
    (* Create the recursive functions and eliminate pseudo-constructors.       *)
    (* (These are kept just long enough to derive the key property.)           *)
    (* ----------------------------------------------------------------------- *)
    let create_recursive_functions tybijpairs consindex conthms rth = 
        let domtys = 
            map (hd << snd << dest_type << type_of << snd << snd) consindex
        let recty = 
            (hd << snd << dest_type << type_of << fst << snd << hd) consindex
        let ranty = mk_vartype "Z"
        let fn = mk_var("fn", mk_fun_ty recty ranty)
        let fns = make_args "fn" [] (map (C mk_fun_ty ranty) domtys)
        let args = make_args "a" [] domtys
        let rights = 
            map2 (fun (_, (_, d)) a -> mk_abs(a, mk_comb(fn, mk_comb(d, a)))) consindex 
                args
        let eqs = map2 (curry mk_eq) fns rights
        let fdefs = map ASSUME eqs
        let fxths1 = 
            map (fun th1 -> tryfind (fun th2 -> MK_COMB(th2, th1)) fdefs) 
                conthms
        let fxths2 = map (fun th -> TRANS th (BETA_CONV(rand(concl th)))) fxths1
        let mk_tybijcons(th1, th2) = 
            let th3 = INST [rand(lhand(concl th1)), rand(lhand(concl th2))] th2
            let th4 = AP_TERM (rator(lhand(rand(concl th2)))) th1
            EQ_MP (SYM th3) th4
        let SCONV = GEN_REWRITE_CONV I (map mk_tybijcons tybijpairs)
        let ERULE = GEN_REWRITE_RULE I (map snd tybijpairs)
        let simplify_fxthm rthm fxth = 
            let pat = funpow 4 rand (concl fxth)
            if is_imp(repeat (snd << dest_forall) (concl rthm))
            then 
                let th1 = PART_MATCH (rand << rand) rthm pat
                let tms1 = conjuncts(lhand(concl th1))
                let ths2 = map (fun t -> EQ_MP (SYM(SCONV t)) TRUTH) tms1
                ERULE(MP th1 (end_itlist CONJ ths2))
            else ERULE(PART_MATCH rand rthm pat)
        let fxths3 = map2 simplify_fxthm (CONJUNCTS rth) fxths2
        let fxths4 = map2 (fun th1 -> TRANS th1 << AP_TERM fn) fxths2 fxths3
        let cleanup_fxthm cth fxth = 
            let tms = snd(strip_comb(rand(rand(concl fxth))))
            let kth = RIGHT_BETAS tms (ASSUME(hd(hyp cth)))
            TRANS fxth (AP_TERM fn kth)
        let fxth5 = end_itlist CONJ (map2 cleanup_fxthm conthms fxths4)
        let pasms = filter (C mem (map fst consindex) << lhand) (hyp fxth5)
        let fxth6 = itlist DISCH pasms fxth5
        let fxth7, _ = 
            itlist SCRUB_EQUATION (itlist (union << hyp) conthms []) (fxth6, [])
        let fxth8 = UNDISCH_ALL fxth7
        fst(itlist SCRUB_EQUATION (subtract (hyp fxth8) eqs) (fxth8, []))
    (* ----------------------------------------------------------------------- *)
    (* Create a function for recursion clause.                                 *)
    (* ----------------------------------------------------------------------- *)
    let create_recursion_iso_constructor = 
        let s = (parse_term @"s:num->Z")
        let zty = (parse_type @"Z")
        let numty = (parse_type @"num")
        let rec extract_arg tup v = 
            if v = tup
            then REFL tup
            else 
                let t1, t2 = dest_pair tup
                let PAIR_th = 
                    ISPECL [t1; t2] (if free_in v t1
                                     then FST
                                     else SND)
                let tup' = rand(concl PAIR_th)
                if tup' = v
                then PAIR_th
                else 
                    let th = extract_arg (rand(concl PAIR_th)) v
                    SUBS [SYM PAIR_th] th
        fun consindex -> 
            let recty = hd(snd(dest_type(type_of(fst(hd consindex)))))
            let domty = hd(snd(dest_type recty))
            let i = mk_var("i", domty)
            let r = mk_var("r", mk_fun_ty numty recty)
            let mks = map (fst << snd) consindex
            let mkindex = 
                map (fun t -> hd(tl(snd(dest_type(type_of t)))), t) mks
            fun cth -> 
                let artms = snd(strip_comb(rand(rand(concl cth))))
                let artys = mapfilter (type_of << rand) artms
                let args, bod = strip_abs(rand(hd(hyp cth)))
                let ccitm, rtm = dest_comb bod
                let cctm, itm = dest_comb ccitm
                let rargs, iargs = partition (C free_in rtm) args
                let xths = map (extract_arg itm) iargs
                let cargs' = map (subst [i, itm] << lhand << concl) xths
                let indices = map sucivate (0 -- (length rargs - 1))
                let rindexed = map (curry mk_comb r) indices
                let rargs' = 
                    map2 (fun a rx -> mk_comb(assoc a mkindex, rx)) artys 
                        rindexed
                let sargs' = map (curry mk_comb s) indices
                let allargs = cargs' @ rargs' @ sargs'
                let funty = itlist (mk_fun_ty << type_of) allargs zty
                let funname = 
                    fst(dest_const(repeat rator (lhand(concl cth)))) ^ "'"
                let funarg = mk_var(funname, funty)
                list_mk_abs([i; r; s], list_mk_comb(funarg, allargs))
    (* ----------------------------------------------------------------------- *)
    (* Derive the recursion theorem.                                           *)
    (* ----------------------------------------------------------------------- *)
    let derive_recursion_theorem = 
        let CCONV = funpow 3 RATOR_CONV (REPEATC(GEN_REWRITE_CONV I [FCONS]))
        fun tybijpairs consindex conthms rath -> 
            let isocons = 
                map (create_recursion_iso_constructor consindex) conthms
            let ty = type_of(hd isocons)
            let fcons = mk_const("FCONS", [ty, aty])
            let fnil = mk_const("FNIL", [ty, aty])
            let bigfun = itlist (mk_binop fcons) isocons fnil
            let eth = ISPEC bigfun CONSTR_REC
            let fn = rator(rand(hd(conjuncts(concl rath))))
            let betm = 
                let v, bod = dest_abs(rand(concl eth))
                vsubst [fn, v] bod
            let LCONV = REWR_CONV(ASSUME betm)
            let fnths = 
                map (fun t -> RIGHT_BETAS [bndvar(rand t)] (ASSUME t)) 
                    (hyp rath)
            let SIMPER = 
                PURE_REWRITE_RULE
                    (map SYM fnths 
                     @ map fst tybijpairs @ [FST; SND; FCONS; BETA_THM])
            let hackdown_rath th = 
                let ltm, rtm = dest_eq(concl th)
                let wargs = snd(strip_comb(rand ltm))
                let th1 = TRANS th (LCONV rtm)
                let th2 = TRANS th1 (CCONV(rand(concl th1)))
                let th3 = 
                    TRANS th2 (funpow 2 RATOR_CONV BETA_CONV (rand(concl th2)))
                let th4 = TRANS th3 (RATOR_CONV BETA_CONV (rand(concl th3)))
                let th5 = TRANS th4 (BETA_CONV(rand(concl th4)))
                GENL wargs (SIMPER th5)
            let rthm = end_itlist CONJ (map hackdown_rath (CONJUNCTS rath))
            let seqs = 
                let unseqs = filter is_eq (hyp rthm)
                let tys = 
                    map (hd << snd << dest_type << type_of << snd << snd) 
                        consindex
                map 
                    (fun ty -> 
                        find 
                            (fun t -> hd(snd(dest_type(type_of(lhand t)))) = ty) 
                            unseqs) tys
            let rethm = itlist EXISTS_EQUATION seqs rthm
            let fethm = CHOOSE (fn, eth) rethm
            let pcons = 
                map (repeat rator << rand << repeat(snd << dest_forall)) 
                    (conjuncts(concl rthm))
            GENL pcons fethm
    fun def -> 
        (* ----------------------------------------------------------------------- *)
        (* Basic function: returns induction and recursion separately. No parser.  *)
        (* ----------------------------------------------------------------------- *)
        let defs, rth, ith = justify_inductive_type_model def
        let neths = prove_model_inhabitation rth
        let tybijpairs = map (define_inductive_type defs) neths
        let preds = map (repeat rator << concl) neths
        let mkdests = 
            map (fun (th, _) -> 
                    let tm = lhand(concl th)
                    rator tm, rator(rand tm)) tybijpairs
        let consindex = zip preds mkdests
        let condefs = 
            map (define_inductive_type_constructor defs consindex) 
                (CONJUNCTS rth)
        let conthms = 
            map (fun th -> 
                    let args = fst(strip_abs(rand(concl th)))
                    RIGHT_BETAS args th) condefs
        let iith = instantiate_induction_theorem consindex ith
        let fth = derive_induction_theorem consindex tybijpairs conthms iith rth
        let rath = create_recursive_functions tybijpairs consindex conthms rth
        let kth = derive_recursion_theorem tybijpairs consindex conthms rath
        fth, kth

(* ------------------------------------------------------------------------- *)
(* Parser to present a nice interface a la Melham.                           *)
(* ------------------------------------------------------------------------- *)
let parse_inductive_type_specification = 
    let parse_type_loc src = 
        let pty, rst = parse_pretype src
        type_of_pretype pty, rst
    let parse_type_conapp src = 
        let cn, sps = 
            match src with
            | (Ident cn) :: sps -> cn, sps
            | _ -> fail()
        let tys, rst = many parse_type_loc sps
        (cn, tys), rst
    let parse_type_clause src = 
        let tn, sps = 
            match src with
            | (Ident tn) :: sps -> tn, sps
            | _ -> fail()
        let tys, rst = 
            (a(Ident "=") 
             .>>. listof parse_type_conapp (a(Resword "|")) 
                      "type definition clauses" |>> snd) sps
        (mk_vartype tn, tys), rst
    let parse_type_definition = 
        listof parse_type_clause (a(Resword ";")) "type definition"
    fun s -> 
        let spec, rst = (parse_type_definition << lex << explode) s
        if rst = []
        then spec
        else failwith "parse_inductive_type_specification: junk after def"

(* ------------------------------------------------------------------------- *)
(* Use this temporary version to define the sum type.                        *)
(* ------------------------------------------------------------------------- *)
let sum_INDUCT, sum_RECURSION = 
    define_type_raw_001
        (parse_inductive_type_specification "sum = INL A | INR B")

let OUTL = 
    new_recursive_definition sum_RECURSION (parse_term @"OUTL (INL x :A+B) = x")
let OUTR = 
    new_recursive_definition sum_RECURSION (parse_term @"OUTR (INR y :A+B) = y")

(* ------------------------------------------------------------------------- *)
(* Generalize the recursion theorem to multiple domain types.                *)
(* (We needed to use a single type to justify it via a proforma theorem.)    *)
(*                                                                           *)
(* NB! Before this is called nontrivially (i.e. more than one new type)      *)
(*     the type constructor ":sum", used internally, must have been defined. *)
(* ------------------------------------------------------------------------- *)
let rec define_type_raw_002 = 
    let generalize_recursion_theorem = 
        let ELIM_OUTCOMBS = GEN_REWRITE_RULE TOP_DEPTH_CONV [OUTL; OUTR]
        let rec mk_sum tys = 
            let k = length tys
            if k = 1
            then hd tys
            else 
                let tys1, tys2 = chop_list (k / 2) tys
                mk_type("sum", [mk_sum tys1
                                mk_sum tys2])
        let mk_inls = 
            let rec mk_inls ty = 
                if is_vartype ty
                then [mk_var("x", ty)]
                else 
                    let _, [ty1; ty2] = dest_type ty
                    let inls1 = mk_inls ty1
                    let inls2 = mk_inls ty2
                    let inl = 
                        mk_const("INL", [ty1, aty
                                         ty2, bty])
                    let inr = 
                        mk_const("INR", [ty1, aty
                                         ty2, bty])
                    map (curry mk_comb inl) inls1 
                    @ map (curry mk_comb inr) inls2
            fun ty -> 
                let bods = mk_inls ty
                map (fun t -> mk_abs(find_term is_var t, t)) bods
        let mk_outls = 
            let rec mk_inls sof ty = 
                if is_vartype ty
                then [sof]
                else 
                    let _, [ty1; ty2] = dest_type ty
                    let outl = 
                        mk_const("OUTL", [ty1, aty
                                          ty2, bty])
                    let outr = 
                        mk_const("OUTR", [ty1, aty
                                          ty2, bty])
                    mk_inls (mk_comb(outl, sof)) ty1 
                    @ mk_inls (mk_comb(outr, sof)) ty2
            fun ty -> 
                let x = mk_var("x", ty)
                map (curry mk_abs x) (mk_inls x ty)
        let mk_newfun fn outl = 
            let s, ty = dest_var fn
            let dty = hd(snd(dest_type ty))
            let x = mk_var("x", dty)
            let y, bod = dest_abs outl
            let r = mk_abs(x, vsubst [mk_comb(fn, x), y] bod)
            let l = mk_var(s, type_of r)
            let th1 = ASSUME(mk_eq(l, r))
            RIGHT_BETAS [x] th1
        fun th -> 
            let avs, ebod = strip_forall(concl th)
            let evs, bod = strip_exists ebod
            let n = length evs
            if n = 1
            then th
            else 
                let tys = 
                    map (fun i -> mk_vartype("Z" ^ (string_of_int i))) 
                        (0 -- (n - 1))
                let sty = mk_sum tys
                let inls = mk_inls sty
                let outls = mk_outls sty
                let zty = type_of(rand(snd(strip_forall(hd(conjuncts bod)))))
                let ith = INST_TYPE [sty, zty] th
                let avs, ebod = strip_forall(concl ith)
                let evs, bod = strip_exists ebod
                let fns' = map2 mk_newfun evs outls
                let fnalist = zip evs (map (rator << lhs << concl) fns')
                let inlalist = zip evs inls
                let outlalist = zip evs outls
                let hack_clause tm = 
                    let avs, bod = strip_forall tm
                    let l, r = dest_eq bod
                    let fn, args = strip_comb r
                    let pargs = 
                        map (fun a -> 
                                let g = genvar(type_of a)
                                if is_var a
                                then g, g
                                else 
                                    let outl = assoc (rator a) outlalist
                                    mk_comb(outl, g), g) args
                    let args', args'' = unzip pargs
                    let inl = assoc (rator l) inlalist
                    let rty = hd(snd(dest_type(type_of inl)))
                    let nty = itlist (mk_fun_ty << type_of) args' rty
                    let fn' = mk_var(fst(dest_var fn), nty)
                    let r' = 
                        list_mk_abs
                            (args'', mk_comb(inl, list_mk_comb(fn', args')))
                    r', fn
                let defs = map hack_clause (conjuncts bod)
                let jth = BETA_RULE(SPECL (map fst defs) ith)
                let bth = ASSUME(snd(strip_exists(concl jth)))
                let finish_clause th = 
                    let avs, bod = strip_forall(concl th)
                    let outl = assoc (rator(lhand bod)) outlalist
                    GENL avs (BETA_RULE(AP_TERM outl (SPECL avs th)))
                let cth = end_itlist CONJ (map finish_clause (CONJUNCTS bth))
                let dth = ELIM_OUTCOMBS cth
                let eth = GEN_REWRITE_RULE ONCE_DEPTH_CONV (map SYM fns') dth
                let fth = itlist SIMPLE_EXISTS (map snd fnalist) eth
                let dtms = map (hd << hyp) fns'
                let gth = 
                    itlist (fun e th -> 
                            let l, r = dest_eq e
                            MP (INST [r, l] (DISCH e th)) (REFL r)) dtms fth
                let hth = PROVE_HYP jth (itlist SIMPLE_CHOOSE evs gth)
                let xvs = 
                    map (fst << strip_comb << rand << snd << strip_forall) 
                        (conjuncts(concl eth))
                GENL xvs hth
    fun def -> 
        let ith, rth = define_type_raw_002 def
        ith, generalize_recursion_theorem rth

(* ------------------------------------------------------------------------- *)
(* Set up options and lists.                                                 *)
(* ------------------------------------------------------------------------- *)
let option_INDUCT, option_RECURSION = 
    define_type_raw_002
        (parse_inductive_type_specification "option = NONE | SOME A")

let list_INDUCT, list_RECURSION = 
    define_type_raw_002
        (parse_inductive_type_specification "list = NIL | CONS A list")

(* ------------------------------------------------------------------------- *)
(* Tools for proving injectivity and distinctness of constructors.           *)
(* ------------------------------------------------------------------------- *)
let prove_constructors_injective = 
    let DEPAIR = GEN_REWRITE_RULE TOP_SWEEP_CONV [PAIR_EQ]
    let prove_distinctness ax pat = 
        let f, args = strip_comb pat
        let rt = end_itlist (curry mk_pair) args
        let ty = mk_fun_ty (type_of pat) (type_of rt)
        let fn = genvar ty
        let dtm = mk_eq(mk_comb(fn, pat), rt)
        let eth = prove_recursive_functions_exist ax (list_mk_forall(args, dtm))
        let args' = variants args args
        let atm = mk_eq(pat, list_mk_comb(f, args'))
        let ath = ASSUME atm
        let bth = AP_TERM fn ath
        let cth1 = SPECL args (ASSUME(snd(dest_exists(concl eth))))
        let cth2 = INST (zip args' args) cth1
        let pth = TRANS (TRANS (SYM cth1) bth) cth2
        let qth = DEPAIR pth
        let qtm = concl qth
        let rth = rev_itlist (C(curry MK_COMB)) (CONJUNCTS(ASSUME qtm)) (REFL f)
        let tth = IMP_ANTISYM_RULE (DISCH atm qth) (DISCH qtm rth)
        let uth = GENL args (GENL args' tth)
        PROVE_HYP eth (SIMPLE_CHOOSE fn uth)
    fun ax -> 
        let cls = conjuncts(snd(strip_exists(snd(strip_forall(concl ax)))))
        let pats = map (rand << lhand << snd << strip_forall) cls
        end_itlist CONJ (mapfilter (prove_distinctness ax) pats)

let prove_constructors_distinct = 
    let num_ty = (parse_type @"num")
    let rec allopairs f l m = 
        if l = []
        then []
        else map (f(hd l)) (tl m) @ allopairs f (tl l) (tl m)
    let NEGATE = 
        GEN_ALL << CONV_RULE(REWR_CONV(TAUT(parse_term @"a ==> F <=> ~a")))
    let prove_distinct ax pat = 
        let nums = map mk_small_numeral (0 -- (length pat - 1))
        let fn = 
            genvar(mk_type("fun", [type_of(hd pat)
                                   num_ty]))
        let ls = map (curry mk_comb fn) pat
        let defs = 
            map2 (fun l r -> list_mk_forall(frees(rand l), mk_eq(l, r))) ls nums
        let eth = prove_recursive_functions_exist ax (list_mk_conj defs)
        let ev, bod = dest_exists(concl eth)
        let REWRITE = GEN_REWRITE_RULE ONCE_DEPTH_CONV (CONJUNCTS(ASSUME bod))
        let pat' = 
            map (fun t -> 
                    let f, args = 
                        if is_numeral t
                        then t, []
                        else strip_comb t
                    list_mk_comb(f, variants args args)) pat
        let pairs = allopairs (curry mk_eq) pat pat'
        let nths = map (REWRITE << AP_TERM fn << ASSUME) pairs
        let fths = 
            map2 (fun t th -> NEGATE(DISCH t (CONV_RULE NUM_EQ_CONV th))) pairs 
                nths
        CONJUNCTS(PROVE_HYP eth (SIMPLE_CHOOSE ev (end_itlist CONJ fths)))
    fun ax -> 
        let cls = conjuncts(snd(strip_exists(snd(strip_forall(concl ax)))))
        let lefts = map (dest_comb << lhand << snd << strip_forall) cls
        let fns = itlist (insert << fst) lefts []
        let pats = map (fun f -> map snd (filter ((=) f << fst) lefts)) fns
        end_itlist CONJ (end_itlist (@) (mapfilter (prove_distinct ax) pats))

(* ------------------------------------------------------------------------- *)
(* Automatically prove the case analysis theorems.                           *)
(* ------------------------------------------------------------------------- *)
let prove_cases_thm = 
    let mk_exclauses x rpats = 
        let xts = map (fun t -> list_mk_exists(frees t, mk_eq(x, t))) rpats
        mk_abs(x, list_mk_disj xts)
    let prove_triv tm = 
        let evs, bod = strip_exists tm
        let l, r = dest_eq bod
        if l = r
        then REFL l
        else 
            let lf, largs = strip_comb l
            let rf, rargs = strip_comb r
            if lf = rf
            then 
                let ths = map (ASSUME << mk_eq) (zip rargs largs)
                let th1 = rev_itlist (C(curry MK_COMB)) ths (REFL lf)
                itlist EXISTS_EQUATION (map concl ths) (SYM th1)
            else failwith "prove_triv"
    let rec prove_disj tm = 
        if is_disj tm
        then 
            let l, r = dest_disj tm
            try 
                DISJ1 (prove_triv l) r
            with
            | Failure _ -> DISJ2 l (prove_disj r)
        else prove_triv tm
    let prove_eclause tm = 
        let avs, bod = strip_forall tm
        let ctm = 
            if is_imp bod
            then rand bod
            else bod
        let cth = prove_disj ctm
        let dth = 
            if is_imp bod
            then DISCH (lhand bod) cth
            else cth
        GENL avs dth
    fun th -> 
        let avs, bod = strip_forall(concl th)
        let cls = map (snd << strip_forall) (conjuncts(lhand bod))
        let pats = 
            map (fun t -> 
                    if is_imp t
                    then rand t
                    else t) cls
        let spats = map dest_comb pats
        let preds = itlist (insert << fst) spats []
        let rpatlist = 
            map (fun pr -> map snd (filter (fun (p, x) -> p = pr) spats)) preds
        let xs = make_args "x" (freesl pats) (map (type_of << hd) rpatlist)
        let xpreds = map2 mk_exclauses xs rpatlist
        let ith = BETA_RULE(INST (zip xpreds preds) (SPEC_ALL th))
        let eclauses = conjuncts(fst(dest_imp(concl ith)))
        MP ith (end_itlist CONJ (map prove_eclause eclauses))

inductive_type_store 
:= ["list", (2, list_INDUCT, list_RECURSION)
    "option", (2, option_INDUCT, option_RECURSION)
    "sum", (2, sum_INDUCT, sum_RECURSION)] @ (!inductive_type_store)

(* ------------------------------------------------------------------------- *)
(* Now deal with nested recursion. Need a store of previous theorems.        *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Also add a cached rewrite of distinctness and injectivity theorems. Since *)
(* there can be quadratically many distinctness clauses, it would really be  *)
(* preferable to have a conversion, but this seems OK up 100 constructors.   *)
(* ------------------------------------------------------------------------- *)
let basic_rectype_net = ref empty_net

let distinctness_store = ref ["bool", TAUT(parse_term @"(T <=> F) <=> F")]
let injectivity_store = ref []

let extend_rectype_net(tyname, (_, _, rth)) = 
    let ths1 = 
        try 
            [prove_constructors_distinct rth]
        with
        | Failure _ -> []
    let ths2 = 
        try 
            [prove_constructors_injective rth]
        with
        | Failure _ -> []
    let canon_thl = itlist (mk_rewrites false) (ths1 @ ths2) []
    distinctness_store 
    := map (fun th -> tyname, th) ths1 @ (!distinctness_store)
    injectivity_store := map (fun th -> tyname, th) ths2 @ (!injectivity_store)
    basic_rectype_net := itlist (net_of_thm true) canon_thl (!basic_rectype_net)

do_list extend_rectype_net (!inductive_type_store)

(* ------------------------------------------------------------------------- *)
(* Return distinctness and injectivity for a type by simple lookup.          *)
(* ------------------------------------------------------------------------- *)
let distinctness ty = assoc ty (!distinctness_store)

let injectivity ty = assoc ty (!injectivity_store)

let cases ty = 
    if ty = "num"
    then num_CASES
    else 
        let _, ith, _ = assoc ty (!inductive_type_store)
        prove_cases_thm ith

(* ------------------------------------------------------------------------- *)
(* Convenient definitions for type isomorphism.                              *)
(* ------------------------------------------------------------------------- *)
let ISO = 
    new_definition
        (parse_term 
             "ISO (f:A->B) (g:B->A) <=> (!x. f(g x) = x) /\ (!y. g(f y) = y)")

let ISO_REFL = prove((parse_term @"ISO (\x:A. x) (\x. x)"), REWRITE_TAC [ISO])
let ISO_FUN = 
    prove
        ((parse_term @"ISO (f:A->A') f' /\ ISO (g:B->B') g'
     ==> ISO (\h a'. g(h(f' a'))) (\h a. g'(h(f a)))"),
     REWRITE_TAC 
                                                             [ISO; FUN_EQ_THM]
                                                         |> THEN <| MESON_TAC [])
let ISO_USAGE = prove((parse_term @"ISO f g
   ==> (!P. (!x. P x) <=> (!x. P(g x))) /\
       (!P. (?x. P x) <=> (?x. P(g x))) /\
       (!a b. (a = g b) <=> (f a = b))"), REWRITE_TAC [ISO; FUN_EQ_THM]
                                          |> THEN <| MESON_TAC [])

(* ------------------------------------------------------------------------- *)
(* Hence extend type definition to nested types.                             *)
(* ------------------------------------------------------------------------- *)
let rec define_type_raw = 
    (* ----------------------------------------------------------------------- *)
    (* Dispose of trivial antecedent.                                          *)
    (* ----------------------------------------------------------------------- *)
    let TRIV_ANTE_RULE = 
        let TRIV_IMP_CONV tm = 
            let avs, bod = strip_forall tm
            let bth = 
                if is_eq bod
                then REFL(rand bod)
                else 
                    let ant, con = dest_imp bod
                    let ith = SUBS_CONV (CONJUNCTS(ASSUME ant)) (lhs con)
                    DISCH ant ith
            GENL avs bth
        fun th -> 
            let tm = concl th
            if is_imp tm
            then 
                let ant, con = dest_imp(concl th)
                let cjs = conjuncts ant
                let cths = map TRIV_IMP_CONV cjs
                MP th (end_itlist CONJ cths)
            else th
    (* ----------------------------------------------------------------------- *)
    (* Lift type bijections to "arbitrary" (well, free rec or function) type.  *)
    (* ----------------------------------------------------------------------- *)
    let ISO_EXPAND_CONV = PURE_ONCE_REWRITE_CONV [ISO]
    let rec lift_type_bijections iths cty = 
        let itys = 
            map (hd << snd << dest_type << type_of << lhand << concl) iths
        try 
            assoc cty (zip itys iths)
        with
        | Failure _ -> 
            if not(exists (C occurs_in cty) itys)
            then INST_TYPE [cty, aty] ISO_REFL
            else 
                let tycon, isotys = dest_type cty
                if tycon = "fun"
                then 
                    MATCH_MP ISO_FUN 
                        (end_itlist CONJ 
                             (map (lift_type_bijections iths) isotys))
                else 
                    failwith
                        ("lift_type_bijections: Unexpected type operator \"" 
                         ^ tycon ^ "\"")
    (* ----------------------------------------------------------------------- *)
    (* Prove isomorphism of nested types where former is the smaller.          *)
    (* ----------------------------------------------------------------------- *)
    let DE_EXISTENTIALIZE_RULE = 
        let pth = 
            prove
                ((parse_term @"(?) P ==> (c = (@)P) ==> P c"), 
                 GEN_REWRITE_TAC (LAND_CONV << RAND_CONV) [GSYM ETA_AX]
                 |> THEN <| DISCH_TAC
                 |> THEN <| DISCH_THEN SUBST1_TAC
                 |> THEN <| MATCH_MP_TAC SELECT_AX
                 |> THEN <| POP_ASSUM ACCEPT_TAC)
        let USE_PTH = MATCH_MP pth
        let rec DE_EXISTENTIALIZE_RULE th = 
            if not(is_exists(concl th))
            then [], th
            else 
                let th1 = USE_PTH th
                let v1 = rand(rand(concl th1))
                let gv = genvar(type_of v1)
                let th2 = CONV_RULE BETA_CONV (UNDISCH(INST [gv, v1] th1))
                let vs, th3 = DE_EXISTENTIALIZE_RULE th2
                gv :: vs, th3
        DE_EXISTENTIALIZE_RULE
    let grab_type = type_of << rand << lhand << snd << strip_forall
    let clause_corresponds cl0 = 
        let f0, ctm0 = dest_comb(lhs cl0)
        let c0 = fst(dest_const(fst(strip_comb ctm0)))
        let dty0, rty0 = dest_fun_ty(type_of f0)
        fun cl1 -> 
            let f1, ctm1 = dest_comb(lhs cl1)
            let c1 = fst(dest_const(fst(strip_comb ctm1)))
            let dty1, rty1 = dest_fun_ty(type_of f1)
            c0 = c1 && dty0 = rty1 && rty0 = dty1
    let prove_inductive_types_isomorphic n k (ith0, rth0) (ith1, rth1) = 
        let sth0 = SPEC_ALL rth0
        let sth1 = SPEC_ALL rth1
        let t_tm = concl TRUTH
        let pevs0, pbod0 = strip_exists(concl sth0)
        let pevs1, pbod1 = strip_exists(concl sth1)
        let pcjs0, qcjs0 = chop_list k (conjuncts pbod0)
        let pcjs1, qcjs1 = chop_list k (snd(chop_list n (conjuncts pbod1)))
        let tyal0 = setify(zip (map grab_type pcjs1) (map grab_type pcjs0))
        let tyal1 = map (fun (a, b) -> (b, a)) tyal0
        let tyins0 = 
            map (fun f -> 
                    let domty, ranty = dest_fun_ty(type_of f)
                    tysubst tyal0 domty, ranty) pevs0
        let tyins1 = 
            map (fun f -> 
                    let domty, ranty = dest_fun_ty(type_of f)
                    tysubst tyal1 domty, ranty) pevs1
        let tth0 = INST_TYPE tyins0 sth0
        let tth1 = INST_TYPE tyins1 sth1
        let evs0, bod0 = strip_exists(concl tth0)
        let evs1, bod1 = strip_exists(concl tth1)
        let lcjs0, rcjs0 = 
            chop_list k (map (snd << strip_forall) (conjuncts bod0))
        let lcjs1, rcjsx = 
            chop_list k 
                (map (snd << strip_forall) (snd(chop_list n (conjuncts bod1))))
        let rcjs1 = map (fun t -> find (clause_corresponds t) rcjsx) rcjs0
        let proc_clause tm0 tm1 = 
            let l0, r0 = dest_eq tm0
            let l1, r1 = dest_eq tm1
            let vc0, wargs0 = strip_comb r0
            let con0, vargs0 = strip_comb(rand l0)
            let gargs0 = map (genvar << type_of) wargs0
            let nestf0 = 
                map 
                    (fun a -> 
                        can (find(fun t -> is_comb t && rand t = a)) wargs0) 
                    vargs0
            let targs0 = 
                map2 (fun a f -> 
                        if f
                        then find (fun t -> is_comb t && rand t = a) wargs0
                        else a) vargs0 nestf0
            let gvlist0 = zip wargs0 gargs0
            let xargs = map (fun v -> assoc v gvlist0) targs0
            let inst0 = 
                list_mk_abs
                    (gargs0, list_mk_comb(fst(strip_comb(rand l1)), xargs)), vc0
            let vc1, wargs1 = strip_comb r1
            let con1, vargs1 = strip_comb(rand l1)
            let gargs1 = map (genvar << type_of) wargs1
            let targs1 = 
                map2 (fun a f -> 
                        if f
                        then find (fun t -> is_comb t && rand t = a) wargs1
                        else a) vargs1 nestf0
            let gvlist1 = zip wargs1 gargs1
            let xargs = map (fun v -> assoc v gvlist1) targs1
            let inst1 = 
                list_mk_abs
                    (gargs1, list_mk_comb(fst(strip_comb(rand l0)), xargs)), vc1
            inst0, inst1
        let insts0, insts1 = 
            unzip(map2 proc_clause (lcjs0 @ rcjs0) (lcjs1 @ rcjs1))
        let uth0 = BETA_RULE(INST insts0 tth0)
        let uth1 = BETA_RULE(INST insts1 tth1)
        let efvs0, sth0 = DE_EXISTENTIALIZE_RULE uth0
        let efvs1, sth1 = DE_EXISTENTIALIZE_RULE uth1
        let efvs2 = 
            map 
                (fun t1 -> 
                    find 
                        (fun t2 -> 
                            hd(tl(snd(dest_type(type_of t1)))) = hd
                                                                     (snd
                                                                          (dest_type
                                                                               (type_of 
                                                                                    t2)))) 
                        efvs1) efvs0
        let isotms = 
            map2 (fun ff gg -> list_mk_icomb "ISO" [ff; gg]) efvs0 efvs2
        let ctm = list_mk_conj isotms
        let cth1 = ISO_EXPAND_CONV ctm
        let ctm1 = rand(concl cth1)
        let cjs = conjuncts ctm1
        let eee = map (fun n -> n mod 2 = 0) (0 -- (length cjs - 1))
        let cjs1, cjs2 = partition fst (zip eee cjs)
        let ctm2 = 
            mk_conj(list_mk_conj(map snd cjs1), list_mk_conj(map snd cjs2))
        let DETRIV_RULE = TRIV_ANTE_RULE << REWRITE_RULE [sth0; sth1]
        let jth0 = 
            let itha = SPEC_ALL ith0
            let icjs = conjuncts(rand(concl itha))
            let cinsts = 
                map (fun tm -> tryfind (fun vtm -> term_match [] vtm tm) icjs) 
                    (conjuncts(rand ctm2))
            let tvs = 
                subtract (fst(strip_forall(concl ith0))) 
                    (itlist (fun (_, x, _) -> union(map snd x)) cinsts [])
            let ctvs = 
                map (fun p -> 
                        let x = mk_var("x", hd(snd(dest_type(type_of p))))
                        mk_abs(x, t_tm), p) tvs
            DETRIV_RULE(INST ctvs (itlist INSTANTIATE cinsts itha))
        let jth1 = 
            let itha = SPEC_ALL ith1
            let icjs = conjuncts(rand(concl itha))
            let cinsts = 
                map (fun tm -> tryfind (fun vtm -> term_match [] vtm tm) icjs) 
                    (conjuncts(lhand ctm2))
            let tvs = 
                subtract (fst(strip_forall(concl ith1))) 
                    (itlist (fun (_, x, _) -> union(map snd x)) cinsts [])
            let ctvs = 
                map (fun p -> 
                        let x = mk_var("x", hd(snd(dest_type(type_of p))))
                        mk_abs(x, t_tm), p) tvs
            DETRIV_RULE(INST ctvs (itlist INSTANTIATE cinsts itha))
        let cths4 = map2 CONJ (CONJUNCTS jth0) (CONJUNCTS jth1)
        let cths5 = map (PURE_ONCE_REWRITE_RULE [GSYM ISO]) cths4
        let cth6 = end_itlist CONJ cths5
        cth6, CONJ sth0 sth1
    (* ----------------------------------------------------------------------- *)
    (* Define nested type by doing a 1-level unwinding.                        *)
    (* ----------------------------------------------------------------------- *)
    let SCRUB_ASSUMPTION th = 
        let hyps = hyp th
        let eqn = 
            find (fun t -> 
                    let x = lhs t
                    forall (fun u -> not(free_in x (rand u))) hyps) hyps
        let l, r = dest_eq eqn
        MP (INST [r, l] (DISCH eqn th)) (REFL r)
    let define_type_basecase def = 
        let add_id s = fst(dest_var(genvar bool_ty))
        let def' = map (I ||>> (map(add_id ||>> I))) def
        define_type_raw def'
    let SIMPLE_BETA_RULE = GSYM << PURE_REWRITE_RULE [BETA_THM; FUN_EQ_THM]
    let ISO_USAGE_RULE = MATCH_MP ISO_USAGE
    let SIMPLE_ISO_EXPAND_RULE = CONV_RULE(REWR_CONV ISO)
    let REWRITE_FUN_EQ_RULE = 
        let ths = itlist (mk_rewrites false) [FUN_EQ_THM] []
        let net = itlist (net_of_thm false) ths (basic_net())
        CONV_RULE << GENERAL_REWRITE_CONV true TOP_DEPTH_CONV net
    let is_nested vs ty = 
        not(is_vartype ty) && not(intersect (tyvars ty) vs = [])
    let rec modify_type alist ty = 
        try 
            rev_assoc ty alist
        with
        | Failure _ -> 
            try 
                let tycon, tyargs = dest_type ty
                mk_type(tycon, map (modify_type alist) tyargs)
            with
            | Failure _ -> ty
    let modify_item alist (s, l) = s, map (modify_type alist) l
    let modify_clause alist (l, lis) = l, map (modify_item alist) lis
    let recover_clause id tm = 
        let con, args = strip_comb tm
        fst(dest_const con) ^ id, map type_of args
    let rec create_auxiliary_clauses nty = 
        let id = fst(dest_var(genvar bool_ty))
        let tycon, tyargs = dest_type nty
        let k, ith, rth = 
            try 
                assoc tycon (!inductive_type_store)
            with
            | Failure _ -> 
                failwith("Can't find definition for nested type: " ^ tycon)
        let evs, bod = strip_exists(snd(strip_forall(concl rth)))
        let cjs = map (lhand << snd << strip_forall) (conjuncts bod)
        let rtys = map (hd << snd << dest_type << type_of) evs
        let tyins = tryfind (fun vty -> type_match vty nty []) rtys
        let cjs' = map (inst tyins << rand) (fst(chop_list k cjs))
        let mtys = itlist (insert << type_of) cjs' []
        let pcons = map (fun ty -> filter (fun t -> type_of t = ty) cjs') mtys
        let cls' = zip mtys (map (map(recover_clause id)) pcons)
        let tyal = map (fun ty -> mk_vartype(fst(dest_type ty) ^ id), ty) mtys
        let cls'' = map (modify_type tyal ||>> map(modify_item tyal)) cls'
        k, tyal, cls'', INST_TYPE tyins ith, INST_TYPE tyins rth
    let rec define_type_nested def = 
        let n = length(itlist (@) (map (map fst << snd) def) [])
        let newtys = map fst def
        let utys = unions(itlist (union << map snd << snd) def [])
        let rectys = filter (is_nested newtys) utys
        if rectys = []
        then 
            let th1, th2 = define_type_basecase def
            n, th1, th2
        else 
            let nty = hd(sort (fun t1 t2 -> occurs_in t2 t1) rectys)
            let k, tyal, ncls, ith, rth = create_auxiliary_clauses nty
            let cls = map (modify_clause tyal) def @ ncls
            let _, ith1, rth1 = define_type_nested cls
            let xnewtys = 
                map (hd << snd << dest_type << type_of) 
                    (fst(strip_exists(snd(strip_forall(concl rth1)))))
            let xtyal = 
                map (fun ty -> 
                        let s = dest_vartype ty
                        find (fun t -> fst(dest_type t) = s) xnewtys, ty) 
                    (map fst cls)
            let ith0 = INST_TYPE xtyal ith
            let rth0 = INST_TYPE xtyal rth
            let isoth, rclauses = 
                prove_inductive_types_isomorphic n k (ith0, rth0) (ith1, rth1)
            let irth3 = CONJ ith1 rth1
            let vtylist = itlist (insert << type_of) (variables(concl irth3)) []
            let isoths = CONJUNCTS isoth
            let isotys = 
                map (hd << snd << dest_type << type_of << lhand << concl) isoths
            let ctylist = 
                filter (fun ty -> exists (fun t -> occurs_in t ty) isotys) 
                    vtylist
            let atylist = itlist (union << striplist dest_fun_ty) ctylist []
            let isoths' = 
                map (lift_type_bijections isoths) 
                    (filter (fun ty -> exists (fun t -> occurs_in t ty) isotys) 
                         atylist)
            let cisoths = 
                map (BETA_RULE << lift_type_bijections isoths') ctylist
            let uisoths = map ISO_USAGE_RULE cisoths
            let visoths = map (ASSUME << concl) uisoths
            let irth4 = 
                itlist PROVE_HYP uisoths (REWRITE_FUN_EQ_RULE visoths irth3)
            let irth5 = 
                REWRITE_RULE (rclauses :: map SIMPLE_ISO_EXPAND_RULE isoths') 
                    irth4
            let irth6 = repeat SCRUB_ASSUMPTION irth5
            let ncjs = 
                filter 
                    (fun t -> 
                        exists (fun v -> not(is_var v)) 
                            (snd(strip_comb(rand(lhs(snd(strip_forall t))))))) 
                    (conjuncts
                         (snd
                              (strip_exists
                                   (snd(strip_forall(rand(concl irth6)))))))
            let mk_newcon tm = 
                let vs, bod = strip_forall tm
                let rdeb = rand(lhs bod)
                let rdef = list_mk_abs(vs, rdeb)
                let newname = fst(dest_var(genvar bool_ty))
                let def = mk_eq(mk_var(newname, type_of rdef), rdef)
                let dth = new_definition def
                SIMPLE_BETA_RULE dth
            let dths = map mk_newcon ncjs
            let ith6, rth6 = CONJ_PAIR(PURE_REWRITE_RULE dths irth6)
            n, ith6, rth6
    fun def -> 
        let newtys = map fst def
        let truecons = itlist (@) (map (map fst << snd) def) []
        let (p, ith0, rth0) = define_type_nested def
        let avs, etm = strip_forall(concl rth0)
        let allcls = conjuncts(snd(strip_exists etm))
        let relcls = fst(chop_list (length truecons) allcls)
        let gencons = 
            map (repeat rator << rand << lhand << snd << strip_forall) relcls
        let cdefs = 
            map2 
                (fun s r -> SYM(new_definition(mk_eq(mk_var(s, type_of r), r)))) 
                truecons gencons
        let tavs = make_args "f" [] (map type_of avs)
        let ith1 = SUBS cdefs ith0
        let rth1 = GENL tavs (SUBS cdefs (SPECL tavs rth0))
        let retval = p, ith1, rth1
        let newentries = map (fun s -> dest_vartype s, retval) newtys
        (inductive_type_store := newentries @ (!inductive_type_store)
         do_list extend_rectype_net newentries
         ith1, rth1)

(* ----------------------------------------------------------------------- *)
(* The overall function, with rather crude string-based benignity.         *)
(* ----------------------------------------------------------------------- *)
let the_inductive_types = 
    ref ["list = NIL | CONS A list", (list_INDUCT, list_RECURSION)
         "option = NONE | SOME A", (option_INDUCT, option_RECURSION)
         "sum = INL A | INR B", (sum_INDUCT, sum_RECURSION)]

let define_type s = 
    try 
        let retval = assoc s (!the_inductive_types)
        (warn true "Benign redefinition of inductive type"
         retval)
    with
    | Failure _ -> 
        let defspec = parse_inductive_type_specification s
        let newtypes = map fst defspec
        let constructors = itlist ((@) << map fst) (map snd defspec) []
        if not(length(setify newtypes) = length newtypes)
        then failwith "define_type: multiple definitions of a type"
        elif not(length(setify constructors) = length constructors)
        then failwith "define_type: multiple instances of a constructor"
        elif exists (can get_type_arity << dest_vartype) newtypes
        then 
            let t = find (can get_type_arity) (map dest_vartype newtypes)
            failwith("define_type: type :" ^ t ^ " already defined")
        elif exists (can get_const_type) constructors
        then 
            let t = find (can get_const_type) constructors
            failwith("define_type: constant " ^ t ^ " already defined")
        else 
            let retval = define_type_raw defspec
            the_inductive_types := (s, retval) :: (!the_inductive_types)
            retval

(* ------------------------------------------------------------------------- *)
(* Unwinding, and application of patterns. Add easy cases to default net.    *)
(* ------------------------------------------------------------------------- *)
let UNWIND_CONV, MATCH_CONV = 
    let pth_0 = 
      prove((parse_term @"(if ?!x. x = a /\ p then @x. x = a /\ p else @x. F) =
      (if p then a else @x. F)"),
        BOOL_CASES_TAC(parse_term @"p:bool")
        |> THEN <| ASM_REWRITE_TAC [COND_ID]
        |> THEN <| MESON_TAC [])
    let pth_1 = 
      prove((parse_term @"_MATCH x (_SEQPATTERN r s) =
      (if ?y. r x y then _MATCH x r else _MATCH x s) /\
      _FUNCTION (_SEQPATTERN r s) x =
      (if ?y. r x y then _FUNCTION r x else _FUNCTION s x)"),
        REWRITE_TAC [_MATCH; _SEQPATTERN; _FUNCTION]
        |> THEN <| MESON_TAC [])
    let pth_2 = 
        prove
            ((parse_term @"((?y. _UNGUARDED_PATTERN (GEQ s t) (GEQ u y)) <=> s = t) /\
     ((?y. _GUARDED_PATTERN (GEQ s t) p (GEQ u y)) <=> s = t /\ p)"), 
             REWRITE_TAC [_UNGUARDED_PATTERN; _GUARDED_PATTERN; GEQ_DEF]
             |> THEN <| MESON_TAC [])
    let pth_3 = 
        prove
            ((parse_term @"(_MATCH x (\y z. P y z) = if ?!z. P x z then @z. P x z else @x. F) /\
     (_FUNCTION (\y z. P y z) x = if ?!z. P x z then @z. P x z else @x. F)"), 
             REWRITE_TAC [_MATCH; _FUNCTION])
    let pth_4 = 
        prove
            ((parse_term @"(_UNGUARDED_PATTERN (GEQ s t) (GEQ u y) <=> y = u /\ s = t) /\
     (_GUARDED_PATTERN (GEQ s t) p (GEQ u y) <=> y = u /\ s = t /\ p)"), 
             REWRITE_TAC [_UNGUARDED_PATTERN; _GUARDED_PATTERN; GEQ_DEF]
             |> THEN <| MESON_TAC [])
    let pth_5 = 
        prove
            ((parse_term @"(if ?!z. z = k then @z. z = k else @x. F) = k"), 
             MESON_TAC [])
    let rec INSIDE_EXISTS_CONV conv tm = 
        if is_exists tm
        then BINDER_CONV (INSIDE_EXISTS_CONV conv) tm
        else conv tm
    let PUSH_EXISTS_CONV = 
        let econv = REWR_CONV SWAP_EXISTS_THM
        let rec conv bc tm = 
            try 
                (econv
                 |> THENC <| BINDER_CONV(conv bc)) tm
            with
            | Failure _ -> bc tm
        conv
    let BREAK_CONS_CONV = 
        let conv2 = GEN_REWRITE_CONV DEPTH_CONV [AND_CLAUSES; OR_CLAUSES]
                    |> THENC <| ASSOC_CONV CONJ_ASSOC
        fun tm -> 
            let conv0 = TOP_SWEEP_CONV(REWRITES_CONV(!basic_rectype_net))
            let conv1 = 
                if is_conj tm
                then LAND_CONV conv0
                else conv0
            (conv1
             |> THENC <| conv2) tm
    let UNWIND_CONV = 
        let baseconv = 
            GEN_REWRITE_CONV I [UNWIND_THM1
                                UNWIND_THM2
                                EQT_INTRO(SPEC_ALL EXISTS_REFL)
                                EQT_INTRO(GSYM(SPEC_ALL EXISTS_REFL))]
        let rec UNWIND_CONV tm = 
            let evs, bod = strip_exists tm
            let eqs = conjuncts bod
            try 
                let eq = find (fun tm -> 
                    is_eq tm &&
                    let l, r = dest_eq tm
                    (mem l evs && not(free_in l r)) || 
                    (mem r evs && not(free_in r l))) eqs
                let l, r = dest_eq eq
                let v = 
                    if mem l evs && not(free_in l r)
                    then l
                    else r
                let cjs' = eq :: (subtract eqs [eq])
                let n = length evs - (1 + index v (rev evs))
                let th1 = CONJ_ACI_RULE(mk_eq(bod, list_mk_conj cjs'))
                let th2 = itlist MK_EXISTS evs th1
                let th3 = 
                    funpow n BINDER_CONV (PUSH_EXISTS_CONV baseconv) 
                        (rand(concl th2))
                CONV_RULE (RAND_CONV UNWIND_CONV) (TRANS th2 th3)
            with
            | Failure _ -> REFL tm
        UNWIND_CONV
    let MATCH_SEQPATTERN_CONV = 
        GEN_REWRITE_CONV I [pth_1]
        |> THENC 
        <| RATOR_CONV
               (LAND_CONV(BINDER_CONV(RATOR_CONV BETA_CONV
                                      |> THENC <| BETA_CONV)
                          |> THENC 
                          <| PUSH_EXISTS_CONV(GEN_REWRITE_CONV I [pth_2]
                                              |> THENC <| BREAK_CONS_CONV)
                          |> THENC <| UNWIND_CONV
                          |> THENC <| GEN_REWRITE_CONV DEPTH_CONV [EQT_INTRO
                                                                       (SPEC_ALL 
                                                                            EQ_REFL)
                                                                   AND_CLAUSES]
                          |> THENC <| GEN_REWRITE_CONV DEPTH_CONV [EXISTS_SIMP]))
    let MATCH_ONEPATTERN_CONV tm = 
        let th1 = GEN_REWRITE_CONV I [pth_3] tm
        let tm' = body(rand(lhand(rand(concl th1))))
        let th2 = 
            (INSIDE_EXISTS_CONV(GEN_REWRITE_CONV I [pth_4]
                                |> THENC <| RAND_CONV BREAK_CONS_CONV)
             |> THENC <| UNWIND_CONV
             |> THENC <| GEN_REWRITE_CONV DEPTH_CONV [EQT_INTRO
                                                          (SPEC_ALL EQ_REFL)
                                                      AND_CLAUSES]
             |> THENC <| GEN_REWRITE_CONV DEPTH_CONV [EXISTS_SIMP]) tm'
        let conv tm = 
            if tm = lhand(concl th2)
            then th2
            else fail()
        CONV_RULE 
            (RAND_CONV
                 (RATOR_CONV
                      (COMB2_CONV (RAND_CONV(BINDER_CONV conv)) 
                           (BINDER_CONV conv)))) th1
    let MATCH_SEQPATTERN_CONV_TRIV = 
        MATCH_SEQPATTERN_CONV
        |> THENC <| GEN_REWRITE_CONV I [COND_CLAUSES]
    let MATCH_SEQPATTERN_CONV_GEN = 
        MATCH_SEQPATTERN_CONV
        |> THENC <| GEN_REWRITE_CONV TRY_CONV [COND_CLAUSES]
    let MATCH_ONEPATTERN_CONV_TRIV = MATCH_ONEPATTERN_CONV
                                     |> THENC <| GEN_REWRITE_CONV I [pth_5]
    let MATCH_ONEPATTERN_CONV_GEN = 
        MATCH_ONEPATTERN_CONV
        |> THENC <| GEN_REWRITE_CONV TRY_CONV [pth_0; pth_5]
    do_list extend_basic_convs 
        ["MATCH_SEQPATTERN_CONV", 
         ((parse_term @"_MATCH x (_SEQPATTERN r s)"), MATCH_SEQPATTERN_CONV_TRIV)
         "FUN_SEQPATTERN_CONV", 
         ((parse_term @"_FUNCTION (_SEQPATTERN r s) x"), 
          MATCH_SEQPATTERN_CONV_TRIV)
         "MATCH_ONEPATTERN_CONV", 
         ((parse_term @"_MATCH x (\y z. P y z)"), MATCH_ONEPATTERN_CONV_TRIV)
         "FUN_ONEPATTERN_CONV", 
         ((parse_term @"_FUNCTION (\y z. P y z) x"), MATCH_ONEPATTERN_CONV_TRIV)]
    (CHANGED_CONV UNWIND_CONV, (MATCH_SEQPATTERN_CONV_GEN
                                |> ORELSEC <| MATCH_ONEPATTERN_CONV_GEN))

let FORALL_UNWIND_CONV = 
    let PUSH_FORALL_CONV = 
        let econv = REWR_CONV SWAP_FORALL_THM
        let rec conv bc tm = 
            try 
                (econv
                 |> THENC <| BINDER_CONV(conv bc)) tm
            with
            | Failure _ -> bc tm
        conv
    let baseconv = 
        GEN_REWRITE_CONV I [MESON [] 
                                (parse_term 
                                     "(!x. x = a /\ p x ==> q x) <=> (p a ==> q a)")
                            MESON [] 
                                (parse_term 
                                     "(!x. a = x /\ p x ==> q x) <=> (p a ==> q a)")
                            MESON [] (parse_term @"(!x. x = a ==> q x) <=> q a")
                            MESON [] (parse_term @"(!x. a = x ==> q x) <=> q a")]
    let rec FORALL_UNWIND_CONV tm = 
        try 
            let avs, bod = strip_forall tm
            let ant, con = dest_imp bod
            let eqs = conjuncts ant
            let eq = 
                find (fun tm -> 
                    is_eq tm && 
                    let l, r = dest_eq tm
                    (mem l avs && not(free_in l r)) || 
                    (mem r avs && not(free_in r l))) eqs
            let l, r = dest_eq eq
            let v = 
                if mem l avs && not(free_in l r)
                then l
                else r
            let cjs' = eq :: (subtract eqs [eq])
            let n = length avs - (1 + index v (rev avs))
            let th1 = CONJ_ACI_RULE(mk_eq(ant, list_mk_conj cjs'))
            let th2 = AP_THM (AP_TERM (rator(rator bod)) th1) con
            let th3 = itlist MK_FORALL avs th2
            let th4 = 
                funpow n BINDER_CONV (PUSH_FORALL_CONV baseconv) 
                    (rand(concl th3))
            CONV_RULE (RAND_CONV FORALL_UNWIND_CONV) (TRANS th3 th4)
        with
        | Failure _ -> REFL tm
    FORALL_UNWIND_CONV