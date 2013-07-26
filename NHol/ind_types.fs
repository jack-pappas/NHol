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
//// Tools for defining inductive types.
module NHol.ind_types

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
#endif

(* ------------------------------------------------------------------------- *)
(* Abstract left inverses for binary injections (we could construct them...) *)
(* ------------------------------------------------------------------------- *)

let INJ_INVERSE2 = 
#if BUGGY
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
   |> THEN <| W(EXISTS_TAC << Choice.get <| rand << snd << Choice.get <| dest_exists << snd)
   |> THEN <| REFL_TAC)
#else
    Choice.succeed <| Sequent([], parse_term @"!P. (!x1 y1 x2 y2. P x1 y1 = P x2 y2 <=> x1 = x2 /\ y1 = y2)
         ==> (?X Y. !x y. X (P x y) = x /\ Y (P x y) = y)") : thm
#endif

(* ------------------------------------------------------------------------- *)
(* Define an injective pairing function on ":num".                           *)
(* ------------------------------------------------------------------------- *)

let NUMPAIR = new_definition(parse_term @"NUMPAIR x y = (2 EXP x) * (2 * y + 1)")

let NUMPAIR_INJ_LEMMA = 
    prove
        ((parse_term @"!x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) ==> (x1 = x2)"), 
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
         |> THEN <| REWRITE_TAC [EVEN_MULT; EVEN_ADD; ARITH]);;

let NUMPAIR_INJ =     
#if BUGGY
    prove
        ((parse_term @"!x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) <=> (x1 = x2) /\ (y1 = y2)"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| FIRST_ASSUM(SUBST_ALL_TAC << MATCH_MP NUMPAIR_INJ_LEMMA)
         |> THEN <| POP_ASSUM MP_TAC
         |> THEN <| REWRITE_TAC [NUMPAIR]
         |> THEN <| REWRITE_TAC [EQ_MULT_LCANCEL; EQ_ADD_RCANCEL; EXP_EQ_0; ARITH])
#else
    Choice.succeed <| Sequent([], parse_term @"!x1 y1 x2 y2. NUMPAIR x1 y1 = NUMPAIR x2 y2 <=> x1 = x2 /\ y1 = y2") : thm
#endif

let NUMPAIR_DEST = 
    new_specification ["NUMFST"
                       "NUMSND"] (MATCH_MP INJ_INVERSE2 NUMPAIR_INJ)

(* ------------------------------------------------------------------------- *)
(* Also, an injective map bool->num->num (even easier!)                      *)
(* ------------------------------------------------------------------------- *)

let NUMSUM = 
    new_definition(parse_term @"NUMSUM b x = if b then SUC(2 * x) else 2 * x")

let NUMSUM_INJ =    
#if BUGGY
    prove
        ((parse_term @"!b1 x1 b2 x2. (NUMSUM b1 x1 = NUMSUM b2 x2) <=> (b1 = b2) /\ (x1 = x2)"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| POP_ASSUM(MP_TAC << REWRITE_RULE [NUMSUM])
         |> THEN <| DISCH_THEN
                        (fun th -> MP_TAC th
                                   |> THEN <| MP_TAC(AP_TERM (parse_term @"EVEN") th))
         |> THEN <| REPEAT COND_CASES_TAC
         |> THEN <| REWRITE_TAC [EVEN; EVEN_DOUBLE]
         |> THEN <| REWRITE_TAC [SUC_INJ; EQ_MULT_LCANCEL; ARITH])
#else
    Choice.succeed <| Sequent([], parse_term @"!b1 x1 b2 x2. NUMSUM b1 x1 = NUMSUM b2 x2 <=> (b1 <=> b2) /\ x1 = x2") : thm
#endif

let NUMSUM_DEST = 
    new_specification ["NUMLEFT"
                       "NUMRIGHT"] (MATCH_MP INJ_INVERSE2 NUMSUM_INJ)

(* ------------------------------------------------------------------------- *)
(* Injection num->Z, where Z == num->A->bool.                                *)
(* ------------------------------------------------------------------------- *)

let INJN = new_definition(parse_term @"INJN (m:num) = \(n:num) (a:A). n = m")

let INJN_INJ = 
#if BUGGY
    prove
        ((parse_term @"!n1 n2. (INJN n1 :num->A->bool = INJN n2) <=> (n1 = n2)"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| POP_ASSUM
                        (MP_TAC << C AP_THM (parse_term @"n1:num") << REWRITE_RULE [INJN])
         |> THEN <| DISCH_THEN(MP_TAC << C AP_THM (parse_term @"a:A"))
         |> THEN <| REWRITE_TAC [BETA_THM])
#else
    Choice.succeed <| Sequent([], parse_term @"!n1 n2. INJN n1 = INJN n2 <=> n1 = n2") : thm
#endif

(* ------------------------------------------------------------------------- *)
(* Injection A->Z, where Z == num->A->bool.                                  *)
(* ------------------------------------------------------------------------- *)

let INJA = new_definition(parse_term @"INJA (a:A) = \(n:num) b. b = a")

let INJA_INJ = 
#if BUGGY
    prove
        ((parse_term @"!a1 a2. (INJA a1 = INJA a2) <=> (a1:A = a2)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [INJA; FUN_EQ_THM]
         |> THEN <| EQ_TAC
         |> THENL <| [DISCH_THEN(MP_TAC << SPEC(parse_term @"a1:A"))
                      |> THEN <| REWRITE_TAC []
                      DISCH_THEN SUBST1_TAC
                      |> THEN <| REWRITE_TAC []])
#else
    Choice.succeed <| Sequent([], parse_term @"!n1 n2. INJN n1 = INJN n2 <=> n1 = n2") : thm
#endif

(* ------------------------------------------------------------------------- *)
(* Injection (num->Z)->Z, where Z == num->A->bool.                           *)
(* ------------------------------------------------------------------------- *)

let INJF = 
    new_definition
        (parse_term @"INJF (f:num->(num->A->bool)) = \n. f (NUMFST n) (NUMSND n)")

let INJF_INJ = 
#if BUGGY
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
         |> THEN <| DISCH_THEN
                        (MP_TAC << C AP_THM (parse_term @"a:A") << C AP_THM (parse_term @"NUMPAIR n m"))
         |> THEN <| REWRITE_TAC [NUMPAIR_DEST])
#else
    Choice.succeed <| Sequent([], parse_term @"!f1 f2. INJF f1 = INJF f2 <=> f1 = f2") : thm
#endif

(* ------------------------------------------------------------------------- *)
(* Injection Z->Z->Z, where Z == num->A->bool.                               *)
(* ------------------------------------------------------------------------- *)

let INJP = 
    new_definition
        (parse_term @"INJP f1 f2:num->A->bool = \n a. if NUMLEFT n then f1 (NUMRIGHT n) a else f2 (NUMRIGHT n) a");;

let INJP_INJ = 
#if BUGGY
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
       |> THEN <| DISCH_THEN
                      (MP_TAC << GEN(parse_term @"b:bool") 
                       << C AP_THM (parse_term @"NUMSUM b n"))
       |> THEN <| DISCH_THEN(fun th -> MP_TAC(SPEC (parse_term @"T") th)
                                       |> THEN <| MP_TAC(SPEC (parse_term @"F") th))
       |> THEN <| ASM_SIMP_TAC [NUMSUM_DEST; ETA_AX])
#else
    Choice.succeed <| Sequent([], parse_term @"!f1 f1' f2 f2'. INJP f1 f2 = INJP f1' f2' <=> f1 = f1' /\ f2 = f2'") : thm
#endif

(* ------------------------------------------------------------------------- *)
(* Now, set up "constructor" and "bottom" element.                           *)
(* ------------------------------------------------------------------------- *)

let ZCONSTR = 
    new_definition
        (parse_term @"ZCONSTR c i r :num->A->bool = INJP (INJN (SUC c)) (INJP (INJA i) (INJF r))")

let ZBOT = 
    new_definition(parse_term @"ZBOT = INJP (INJN 0) (@z:num->A->bool. T)");;

let ZCONSTR_ZBOT = 
    prove
        ((parse_term @"!c i r. ~(ZCONSTR c i r :num->A->bool = ZBOT)"), 
         REWRITE_TAC [ZCONSTR; ZBOT; INJP_INJ; INJN_INJ; NOT_SUC])

(* ------------------------------------------------------------------------- *)
(* Carve out an inductively defined set.                                     *)
(* ------------------------------------------------------------------------- *)
let ZRECSPACE_RULES, ZRECSPACE_INDUCT, ZRECSPACE_CASES = 
    new_inductive_definition(parse_term @"ZRECSPACE (ZBOT:num->A->bool) /\
    (!c i r. (!n. ZRECSPACE (r n)) ==> ZRECSPACE (ZCONSTR c i r))")

let recspace_tydef = 
    new_basic_type_definition "recspace" ("_mk_rec", "_dest_rec") 
        (CONJUNCT1 ZRECSPACE_RULES)

(* ------------------------------------------------------------------------- *)
(* Define lifted constructors.                                               *)
(* ------------------------------------------------------------------------- *)

let BOTTOM = new_definition(parse_term @"BOTTOM = _mk_rec (ZBOT:num->A->bool)");;

let CONSTR = 
    new_definition
        (parse_term @"CONSTR c i r :(A)recspace = _mk_rec (ZCONSTR c i (\n. _dest_rec(r n)))")

(* ------------------------------------------------------------------------- *)
(* Some lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let MK_REC_INJ = 
#if BUGGY
    prove((parse_term @"!x y. (_mk_rec x :(A)recspace = _mk_rec y)
         ==> (ZRECSPACE x /\ ZRECSPACE y ==> (x = y))"),
        REPEAT GEN_TAC
        |> THEN <| DISCH_TAC
        |> THEN <| REWRITE_TAC [snd recspace_tydef]
        |> THEN <| DISCH_THEN(fun th -> ONCE_REWRITE_TAC [GSYM th])
        |> THEN <| ASM_REWRITE_TAC [])
#else
    Choice.succeed <| Sequent([], parse_term @"!x y. _mk_rec x = _mk_rec y ==> ZRECSPACE x /\ ZRECSPACE y ==> x = y") : thm
#endif
;;

let DEST_REC_INJ = 
#if BUGGY
    prove
        ((parse_term @"!x y. (_dest_rec x = _dest_rec y) <=> (x:(A)recspace = y)"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| POP_ASSUM
                        (MP_TAC 
                         << AP_TERM(parse_term @"_mk_rec:(num->A->bool)->(A)recspace"))
         |> THEN <| REWRITE_TAC [fst recspace_tydef])
#else
    Choice.succeed <| Sequent([], parse_term @"!x y. _dest_rec x = _dest_rec y <=> x = y") : thm
#endif
;;

(* ------------------------------------------------------------------------- *)
(* Show that the set is freely inductively generated.                        *)
(* ------------------------------------------------------------------------- *)

let CONSTR_BOT = 
#if BUGGY
    prove
        ((parse_term @"!c i r. ~(CONSTR c i r :(A)recspace = BOTTOM)"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [CONSTR; BOTTOM]
         |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP MK_REC_INJ)
         |> THEN <| REWRITE_TAC [ZCONSTR_ZBOT; ZRECSPACE_RULES]
         |> THEN <| MATCH_MP_TAC(CONJUNCT2 ZRECSPACE_RULES)
         |> THEN <| REWRITE_TAC [fst recspace_tydef
                                 snd recspace_tydef])
#else
    Choice.succeed <| Sequent([], parse_term @"!c i r. ~(CONSTR c i r = BOTTOM)") : thm
#endif
;;

let CONSTR_INJ = 
#if BUGGY
    prove
        ((parse_term @"!c1 i1 r1 c2 i2 r2. (CONSTR c1 i1 r1 :(A)recspace = CONSTR c2 i2 r2) <=>
                       (c1 = c2) /\ (i1 = i2) /\ (r1 = r2)"),
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| DISCH_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| POP_ASSUM(MP_TAC << REWRITE_RULE [CONSTR])
         |> THEN <| DISCH_THEN(MP_TAC << MATCH_MP MK_REC_INJ)
         |> THEN <| W(C SUBGOAL_THEN ASSUME_TAC << funpow 2 Choice.get <| lhand << snd)
         |> THENL <| [CONJ_TAC
                      |> THEN <| MATCH_MP_TAC(CONJUNCT2 ZRECSPACE_RULES)
                      |> THEN <| REWRITE_TAC [fst recspace_tydef
                                              snd recspace_tydef]
                      ASM_REWRITE_TAC []
                      |> THEN <| REWRITE_TAC [ZCONSTR]
                      |> THEN <| REWRITE_TAC [INJP_INJ; INJN_INJ; INJF_INJ; INJA_INJ]
                      |> THEN <| ONCE_REWRITE_TAC [FUN_EQ_THM]
                      |> THEN <| BETA_TAC
                      |> THEN <| REWRITE_TAC [SUC_INJ; DEST_REC_INJ]])
#else
    Choice.succeed <| Sequent([], parse_term @"!c1 i1 r1 c2 i2 r2.
         CONSTR c1 i1 r1 = CONSTR c2 i2 r2 <=> c1 = c2 /\ i1 = i2 /\ r1 = r2") : thm
#endif
;;

let CONSTR_IND = 
#if BUGGY
    prove((parse_term @"!P. P(BOTTOM) /\
       (!c i r. (!n. P(r n)) ==> P(CONSTR c i r))
       ==> !x:(A)recspace. P(x)"),
      REPEAT STRIP_TAC
      |> THEN <| MP_TAC
                     (SPEC (parse_term @"\z:num->A->bool. ZRECSPACE(z) /\ P(_mk_rec z)") 
                          ZRECSPACE_INDUCT)
      |> THEN <| BETA_TAC
      |> THEN <| ASM_REWRITE_TAC [ZRECSPACE_RULES
                                  GSYM BOTTOM]
      |> THEN <| W(C SUBGOAL_THEN ASSUME_TAC << funpow 2 Choice.get <| lhand << snd)
      |> THENL <| [REPEAT GEN_TAC
                   |> THEN <| REWRITE_TAC [FORALL_AND_THM]
                   |> THEN <| REPEAT STRIP_TAC
                   |> THENL <| [MATCH_MP_TAC(CONJUNCT2 ZRECSPACE_RULES)
                                |> THEN <| ASM_REWRITE_TAC []
                                FIRST_ASSUM(ANTE_RES_THEN MP_TAC)
                                |> THEN <| REWRITE_TAC [CONSTR]
                                |> THEN <| RULE_ASSUM_TAC
                                            (REWRITE_RULE [snd recspace_tydef])
                                |> THEN <| ASM_SIMP_TAC [ETA_AX]]
                   ASM_REWRITE_TAC []
                   |> THEN <| DISCH_THEN
                                  (MP_TAC 
                                   << SPEC(parse_term @"_dest_rec (x:(A)recspace)"))
                   |> THEN <| REWRITE_TAC [fst recspace_tydef]
                   |> THEN <| REWRITE_TAC 
                                [ITAUT(parse_term @"(a ==> a /\ b) <=> (a ==> b)")]
                   |> THEN <| DISCH_THEN MATCH_MP_TAC
                   |> THEN <| REWRITE_TAC [fst recspace_tydef
                                           snd recspace_tydef]])
#else
    Choice.succeed <| Sequent([], parse_term @"!P. P BOTTOM /\ (!c i r. (!n. P (r n)) ==> P (CONSTR c i r))
         ==> (!x. P x)") : thm
#endif
;;

(* ------------------------------------------------------------------------- *)
(* Now prove the recursion theorem (this subcase is all we need).            *)
(* ------------------------------------------------------------------------- *)

let CONSTR_REC = 
#if BUGGY
  prove((parse_term @"!Fn:num->A->(num->(A)recspace)->(num->B)->B.
     ?f. (!c i r. f (CONSTR c i r) = Fn c i r (\n. f (r n)))"),
    REPEAT STRIP_TAC
    |> THEN <| (MP_TAC << prove_inductive_relations_exist)(parse_term @"(Z:(A)recspace->B->bool) BOTTOM b /\
     (!c i r y. (!n. Z (r n) (y n)) ==> Z (CONSTR c i r) (Fn c i r y))")
    |> THEN <| DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC))
    |> THEN <| DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC << GSYM))
    |> THEN <| SUBGOAL_THEN (parse_term @"!x. ?!y. (Z:(A)recspace->B->bool) x y") MP_TAC
    |> THENL <| [W(MP_TAC << PART_MATCH Choice.get <| rand CONSTR_IND << snd)
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
                              |> THEN <| DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)
                              |> THEN <| DISCH_THEN(MP_TAC << REWRITE_RULE [SKOLEM_THM])
                              |> THEN <| DISCH_THEN
                                             (X_CHOOSE_THEN (parse_term @"y:num->B") 
                                                  ASSUME_TAC)
                              |> THEN <| REWRITE_TAC [EXISTS_UNIQUE_THM]
                              |> THEN <| FIRST_ASSUM
                                             (fun th -> 
                                                 CHANGED_TAC(ONCE_REWRITE_TAC [GSYM th]))
                              |> THEN <| CONJ_TAC
                              |> THENL <| [EXISTS_TAC
                                               (parse_term @"(Fn:num->A->(num->(A)recspace)->(num->B)->B) c i r y")
                                           |> THEN <| REWRITE_TAC [CONSTR_BOT;
                                                                   CONSTR_INJ;
                                                                   GSYM CONJ_ASSOC]
                                           |> THEN <| REWRITE_TAC 
                                                        [UNWIND_THM1; 
                                                         RIGHT_EXISTS_AND_THM]
                                           |> THEN <| EXISTS_TAC(parse_term @"y:num->B")
                                           |> THEN <| ASM_REWRITE_TAC []

                                           REWRITE_TAC [CONSTR_BOT
                                                        CONSTR_INJ
                                                        GSYM CONJ_ASSOC]
                                           |> THEN <| REWRITE_TAC 
                                                        [UNWIND_THM1; 
                                                         RIGHT_EXISTS_AND_THM]
                                           |> THEN <| REPEAT STRIP_TAC
                                           |> THEN <| ASM_REWRITE_TAC []
                                           |> THEN <| REPEAT AP_TERM_TAC
                                           |> THEN <| ONCE_REWRITE_TAC [FUN_EQ_THM]
                                           |> THEN <| X_GEN_TAC(parse_term @"w:num")
                                           |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                                           |> THEN <| EXISTS_TAC(parse_term @"w:num")
                                           |> THEN <| ASM_REWRITE_TAC []]]
                 REWRITE_TAC [UNIQUE_SKOLEM_ALT]
                 |> THEN <| DISCH_THEN
                                (X_CHOOSE_THEN (parse_term @"fn:(A)recspace->B") 
                                     (ASSUME_TAC << GSYM))
                 |> THEN <| EXISTS_TAC(parse_term @"fn:(A)recspace->B")
                 |> THEN <| ASM_REWRITE_TAC []
                 |> THEN <| REPEAT GEN_TAC
                 |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                 |> THEN <| GEN_TAC
                 |> THEN <| FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th])
                 |> THEN <| REWRITE_TAC [BETA_THM]])
#else
    Choice.succeed <| Sequent([], parse_term @"!Fn. ?f. !c i r. f (CONSTR c i r) = Fn c i r (\n. f (r n))") : thm
#endif

(* ------------------------------------------------------------------------- *)
(* The following is useful for coding up functions casewise.                 *)
(* ------------------------------------------------------------------------- *)

let FCONS = 
    new_recursive_definition num_RECURSION 
        (parse_term @"(!a f. FCONS (a:A) f 0 = a) /\ (!a f n. FCONS (a:A) f (SUC n) = f n)");;

// Some error occurs 
let FCONS_UNDO = 
#if BUGGY
    prove
        ((parse_term @"!f:num->A. f = FCONS (f 0) (f << SUC)"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [FUN_EQ_THM]
         |> THEN <| INDUCT_TAC
         |> THEN <| REWRITE_TAC [FCONS; o_THM])
#else
    Choice.succeed <| Sequent([],parse_term @"!f:num->A. f = FCONS (f 0) (f << SUC)") : thm
#endif

let FNIL = new_definition(parse_term @"FNIL (n:num) = @x:A. T");;

(* ------------------------------------------------------------------------- *)
(* The initial mutual type definition function, with a type-restricted       *)
(* recursion theorem.                                                        *)
(* ------------------------------------------------------------------------- *)

let define_type_raw_001 = 

    (* ----------------------------------------------------------------------- *)
    (* Handy utility to produce "SUC << SUC << SUC ..." form of numeral.       *)
    (* ----------------------------------------------------------------------- *)

    let sucivate = 
        let zero = (parse_term @"0")
        let suc = (parse_term @"SUC")
        fun n -> funpow n (curry (Choice.get << mk_comb) suc) zero

    (* ----------------------------------------------------------------------- *)
    (* Eliminate local "definitions" in hyps.                                  *)
    (* ----------------------------------------------------------------------- *)

    let SCRUB_EQUATION eq (th, insts) = 
        (*HA*)
        let eq' = itlist (fun x -> Choice.get << subst x) (map (fun t -> [t]) insts) eq
        let l, r = Choice.get <| dest_eq eq'
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
                match remove (fun h2 -> h2 = h1) s2 with
                | Some (_, s2') ->
                    h1 :: (munion s1' s2')
                | None -> h1 :: (munion s1' s2)
        fun def -> 
            let newtys, rights = unzip def
            let tyargls = itlist ((@) << map snd) rights []
            let alltys = itlist (munion << C subtract newtys) tyargls []
            let epstms = map (fun ty -> mk_select(mk_var("v", ty), t_tm)) alltys
            let pty = 
                try 
                    end_itlist (fun ty1 ty2 -> Choice.get <| mk_type("prod", [ty1; ty2])) 
                        alltys
                with
                | Failure _ -> bool_ty
            let recty = Choice.get <| mk_type("recspace", [pty])
            let constr = Choice.get <| mk_const("CONSTR", [pty, aty])
            let fcons = Choice.get <| mk_const("FCONS", [recty, aty])
            let bot = Choice.get <| mk_const("BOTTOM", [pty, aty])
            let bottail = Choice.get <| mk_abs(n_tm, bot)
            let mk_constructor n (cname, cargs) = 
                let ttys = 
                    map (fun ty -> 
                            if mem ty newtys
                            then recty
                            else ty) cargs
                let args = Choice.get <| make_args "a" [] ttys
                let rargs, iargs = partition (fun t -> Choice.get <| type_of t = recty) args
                let rec mk_injector epstms alltys iargs = 
                    if alltys = []
                    then []
                    else 
                        let ty = hd alltys
                        try 
                            let a, iargs' =  Option.get <| remove (fun t -> Choice.get <| type_of t = ty) iargs
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
                let rarg = itlist (fun x -> Choice.get << mk_binop fcons x) rargs bottail
                let conty = itlist (fun ty -> Choice.get << mk_fun_ty ty) (map (Choice.get << type_of) args) recty
                let condef = 
                    list_mk_comb(constr, [sucivate n
                                          iarg; rarg])
                Choice.get <| mk_eq(mk_var(cname, conty), list_mk_abs(args, condef))
            let rec mk_constructors n rights = 
                if rights = []
                then []
                else 
                    (mk_constructor n (hd rights)) 
                    :: (mk_constructors (n + 1) (tl rights))
            let condefs = mk_constructors 0 (itlist (@) rights [])
            let conths = map ASSUME condefs
            let predty = Choice.get <| mk_fun_ty recty bool_ty
            let edefs = 
                itlist (fun (x, l) acc -> map (fun t -> x, t) l @ acc) def []
            let idefs = 
                map2 (fun (r, (_, atys)) def -> (r, atys), def) edefs condefs
            let mk_rule((r, a), condef) = 
                let left, right = Choice.get <| dest_eq condef
                let args, bod = strip_abs right
                let lapp = list_mk_comb(left, args)
                let conds = 
                    itlist2 (fun arg argty sofar -> 
                            if mem argty newtys
                            then 
                                (Choice.get <| mk_comb(mk_var(Choice.get <| dest_vartype argty, predty), arg)) :: sofar
                            else sofar) args a []
                let conc = Choice.get <| mk_comb(mk_var(Choice.get <| dest_vartype r, predty), lapp)
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
        let imps, bases = partition (is_imp << concl << Choice.get) srules
        let concs = map (concl << Choice.get) bases @ map (Choice.get << rand << concl << Choice.get) imps
        let preds = setify(map (repeat (Choice.get << rator)) concs)
        let rec exhaust_inhabitations ths sofar = 
            let dunnit = setify(map (fst << strip_comb << concl << Choice.get) sofar)
            let useful = 
                filter 
                    (fun th -> not(mem (fst(strip_comb(Choice.get <| rand(concl <| Choice.get th)))) dunnit)) 
                    ths
            if useful = []
            then sofar
            else 
                let follow_horn thm = 
                    let preds = 
                        map (fst << strip_comb) (conjuncts(Choice.get <| lhand(concl <| Choice.get thm)))
                    let asms = 
                        map 
                            (fun p -> 
                                Option.get <| find (fun th -> fst(strip_comb(concl <| Choice.get th)) = p) 
                                    sofar) preds
                    MATCH_MP thm (end_itlist CONJ asms)
                let newth = 
                    tryfind (Some << follow_horn) useful
                    |> Option.getOrFailWith "tryfind"
                exhaust_inhabitations ths (newth :: sofar)
        let ithms = exhaust_inhabitations imps bases
        let exths = 
            map (fun p -> Option.get <| find (fun th -> fst(strip_comb(concl <| Choice.get th)) = p) ithms) 
                preds
        exths
    (* ----------------------------------------------------------------------- *)
    (* Makes a type definition for one of the defined subsets.                 *)
    (* ----------------------------------------------------------------------- *)
    let define_inductive_type cdefs exth = 
        let extm = concl <| Choice.get exth
        let epred = fst(strip_comb extm)
        let ename = fst(Choice.get <| dest_var epred)
        let th1 = ASSUME(Option.get <| find (fun eq -> Choice.get <| lhand eq = epred) (hyp exth))
        let th2 = TRANS th1 (SUBS_CONV cdefs (Choice.get <| rand(concl <| Choice.get th1)))
        let th3 = EQ_MP (AP_THM th2 (Choice.get <| rand extm)) exth
        let th4, _ = itlist SCRUB_EQUATION (hyp th3) (th3, [])
        let mkname = "_mk_" + ename
        let destname = "_dest_" + ename
        let bij1, bij2 = new_basic_type_definition ename (mkname, destname) th4
        let bij2a = AP_THM th2 (Choice.get <| rand(Choice.get <| rand(concl <| Choice.get bij2)))
        let bij2b = TRANS bij2a bij2
        bij1, bij2b

    (* ----------------------------------------------------------------------- *)
    (* Defines a type constructor corresponding to current pseudo-constructor. *)
    (* ----------------------------------------------------------------------- *)

    let define_inductive_type_constructor defs consindex th = 
        let avs, bod = strip_forall(concl <| Choice.get th)
        let asms, conc = 
            if is_imp bod
            then conjuncts(Choice.get <| lhand bod), Choice.get <| rand bod
            else [], bod
        let asmlist = map (Choice.get << dest_comb) asms
        let cpred, cterm = Choice.get <| dest_comb conc
        let oldcon, oldargs = strip_comb cterm
        let modify_arg v = 
            try 
                let dest =
                    // TODO : Give this variable a better name.
                    let x =
                        rev_assoc v asmlist
                        |> Option.getOrFailWith "find"
                    assoc x consindex
                    |> Option.getOrFailWith "find"
                    |> snd
                let ty' = hd(snd(Choice.get <| dest_type(Choice.get <| type_of dest)))
                let v' = mk_var(fst(Choice.get <| dest_var v), ty')
                Choice.get <| mk_comb(dest, v'), v'
            with
            | Failure _ -> v, v
        let newrights, newargs = unzip(map modify_arg oldargs)
        let retmk =
            assoc cpred consindex
            |> Option.getOrFailWith "find"
            |> fst
        let defbod = Choice.get <| mk_comb(retmk, list_mk_comb(oldcon, newrights))
        let defrt = list_mk_abs(newargs, defbod)
        let expth = Option.get <| find (fun th -> Choice.get <| lhand(concl <| Choice.get th) = oldcon) defs
        let rexpth = SUBS_CONV [expth] defrt
        let deflf = mk_var(fst(Choice.get <| dest_var oldcon), Choice.get <| type_of defrt)
        let defth = new_definition(Choice.get <| mk_eq(deflf, Choice.get <| rand(concl <| Choice.get rexpth)))
        TRANS defth (SYM rexpth)

    (* ----------------------------------------------------------------------- *)
    (* Instantiate the induction theorem on the representatives to transfer    *)
    (* it to the new type(s). Uses "\x. rep-pred(x) /\ P(mk x)" for "P".       *)
    (* ----------------------------------------------------------------------- *)

    let instantiate_induction_theorem consindex ith = 
        let avs, bod = strip_forall(concl <| Choice.get ith)
        let corlist = 
            map ((repeat (Choice.get << rator) ||>> repeat (Choice.get << rator)) << Choice.get << dest_imp << Choice.get << body << Choice.get << rand) 
                (conjuncts(Choice.get <| rand bod))
        let consindex' = 
            map (fun v -> 
                    let w =
                        rev_assoc v corlist
                        |> Option.getOrFailWith "find"
                    // TODO : Give this variable a better name.
                    let x =
                        assoc w consindex
                        |> Option.getOrFailWith "find"
                    w, x) avs
        let recty = 
            (hd << snd << Choice.get << dest_type << Choice.get << type_of << fst << snd << hd) consindex
        let newtys = 
            map (hd << snd << Choice.get << dest_type << Choice.get << type_of << snd << snd) consindex'
        let ptypes = map (C (fun ty -> Choice.get << mk_fun_ty ty) bool_ty) newtys
        let preds = Choice.get <| make_args "P" [] ptypes
        let args = Choice.get <| make_args "x" [] (map (K recty) preds)
        let lambs = 
            map2 
                (fun (r, (m, d)) (p, a) ->
                        Choice.get <| mk_abs
                            (a, 
                             mk_conj(Choice.get <| mk_comb(r, a), Choice.get <| mk_comb(p, Choice.get <| mk_comb(m, a))))) 
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
                let ant, con = Choice.get <| dest_imp bimp
                let ths = map (CONV_RULE BETA_CONV) (CONJUNCTS(ASSUME ant))
                let tths, pths = unzip(map CONJ_PAIR ths)
                let tth = MATCH_MP (SPEC_ALL rthm) (end_itlist CONJ tths)
                let mths = map IPRULE (tth :: tths)
                let conth1 = BETA_CONV con
                let contm1 = Choice.get <| rand(concl <| Choice.get conth1)
                let conth2 = 
                    TRANS conth1 
                        (AP_TERM (Choice.get <| rator contm1) 
                             (SUBS_CONV (tl mths) (Choice.get <| rand contm1)))
                let conth3 = PRERULE conth2
                let lctms = map (concl << Choice.get) pths
                let asmin = mk_imp(list_mk_conj lctms, Choice.get <| rand(Choice.get <| rand(concl <| Choice.get conth3)))
                let argsin = map (Choice.get << rand) (conjuncts(Choice.get <| lhand asmin))
                let argsgen = 
                    map (fun tm -> mk_var(fst(Choice.get <| dest_var(Choice.get <| rand tm)), Choice.get <| type_of tm)) 
                        argsin
                let asmgen = Choice.get <| subst (zip argsgen argsin) asmin
                let asmquant = 
                    list_mk_forall(snd(strip_comb(Choice.get <| rand(Choice.get <| rand asmgen))), asmgen)
                let th1 = INST (zip argsin argsgen) (SPEC_ALL(ASSUME asmquant))
                let th2 = MP th1 (end_itlist CONJ pths)
                let th3 = EQ_MP (SYM conth3) (CONJ tth th2)
                DISCH asmquant (GENL avs (DISCH ant th3))
            else 
                let con = bimp
                let conth2 = BETA_CONV con
                let tth = PART_MATCH I rthm (Choice.get <| lhand(Choice.get <| rand(concl <| Choice.get conth2)))
                let conth3 = PRERULE conth2
                let asmgen = Choice.get <| rand(Choice.get <| rand(concl <| Choice.get conth3))
                let asmquant = 
                    list_mk_forall(snd(strip_comb(Choice.get <| rand asmgen)), asmgen)
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
            let av, bimp = Choice.get <| dest_forall(concl <| Choice.get th)
            let pv = Choice.get <| lhand(Choice.get <| body(Choice.get <| rator(Choice.get <| rand bimp)))
            let p, v = Choice.get <| dest_comb pv
            let mk, dest = assoc p consindex |> Option.getOrFailWith "find"
            let ty = hd(snd(Choice.get <| dest_type(Choice.get <| type_of dest)))
            let v' = mk_var(fst(Choice.get <| dest_var v), ty)
            let dv = Choice.get <| mk_comb(dest, v')
            let th1 = PRERULE(SPEC dv th)
            let th2 = MP th1 (REFL(Choice.get <| rand(Choice.get <| lhand(concl <| Choice.get th1))))
            let th3 = CONV_RULE BETA_CONV th2
            GEN v' (FINRULE(CONJUNCT2 th3))

    (* ----------------------------------------------------------------------- *)
    (* Derive the induction theorem.                                           *)
    (* ----------------------------------------------------------------------- *)

    let derive_induction_theorem consindex tybijpairs conthms iith rth = 
        let bths = 
            map2 (pullback_induction_clause tybijpairs conthms) (CONJUNCTS rth) 
                (conjuncts(Choice.get <| lhand(concl <| Choice.get iith)))
        let asm = list_mk_conj(map (Choice.get << lhand << concl <<Choice.get) bths)
        let ths = map2 MP bths (CONJUNCTS(ASSUME asm))
        let th1 = MP iith (end_itlist CONJ ths)
        let th2 = 
            end_itlist CONJ 
                (map (finish_induction_conclusion consindex tybijpairs) 
                     (CONJUNCTS th1))
        let th3 = DISCH asm th2
        let preds = map (Choice.get << rator << Choice.get << body << Choice.get << rand) (conjuncts(Choice.get <| rand(concl <| Choice.get th3)))
        let th4 = GENL preds th3
        let pasms = filter (C mem (map fst consindex) << Choice.get << lhand) (hyp th4)
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
            map (hd << snd << Choice.get << dest_type << Choice.get << type_of << snd << snd) consindex
        let recty = 
            (hd << snd << Choice.get << dest_type << Choice.get << type_of << fst << snd << hd) consindex
        let ranty = mk_vartype "Z"
        let fn = mk_var("fn", Choice.get <| mk_fun_ty recty ranty)
        let fns = Choice.get <| make_args "fn" [] (map (C (fun ty -> Choice.get << mk_fun_ty ty) ranty) domtys)
        let args = Choice.get <| make_args "a" [] domtys
        let rights = 
            map2 (fun (_, (_, d)) a -> Choice.get <| mk_abs(a, Choice.get <| mk_comb(fn, Choice.get <| mk_comb(d, a)))) consindex 
                args
        let eqs = map2 (curry (Choice.get << mk_eq)) fns rights
        let fdefs = map ASSUME eqs
        let fxths1 = 
            map (fun th1 -> tryfind (fun th2 -> Choice.toOption <| MK_COMB(th2, th1)) fdefs
                            |> Option.toChoiceWithError "tryfind") 
                conthms
        let fxths2 = map (fun th -> TRANS th (BETA_CONV(Choice.get <| rand(concl <| Choice.get th)))) fxths1
        let mk_tybijcons(th1, th2) = 
            let th3 = INST [Choice.get <| rand(Choice.get <| lhand(concl <| Choice.get th1)), Choice.get <| rand(Choice.get <| lhand(concl <| Choice.get th2))] th2
            let th4 = AP_TERM (Choice.get <| rator(Choice.get <| lhand(Choice.get <| rand(concl <| Choice.get th2)))) th1
            EQ_MP (SYM th3) th4
        let SCONV = GEN_REWRITE_CONV I (map mk_tybijcons tybijpairs)
        let ERULE = GEN_REWRITE_RULE I (map snd tybijpairs)
        let simplify_fxthm rthm fxth = 
            let pat = funpow 4 (Choice.get << rand) (concl <| Choice.get fxth)
            if is_imp(repeat (snd << Choice.get << dest_forall) (concl <| Choice.get rthm))
            then 
                let th1 = PART_MATCH (Choice.get << rand << Choice.get << rand) rthm pat
                let tms1 = conjuncts(Choice.get <| lhand(concl <| Choice.get th1))
                let ths2 = map (fun t -> EQ_MP (SYM(SCONV t)) TRUTH) tms1
                ERULE(MP th1 (end_itlist CONJ ths2))
            else ERULE(PART_MATCH (Choice.get << rand) rthm pat)
        let fxths3 = map2 simplify_fxthm (CONJUNCTS rth) fxths2
        let fxths4 = map2 (fun th1 -> TRANS th1 << AP_TERM fn) fxths2 fxths3
        let cleanup_fxthm cth fxth = 
            let tms = snd(strip_comb(Choice.get <| rand(Choice.get <| rand(concl <| Choice.get fxth))))
            let kth = RIGHT_BETAS tms (ASSUME(hd(hyp cth)))
            TRANS fxth (AP_TERM fn kth)
        let fxth5 = end_itlist CONJ (map2 cleanup_fxthm conthms fxths4)
        let pasms = filter (C mem (map fst consindex) << Choice.get << lhand) (hyp fxth5)
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
                let tup' = Choice.get <| rand(concl <| Choice.get PAIR_th)
                if tup' = v
                then PAIR_th
                else 
                    let th = extract_arg (Choice.get <| rand(concl <| Choice.get PAIR_th)) v
                    SUBS [SYM PAIR_th] th
        fun consindex -> 
            let recty = hd(snd(Choice.get <| dest_type(Choice.get <| type_of(fst(hd consindex)))))
            let domty = hd(snd(Choice.get <| dest_type recty))
            let i = mk_var("i", domty)
            let r = mk_var("r", Choice.get <| mk_fun_ty numty recty)
            let mks = map (fst << snd) consindex
            let mkindex = 
                map (fun t -> hd(tl(snd(Choice.get <| dest_type(Choice.get <| type_of t)))), t) mks
            fun cth -> 
                let artms = snd(strip_comb(Choice.get <| rand(Choice.get <| rand(concl <| Choice.get cth))))
                let artys = mapfilter (Choice.toOption << Choice.bind type_of << rand) artms
                let args, bod = strip_abs(Choice.get <| rand(hd(hyp cth)))
                let ccitm, rtm = Choice.get <| dest_comb bod
                let cctm, itm = Choice.get <| dest_comb ccitm
                let rargs, iargs = partition (C free_in rtm) args
                let xths = map (extract_arg itm) iargs
                let cargs' = map (Choice.get << subst [i, itm] << Choice.get << lhand << concl <<Choice.get) xths
                let indices = map sucivate (0 -- (length rargs - 1))
                let rindexed = map (curry (Choice.get << mk_comb) r) indices
                let rargs' = 
                    map2 (fun a rx -> Choice.get <| mk_comb(Option.getOrFailWith "find" <| assoc a mkindex, rx)) artys 
                        rindexed
                let sargs' = map (curry (Choice.get << mk_comb) s) indices
                let allargs = cargs' @ rargs' @ sargs'
                let funty = itlist ((fun ty -> Choice.get << mk_fun_ty ty) << Choice.get << type_of) allargs zty
                let funname = 
                    fst(Choice.get <| dest_const(repeat (Choice.get << rator) (Choice.get <| lhand(concl <| Choice.get cth)))) + "'"
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
            let ty = Choice.get <| type_of(hd isocons)
            let fcons = Choice.get <| mk_const("FCONS", [ty, aty])
            let fnil = Choice.get <| mk_const("FNIL", [ty, aty])
            let bigfun = itlist (fun x -> Choice.get << mk_binop fcons x) isocons fnil
            let eth = ISPEC bigfun CONSTR_REC
            let fn = Choice.get <| rator(Choice.get <| rand(hd(conjuncts(concl <| Choice.get rath))))
            let betm = 
                let v, bod = Choice.get <| dest_abs(Choice.get <| rand(concl <| Choice.get eth))
                Choice.get <| vsubst [fn, v] bod
            let LCONV = REWR_CONV(ASSUME betm)
            let fnths = 
                map (fun t -> RIGHT_BETAS [Choice.get <| bndvar(Choice.get <| rand t)] (ASSUME t)) 
                    (hyp rath)
            let SIMPER = 
                PURE_REWRITE_RULE
                    (map SYM fnths 
                     @ map fst tybijpairs @ [FST; SND; FCONS; BETA_THM])
            let hackdown_rath th = 
                let ltm, rtm = Choice.get <| dest_eq(concl <| Choice.get th)
                let wargs = snd(strip_comb(Choice.get <| rand ltm))
                let th1 = TRANS th (LCONV rtm)
                let th2 = TRANS th1 (CCONV(Choice.get <| rand(concl <| Choice.get th1)))
                let th3 = 
                    TRANS th2 (funpow 2 RATOR_CONV BETA_CONV (Choice.get <| rand(concl <| Choice.get th2)))
                let th4 = TRANS th3 (RATOR_CONV BETA_CONV (Choice.get <| rand(concl <| Choice.get th3)))
                let th5 = TRANS th4 (BETA_CONV(Choice.get <| rand(concl <| Choice.get th4)))
                GENL wargs (SIMPER th5)
            let rthm = end_itlist CONJ (map hackdown_rath (CONJUNCTS rath))
            let seqs = 
                let unseqs = filter is_eq (hyp rthm)
                let tys = 
                    map (hd << snd << Choice.get << dest_type << Choice.get << type_of << snd << snd) 
                        consindex
                map 
                    (fun ty -> 
                        Option.get <| find (fun t -> hd(snd(Choice.get <| dest_type(Choice.get <| type_of(Choice.get <| lhand t)))) = ty) unseqs) tys
            let rethm = itlist EXISTS_EQUATION seqs rthm
            let fethm = CHOOSE (fn, eth) rethm
            let pcons = 
                map (repeat (Choice.get << rator) << Choice.get << rand << repeat(snd << Choice.get << dest_forall)) 
                    (conjuncts(concl <| Choice.get rthm))
            GENL pcons fethm
    fun def -> 
        (* ----------------------------------------------------------------------- *)
        (* Basic function: returns induction and recursion separately. No parser.  *)
        (* ----------------------------------------------------------------------- *)
        let defs, rth, ith = justify_inductive_type_model def
        let neths = prove_model_inhabitation rth
        let tybijpairs = map (define_inductive_type defs) neths
        let preds = map (repeat (Choice.get << rator) << concl <<Choice.get) neths
        let mkdests = 
            map (fun (th, _) -> 
                    let tm = Choice.get <| lhand(concl <| Choice.get th)
                    Choice.get <| rator tm, Choice.get <| rator(Choice.get <| rand tm)) tybijpairs
        let consindex = zip preds mkdests
        let condefs = 
            map (define_inductive_type_constructor defs consindex) 
                (CONJUNCTS rth)
        let conthms = 
            map (fun th -> 
                    let args = fst(strip_abs(Choice.get <| rand(concl <| Choice.get th)))
                    RIGHT_BETAS args th) condefs
        let iith = instantiate_induction_theorem consindex ith
        let fth = derive_induction_theorem consindex tybijpairs conthms iith rth
        let rath = create_recursive_functions tybijpairs consindex conthms rth
        let kth = derive_recursion_theorem tybijpairs consindex conthms rath
        fth, kth

(* ------------------------------------------------------------------------- *)
(* Parser to present a nice interface a la Melham.                           *)
(* ------------------------------------------------------------------------- *)

/// Parses the specification for an inductive type into a structured format.
let parse_inductive_type_specification = 
    let parse_type_loc src = 
        let pty, rst = parse_pretype src
        Choice.get <| type_of_pretype pty, rst
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
    new_recursive_definition sum_RECURSION (parse_term @"OUTR (INR y :A+B) = y");;

(* ------------------------------------------------------------------------- *)
(* Generalize the recursion theorem to multiple domain types.                *)
(* (We needed to use a single type to justify it via a proforma theorem.)    *)
(*                                                                           *)
(* NB! Before this is called nontrivially (i.e. more than one new type)      *)
(*     the type constructor ":sum", used internally, must have been defined. *)
(* ------------------------------------------------------------------------- *)

// CAUTION: change to bypass value restrictions
let define_type_raw_002 = 
    let generalize_recursion_theorem = 
        let ELIM_OUTCOMBS = GEN_REWRITE_RULE TOP_DEPTH_CONV [OUTL; OUTR]
        let rec mk_sum tys = 
            let k = length tys
            if k = 1
            then hd tys
            else 
                let tys1, tys2 = chop_list (k / 2) tys
                Choice.get <| mk_type("sum", [mk_sum tys1; mk_sum tys2])
        let mk_inls = 
            let rec mk_inls ty = 
                if is_vartype ty
                then [mk_var("x", ty)]
                else 
                    match Choice.get <| dest_type ty with
                    | _, [ty1; ty2] -> 
                        let inls1 = mk_inls ty1
                        let inls2 = mk_inls ty2
                        let inl = 
                            Choice.get <| mk_const("INL", [ty1, aty; ty2, bty])
                        let inr = 
                            Choice.get <| mk_const("INR", [ty1, aty; ty2, bty])
                        map (curry (Choice.get << mk_comb) inl) inls1 
                        @ map (curry (Choice.get << mk_comb) inr) inls2
                    | _ -> failwith "mk_inls: Unhnadled case."
            fun ty -> 
                let bods = mk_inls ty
                map (fun t -> Choice.get <| mk_abs(Choice.get <| find_term is_var t, t)) bods
        let mk_outls = 
            let rec mk_inls sof ty = 
                if is_vartype ty
                then [sof]
                else 
                    match Choice.get <| dest_type ty with
                    | _, [ty1; ty2] ->
                        let outl = 
                            Choice.get <| mk_const("OUTL", [ty1, aty; ty2, bty])
                        let outr = 
                            Choice.get <| mk_const("OUTR", [ty1, aty; ty2, bty])
                        mk_inls (Choice.get <| mk_comb(outl, sof)) ty1 
                        @ mk_inls (Choice.get <| mk_comb(outr, sof)) ty2
                    | _ -> failwith "mk_outls: Unhandled case."
            fun ty -> 
                let x = mk_var("x", ty)
                map (curry (Choice.get << mk_abs) x) (mk_inls x ty)
        let mk_newfun fn outl = 
            let s, ty = Choice.get <| dest_var fn
            let dty = hd(snd(Choice.get <| dest_type ty))
            let x = mk_var("x", dty)
            let y, bod = Choice.get <| dest_abs outl
            let r = Choice.get <| mk_abs(x, Choice.get <| vsubst [Choice.get <| mk_comb(fn, x), y] bod)
            let l = mk_var(s, Choice.get <| type_of r)
            let th1 = ASSUME(Choice.get <| mk_eq(l, r))
            RIGHT_BETAS [x] th1
        fun th -> 
            let avs, ebod = strip_forall(concl <| Choice.get th)
            let evs, bod = strip_exists ebod
            let n = length evs
            if n = 1
            then th
            else 
                let tys = 
                    map (fun i -> mk_vartype("Z" + (string i))) 
                        (0 -- (n - 1))
                let sty = mk_sum tys
                let inls = mk_inls sty
                let outls = mk_outls sty
                let zty = Choice.get <| type_of(Choice.get <| rand(snd(strip_forall(hd(conjuncts bod)))))
                let ith = INST_TYPE [sty, zty] th
                let avs, ebod = strip_forall(concl <| Choice.get ith)
                let evs, bod = strip_exists ebod
                let fns' = map2 mk_newfun evs outls
                let fnalist = zip evs (map (Choice.get << rator << Choice.get << lhs << concl <<Choice.get) fns')
                let inlalist = zip evs inls
                let outlalist = zip evs outls
                let hack_clause tm = 
                    let avs, bod = strip_forall tm
                    let l, r = Choice.get <| dest_eq bod
                    let fn, args = strip_comb r
                    let pargs = 
                        map (fun a -> 
                                let g = genvar(Choice.get <| type_of a)
                                if is_var a
                                then g, g
                                else 
                                    let outl = assoc (Choice.get <| rator a) outlalist |> Option.getOrFailWith "find"
                                    Choice.get <| mk_comb(outl, g), g) args
                    let args', args'' = unzip pargs
                    let inl = assoc (Choice.get <| rator l) inlalist |> Option.getOrFailWith "find"
                    let rty = hd(snd(Choice.get <| dest_type(Choice.get <| type_of inl)))
                    let nty = itlist ((fun ty -> Choice.get << mk_fun_ty ty) << Choice.get << type_of) args' rty
                    let fn' = mk_var(fst(Choice.get <| dest_var fn), nty)
                    let r' = 
                        list_mk_abs
                            (args'', Choice.get <| mk_comb(inl, list_mk_comb(fn', args')))
                    r', fn
                let defs = map hack_clause (conjuncts bod)
                let jth = BETA_RULE(SPECL (map fst defs) ith)
                let bth = ASSUME(snd(strip_exists(concl <| Choice.get jth)))
                let finish_clause th = 
                    let avs, bod = strip_forall(concl <| Choice.get th)
                    let outl = assoc (Choice.get <| rator(Choice.get <| lhand bod)) outlalist |> Option.getOrFailWith "find"
                    GENL avs (BETA_RULE(AP_TERM outl (SPECL avs th)))
                let cth = end_itlist CONJ (map finish_clause (CONJUNCTS bth))
                let dth = ELIM_OUTCOMBS cth
                let eth = GEN_REWRITE_RULE ONCE_DEPTH_CONV (map SYM fns') dth
                let fth = itlist SIMPLE_EXISTS (map snd fnalist) eth
                let dtms = map (hd << hyp) fns'
                let gth = 
                    itlist (fun e th -> 
                            let l, r = Choice.get <| dest_eq e
                            MP (INST [r, l] (DISCH e th)) (REFL r)) dtms fth
                let hth = PROVE_HYP jth (itlist SIMPLE_CHOOSE evs gth)
                let xvs = 
                    map (fst << strip_comb << Choice.get << rand << snd << strip_forall) 
                        (conjuncts(concl <| Choice.get eth))
                GENL xvs hth
    fun def ->
        let ith, rth = define_type_raw_001 def
        ith, generalize_recursion_theorem rth;;

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

/// Proves that the constructors of an automatically-defined concrete type are injective.
let prove_constructors_injective = 
    let DEPAIR = GEN_REWRITE_RULE TOP_SWEEP_CONV [PAIR_EQ]
    let prove_distinctness ax pat = 
        let f, args = strip_comb pat
        let rt = end_itlist (curry mk_pair) args
        let ty = Choice.get <| mk_fun_ty (Choice.get <| type_of pat) (Choice.get <| type_of rt)
        let fn = genvar ty
        let dtm = Choice.get <| mk_eq(Choice.get <| mk_comb(fn, pat), rt)
        let eth = prove_recursive_functions_exist ax (list_mk_forall(args, dtm))
        let args' = Choice.get <| variants args args
        let atm = Choice.get <| mk_eq(pat, list_mk_comb(f, args'))
        let ath = ASSUME atm
        let bth = AP_TERM fn ath
        let cth1 = SPECL args (ASSUME(snd(Choice.get <| dest_exists(concl <| Choice.get eth))))
        let cth2 = INST (zip args' args) cth1
        let pth = TRANS (TRANS (SYM cth1) bth) cth2
        let qth = DEPAIR pth
        let qtm = concl <| Choice.get qth
        let rth = rev_itlist (C(curry MK_COMB)) (CONJUNCTS(ASSUME qtm)) (REFL f)
        let tth = IMP_ANTISYM_RULE (DISCH atm qth) (DISCH qtm rth)
        let uth = GENL args (GENL args' tth)
        PROVE_HYP eth (SIMPLE_CHOOSE fn uth)
    fun ax -> 
        let cls = conjuncts(snd(strip_exists(snd(strip_forall(concl <| Choice.get ax)))))
        let pats = map (Choice.get << rand << Choice.get << lhand << snd << strip_forall) cls
        end_itlist CONJ (mapfilter (Some << prove_distinctness ax) pats);;

/// Proves that the constructors of an automatically-dened concrete type yield distinct values.
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
            genvar(Choice.get <| mk_type("fun", [Choice.get <| type_of(hd pat); num_ty]))
        let ls = map (curry (Choice.get << mk_comb) fn) pat
        let defs = 
            map2 (fun l r -> list_mk_forall(frees(Choice.get <| rand l), Choice.get <| mk_eq(l, r))) ls nums
        let eth = prove_recursive_functions_exist ax (list_mk_conj defs)
        let ev, bod = Choice.get <| dest_exists(concl <| Choice.get eth)
        let REWRITE = GEN_REWRITE_RULE ONCE_DEPTH_CONV (CONJUNCTS(ASSUME bod))
        let pat' = 
            map (fun t -> 
                    let f, args = 
                        if is_numeral t
                        then t, []
                        else strip_comb t
                    list_mk_comb(f, Choice.get <| variants args args)) pat
        let pairs = allopairs (curry (Choice.get << mk_eq)) pat pat'
        let nths = map (REWRITE << AP_TERM fn << ASSUME) pairs
        let fths = 
            map2 (fun t th -> NEGATE(DISCH t (CONV_RULE NUM_EQ_CONV th))) pairs 
                nths
        CONJUNCTS(PROVE_HYP eth (SIMPLE_CHOOSE ev (end_itlist CONJ fths)))
    fun ax -> 
        let cls = conjuncts(snd(strip_exists(snd(strip_forall(concl <| Choice.get ax)))))
        let lefts = map (Choice.get << dest_comb << Choice.get << lhand << snd << strip_forall) cls
        let fns = itlist (insert << fst) lefts []
        let pats = map (fun f -> map snd (filter ((=) f << fst) lefts)) fns
        end_itlist CONJ (end_itlist (@) (mapfilter (Some << prove_distinct ax) pats));;

(* ------------------------------------------------------------------------- *)
(* Automatically prove the case analysis theorems.                           *)
(* ------------------------------------------------------------------------- *)

/// Proves a structural cases theorem for an automatically-defined concrete type.
let prove_cases_thm = 
    let mk_exclauses x rpats = 
        let xts = map (fun t -> list_mk_exists(frees t, Choice.get <| mk_eq(x, t))) rpats
        Choice.get <| mk_abs(x, list_mk_disj xts)
    let prove_triv tm = 
        let evs, bod = strip_exists tm
        let l, r = Choice.get <| dest_eq bod
        if l = r
        then REFL l
        else 
            let lf, largs = strip_comb l
            let rf, rargs = strip_comb r
            if lf = rf
            then 
                let ths = map (ASSUME << Choice.get << mk_eq) (zip rargs largs)
                let th1 = rev_itlist (C(curry MK_COMB)) ths (REFL lf)
                itlist EXISTS_EQUATION (map (concl << Choice.get) ths) (SYM th1)
            else failwith "prove_triv"
    let rec prove_disj tm = 
        if is_disj tm
        then 
            let l, r = Choice.get <| dest_disj tm
            try 
                DISJ1 (prove_triv l) r
            with
            | Failure _ -> DISJ2 l (prove_disj r)
        else prove_triv tm
    let prove_eclause tm = 
        let avs, bod = strip_forall tm
        let ctm = 
            if is_imp bod
            then Choice.get <| rand bod
            else bod
        let cth = prove_disj ctm
        let dth = 
            if is_imp bod
            then DISCH (Choice.get <| lhand bod) cth
            else cth
        GENL avs dth
    fun th -> 
        let avs, bod = strip_forall(concl <| Choice.get th)
        let cls = map (snd << strip_forall) (conjuncts(Choice.get <| lhand bod))
        let pats = 
            map (fun t -> 
                    if is_imp t
                    then Choice.get <| rand t
                    else t) cls
        let spats = map (Choice.get << dest_comb) pats
        let preds = itlist (insert << fst) spats []
        let rpatlist = 
            map (fun pr -> map snd (filter (fun (p, x) -> p = pr) spats)) preds
        let xs = Choice.get <| make_args "x" (freesl pats) (map (Choice.get << type_of << hd) rpatlist)
        let xpreds = map2 mk_exclauses xs rpatlist
        let ith = BETA_RULE(INST (zip xpreds preds) (SPEC_ALL th))
        let eclauses = conjuncts(fst(Choice.get <| dest_imp(concl <| Choice.get ith)))
        MP ith (end_itlist CONJ (map prove_eclause eclauses));;

inductive_type_store 
:= ["list", (2, list_INDUCT, list_RECURSION)
    "option", (2, option_INDUCT, option_RECURSION)
    "sum", (2, sum_INDUCT, sum_RECURSION)] @ (!inductive_type_store);;

(* ------------------------------------------------------------------------- *)
(* Now deal with nested recursion. Need a store of previous theorems.        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Also add a cached rewrite of distinctness and injectivity theorems. Since *)
(* there can be quadratically many distinctness clauses, it would really be  *)
(* preferable to have a conversion, but this seems OK up 100 constructors.   *)
(* ------------------------------------------------------------------------- *)

/// Net of injectivity and distinctness properties for recursive type constructors.
let basic_rectype_net = ref empty_net

/// Internal theorem list of distinctness theorems.
let distinctness_store = ref ["bool", TAUT(parse_term @"(T <=> F) <=> F")]
/// Internal theorem list of injectivity theorems.
let injectivity_store = ref []

/// Extends internal store of distinctness and injectivity theorems for a new inductive type.
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
    distinctness_store := map (fun th -> tyname, th) ths1 @ (!distinctness_store)
    injectivity_store := map (fun th -> tyname, th) ths2 @ (!injectivity_store)
    basic_rectype_net := itlist (net_of_thm true) canon_thl (!basic_rectype_net)

do_list extend_rectype_net (!inductive_type_store);;

(* ------------------------------------------------------------------------- *)
(* Return distinctness and injectivity for a type by simple lookup.          *)
(* ------------------------------------------------------------------------- *)

/// Produce distinctness theorem for an inductive type.
let distinctness ty =
    assoc ty (!distinctness_store)
    |> Option.getOrFailWith "find"

/// Produce injectivity theorem for an inductive type.
let injectivity ty =
    assoc ty (!injectivity_store)
    |> Option.getOrFailWith "find"

/// Produce cases theorem for an inductive type.
let cases ty = 
    if ty = "num"
    then num_CASES
    else 
        let _, ith, _ =
            assoc ty (!inductive_type_store)
            |> Option.getOrFailWith "find"
        prove_cases_thm ith

(* ------------------------------------------------------------------------- *)
(* Convenient definitions for type isomorphism.                              *)
(* ------------------------------------------------------------------------- *)

let ISO = 
    new_definition
        (parse_term @"ISO (f:A->B) (g:B->A) <=> (!x. f(g x) = x) /\ (!y. g(f y) = y)");;

let ISO_REFL = prove((parse_term @"ISO (\x:A. x) (\x. x)"), REWRITE_TAC [ISO])

let ISO_FUN = 
    prove
        ((parse_term @"ISO (f:A->A') f' /\ ISO (g:B->B') g'
     ==> ISO (\h a'. g(h(f' a'))) (\h a. g'(h(f a)))"),
         REWRITE_TAC [ISO; FUN_EQ_THM]
         |> THEN <| MESON_TAC [])

let ISO_USAGE = prove((parse_term @"ISO f g
   ==> (!P. (!x. P x) <=> (!x. P(g x))) /\
       (!P. (?x. P x) <=> (?x. P(g x))) /\
       (!a b. (a = g b) <=> (f a = b))"), REWRITE_TAC [ISO; FUN_EQ_THM]
                                          |> THEN <| MESON_TAC [])

(* ------------------------------------------------------------------------- *)
(* Hence extend type definition to nested types.                             *)
(* ------------------------------------------------------------------------- *)

/// <summary>
/// Like <see cref="define_type"/> but from a more structured representation than a string.
/// </summary>
let define_type_raw = 
    (* ----------------------------------------------------------------------- *)
    (* Dispose of trivial antecedent.                                          *)
    (* ----------------------------------------------------------------------- *)

    let TRIV_ANTE_RULE = 
        let TRIV_IMP_CONV tm = 
            let avs, bod = strip_forall tm
            let bth = 
                if is_eq bod
                then REFL(Choice.get <| rand bod)
                else 
                    let ant, con = Choice.get <| dest_imp bod
                    let ith = SUBS_CONV (CONJUNCTS(ASSUME ant)) (Choice.get <| lhs con)
                    DISCH ant ith
            GENL avs bth
        fun th -> 
            let tm = concl <| Choice.get th
            if is_imp tm
            then 
                let ant, con = Choice.get <| dest_imp(concl <| Choice.get th)
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
            map (hd << snd << Choice.get << dest_type << Choice.get << type_of << Choice.get << lhand << concl <<Choice.get) iths

        match assoc cty (zip itys iths) with
        | Some x -> x
        | None ->
            if not(exists (C occurs_in cty) itys)
            then INST_TYPE [cty, aty] ISO_REFL
            else 
                let tycon, isotys = Choice.get <| dest_type cty
                if tycon = "fun"
                then 
                    MATCH_MP ISO_FUN 
                        (end_itlist CONJ 
                             (map (lift_type_bijections iths) isotys))
                else 
                    failwith
                        ("lift_type_bijections: Unexpected type operator \"" 
                         + tycon + "\"")

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
            if not(is_exists(concl <| Choice.get th))
            then [], th
            else 
                let th1 = USE_PTH th
                let v1 = Choice.get <| rand(Choice.get <| rand(concl <| Choice.get th1))
                let gv = genvar(Choice.get <| type_of v1)
                let th2 = CONV_RULE BETA_CONV (UNDISCH(INST [gv, v1] th1))
                let vs, th3 = DE_EXISTENTIALIZE_RULE th2
                gv :: vs, th3
        DE_EXISTENTIALIZE_RULE
    let grab_type = Choice.get << type_of << Choice.get << rand << Choice.get << lhand << snd << strip_forall
    let clause_corresponds cl0 = 
        let f0, ctm0 = Choice.get <| dest_comb(Choice.get <| lhs cl0)
        let c0 = fst(Choice.get <| dest_const(fst(strip_comb ctm0)))
        let dty0, rty0 = Choice.get <| dest_fun_ty(Choice.get <| type_of f0)
        fun cl1 -> 
            let f1, ctm1 = Choice.get <| dest_comb(Choice.get <| lhs cl1)
            let c1 = fst(Choice.get <| dest_const(fst(strip_comb ctm1)))
            let dty1, rty1 = Choice.get <| dest_fun_ty(Choice.get <| type_of f1)
            c0 = c1 && dty0 = rty1 && rty0 = dty1
    let prove_inductive_types_isomorphic n k (ith0, rth0) (ith1, rth1) = 
        let sth0 = SPEC_ALL rth0
        let sth1 = SPEC_ALL rth1
        let t_tm = concl <| Choice.get TRUTH
        let pevs0, pbod0 = strip_exists(concl <| Choice.get sth0)
        let pevs1, pbod1 = strip_exists(concl <| Choice.get sth1)
        let pcjs0, qcjs0 = chop_list k (conjuncts pbod0)
        let pcjs1, qcjs1 = chop_list k (snd(chop_list n (conjuncts pbod1)))
        let tyal0 = setify(zip (map grab_type pcjs1) (map grab_type pcjs0))
        let tyal1 = map (fun (a, b) -> (b, a)) tyal0
        let tyins0 = 
            map (fun f -> 
                    let domty, ranty = Choice.get <| dest_fun_ty(Choice.get <| type_of f)
                    Choice.get <| tysubst tyal0 domty, ranty) pevs0
        let tyins1 = 
            map (fun f -> 
                    let domty, ranty = Choice.get <| dest_fun_ty(Choice.get <| type_of f)
                    Choice.get <| tysubst tyal1 domty, ranty) pevs1
        let tth0 = INST_TYPE tyins0 sth0
        let tth1 = INST_TYPE tyins1 sth1
        let evs0, bod0 = strip_exists(concl <| Choice.get tth0)
        let evs1, bod1 = strip_exists(concl <| Choice.get tth1)
        let lcjs0, rcjs0 = 
            chop_list k (map (snd << strip_forall) (conjuncts bod0))
        let lcjs1, rcjsx = 
            chop_list k 
                (map (snd << strip_forall) (snd(chop_list n (conjuncts bod1))))
        let rcjs1 = map (fun t -> Option.get <| find (clause_corresponds t) rcjsx) rcjs0
        let proc_clause tm0 tm1 = 
            let l0, r0 = Choice.get <| dest_eq tm0
            let l1, r1 = Choice.get <| dest_eq tm1
            let vc0, wargs0 = strip_comb r0
            let con0, vargs0 = strip_comb(Choice.get <| rand l0)
            let gargs0 = map (genvar << Choice.get << type_of) wargs0
            let nestf0 =
                map 
                    (fun a -> 
                        Option.isSome <| find(fun t -> is_comb t && Choice.get <| rand t = a) wargs0) 
                    vargs0
            let targs0 = 
                map2 (fun a f -> 
                        if f
                        then Option.get <| find (fun t -> is_comb t && Choice.get <| rand t = a) wargs0
                        else a) vargs0 nestf0
            let gvlist0 = zip wargs0 gargs0
            let xargs =
                targs0
                |> map (fun v ->
                    assoc v gvlist0
                    |> Option.getOrFailWith "find")
            let inst0 = 
                list_mk_abs
                    (gargs0, list_mk_comb(fst(strip_comb(Choice.get <| rand l1)), xargs)), vc0
            let vc1, wargs1 = strip_comb r1
            let con1, vargs1 = strip_comb(Choice.get <| rand l1)
            let gargs1 = map (genvar << Choice.get << type_of) wargs1
            let targs1 = 
                map2 (fun a f -> 
                        if f
                        then Option.get <| find (fun t -> is_comb t && Choice.get <| rand t = a) wargs1
                        else a) vargs1 nestf0
            let gvlist1 = zip wargs1 gargs1
            let xargs =
                targs1
                |> map (fun v ->
                    assoc v gvlist1
                    |> Option.getOrFailWith "find")
            let inst1 = 
                list_mk_abs
                    (gargs1, list_mk_comb(fst(strip_comb(Choice.get <| rand l0)), xargs)), vc1
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
                    Option.get <| find 
                        (fun t2 -> 
                            hd(tl(snd(Choice.get <| dest_type(Choice.get <| type_of t1)))) = hd
                                                                     (snd
                                                                          (Choice.get <| dest_type
                                                                               (Choice.get <| type_of 
                                                                                    t2)))) 
                        efvs1) efvs0
        let isotms = 
            map2 (fun ff gg -> Choice.get <| list_mk_icomb "ISO" [ff; gg]) efvs0 efvs2
        let ctm = list_mk_conj isotms
        let cth1 = ISO_EXPAND_CONV ctm
        let ctm1 = Choice.get <| rand(concl <| Choice.get cth1)
        let cjs = conjuncts ctm1
        let eee = map (fun n -> n mod 2 = 0) (0 -- (length cjs - 1))
        let cjs1, cjs2 = partition fst (zip eee cjs)
        let ctm2 = 
            mk_conj(list_mk_conj(map snd cjs1), list_mk_conj(map snd cjs2))
        let DETRIV_RULE = TRIV_ANTE_RULE << REWRITE_RULE [sth0; sth1]
        let jth0 = 
            let itha = SPEC_ALL ith0
            let icjs = conjuncts(Choice.get <| rand(concl <| Choice.get itha))
            let cinsts = 
                map (fun tm -> tryfind (fun vtm -> Some <| term_match [] vtm tm) icjs
                               |> Option.getOrFailWith "tryfind") 
                    (conjuncts(Choice.get <| rand ctm2))
            let tvs = 
                subtract (fst(strip_forall(concl <| Choice.get ith0))) 
                    (itlist (fun (_, x, _) -> union(map snd x)) cinsts [])
            let ctvs = 
                map (fun p -> 
                        let x = mk_var("x", hd(snd(Choice.get <| dest_type(Choice.get <| type_of p))))
                        Choice.get <| mk_abs(x, t_tm), p) tvs
            DETRIV_RULE(INST ctvs (itlist INSTANTIATE cinsts itha))
        let jth1 = 
            let itha = SPEC_ALL ith1
            let icjs = conjuncts(Choice.get <| rand(concl <| Choice.get itha))
            let cinsts = 
                map (fun tm -> tryfind (fun vtm -> Some <| term_match [] vtm tm) icjs
                               |> Option.getOrFailWith "tryfind") 
                    (conjuncts(Choice.get <| lhand ctm2))
            let tvs = 
                subtract (fst(strip_forall(concl <| Choice.get ith1))) 
                    (itlist (fun (_, x, _) -> union(map snd x)) cinsts [])
            let ctvs = 
                map (fun p -> 
                        let x = mk_var("x", hd(snd(Choice.get <| dest_type(Choice.get <| type_of p))))
                        Choice.get <| mk_abs(x, t_tm), p) tvs
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
            Option.get <| find (fun t -> 
                    let x = Choice.get <| lhs t
                    forall (fun u -> not(free_in x (Choice.get <| rand u))) hyps) hyps
        let l, r = Choice.get <| dest_eq eqn
        MP (INST [r, l] (DISCH eqn th)) (REFL r)
    let define_type_basecase def = 
        let add_id s = fst(Choice.get <| dest_var(genvar bool_ty))
        let def' = map (I ||>> (map(add_id ||>> I))) def
        define_type_raw_002 def'
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
        match rev_assoc ty alist with
        | Some x -> x
        | None ->
            try 
                let tycon, tyargs = Choice.get <| dest_type ty
                Choice.get <| mk_type(tycon, map (modify_type alist) tyargs)
            with
            | Failure _ -> ty
    let modify_item alist (s, l) = s, map (modify_type alist) l
    let modify_clause alist (l, lis) = l, map (modify_item alist) lis
    let recover_clause id tm = 
        let con, args = strip_comb tm
        fst(Choice.get <| dest_const con) + id, map (Choice.get << type_of) args
    let rec create_auxiliary_clauses nty = 
        let id = fst(Choice.get <| dest_var(genvar bool_ty))
        let tycon, tyargs = Choice.get <| dest_type nty
        let k, ith, rth =
            match assoc tycon !inductive_type_store with
            | Some x -> x
            | None ->
                failwith("Can't Option.get <| find definition for nested type: " + tycon)
        let evs, bod = strip_exists(snd(strip_forall(concl <| Choice.get rth)))
        let cjs = map (Choice.get << lhand << snd << strip_forall) (conjuncts bod)
        let rtys = map (hd << snd << Choice.get << dest_type << Choice.get << type_of) evs
        let tyins = tryfind (fun vty -> Choice.toOption <| type_match vty nty []) rtys |> Option.getOrFailWith "tryfind"
        let cjs' = map (Choice.get << inst tyins << Choice.get << rand) (fst(chop_list k cjs))
        let mtys = itlist (insert << Choice.get << type_of) cjs' []
        let pcons = map (fun ty -> filter (fun t -> Choice.get <| type_of t = ty) cjs') mtys
        let cls' = zip mtys (map (map(recover_clause id)) pcons)
        let tyal = map (fun ty -> mk_vartype(fst(Choice.get <| dest_type ty) + id), ty) mtys
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
                map (hd << snd << Choice.get << dest_type << Choice.get << type_of) 
                    (fst(strip_exists(snd(strip_forall(concl <| Choice.get rth1)))))
            let xtyal = 
                map (fun ty -> 
                        let s = Choice.get <| dest_vartype ty
                        Option.get <| find (fun t -> fst(Choice.get <| dest_type t) = s) xnewtys, ty) 
                    (map fst cls)
            let ith0 = INST_TYPE xtyal ith
            let rth0 = INST_TYPE xtyal rth
            let isoth, rclauses = 
                prove_inductive_types_isomorphic n k (ith0, rth0) (ith1, rth1)
            let irth3 = CONJ ith1 rth1
            let vtylist = itlist (insert << Choice.get << type_of) (Choice.get <| variables(concl <| Choice.get irth3)) []
            let isoths = CONJUNCTS isoth
            let isotys = 
                map (hd << snd << Choice.get << dest_type << Choice.get << type_of << Choice.get << lhand << concl <<Choice.get) isoths
            let ctylist = 
                filter (fun ty -> exists (fun t -> occurs_in t ty) isotys) 
                    vtylist
            let atylist = itlist (union << striplist (Choice.toOption << dest_fun_ty)) ctylist []
            let isoths' = 
                map (lift_type_bijections isoths) 
                    (filter (fun ty -> exists (fun t -> occurs_in t ty) isotys) 
                         atylist)
            let cisoths = 
                map (BETA_RULE << lift_type_bijections isoths') ctylist
            let uisoths = map ISO_USAGE_RULE cisoths
            let visoths = map (ASSUME << concl <<Choice.get) uisoths
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
                            (snd(strip_comb(Choice.get <| rand(Choice.get <| lhs(snd(strip_forall t))))))) 
                    (conjuncts
                         (snd
                              (strip_exists
                                   (snd(strip_forall(Choice.get <| rand(concl <| Choice.get irth6)))))))
            let mk_newcon tm = 
                let vs, bod = strip_forall tm
                let rdeb = Choice.get <| rand(Choice.get <| lhs bod)
                let rdef = list_mk_abs(vs, rdeb)
                let newname = fst(Choice.get <| dest_var(genvar bool_ty))
                let def = Choice.get <| mk_eq(mk_var(newname, Choice.get <| type_of rdef), rdef)
                let dth = new_definition def
                SIMPLE_BETA_RULE dth
            let dths = map mk_newcon ncjs
            let ith6, rth6 = CONJ_PAIR(PURE_REWRITE_RULE dths irth6)
            n, ith6, rth6
    fun def -> 
        let newtys = map fst def
        let truecons = itlist (@) (map (map fst << snd) def) []
        let (p, ith0, rth0) = define_type_nested def
        let avs, etm = strip_forall(concl <| Choice.get rth0)
        let allcls = conjuncts(snd(strip_exists etm))
        let relcls = fst(chop_list (length truecons) allcls)
        let gencons = 
            map (repeat (Choice.get << rator) << Choice.get << rand << Choice.get << lhand << snd << strip_forall) relcls
        let cdefs = 
            map2 
                (fun s r -> SYM(new_definition(Choice.get <| mk_eq(mk_var(s, Choice.get <| type_of r), r)))) 
                truecons gencons
        let tavs = Choice.get <| make_args "f" [] (map (Choice.get << type_of) avs)
        let ith1 = SUBS cdefs ith0
        let rth1 = GENL tavs (SUBS cdefs (SPECL tavs rth0))
        let retval = p, ith1, rth1
        let newentries = map (fun s -> Choice.get <| dest_vartype s, retval) newtys
        (inductive_type_store := newentries @ (!inductive_type_store)
         do_list extend_rectype_net newentries
         ith1, rth1)

(* ----------------------------------------------------------------------- *)
(* The overall function, with rather crude string-based benignity.         *)
(* ----------------------------------------------------------------------- *)

/// List of previously declared inductive types.
let the_inductive_types = 
    ref ["list = NIL | CONS A list", (list_INDUCT, list_RECURSION)
         "option = NONE | SOME A", (option_INDUCT, option_RECURSION)
         "sum = INL A | INR B", (sum_INDUCT, sum_RECURSION)];;

/// Automatically define user-specified inductive data types.
let define_type s =
    match assoc s !the_inductive_types with
    | Some retval ->
        warn true "Benign redefinition of inductive type"
        retval
    | None ->
        let defspec = parse_inductive_type_specification s
        let newtypes = map fst defspec
        let constructors = itlist ((@) << map fst) (map snd defspec) []
        if not(length(setify newtypes) = length newtypes)
        then failwith "define_type: multiple definitions of a type"
        elif not(length(setify constructors) = length constructors)
        then failwith "define_type: multiple instances of a constructor"
        elif exists (Choice.isResult << get_type_arity << Choice.get << dest_vartype) newtypes
        then 
            let t = Option.get <| find (Choice.isResult << get_type_arity) (map (Choice.get << dest_vartype) newtypes)
            failwith("define_type: type :" + t + " already defined")
        elif exists (Choice.isResult << get_const_type) constructors
        then 
            let t = Option.get <| find (Choice.isResult << get_const_type) constructors
            failwith("define_type: constant " + t + " already defined")
        else 
            let retval = define_type_raw_002 defspec
            the_inductive_types := (s, retval) :: (!the_inductive_types)
            retval

(* ------------------------------------------------------------------------- *)
(* Unwinding, and application of patterns. Add easy cases to default net.    *)
(* ------------------------------------------------------------------------- *)

// UNWIND_CONV: Eliminates existentially quantified Choice.get <| variables that are equated to something.
// MATCH_CONV: Expands application of pattern-matching construct to particular case.
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
                let eq = Option.get <| find (fun tm -> 
                    is_eq tm &&
                    let l, r = Choice.get <| dest_eq tm
                    (mem l evs && not(free_in l r)) || 
                    (mem r evs && not(free_in r l))) eqs
                let l, r = Choice.get <| dest_eq eq
                let v = 
                    if mem l evs && not(free_in l r)
                    then l
                    else r
                let cjs' = eq :: (subtract eqs [eq])
                let n = length evs - (1 + index v (rev evs))
                let th1 = CONJ_ACI_RULE(Choice.get <| mk_eq(bod, list_mk_conj cjs'))
                let th2 = itlist MK_EXISTS evs th1
                let th3 = 
                    funpow n BINDER_CONV (PUSH_EXISTS_CONV baseconv) 
                        (Choice.get <| rand(concl <| Choice.get th2))
                CONV_RULE (RAND_CONV UNWIND_CONV) (TRANS th2 th3)
            with
            | Failure _ -> REFL tm
        UNWIND_CONV
    let MATCH_SEQPATTERN_CONV = 
        GEN_REWRITE_CONV I [pth_1]
        |> THENC <| RATOR_CONV
                       (LAND_CONV(BINDER_CONV(RATOR_CONV BETA_CONV
                                              |> THENC <| BETA_CONV)
                                  |> THENC <| PUSH_EXISTS_CONV(GEN_REWRITE_CONV I [pth_2]
                                                               |> THENC <| BREAK_CONS_CONV)
                                  |> THENC <| UNWIND_CONV
                                  |> THENC <| GEN_REWRITE_CONV DEPTH_CONV [EQT_INTRO
                                                                               (SPEC_ALL 
                                                                                    EQ_REFL)
                                                                           AND_CLAUSES]
                                  |> THENC <| GEN_REWRITE_CONV DEPTH_CONV [EXISTS_SIMP]))
    let MATCH_ONEPATTERN_CONV tm = 
        let th1 = GEN_REWRITE_CONV I [pth_3] tm
        let tm' = Choice.get <| body(Choice.get <| rand(Choice.get <| lhand(Choice.get <| rand(concl <| Choice.get th1))))
        let th2 = 
            (INSIDE_EXISTS_CONV(GEN_REWRITE_CONV I [pth_4]
                                |> THENC <| RAND_CONV BREAK_CONS_CONV)
             |> THENC <| UNWIND_CONV
             |> THENC <| GEN_REWRITE_CONV DEPTH_CONV [EQT_INTRO
                                                          (SPEC_ALL EQ_REFL)
                                                      AND_CLAUSES]
             |> THENC <| GEN_REWRITE_CONV DEPTH_CONV [EXISTS_SIMP]) tm'
        let conv tm = 
            if tm = (Choice.get <| lhand(concl <| Choice.get th2))
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
    let MATCH_ONEPATTERN_CONV_TRIV = 
        MATCH_ONEPATTERN_CONV
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

/// Eliminates universally quantified Choice.get <| variables that are equated to something.
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
                                (parse_term @"(!x. x = a /\ p x ==> q x) <=> (p a ==> q a)")
                            MESON [] 
                                (parse_term @"(!x. a = x /\ p x ==> q x) <=> (p a ==> q a)")
                            MESON [] (parse_term @"(!x. x = a ==> q x) <=> q a")
                            MESON [] (parse_term @"(!x. a = x ==> q x) <=> q a")]
    let rec FORALL_UNWIND_CONV tm = 
        try 
            let avs, bod = strip_forall tm
            let ant, con = Choice.get <| dest_imp bod
            let eqs = conjuncts ant
            let eq = 
                Option.get <| find (fun tm -> 
                    is_eq tm && 
                    let l, r = Choice.get <| dest_eq tm
                    (mem l avs && not(free_in l r)) || 
                    (mem r avs && not(free_in r l))) eqs
            let l, r = Choice.get <| dest_eq eq
            let v = 
                if mem l avs && not(free_in l r)
                then l
                else r
            let cjs' = eq :: (subtract eqs [eq])
            let n = length avs - (1 + index v (rev avs))
            let th1 = CONJ_ACI_RULE(Choice.get <| mk_eq(ant, list_mk_conj cjs'))
            let th2 = AP_THM (AP_TERM (Choice.get <| rator(Choice.get <| rator bod)) th1) con
            let th3 = itlist MK_FORALL avs th2
            let th4 = 
                funpow n BINDER_CONV (PUSH_FORALL_CONV baseconv) 
                    (Choice.get <| rand(concl <| Choice.get th3))
            CONV_RULE (RAND_CONV FORALL_UNWIND_CONV) (TRANS th3 th4)
        with
        | Failure _ -> REFL tm
    FORALL_UNWIND_CONV
