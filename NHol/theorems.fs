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
/// Additional theorems (mainly for quantifiers) etc.
module NHol.theorems

open FSharp.Compatibility.OCaml

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

(* ------------------------------------------------------------------------- *)
(* More stuff about equality.                                                *)
(* ------------------------------------------------------------------------- *)
let EQ_REFL = prove((parse_term @"!x:A. x = x"), GEN_TAC
                                                |> THEN <| REFL_TAC)

let REFL_CLAUSE = 
    prove
        ((parse_term @"!x:A. (x = x) <=> T"), 
         GEN_TAC
         |> THEN <| MATCH_ACCEPT_TAC(EQT_INTRO(SPEC_ALL EQ_REFL)))

let EQ_SYM = 
    prove
        ((parse_term @"!(x:A) y. (x = y) ==> (y = x)"), 
         REPEAT GEN_TAC
         |> THEN <| DISCH_THEN(ACCEPT_TAC << SYM))

let EQ_SYM_EQ = 
    prove
        ((parse_term @"!(x:A) y. (x = y) <=> (y = x)"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| MATCH_ACCEPT_TAC EQ_SYM)

let EQ_TRANS = 
    prove
        ((parse_term @"!(x:A) y z. (x = y) /\ (y = z) ==> (x = z)"), 
         REPEAT STRIP_TAC
         |> THEN <| PURE_ASM_REWRITE_TAC []
         |> THEN <| REFL_TAC)

(* ------------------------------------------------------------------------- *)
(* The following is a common special case of ordered rewriting.              *)
(* ------------------------------------------------------------------------- *)
let AC acsuite = EQT_ELIM << PURE_REWRITE_CONV [acsuite; REFL_CLAUSE]

(* ------------------------------------------------------------------------- *)
(* A couple of theorems about beta reduction.                                *)
(* ------------------------------------------------------------------------- *)
let BETA_THM = 
    prove
        ((parse_term @"!(f:A->B) y. (\x. (f:A->B) x) y = f y"), 
         REPEAT GEN_TAC
         |> THEN <| BETA_TAC
         |> THEN <| REFL_TAC)

let ABS_SIMP = 
    prove
        ((parse_term @"!(t1:A) (t2:B). (\x. t1) t2 = t1"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [BETA_THM; REFL_CLAUSE])

(* ------------------------------------------------------------------------- *)
(* A few "big name" intuitionistic tautologies.                              *)
(* ------------------------------------------------------------------------- *)
let CONJ_ASSOC = 
    prove
        ((parse_term @"!t1 t2 t3. t1 /\ t2 /\ t3 <=> (t1 /\ t2) /\ t3"), 
         ITAUT_TAC)

let CONJ_SYM = prove((parse_term @"!t1 t2. t1 /\ t2 <=> t2 /\ t1"), ITAUT_TAC)
let CONJ_ACI = prove((parse_term @"(p /\ q <=> q /\ p) /\
   ((p /\ q) /\ r <=> p /\ (q /\ r)) /\
   (p /\ (q /\ r) <=> q /\ (p /\ r)) /\
   (p /\ p <=> p) /\
   (p /\ (p /\ q) <=> p /\ q)"), ITAUT_TAC)
let DISJ_ASSOC = 
    prove
        ((parse_term @"!t1 t2 t3. t1 \/ t2 \/ t3 <=> (t1 \/ t2) \/ t3"), 
         ITAUT_TAC)
let DISJ_SYM = prove((parse_term @"!t1 t2. t1 \/ t2 <=> t2 \/ t1"), ITAUT_TAC)
let DISJ_ACI = prove((parse_term @"(p \/ q <=> q \/ p) /\
   ((p \/ q) \/ r <=> p \/ (q \/ r)) /\
   (p \/ (q \/ r) <=> q \/ (p \/ r)) /\
   (p \/ p <=> p) /\
   (p \/ (p \/ q) <=> p \/ q)"), ITAUT_TAC)
let IMP_CONJ = prove((parse_term @"p /\ q ==> r <=> p ==> q ==> r"), ITAUT_TAC)
let IMP_IMP = GSYM IMP_CONJ
let IMP_CONJ_ALT = 
    prove((parse_term @"p /\ q ==> r <=> q ==> p ==> r"), ITAUT_TAC)

(* ------------------------------------------------------------------------- *)
(* A couple of "distribution" tautologies are useful.                        *)
(* ------------------------------------------------------------------------- *)
let LEFT_OR_DISTRIB = 
    prove((parse_term @"!p q r. p /\ (q \/ r) <=> p /\ q \/ p /\ r"), ITAUT_TAC)

let RIGHT_OR_DISTRIB = 
    prove((parse_term @"!p q r. (p \/ q) /\ r <=> p /\ r \/ q /\ r"), ITAUT_TAC)

(* ------------------------------------------------------------------------- *)
(* Degenerate cases of quantifiers.                                          *)
(* ------------------------------------------------------------------------- *)
let FORALL_SIMP = prove((parse_term @"!t. (!x:A. t) = t"), ITAUT_TAC)

let EXISTS_SIMP = prove((parse_term @"!t. (?x:A. t) = t"), ITAUT_TAC)

(* ------------------------------------------------------------------------- *)
(* I also use this a lot (as a prelude to congruence reasoning).             *)
(* ------------------------------------------------------------------------- *)
let EQ_IMP = ITAUT(parse_term @"(a <=> b) ==> a ==> b")

(* ------------------------------------------------------------------------- *)
(* Start building up the basic rewrites; we add a few more later.            *)
(* ------------------------------------------------------------------------- *)
let EQ_CLAUSES = prove((parse_term @"!t. ((T <=> t) <=> t) /\ ((t <=> T) <=> t) /\
       ((F <=> t) <=> ~t) /\ ((t <=> F) <=> ~t)"), ITAUT_TAC)

let NOT_CLAUSES_WEAK = prove((parse_term @"(~T <=> F) /\ (~F <=> T)"), ITAUT_TAC)
let AND_CLAUSES = prove((parse_term @"!t. (T /\ t <=> t) /\ (t /\ T <=> t) /\ (F /\ t <=> F) /\
       (t /\ F <=> F) /\ (t /\ t <=> t)"), ITAUT_TAC)
let OR_CLAUSES = prove((parse_term @"!t. (T \/ t <=> T) /\ (t \/ T <=> T) /\ (F \/ t <=> t) /\
       (t \/ F <=> t) /\ (t \/ t <=> t)"), ITAUT_TAC)
let IMP_CLAUSES = prove((parse_term @"!t. (T ==> t <=> t) /\ (t ==> T <=> T) /\ (F ==> t <=> T) /\
       (t ==> t <=> T) /\ (t ==> F <=> ~t)"), ITAUT_TAC)

extend_basic_rewrites [REFL_CLAUSE;
                       EQ_CLAUSES;
                       NOT_CLAUSES_WEAK;
                       AND_CLAUSES;
                       OR_CLAUSES;
                       IMP_CLAUSES;
                       FORALL_SIMP;
                       EXISTS_SIMP;
                       BETA_THM;
                       (let IMP_EQ_CLAUSE = 
                           prove
                               ((parse_term @"((x = x) ==> p) <=> p"), 
                                REWRITE_TAC [EQT_INTRO(SPEC_ALL EQ_REFL)
                                             IMP_CLAUSES]) in IMP_EQ_CLAUSE);]
extend_basic_congs 
    [ITAUT
         (parse_term 
              @"(p <=> p') ==> (p' ==> (q <=> q')) ==> (p ==> q <=> p' ==> q')")]

(* ------------------------------------------------------------------------- *)
(* Rewrite rule for unique existence.                                        *)
(* ------------------------------------------------------------------------- *)
let EXISTS_UNIQUE_THM = 
    prove
        ((parse_term 
              @"!P. (?!x:A. P x) <=> (?x. P x) /\ (!x x'. P x /\ P x' ==> (x = x'))"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [EXISTS_UNIQUE_DEF])

(* ------------------------------------------------------------------------- *)
(* Trivial instances of existence.                                           *)
(* ------------------------------------------------------------------------- *)
let EXISTS_REFL = 
    prove((parse_term @"!a:A. ?x. x = a"), GEN_TAC
                                          |> THEN 
                                          <| EXISTS_TAC(parse_term @"a:A")
                                          |> THEN <| REFL_TAC)

let EXISTS_UNIQUE_REFL = 
    prove((parse_term @"!a:A. ?!x. x = a"), GEN_TAC
                                           |> THEN 
                                           <| REWRITE_TAC [EXISTS_UNIQUE_THM]
                                           |> THEN 
                                           <| REPEAT(EQ_TAC
                                                     |> ORELSE <| STRIP_TAC)
                                           |> THENL <| [EXISTS_TAC
                                                            (parse_term @"a:A")
                                                        ASM_REWRITE_TAC []]
                                           |> THEN <| REFL_TAC)

(* ------------------------------------------------------------------------- *)
(* Unwinding.                                                                *)
(* ------------------------------------------------------------------------- *)
let UNWIND_THM1 = 
    prove
        ((parse_term @"!P (a:A). (?x. a = x /\ P x) <=> P a"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THENL <| [DISCH_THEN
                          (CHOOSE_THEN(CONJUNCTS_THEN2 SUBST1_TAC ACCEPT_TAC))
                      DISCH_TAC
                      |> THEN <| EXISTS_TAC(parse_term @"a:A")
                      |> THEN <| CONJ_TAC
                      |> THEN <| TRY(FIRST_ASSUM MATCH_ACCEPT_TAC)
                      |> THEN <| REFL_TAC])

let UNWIND_THM2 = 
    prove
        ((parse_term @"!P (a:A). (?x. x = a /\ P x) <=> P a"), 
         REPEAT GEN_TAC
         |> THEN <| CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV))
         |> THEN <| MATCH_ACCEPT_TAC UNWIND_THM1)

let FORALL_UNWIND_THM2 = 
    prove
        ((parse_term @"!P (a:A). (!x. x = a ==> P x) <=> P a"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THENL <| [DISCH_THEN(MP_TAC << SPEC(parse_term @"a:A"))
                      |> THEN <| REWRITE_TAC []
                      DISCH_TAC
                      |> THEN <| GEN_TAC
                      |> THEN <| DISCH_THEN SUBST1_TAC
                      |> THEN <| ASM_REWRITE_TAC []])

let FORALL_UNWIND_THM1 = 
    prove
        ((parse_term @"!P a. (!x. a = x ==> P x) <=> P a"), 
         REPEAT GEN_TAC
         |> THEN <| CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV))
         |> THEN <| MATCH_ACCEPT_TAC FORALL_UNWIND_THM2)

(* ------------------------------------------------------------------------- *)
(* Permuting quantifiers.                                                    *)
(* ------------------------------------------------------------------------- *)
let SWAP_FORALL_THM = 
    prove
        ((parse_term @"!P:A->B->bool. (!x y. P x y) <=> (!y x. P x y)"), 
         ITAUT_TAC)

let SWAP_EXISTS_THM = 
    prove
        ((parse_term @"!P:A->B->bool. (?x y. P x y) <=> (?y x. P x y)"), 
         ITAUT_TAC)

(* ------------------------------------------------------------------------- *)
(* Universal quantifier and conjunction.                                     *)
(* ------------------------------------------------------------------------- *)
let FORALL_AND_THM = 
    prove
        ((parse_term @"!P Q. (!x:A. P x /\ Q x) <=> (!x. P x) /\ (!x. Q x)"), 
         ITAUT_TAC)

let AND_FORALL_THM = 
    prove
        ((parse_term @"!P Q. (!x. P x) /\ (!x. Q x) <=> (!x:A. P x /\ Q x)"), 
         ITAUT_TAC)
let LEFT_AND_FORALL_THM = 
    prove((parse_term @"!P Q. (!x:A. P x) /\ Q <=> (!x:A. P x /\ Q)"), ITAUT_TAC)
let RIGHT_AND_FORALL_THM = 
    prove((parse_term @"!P Q. P /\ (!x:A. Q x) <=> (!x. P /\ Q x)"), ITAUT_TAC)

(* ------------------------------------------------------------------------- *)
(* Existential quantifier and disjunction.                                   *)
(* ------------------------------------------------------------------------- *)
let EXISTS_OR_THM = 
    prove
        ((parse_term @"!P Q. (?x:A. P x \/ Q x) <=> (?x. P x) \/ (?x. Q x)"), 
         ITAUT_TAC)

let OR_EXISTS_THM = 
    prove
        ((parse_term @"!P Q. (?x. P x) \/ (?x. Q x) <=> (?x:A. P x \/ Q x)"), 
         ITAUT_TAC)
let LEFT_OR_EXISTS_THM = 
    prove((parse_term @"!P Q. (?x. P x) \/ Q <=> (?x:A. P x \/ Q)"), ITAUT_TAC)
let RIGHT_OR_EXISTS_THM = 
    prove((parse_term @"!P Q. P \/ (?x. Q x) <=> (?x:A. P \/ Q x)"), ITAUT_TAC)

(* ------------------------------------------------------------------------- *)
(* Existential quantifier and conjunction.                                   *)
(* ------------------------------------------------------------------------- *)
let LEFT_EXISTS_AND_THM = 
    prove((parse_term @"!P Q. (?x:A. P x /\ Q) <=> (?x:A. P x) /\ Q"), ITAUT_TAC)

let RIGHT_EXISTS_AND_THM = 
    prove((parse_term @"!P Q. (?x:A. P /\ Q x) <=> P /\ (?x:A. Q x)"), ITAUT_TAC)
let TRIV_EXISTS_AND_THM = 
    prove
        ((parse_term @"!P Q. (?x:A. P /\ Q) <=> (?x:A. P) /\ (?x:A. Q)"), 
         ITAUT_TAC)
let LEFT_AND_EXISTS_THM = 
    prove((parse_term @"!P Q. (?x:A. P x) /\ Q <=> (?x:A. P x /\ Q)"), ITAUT_TAC)
let RIGHT_AND_EXISTS_THM = 
    prove((parse_term @"!P Q. P /\ (?x:A. Q x) <=> (?x:A. P /\ Q x)"), ITAUT_TAC)
let TRIV_AND_EXISTS_THM = 
    prove
        ((parse_term @"!P Q. (?x:A. P) /\ (?x:A. Q) <=> (?x:A. P /\ Q)"), 
         ITAUT_TAC)

(* ------------------------------------------------------------------------- *)
(* Only trivial instances of universal quantifier and disjunction.           *)
(* ------------------------------------------------------------------------- *)
let TRIV_FORALL_OR_THM = 
    prove
        ((parse_term @"!P Q. (!x:A. P \/ Q) <=> (!x:A. P) \/ (!x:A. Q)"), 
         ITAUT_TAC)

let TRIV_OR_FORALL_THM = 
    prove
        ((parse_term @"!P Q. (!x:A. P) \/ (!x:A. Q) <=> (!x:A. P \/ Q)"), 
         ITAUT_TAC)

(* ------------------------------------------------------------------------- *)
(* Implication and quantifiers.                                              *)
(* ------------------------------------------------------------------------- *)
let RIGHT_IMP_FORALL_THM = 
    prove((parse_term @"!P Q. (P ==> !x:A. Q x) <=> (!x. P ==> Q x)"), ITAUT_TAC)

let RIGHT_FORALL_IMP_THM = 
    prove((parse_term @"!P Q. (!x. P ==> Q x) <=> (P ==> !x:A. Q x)"), ITAUT_TAC)
let LEFT_IMP_EXISTS_THM = 
    prove
        ((parse_term @"!P Q. ((?x:A. P x) ==> Q) <=> (!x. P x ==> Q)"), ITAUT_TAC)
let LEFT_FORALL_IMP_THM = 
    prove
        ((parse_term @"!P Q. (!x. P x ==> Q) <=> ((?x:A. P x) ==> Q)"), ITAUT_TAC)
let TRIV_FORALL_IMP_THM = 
    prove
        ((parse_term @"!P Q. (!x:A. P ==> Q) <=> ((?x:A. P) ==> (!x:A. Q))"), 
         ITAUT_TAC)
let TRIV_EXISTS_IMP_THM = 
    prove
        ((parse_term @"!P Q. (?x:A. P ==> Q) <=> ((!x:A. P) ==> (?x:A. Q))"), 
         ITAUT_TAC)

(* ------------------------------------------------------------------------- *)
(* Alternative versions of unique existence.                                 *)
(* ------------------------------------------------------------------------- *)
let EXISTS_UNIQUE_ALT = 
    prove
        ((parse_term @"!P:A->bool. (?!x. P x) <=> (?x. !y. P y <=> (x = y))"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [EXISTS_UNIQUE_THM]
         |> THEN <| EQ_TAC
         |> THENL <| [DISCH_THEN
                          (CONJUNCTS_THEN2 (X_CHOOSE_TAC(parse_term @"x:A")) 
                               ASSUME_TAC)
                      |> THEN <| EXISTS_TAC(parse_term @"x:A")
                      |> THEN <| GEN_TAC
                      |> THEN <| EQ_TAC
                      |> THENL <| [DISCH_TAC
                                   |> THEN <| FIRST_ASSUM MATCH_MP_TAC
                                   |> THEN <| ASM_REWRITE_TAC []
                                   DISCH_THEN(SUBST1_TAC << SYM)
                                   |> THEN <| FIRST_ASSUM MATCH_ACCEPT_TAC]
                      DISCH_THEN(X_CHOOSE_TAC(parse_term @"x:A"))
                      |> THEN <| ASM_REWRITE_TAC [GSYM EXISTS_REFL]
                      |> THEN <| REPEAT GEN_TAC
                      |> THEN <| DISCH_THEN(CONJUNCTS_THEN(SUBST1_TAC << SYM))
                      |> THEN <| REFL_TAC])

let EXISTS_UNIQUE = 
    prove
        ((parse_term 
              @"!P:A->bool. (?!x. P x) <=> (?x. P x /\ !y. P y ==> (y = x))"), 
         GEN_TAC
         |> THEN <| REWRITE_TAC [EXISTS_UNIQUE_ALT]
         |> THEN <| AP_TERM_TAC
         |> THEN <| ABS_TAC
         |> THEN 
         <| GEN_REWRITE_TAC (LAND_CONV << BINDER_CONV) 
                [ITAUT(parse_term @"(a <=> b) <=> (a ==> b) /\ (b ==> a)")]
         |> THEN <| GEN_REWRITE_TAC (LAND_CONV << ONCE_DEPTH_CONV) [EQ_SYM_EQ]
         |> THEN <| REWRITE_TAC [FORALL_AND_THM]
         |> THEN <| SIMP_TAC []
         |> THEN <| REWRITE_TAC [LEFT_FORALL_IMP_THM; EXISTS_REFL]
         |> THEN <| REWRITE_TAC [CONJ_ACI])

(* ------------------------------------------------------------------------- *)
(* DESTRUCT_TAC, FIX_TAC and INTRO_TAC, giving more brief and elegant ways   *)
(* of naming introduced variables and assumptions (from Marco Maggesi).      *)
(* ------------------------------------------------------------------------- *)
let DESTRUCT_TAC, FIX_TAC, INTRO_TAC = 
    let NAME_GEN_TAC s gl = 
        let ty = (snd << dest_var << fst << dest_forall << snd) gl
        X_GEN_TAC (mk_var(s, ty)) gl
    let OBTAIN_THEN v ttac th = 
        let ty = (snd << dest_var << fst << dest_exists << concl) th
        X_CHOOSE_THEN (mk_var(v, ty)) ttac th
    let CONJ_LIST_TAC = end_itlist(fun t1 t2 -> CONJ_TAC
                                                |> THENL <| [t1; t2])
    let NUM_DISJ_TAC n = 
        if n <= 0
        then failwith "NUM_DISJ_TAC"
        else REPLICATE_TAC (n - 1) DISJ2_TAC
             |> THEN <| REPEAT DISJ1_TAC
    let NAME_PULL_FORALL_CONV = 
        let SWAP_FORALL_CONV = REWR_CONV SWAP_FORALL_THM
        let AND_FORALL_CONV = GEN_REWRITE_CONV I [AND_FORALL_THM]
        let RIGHT_IMP_FORALL_CONV = GEN_REWRITE_CONV I [RIGHT_IMP_FORALL_THM]
        fun s -> 
            let rec PULL_FORALL tm = 
                if is_forall tm
                then 
                    if name_of(fst(dest_forall tm)) = s
                    then REFL tm
                    else (BINDER_CONV PULL_FORALL
                          |> THENC <| SWAP_FORALL_CONV) tm
                elif is_imp tm
                then (RAND_CONV PULL_FORALL
                      |> THENC <| RIGHT_IMP_FORALL_CONV) tm
                elif is_conj tm
                then (BINOP_CONV PULL_FORALL
                      |> THENC <| AND_FORALL_CONV) tm
                else fail()
            PULL_FORALL
    let parse_fix = 
        let ident = 
            function 
            | Ident s :: rest when isalpha s -> s, rest
            | _ -> raise Noparse
        let rename = 
            let old_name = possibly(a(Ident "/") .>>. ident |>> snd)
            (a(Resword "[") .>>. ident |>> snd) .>>. old_name 
            .>>. a(Resword "]") |>> fst
        let mk_var v = CONV_TAC(NAME_PULL_FORALL_CONV v)
                       |> THEN <| GEN_TAC
        let mk_rename = 
            function 
            | u, [v] -> CONV_TAC(NAME_PULL_FORALL_CONV v)
                        |> THEN <| NAME_GEN_TAC u
            | u, _ -> NAME_GEN_TAC u
        let vars = many(rename |>> mk_rename <|> (ident |>> mk_var)) |>> EVERY
        let star = possibly(a(Ident "*") |>> K(REPEAT GEN_TAC))
        vars .>>. star |>> function 
                           | tac, [] -> tac
                           | tac, _ -> tac
                                       |> THEN <| REPEAT GEN_TAC
    let parse_destruct = 
        let OBTAINL_THEN : string list -> thm_tactical = 
            EVERY_TCL << map OBTAIN_THEN
        let ident p = 
            function 
            | Ident s :: rest when p s -> s, rest
            | _ -> raise Noparse
        let rec destruct inp = disj inp
        and disj inp = 
            let DISJ_CASES_LIST = end_itlist DISJ_CASES_THEN2
            (listof conj (a(Resword "|")) "Disjunction" |>> DISJ_CASES_LIST) inp
        and conj inp = (atleast 1 atom |>> end_itlist CONJUNCTS_THEN2) inp
        and obtain inp = 
            let obtain_prfx = 
                let var_list = atleast 1 (ident isalpha)
                (a(Ident "@") .>>. var_list |>> snd) .>>. a(Resword ".") |>> fst
            (obtain_prfx .>>. destruct |>> uncurry OBTAINL_THEN) inp
        and atom inp = 
            let label = ident isalnum |>> LABEL_TAC
            let paren = 
                (a(Resword "(") .>>. destruct |>> snd) .>>. a(Resword ")") 
                |>> fst
            (label <|> obtain <|> paren) inp
        destruct
    let parse_intro = 
        let number = 
            function 
            | Ident s :: rest -> 
                (try 
                     let n = int_of_string s
                     if n < 1
                     then raise Noparse
                     else n, rest
                 with
                 | Failure _ -> raise Noparse)
            | _ -> raise Noparse
        let pa_fix = a(Ident "!") .>>. parse_fix |>> snd
        let pa_dest = parse_destruct |>> DISCH_THEN
        let pa_prefix = 
            elistof (pa_fix <|> pa_dest) (a(Resword ";")) "Prefix intro pattern"
        let rec pa_intro toks = 
            (pa_prefix .>>. possibly pa_postfix |>> uncurry (@) |>> EVERY) toks
        and pa_postfix toks = (pa_conj <|> pa_disj) toks
        and pa_conj toks = 
            let conjs = 
                listof pa_intro (a(Ident "&")) "Intro pattern" |>> CONJ_LIST_TAC
            ((a(Resword "{") .>>. conjs |>> snd) .>>. a(Resword "}") |>> fst) 
                toks
        and pa_disj toks = 
            let disj = number |>> NUM_DISJ_TAC
            ((a(Ident "#") .>>. disj |>> snd) .>>. pa_intro |>> (uncurry THEN)) 
                toks
        pa_intro
    let DESTRUCT_TAC s = 
        let tac, rest = 
            (fix "Destruct pattern" parse_destruct << lex << explode) s
        if rest = []
        then tac
        else failwith "Garbage after destruct pattern"
    let INTRO_TAC s = 
        let tac, rest = 
            (fix "Introduction pattern" parse_intro << lex << explode) s
        if rest = []
        then tac
        else failwith "Garbage after intro pattern"
    let FIX_TAC s = 
        let tac, rest = (parse_fix << lex << explode) s
        if rest = []
        then tac
        else failwith "FIX_TAC: invalid pattern"
    DESTRUCT_TAC, FIX_TAC, INTRO_TAC