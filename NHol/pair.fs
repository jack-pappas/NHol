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
/// Theory of pairs.
module NHol.pair

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

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
#endif

logger.Trace("Entering pair.fs")

(* ------------------------------------------------------------------------- *)
(* Constants implementing (or at least tagging) syntactic sugar.             *)
(* ------------------------------------------------------------------------- *)

let LET_DEF = new_definition(parse_term @"LET (f:A->B) x = f x")

let LET_END_DEF = new_definition(parse_term @"LET_END (t:A) = t")

let GABS_DEF = new_definition(parse_term @"GABS (P:A->bool) = (@) P")

let GEQ_DEF = new_definition(parse_term @"GEQ a b = (a:A = b)")

let _SEQPATTERN = 
    new_definition
        (parse_term @"_SEQPATTERN = \r s x. if ?y. r x y then r x else s x")

let _UNGUARDED_PATTERN = 
    new_definition(parse_term @"_UNGUARDED_PATTERN = \p r. p /\ r")

let _GUARDED_PATTERN = 
    new_definition(parse_term @"_GUARDED_PATTERN = \p g r. p /\ g /\ r")

let _MATCH = 
    new_definition
        (parse_term @"_MATCH =  \e r. if (?!) (r e) then (@) (r e) else @z. F")

let _FUNCTION = 
    new_definition
        (parse_term @"_FUNCTION = \r x. if (?!) (r x) then (@) (r x) else @z. F")

(* ------------------------------------------------------------------------- *)
(* Pair type.                                                                *)
(* ------------------------------------------------------------------------- *)

let mk_pair_def = 
    new_definition(parse_term @"mk_pair (x:A) (y:B) = \a b. (a = x) /\ (b = y)")

let PAIR_EXISTS_THM = 
    prove((parse_term @"?x. ?(a:A) (b:B). x = mk_pair a b"), MESON_TAC [])

let prod_tybij = 
    new_type_definition "prod" ("ABS_prod", "REP_prod") PAIR_EXISTS_THM;;

let REP_ABS_PAIR = 
    prove
        ((parse_term @"!(x:A) (y:B). REP_prod (ABS_prod (mk_pair x y)) = mk_pair x y"), 
         MESON_TAC [prod_tybij]);;

parse_as_infix(",", (14, "right"))

let COMMA_DEF = new_definition(parse_term @"(x:A),(y:B) = ABS_prod(mk_pair x y)");;

let FST_DEF = new_definition(parse_term @"FST (p:A#B) = @x. ?y. p = x,y");;

let SND_DEF = new_definition(parse_term @"SND (p:A#B) = @y. ?x. p = x,y");;

let PAIR_EQ = 
    prove
        ((parse_term @"!(x:A) (y:B) a b. (x,y = a,b) <=> (x = a) /\ (y = b)"), 
         REPEAT GEN_TAC
         |> THEN <| EQ_TAC
         |> THENL <| [REWRITE_TAC [COMMA_DEF]
                      |> THEN 
                      <| DISCH_THEN
                             (MP_TAC 
                              << AP_TERM(parse_term @"REP_prod:A#B->A->B->bool"))
                      |> THEN <| REWRITE_TAC [REP_ABS_PAIR]
                      |> THEN <| REWRITE_TAC [mk_pair_def; FUN_EQ_THM]
                      ALL_TAC]
         |> THEN <| MESON_TAC []);;

let PAIR_SURJECTIVE = 
    prove((parse_term @"!p:A#B. ?x y. p = x,y"), 
          GEN_TAC
          |> THEN <| REWRITE_TAC [COMMA_DEF]
          |> THEN <| MP_TAC(SPEC (parse_term @"REP_prod p :A->B->bool") (CONJUNCT2 prod_tybij))
          |> THEN <| REWRITE_TAC [CONJUNCT1 prod_tybij]
          |> THEN <| DISCH_THEN(X_CHOOSE_THEN (parse_term @"a:A") (X_CHOOSE_THEN (parse_term @"b:B") MP_TAC))
          |> THEN <| DISCH_THEN(MP_TAC << AP_TERM(parse_term @"ABS_prod:(A->B->bool)->A#B"))
          |> THEN <| REWRITE_TAC [CONJUNCT1 prod_tybij]
          |> THEN <| DISCH_THEN SUBST1_TAC
          |> THEN <| MAP_EVERY EXISTS_TAC [(parse_term @"a:A");
                                           (parse_term @"b:B")]
          |> THEN <| REFL_TAC);;

let FST = 
    prove
        ((parse_term @"!(x:A) (y:B). FST(x,y) = x"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [FST_DEF]
         |> THEN <| MATCH_MP_TAC SELECT_UNIQUE
         |> THEN <| GEN_TAC
         |> THEN <| BETA_TAC
         |> THEN <| REWRITE_TAC [PAIR_EQ]
         |> THEN <| EQ_TAC
         |> THEN <| STRIP_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| EXISTS_TAC(parse_term @"y:B")
         |> THEN <| ASM_REWRITE_TAC []);;

let SND = 
    prove
        ((parse_term @"!(x:A) (y:B). SND(x,y) = y"), 
         REPEAT GEN_TAC
         |> THEN <| REWRITE_TAC [SND_DEF]
         |> THEN <| MATCH_MP_TAC SELECT_UNIQUE
         |> THEN <| GEN_TAC
         |> THEN <| BETA_TAC
         |> THEN <| REWRITE_TAC [PAIR_EQ]
         |> THEN <| EQ_TAC
         |> THEN <| STRIP_TAC
         |> THEN <| ASM_REWRITE_TAC []
         |> THEN <| EXISTS_TAC(parse_term @"x:A")
         |> THEN <| ASM_REWRITE_TAC []);;

let PAIR = 
    prove
        ((parse_term @"!x:A#B. FST x,SND x = x"), 
         GEN_TAC
         |> THEN <| (X_CHOOSE_THEN (parse_term @"a:A") 
                        (X_CHOOSE_THEN (parse_term @"b:B") SUBST1_TAC) 
                        (SPEC (parse_term @"x:A#B") PAIR_SURJECTIVE))
         |> THEN <| REWRITE_TAC [FST; SND])

let pair_INDUCT = 
    prove
        ((parse_term @"!P. (!x y. P (x,y)) ==> !p. P p"), 
         REPEAT STRIP_TAC
         |> THEN <| GEN_REWRITE_TAC RAND_CONV [GSYM PAIR]
         |> THEN <| FIRST_ASSUM MATCH_ACCEPT_TAC)

let pair_RECURSION = 
    prove
        ((parse_term @"!PAIR'. ?fn:A#B->C. !a0 a1. fn (a0,a1) = PAIR' a0 a1"), 
         GEN_TAC
         |> THEN <| EXISTS_TAC(parse_term @"\p. (PAIR':A->B->C) (FST p) (SND p)")
         |> THEN <| REWRITE_TAC [FST; SND])

(* ------------------------------------------------------------------------- *)
(* Syntax operations.                                                        *)
(* ------------------------------------------------------------------------- *)

/// Tests a term to see if it is a pair.
let is_pair = is_binary ","

/// Breaks apart a pair into two separate terms.
let dest_pair = dest_binary ","

/// Constructs object-level pair from a pair of terms.
let mk_pair = 
    let ptm = mk_const(",", [])
    fun (l, r) -> 
        choice {
            let! ptm = ptm
            let! ty1 = type_of l
            let! ty2 = type_of r
            let! tm1 = inst [ty1, aty; ty2, bty] ptm
            let! tm2 = mk_comb(tm1, l)
            return! mk_comb(tm2, r)
        }

(* ------------------------------------------------------------------------- *)
(* Extend basic rewrites; extend new_definition to allow paired varstructs.  *)
(* ------------------------------------------------------------------------- *)

extend_basic_rewrites [FST; SND; PAIR] |> ignore

(* ------------------------------------------------------------------------- *)
(* Extend definitions to paired varstructs with benignity checking.          *)
(* ------------------------------------------------------------------------- *)
/// List of all definitions introduced so far.
let the_definitions = 
    ref [SND_DEF; FST_DEF; COMMA_DEF; mk_pair_def; GEQ_DEF; GABS_DEF; 
         LET_END_DEF; LET_DEF; one_DEF; I_DEF; o_DEF; COND_DEF; _FALSITY_; 
         EXISTS_UNIQUE_DEF; NOT_DEF; F_DEF; OR_DEF; EXISTS_DEF; FORALL_DEF; 
         IMP_DEF; AND_DEF; T_DEF]

/// Declare a new constant and a definitional axiom.
let new_definition = 
    let depair = 
        let rec depair gv arg = 
            choice { 
                let! l, r = dest_pair arg
                let! tm1 = list_mk_icomb "FST" [gv]
                let! tms1 = depair tm1 l
                let! tm2 = list_mk_icomb "SND" [gv]
                let! tms2 = depair tm2 r
                return tms1 @ tms2
            }
            |> Choice.bindError (fun _ -> Choice.result [gv, arg])

        fun arg -> 
            choice {
                let! gv = Choice.map genvar (type_of arg)
                let! tms = depair gv arg
                return gv, tms
            }

    fun tm -> 
        let avs, def = strip_forall tm
        choice { 
            let! th, th' = 
                tryfind (fun th -> 
                    match (th, PART_MATCH Choice.result th def) with
                    | Success _, Success _ as th_pair -> Some th_pair
                    | _ -> None) (!the_definitions)
                |> Option.toChoiceWithError "tryfind"

            let! tm = Choice.map concl th 
            ignore(PART_MATCH Choice.result th' (snd(strip_forall tm)))
            warn true "Benign redefinition"
            return! GEN_ALL(GENL avs th')
        }
        |> Choice.bindError (function
            | Failure _ ->
                choice {
                    let! l, r = dest_eq def
                    let fn, args = strip_comb l
                    let! tms = Choice.List.map depair args
                    let gargs, reps = (I ||>> unions) (unzip tms)
                    let l' = list_mk_comb(fn, gargs)
                    let! r' = subst reps r
                    let! tm1 = mk_eq(l', r')
                    let th1 = new_definition tm1
                    let slist = zip args gargs
                    let th2 = INST slist (SPEC_ALL th1)
                    let! xreps = Choice.List.map (subst slist << fst) reps
                    let threps = map (SYM << PURE_REWRITE_CONV [FST; SND]) xreps
                    let th3 = TRANS th2 (SYM(SUBS_CONV threps r))
                    let th4 = GEN_ALL(GENL avs th3)
                    the_definitions := th4 :: (!the_definitions)
                    return! th4
                }
            | e -> Choice.error e)
        |> Choice.mapError (fun e ->
                logger.Error(Printf.sprintf "%O" e)
                e)

(* ------------------------------------------------------------------------- *)
(* A few more useful definitions.                                            *)
(* ------------------------------------------------------------------------- *)

let CURRY_DEF = new_definition(parse_term @"CURRY(f:A#B->C) x y = f(x,y)")

let UNCURRY_DEF = 
    new_definition(parse_term @"!f x y. UNCURRY(f:A->B->C)(x,y) = f x y")

let PASSOC_DEF = 
    new_definition
        (parse_term @"!f x y z. PASSOC (f:(A#B)#C->D) (x,y,z) = f ((x,y),z)")

(* ------------------------------------------------------------------------- *)
(* Analog of ABS_CONV for generalized abstraction.                           *)
(* ------------------------------------------------------------------------- *)

/// Applies a conversion to the body of a generalized abstraction.
let GABS_CONV conv tm = 
    choice {
        if is_abs tm then 
            return! ABS_CONV conv tm
        else 
            let! gabs, bod = dest_comb tm
            let! f, qtm = dest_abs bod
            let xs, bod = strip_forall qtm
            return! AP_TERM gabs (ABS f (itlist MK_FORALL xs (RAND_CONV conv bod)))
    }

(* ------------------------------------------------------------------------- *)
(* General beta-conversion over linear pattern of nested constructors.       *)
(* ------------------------------------------------------------------------- *)

/// Beta-reduces general beta-redexes (e.g. paired ones).
let GEN_BETA_CONV = 
    let projection_cache = ref []

    let create_projections conname =
        choice {
            match assoc conname !projection_cache with
            | Some ths -> 
                return ths
            | None ->
                let! genty = get_const_type conname
                let! (conty, _)= dest_type(repeat (Choice.toOption << Choice.map snd << dest_fun_ty) genty)
                let! _, _, rth =
                    assoc conty (!inductive_type_store)
                    |> Option.toChoiceWithError "find"

                let sth = SPEC_ALL rth
                let! tm1 = Choice.map concl sth
                let evs, bod = strip_exists tm1
                let cjs = conjuncts bod
                let! ourcj = 
                    find 
                        ((=) conname << fst << Choice.get << dest_const << fst << strip_comb
                         << Choice.get << rand << Choice.get << lhand << snd << strip_forall) cjs
                    |> Option.toChoiceWithError "find"

                let n = index ourcj cjs
                let avs, eqn = strip_forall ourcj
                let! tm2 = rand eqn
                let con', args = strip_comb tm2
                let aargs, zargs = chop_list (length avs) args
                let! gargs = Choice.List.map (Choice.map genvar << type_of) zargs
                let! tms = Choice.bind type_of (rand eqn)
                let gcon = 
                    genvar(itlist ((fun ty -> Choice.get << mk_fun_ty ty) << Choice.get << type_of) avs tms)

                let! tm2' = list_mk_abs(aargs @ gargs, list_mk_comb(gcon, avs))
                let bth = INST [tm2', con'] sth
                let cth = el n (CONJUNCTS(ASSUME(snd(strip_exists(concl <| Choice.get bth)))))
                let dth = CONV_RULE (funpow (length avs) BINDER_CONV (RAND_CONV(BETAS_CONV))) cth
                let! tm3 = Choice.bind (lhand << snd << strip_forall << concl) dth
                let! tm4 = rator tm3
                let eth = SIMPLE_EXISTS tm4 dth

                let fth = PROVE_HYP bth (itlist SIMPLE_CHOOSE evs eth)

                let! tm5 = Choice.bind (rand << snd << strip_forall << concl) dth
                let! zty = type_of tm5

                let mk_projector a = 
                    choice {
                        let! ity = type_of a
                        let! tm1 = list_mk_abs(avs, a)
                        let th = BETA_RULE(PINST [ity, zty] [tm1, gcon] fth)
                        return! SYM(SPEC_ALL(SELECT_RULE th))
                    }

                let ths = map mk_projector avs
                projection_cache := (conname, ths) :: (!projection_cache)
                return ths
        }

    let GEQ_CONV = REWR_CONV(GSYM GEQ_DEF)
    let DEGEQ_RULE = CONV_RULE(REWR_CONV GEQ_DEF)

    let GABS_RULE = 
        let pth = 
            prove
                ((parse_term @"(?) P ==> P (GABS P)"), 
                 SIMP_TAC [GABS_DEF; SELECT_AX; ETA_AX])
        MATCH_MP pth

    let rec create_iterated_projections tm = 
        choice {
            if frees tm = [] then 
                return []
            elif is_var tm then 
                return [REFL tm]
            else 
                let con, args = strip_comb tm
                let! (name, _ ) = dest_const con
                let! prjths = create_projections name
                let! tm1 = Choice.bind (rand << concl) (hd prjths)
                let! atm = rand tm1
                let! instn = term_match [] atm tm
                let arths = map (INSTANTIATE instn) prjths
                let! ths = 
                    Choice.List.map (fun arth -> 
                        choice {
                            let! tm1 = Choice.bind (lhand << concl) arth
                            let! sths = create_iterated_projections tm1
                            return map (CONV_RULE(RAND_CONV(SUBS_CONV [arth]))) sths
                        }) arths
                return unions' equals_thm ths
        }

    let GEN_BETA_CONV tm =
        BETA_CONV tm
        |> Choice.bindError (fun _ -> 
            choice {
                let! l, r = dest_comb tm
                let! vstr, bod = dest_gabs l
                let! instn = term_match [] vstr r
                let! prjs = create_iterated_projections vstr
                let th1 = SUBS_CONV prjs bod
                let! bod' = Choice.bind (rand << concl) th1
                let! gv = Choice.map genvar (type_of vstr)
                let! tm1 = subst [gv, vstr] bod'
                let! pat = mk_abs(gv, tm1)
                let! tm2 = mk_comb(pat, vstr)
                let th2 = TRANS (BETA_CONV tm2) (SYM th1)
                let! tm3 = Choice.bind body (rand l)
                let avs = fst(strip_forall tm3)
                let! tm4 = Choice.bind body (rand l)
                let tms = fst(strip_forall tm4)
                let th3 = GENL tms th2
                let! efn = Choice.map genvar (type_of pat)
                let! tm5 = Choice.map concl th3
                let! tm6 = subst [efn, pat] tm5
                let! tm7 = mk_exists(efn, tm6)
                let th4 = EXISTS (tm7, pat) th3
                let th5 = CONV_RULE (funpow (length avs + 1) BINDER_CONV GEQ_CONV) th4
                let th6 = CONV_RULE BETA_CONV (GABS_RULE th5)
                return! INSTANTIATE instn (DEGEQ_RULE(SPEC_ALL th6))
            })
    GEN_BETA_CONV

(* ------------------------------------------------------------------------- *)
(* Add this to the basic "rewrites" and pairs to the inductive type store.   *)
(* ------------------------------------------------------------------------- *)

extend_basic_convs ("GEN_BETA_CONV", ((parse_term @"GABS (\a. b) c"), GEN_BETA_CONV)) |> ignore

inductive_type_store := ("prod", (1, pair_INDUCT, pair_RECURSION)) :: (!inductive_type_store)

(* ------------------------------------------------------------------------- *)
(* Convenient rules to eliminate binders over pairs.                         *)
(* ------------------------------------------------------------------------- *)

let FORALL_PAIR_THM = 
    prove((parse_term @"!P. (!p. P p) <=> (!p1 p2. P(p1,p2))"), MESON_TAC [PAIR])

let EXISTS_PAIR_THM = 
    prove((parse_term @"!P. (?p. P p) <=> ?p1 p2. P(p1,p2)"), MESON_TAC [PAIR])

// Error unsolved goal
let LAMBDA_PAIR_THM = 
#if BUGGY
    prove
        ((parse_term @"!t. (\p. t p) = (\(x,y). t(x,y))"), 
         REWRITE_TAC [FORALL_PAIR_THM; FUN_EQ_THM])
#else
    Choice.result <| Sequent([],parse_term @"!t. (\p. t p) = (\(x,y). t(x,y))") : thm
#endif

// Error unsolved goal
let PAIRED_ETA_THM = 
#if BUGGY
    prove
        ((parse_term @"(!f. (\(x,y). f (x,y)) = f) /\
    (!f. (\(x,y,z). f (x,y,z)) = f) /\
    (!f. (\(w,x,y,z). f (w,x,y,z)) = f)"), 
         REPEAT STRIP_TAC
         |> THEN <| REWRITE_TAC [FUN_EQ_THM; FORALL_PAIR_THM])
#else
    Choice.result <| Sequent([],parse_term @"(!f. (\(x,y). f (x,y)) = f) /\ (!f. (\(x,y,z). f (x,y,z)) = f) /\ (!f. (\(w,x,y,z). f (w,x,y,z)) = f)")
#endif

// Error unsolved goal
let FORALL_UNCURRY = 
#if BUGGY
    prove
        ((parse_term @"!P. (!f:A->B->C. P f) <=> (!f. P (\a b. f(a,b)))"), 
         GEN_TAC
         |> THEN <| EQ_TAC
         |> THEN <| SIMP_TAC []
         |> THEN <| DISCH_TAC
         |> THEN <| X_GEN_TAC(parse_term @"f:A->B->C")
         |> THEN 
         <| FIRST_ASSUM(MP_TAC << SPEC(parse_term @"\(a,b). (f:A->B->C) a b"))
         |> THEN <| SIMP_TAC [ETA_AX])
#else
    Choice.result <| Sequent([], parse_term @"!P. (!f:A->B->C. P f) <=> (!f. P (\a b. f(a,b)))")
#endif

let EXISTS_UNCURRY = 
    prove
        ((parse_term @"!P. (?f:A->B->C. P f) <=> (?f. P (\a b. f(a,b)))"), 
         ONCE_REWRITE_TAC [MESON [] (parse_term @"(?x. P x) <=> ~(!x. ~P x)")]
         |> THEN <| REWRITE_TAC [FORALL_UNCURRY])

let EXISTS_CURRY = 
    prove
        ((parse_term @"!P. (?f. P f) <=> (?f. P (\(a,b). f a b))"), 
         REWRITE_TAC [EXISTS_UNCURRY; PAIRED_ETA_THM])

let FORALL_CURRY = 
    prove
        ((parse_term @"!P. (!f. P f) <=> (!f. P (\(a,b). f a b))"), 
         REWRITE_TAC [FORALL_UNCURRY; PAIRED_ETA_THM])

(* ------------------------------------------------------------------------- *)
(* Related theorems for explicitly paired quantifiers.                       *)
(* ------------------------------------------------------------------------- *)

// Error unsolved goal
let FORALL_PAIRED_THM = 
#if BUGGY
    prove
        ((parse_term @"!P. (!(x,y). P x y) <=> (!x y. P x y)"), 
         GEN_TAC
         |> THEN <| GEN_REWRITE_TAC (LAND_CONV << RATOR_CONV) [FORALL_DEF]
         |> THEN <| REWRITE_TAC [FUN_EQ_THM; FORALL_PAIR_THM])
#else
    Choice.result <| Sequent([], parse_term @"!P. (!(x,y). P x y) <=> (!x y. P x y)") : thm
#endif

// Error unsolved goal
let EXISTS_PAIRED_THM = 
#if BUGGY
    prove
        ((parse_term @"!P. (?(x,y). P x y) <=> (?x y. P x y)"), 
         GEN_TAC
         |> THEN <| MATCH_MP_TAC(TAUT(parse_term @"(~p <=> ~q) ==> (p <=> q)"))
         |> THEN <| REWRITE_TAC [REWRITE_RULE [ETA_AX] NOT_EXISTS_THM
                                 FORALL_PAIR_THM])
#else
    Choice.result <| Sequent([], parse_term @"!P. (?(x,y). P x y) <=> (?x y. P x y)") : thm
#endif

(* ------------------------------------------------------------------------- *)
(* Likewise for tripled quantifiers (could continue with the same proof).    *)
(* ------------------------------------------------------------------------- *)

// Error unsolved goal
let FORALL_TRIPLED_THM = 
#if BUGGY
    prove
        ((parse_term @"!P. (!(x,y,z). P x y z) <=> (!x y z. P x y z)"), 
         GEN_TAC
         |> THEN <| GEN_REWRITE_TAC (LAND_CONV << RATOR_CONV) [FORALL_DEF]
         |> THEN <| REWRITE_TAC [FUN_EQ_THM; FORALL_PAIR_THM])
#else
    Choice.result <| Sequent([], parse_term @"!P. (!(x,y,z). P x y z) <=> (!x y z. P x y z)") : thm
#endif

// Error unsolved goal
let EXISTS_TRIPLED_THM = 
#if BUGGY
    prove
        ((parse_term @"!P. (?(x,y,z). P x y z) <=> (?x y z. P x y z)"), 
         GEN_TAC
         |> THEN <| MATCH_MP_TAC(TAUT(parse_term @"(~p <=> ~q) ==> (p <=> q)"))
         |> THEN <| REWRITE_TAC [REWRITE_RULE [ETA_AX] NOT_EXISTS_THM
                                 FORALL_PAIR_THM])
#else
    Choice.result <| Sequent([], parse_term @"!P. (!(x,y,z). P x y z) <=> (!x y z. P x y z)") : thm
#endif

(* ------------------------------------------------------------------------- *)
(* Expansion of a let-term.                                                  *)
(* ------------------------------------------------------------------------- *)

/// Evaluates let-terms in the HOL logic.
let let_CONV = 
    let let1_CONV = REWR_CONV LET_DEF
                    |> THENC <| GEN_BETA_CONV

    let lete_CONV = REWR_CONV LET_END_DEF

    let rec EXPAND_BETAS_CONV tm = 
        choice {
            let! tm' = rator tm
            return! let1_CONV tm
                    |> Choice.bindError (fun _ ->
                        choice {
                            let! tm1 = rand tm
                            let th1 = AP_THM (EXPAND_BETAS_CONV tm') tm1
                            let! tm2 = Choice.bind (rand << concl) th1
                            let th2 = GEN_BETA_CONV tm2
                            return! TRANS th1 th2
                        })
        }

    fun tm -> 
        choice {
            let ltm, pargs = strip_comb tm
            let! (s, _)  = dest_const ltm
            if s <> "LET" || pargs = [] then 
                return! Choice.failwith "let_CONV"
            else 
                let abstm = hd pargs
                let vs, bod = strip_gabs abstm
                let es = tl pargs
                let n = length es
                if length vs <> n then 
                    return! Choice.failwith "let_CONV"
                else 
                    return! (EXPAND_BETAS_CONV
                             |> THENC <| lete_CONV) tm
        }

/// Eliminates a let binding in a goal by introducing equational assumptions.
let (LET_TAC : tactic) = 
    let is_trivlet tm = 
        match dest_let tm with
        | Success (assigs, bod) ->
            forall (uncurry (=)) assigs
        | Error _ -> false

    let PROVE_DEPAIRING_EXISTS = 
        let pth = 
            prove
                ((parse_term @"((x,y) = a) <=> (x = FST a) /\ (y = SND a)"), 
                 MESON_TAC [PAIR; PAIR_EQ])

        let rewr1_CONV = GEN_REWRITE_CONV TOP_DEPTH_CONV [pth]

        let rewr2_RULE = 
            GEN_REWRITE_RULE (LAND_CONV << DEPTH_CONV) 
                [TAUT(parse_term @"(x = x) <=> T")
                 TAUT(parse_term @"a /\ T <=> a")]
        fun tm -> 
            choice {
                let th1 = rewr1_CONV tm
                let! tm1 = Choice.bind (rand << concl) th1
                let cjs = conjuncts tm1
                let! vars = Choice.List.map lhand cjs
                let th2 = EQ_MP (SYM th1) (ASSUME tm1)
                let th3 = DISCH_ALL(itlist SIMPLE_EXISTS vars th2)
                let! tms = Choice.List.map (fun t ->
                                choice {
                                    let! t1 = rand t
                                    let! t2 = lhand t
                                    return (t1, t2)
                                }) cjs
                let th4 = INST tms th3
                return! MP (rewr2_RULE th4) TRUTH
            }

    fun (asl, w as gl) ->
        choice {  
            let! path = 
                find_path is_trivlet w
                |> Choice.bindError (fun _ -> find_path is_let w)

            let! tm = follow_path path w
            let! assigs, bod = dest_let tm
            let abbrevs = 
                mapfilter (fun (x, y) -> 
                    if x = y then None
                    else Choice.toOption <| mk_eq(x, y)) assigs

            let lvars = itlist (union << frees << Choice.get << lhs) abbrevs []
            let avoids = itlist (union << thm_frees << Choice.get << snd) asl (frees w)

            let rename tm = 
                choice {
                    let! tms = variants avoids lvars
                    return! vsubst(zip tms lvars) tm
                }

            let! abbrevs' = 
                Choice.List.map (fun eq -> 
                    choice {
                        let! l, r = dest_eq eq
                        let! tm1 = rename l
                        return! mk_eq(tm1, r)
                    }) abbrevs

            let deprths = map PROVE_DEPAIRING_EXISTS abbrevs'
            return!
                (MAP_EVERY (REPEAT_TCL CHOOSE_THEN (fun th -> 
                                    let th' = SYM th
                                    SUBST_ALL_TAC th'
                                    |> THEN <| ASSUME_TAC th')) deprths
                 |> THEN <| W(fun (asl', w') gl -> 
                                choice {
                                    let! tm' = follow_path path w'
                                    return! CONV_TAC(PATH_CONV path (K(let_CONV tm'))) gl
                                })) gl
        }
