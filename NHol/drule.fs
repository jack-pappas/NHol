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

/// More sophisticated derived rules including definitions and rewriting.

module NHol.drule

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

(* ------------------------------------------------------------------------- *)
(* Type of instantiations, with terms, types and higher-order data.          *)
(* ------------------------------------------------------------------------- *)
type instantiation = (int * term) list * (term * term) list * (hol_type * hol_type) list

(* ------------------------------------------------------------------------- *)
(* The last recourse when all else fails!                                    *)
(* ------------------------------------------------------------------------- *)
let mk_thm(asl, c) = 
    let ax = new_axiom(itlist (curry mk_imp) (rev asl) c)
    rev_itlist (fun t th -> MP th (ASSUME t)) (rev asl) ax

(* ------------------------------------------------------------------------- *)
(* Derived congruence rules; very useful things!                             *)
(* ------------------------------------------------------------------------- *)
let MK_CONJ = 
    let andtm = parse_term @"(/\)"
    fun eq1 eq2 -> MK_COMB(AP_TERM andtm eq1, eq2)

let MK_DISJ = 
    let ortm = parse_term @"(\/)"
    fun eq1 eq2 -> MK_COMB(AP_TERM ortm eq1, eq2)

let MK_FORALL = 
    let atm = mk_const("!", [])
    fun v th -> AP_TERM (inst [type_of v, aty] atm) (ABS v th)

let MK_EXISTS = 
    let atm = mk_const("?", [])
    fun v th -> AP_TERM (inst [type_of v, aty] atm) (ABS v th)

(* ------------------------------------------------------------------------- *)
(* Eliminate the antecedent of a theorem using a conversion/proof rule.      *)
(* ------------------------------------------------------------------------- *)
let MP_CONV (cnv : conv) th = 
    let l, r = dest_imp(concl th)
    let ath = cnv l
    try 
        MP th (EQT_ELIM ath)
    with
    | Failure _ -> MP th ath

(* ------------------------------------------------------------------------- *)
(* Multiple beta-reduction (we use a slight variant below).                  *)
(* ------------------------------------------------------------------------- *)
let rec BETAS_CONV tm = 
    match tm with
    | Comb(Abs(_, _), _) -> BETA_CONV tm
    | Comb(Comb(_, _), _) -> (RATOR_CONV(THENC BETAS_CONV BETA_CONV)) tm
    | _ -> failwith "BETAS_CONV"

(* ------------------------------------------------------------------------- *)
(* Instantiators.                                                            *)
(* ------------------------------------------------------------------------- *)
let (instantiate : instantiation -> term -> term) = 
    let betas n tm = 
        let args, lam = funpow n (fun (l, t) -> (rand t) :: l, rator t) ([], tm)
        rev_itlist (fun a l -> 
                let v, b = dest_abs l
                vsubst [a, v] b) args lam
    let rec ho_betas bcs pat tm = 
        if is_var pat || is_const pat
        then fail()
        else 
            try 
                let bv, bod = dest_abs tm
                mk_abs(bv, ho_betas bcs (body pat) bod)
            with
            | Failure _ -> 
                let hop, args = strip_comb pat
                try 
                    let n = rev_assoc hop bcs
                    if length args = n
                    then betas n tm
                    else fail()
                with
                | Failure _ -> 
                    let lpat, rpat = dest_comb pat
                    let ltm, rtm = dest_comb tm
                    try 
                        let lth = ho_betas bcs lpat ltm
                        try 
                            let rth = ho_betas bcs rpat rtm
                            mk_comb(lth, rth)
                        with
                        | Failure _ -> mk_comb(lth, rtm)
                    with
                    | Failure _ -> 
                        let rth = ho_betas bcs rpat rtm
                        mk_comb(ltm, rth)
    fun (bcs, tmin, tyin) tm -> 
        let itm = 
            if tyin = []
            then tm
            else inst tyin tm
        if tmin = []
        then itm
        else 
            let ttm = vsubst tmin itm
            if bcs = []
            then ttm
            else 
                try 
                    ho_betas bcs itm ttm
                with
                | Failure _ -> ttm

let (INSTANTIATE : instantiation -> thm -> thm) = 
    let rec BETAS_CONV n tm = 
        if n = 1
        then TRY_CONV BETA_CONV tm
        else THENC (RATOR_CONV(BETAS_CONV(n - 1))) (TRY_CONV BETA_CONV) tm
    let rec HO_BETAS bcs pat tm = 
        if is_var pat || is_const pat
        then fail()
        else 
            try 
                let bv, bod = dest_abs tm
                ABS bv (HO_BETAS bcs (body pat) bod)
            with
            | Failure _ -> 
                let hop, args = strip_comb pat
                try 
                    let n = rev_assoc hop bcs
                    if length args = n
                    then BETAS_CONV n tm
                    else fail()
                with
                | Failure _ -> 
                    let lpat, rpat = dest_comb pat
                    let ltm, rtm = dest_comb tm
                    try 
                        let lth = HO_BETAS bcs lpat ltm
                        try 
                            let rth = HO_BETAS bcs rpat rtm
                            MK_COMB(lth, rth)
                        with
                        | Failure _ -> AP_THM lth rtm
                    with
                    | Failure _ -> 
                        let rth = HO_BETAS bcs rpat rtm
                        AP_TERM ltm rth
    fun (bcs, tmin, tyin) th -> 
        let ith = 
            if tyin = []
            then th
            else INST_TYPE tyin th
        if tmin = []
        then ith
        else 
            let tth = INST tmin ith
            if hyp tth = hyp th
            then 
                if bcs = []
                then tth
                else 
                    try 
                        let eth = HO_BETAS bcs (concl ith) (concl tth)
                        EQ_MP eth tth
                    with
                    | Failure _ -> tth
            else failwith "INSTANTIATE: term or type var free in assumptions"

let (INSTANTIATE_ALL : instantiation -> thm -> thm) = 
    fun ((_, tmin, tyin) as i) th -> 
        if tmin = [] && tyin = [] then th
        else 
            let hyps = hyp th
            if hyps = [] then INSTANTIATE i th
            else 
                let tyrel, tyiirel = 
                    if tyin = [] then [], hyps
                    else 
                        let tvs = itlist (union << tyvars << snd) tyin []
                        partition (fun tm -> 
                                let tvs' = type_vars_in_term tm
                                not(intersect tvs tvs' = [])) hyps
                let tmrel, tmirrel = 
                    if tmin = [] then [], tyiirel
                    else 
                        let vs = itlist (union << frees << snd) tmin []
                        partition (fun tm -> 
                                let vs' = frees tm
                                not(intersect vs vs' = [])) tyiirel
                let rhyps = union tyrel tmrel
                let th1 = rev_itlist DISCH rhyps th
                let th2 = INSTANTIATE i th1
                funpow (length rhyps) UNDISCH th2

(* ------------------------------------------------------------------------- *)
(* Higher order matching of terms.                                           *)
(*                                                                           *)
(* Note: in the event of spillover patterns, this may return false results;  *)
(* but there's usually an implicit check outside that the match worked       *)
(* anyway. A test could be put in (see if any "env" variables are left in    *)
(* the term after abstracting out the pattern instances) but it'd be slower. *)
(* ------------------------------------------------------------------------- *)
let (term_match : term list -> term -> term -> instantiation) = 
    let safe_inserta ((y, x) as n) l = 
        try 
            let z = rev_assoc x l
            if aconv y z
            then l
            else failwith "safe_inserta"
        with
        | Failure "find" -> n :: l
    let safe_insert ((y, x) as n) l = 
        try 
            let z = rev_assoc x l
            if compare y z = 0
            then l
            else failwith "safe_insert"
        with
        | Failure "find" -> n :: l
    let mk_dummy = 
        let name = fst(dest_var(genvar aty))
        fun ty -> mk_var(name, ty)
    let rec term_pmatch lconsts env vtm ctm ((insts, homs) as sofar) = 
        match (vtm, ctm) with
        | Var(_, _), _ -> 
            try 
                let ctm' = rev_assoc vtm env
                if compare ctm' ctm = 0
                then sofar
                else failwith "term_pmatch"
            with
            | Failure "find" -> 
                if mem vtm lconsts
                then 
                    if compare ctm vtm = 0
                    then sofar
                    else 
                        failwith "term_pmatch: can't instantiate local constant"
                else safe_inserta (ctm, vtm) insts, homs
        | Const(vname, vty), Const(cname, cty) -> 
            if compare vname cname = 0
            then 
                if compare vty cty = 0
                then sofar
                else safe_insert (mk_dummy cty, mk_dummy vty) insts, homs
            else failwith "term_pmatch"
        | Abs(vv, vbod), Abs(cv, cbod) -> 
            let sofar' = 
                safe_insert 
                    (mk_dummy(snd(dest_var cv)), mk_dummy(snd(dest_var vv))) 
                    insts, homs
            term_pmatch lconsts ((cv, vv) :: env) vbod cbod sofar'
        | _ -> 
            let vhop = repeat rator vtm
            if is_var vhop && not(mem vhop lconsts) 
               && not(can (rev_assoc vhop) env)
            then 
                let vty = type_of vtm
                let cty = type_of ctm
                let insts' = 
                    if compare vty cty = 0
                    then insts
                    else safe_insert (mk_dummy cty, mk_dummy vty) insts
                (insts', (env, ctm, vtm) :: homs)
            else 
                let lv, rv = dest_comb vtm
                let lc, rc = dest_comb ctm
                let sofar' = term_pmatch lconsts env lv lc sofar
                term_pmatch lconsts env rv rc sofar'
    let get_type_insts insts = 
        itlist (fun (t, x) -> type_match (snd(dest_var x)) (type_of t)) insts
    let separate_insts insts = 
        let realinsts, patterns = partition (is_var << snd) insts
        let betacounts = 
            if patterns = []
            then []
            else 
                itlist (fun (_, p) sof -> 
                        let hop, args = strip_comb p
                        try 
                            safe_insert (length args, hop) sof
                        with
                        | Failure _ -> 
                            (warn true 
                                 "Inconsistent patterning in higher order match"
                             sof)) patterns []
        let tyins = get_type_insts realinsts []
        betacounts, mapfilter (fun (t, x) -> 
                            let x' = 
                                let xn, xty = dest_var x
                                mk_var(xn, type_subst tyins xty)
                            if compare t x' = 0
                            then fail()
                            else (t, x')) realinsts, tyins
    let rec term_homatch lconsts tyins (insts, homs) = 
        if homs = []
        then insts
        else 
            let (env, ctm, vtm) = hd homs
            if is_var vtm
            then 
                if compare ctm vtm = 0
                then term_homatch lconsts tyins (insts, tl homs)
                else 
                    let newtyins = 
                        safe_insert (type_of ctm, snd(dest_var vtm)) tyins
                    let newinsts = (ctm, vtm) :: insts
                    term_homatch lconsts newtyins (newinsts, tl homs)
            else 
                let vhop, vargs = strip_comb vtm
                let afvs = freesl vargs
                let inst_fn = inst tyins
                try 
                    let tmins = 
                        map (fun a -> 
                                (try 
                                     rev_assoc a env
                                 with
                                 | Failure _ -> 
                                     try 
                                         rev_assoc a insts
                                     with
                                     | Failure _ -> 
                                         if mem a lconsts
                                         then a
                                         else fail()), inst_fn a) afvs
                    let pats0 = map inst_fn vargs
                    let pats = map (vsubst tmins) pats0
                    let vhop' = inst_fn vhop
                    let ni = 
                        let chop, cargs = strip_comb ctm
                        if compare cargs pats = 0
                        then 
                            if compare chop vhop = 0
                            then insts
                            else safe_inserta (chop, vhop) insts
                        else 
                            let ginsts = 
                                map (fun p -> 
                                        (if is_var p
                                         then p
                                         else genvar(type_of p)), p) pats
                            let ctm' = subst ginsts ctm
                            let gvs = map fst ginsts
                            let abstm = list_mk_abs(gvs, ctm')
                            let vinsts = safe_inserta (abstm, vhop) insts
                            let icpair = ctm', list_mk_comb(vhop', gvs)
                            icpair :: vinsts
                    term_homatch lconsts tyins (ni, tl homs)
                with
                | Failure _ -> 
                    let lc, rc = dest_comb ctm
                    let lv, rv = dest_comb vtm
                    let pinsts_homs' = 
                        term_pmatch lconsts env rv rc 
                            (insts, (env, lc, lv) :: (tl homs))
                    let tyins' = get_type_insts (fst pinsts_homs') []
                    term_homatch lconsts tyins' pinsts_homs'
    fun lconsts vtm ctm -> 
        let pinsts_homs = term_pmatch lconsts [] vtm ctm ([], [])
        let tyins = get_type_insts (fst pinsts_homs) []
        let insts = term_homatch lconsts tyins pinsts_homs
        separate_insts insts

(* ------------------------------------------------------------------------- *)
(* First order unification (no type instantiation -- yet).                   *)
(* ------------------------------------------------------------------------- *)
let (term_unify : term list -> term -> term -> instantiation) = 
    let augment1 sofar (s, x) = 
        let s' = subst sofar s
        if vfree_in x s && not(s = x)
        then failwith "augment_insts"
        else (s', x)
    let raw_augment_insts p insts = p :: (map (augment1 [p]) insts)
    let augment_insts (t, v) insts = 
        let t' = vsubst insts t
        if t' = v
        then insts
        elif vfree_in v t'
        then failwith "augment_insts"
        else raw_augment_insts (t', v) insts
    let rec unify vars tm1 tm2 sofar = 
        if tm1 = tm2
        then sofar
        elif is_var tm1 && mem tm1 vars
        then 
            try 
                let tm1' = rev_assoc tm1 sofar
                unify vars tm1' tm2 sofar
            with
            | Failure "find" -> augment_insts (tm2, tm1) sofar
        elif is_var tm2 && mem tm2 vars
        then 
            try 
                let tm2' = rev_assoc tm2 sofar
                unify vars tm1 tm2' sofar
            with
            | Failure "find" -> augment_insts (tm1, tm2) sofar
        elif is_abs tm1
        then 
            let tm1' = body tm1
            let tm2' = subst [bndvar tm1, bndvar tm2] (body tm2)
            unify vars tm1' tm2' sofar
        else 
            let l1, r1 = dest_comb tm1
            let l2, r2 = dest_comb tm2
            unify vars l1 l2 (unify vars r1 r2 sofar)
    fun vars tm1 tm2 -> [], unify vars tm1 tm2 [], []

(* ------------------------------------------------------------------------- *)
(* Modify bound variable names at depth. (Not very efficient...)             *)
(* ------------------------------------------------------------------------- *)
let deep_alpha = 
    let tryalpha v tm = 
        try 
            alpha v tm
        with
        | Failure _ -> 
            try 
                let v' = variant (frees tm) v
                alpha v' tm
            with
            | Failure _ -> tm
    let rec deep_alpha env tm = 
        if env = []
        then tm
        else 
            try 
                let v, bod = dest_abs tm
                let vn, vty = dest_var v
                try 
                    let (vn', _), newenv = remove (fun (_, x) -> x = vn) env
                    let v' = mk_var(vn', vty)
                    let tm' = tryalpha v' tm
                    let iv, ib = dest_abs tm'
                    mk_abs(iv, deep_alpha newenv ib)
                with
                | Failure _ -> mk_abs(v, deep_alpha env bod)
            with
            | Failure _ -> 
                try 
                    let l, r = dest_comb tm
                    mk_comb(deep_alpha env l, deep_alpha env r)
                with
                | Failure _ -> tm
    deep_alpha

(* ------------------------------------------------------------------------- *)
(* Instantiate theorem by matching part of it to a term.                     *)
(* The GEN_PART_MATCH version renames free vars to avoid clashes.            *)
(* ------------------------------------------------------------------------- *)
let PART_MATCH, GEN_PART_MATCH = 
    let rec match_bvs t1 t2 acc = 
        try 
            let v1, b1 = dest_abs t1
            let v2, b2 = dest_abs t2
            let n1 = fst(dest_var v1)
            let n2 = fst(dest_var v2)
            let newacc = 
                if n1 = n2
                then acc
                else insert (n1, n2) acc
            match_bvs b1 b2 newacc
        with
        | Failure _ -> 
            try 
                let l1, r1 = dest_comb t1
                let l2, r2 = dest_comb t2
                match_bvs l1 l2 (match_bvs r1 r2 acc)
            with
            | Failure _ -> acc
    let PART_MATCH partfn th = 
        let sth = SPEC_ALL th
        let bod = concl sth
        let pbod = partfn bod
        let lconsts = intersect (frees(concl th)) (freesl(hyp th))
        fun tm -> 
            let bvms = match_bvs tm pbod []
            let abod = deep_alpha bvms bod
            let ath = EQ_MP (ALPHA bod abod) sth
            let insts = term_match lconsts (partfn abod) tm
            let fth = INSTANTIATE insts ath
            if hyp fth <> hyp ath
            then failwith "PART_MATCH: instantiated hyps"
            else 
                let tm' = partfn(concl fth)
                if compare tm' tm = 0
                then fth
                else 
                    try 
                        SUBS [ALPHA tm' tm] fth
                    with
                    | Failure _ -> failwith "PART_MATCH: Sanity check failure"
    let GEN_PART_MATCH partfn th = 
        let sth = SPEC_ALL th
        let bod = concl sth
        let pbod = partfn bod
        let lconsts = intersect (frees(concl th)) (freesl(hyp th))
        let fvs = subtract (subtract (frees bod) (frees pbod)) lconsts
        fun tm -> 
            let bvms = match_bvs tm pbod []
            let abod = deep_alpha bvms bod
            let ath = EQ_MP (ALPHA bod abod) sth
            let insts = term_match lconsts (partfn abod) tm
            let eth = INSTANTIATE insts (GENL fvs ath)
            let fth = itlist (fun v th -> snd(SPEC_VAR th)) fvs eth
            if hyp fth <> hyp ath
            then failwith "PART_MATCH: instantiated hyps"
            else 
                let tm' = partfn(concl fth)
                if compare tm' tm = 0
                then fth
                else 
                    try 
                        SUBS [ALPHA tm' tm] fth
                    with
                    | Failure _ -> failwith "PART_MATCH: Sanity check failure"
    PART_MATCH, GEN_PART_MATCH

(* ------------------------------------------------------------------------- *)
(* Matching modus ponens.                                                    *)
(* ------------------------------------------------------------------------- *)
let MATCH_MP ith = 
    let sth = 
        try 
            let tm = concl ith
            let avs, bod = strip_forall tm
            let ant, con = dest_imp bod
            let svs, pvs = partition (C vfree_in ant) avs
            if pvs = []
            then ith
            else 
                let th1 = SPECL avs (ASSUME tm)
                let th2 = GENL svs (DISCH ant (GENL pvs (UNDISCH th1)))
                MP (DISCH tm th2) ith
        with
        | Failure _ -> failwith "MATCH_MP: Not an implication"
    let match_fun = PART_MATCH (fst << dest_imp) sth
    fun th -> 
        try 
            MP (match_fun(concl th)) th
        with
        | Failure _ -> failwith "MATCH_MP: No match"

(* ------------------------------------------------------------------------- *)
(* Useful instance of more general higher order matching.                    *)
(* ------------------------------------------------------------------------- *)
let HIGHER_REWRITE_CONV = 
    let BETA_VAR = 
        let rec BETA_CONVS n = 
            if n = 1
            then TRY_CONV BETA_CONV
            else THENC (RATOR_CONV(BETA_CONVS(n - 1))) (TRY_CONV BETA_CONV)
        let rec free_beta v tm = 
            if is_abs tm
            then 
                let bv, bod = dest_abs tm
                if v = bv
                then failwith "unchanged"
                else ABS_CONV(free_beta v bod)
            else 
                let op, args = strip_comb tm
                if args = []
                then failwith "unchanged"
                elif op = v
                then BETA_CONVS(length args)
                else 
                    let l, r = dest_comb tm
                    try 
                        let lconv = free_beta v l
                        (try 
                             let rconv = free_beta v r
                             COMB2_CONV lconv rconv
                         with
                         | Failure _ -> RATOR_CONV lconv)
                    with
                    | Failure _ -> RAND_CONV(free_beta v r)
        free_beta
    let GINST th = 
        let fvs = subtract (frees(concl th)) (freesl(hyp th))
        let gvs = map (genvar << type_of) fvs
        INST (zip gvs fvs) th
    fun ths -> 
        let thl = map (GINST << SPEC_ALL) ths
        let concs = map concl thl
        let lefts = map lhs concs
        let preds, pats = unzip(map dest_comb lefts)
        let beta_fns = map2 BETA_VAR preds concs
        let ass_list = zip pats (zip preds (zip thl beta_fns))
        let mnet = itlist (fun p n -> enter [] (p, p) n) pats empty_net
        let look_fn t = 
            mapfilter (fun p -> 
                    if can (term_match [] p) t
                    then p
                    else fail()) (lookup t mnet)
        fun top tm -> 
            let pred t = not(look_fn t = []) && free_in t tm
            let stm = 
                if top
                then find_term pred tm
                else hd(sort free_in (find_terms pred tm))
            let pat = hd(look_fn stm)
            let _, tmin, tyin = term_match [] pat stm
            let pred, (th, beta_fn) = assoc pat ass_list
            let gv = genvar(type_of stm)
            let abs = mk_abs(gv, subst [gv, stm] tm)
            let _, tmin0, tyin0 = term_match [] pred abs
            CONV_RULE beta_fn (INST tmin (INST tmin0 (INST_TYPE tyin0 th)))

(* ------------------------------------------------------------------------- *)
(* Derived principle of definition justifying |- c x1 .. xn = t[x1,..,xn]    *)
(* ------------------------------------------------------------------------- *)
let new_definition tm = 
    let avs, bod = strip_forall tm
    let l, r = 
        try 
            dest_eq bod
        with
        | Failure _ -> failwith "new_definition: Not an equation"
    let lv, largs = strip_comb l
    let rtm = 
        try 
            list_mk_abs(largs, r)
        with
        | Failure _ -> failwith "new_definition: Non-variable in LHS pattern"
    let def = mk_eq(lv, rtm)
    let th1 = new_basic_definition def
    let th2 = 
        rev_itlist (fun tm th -> 
                let ith = AP_THM th tm
                TRANS ith (BETA_CONV(rand(concl ith)))) largs th1
    let rvs = filter (not << C mem avs) largs
    itlist GEN rvs (itlist GEN avs th2)