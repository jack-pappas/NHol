(*

Copyright 1998 University of Cambridge
Copyright 1998-2007 John Harrison
Copyright 2013 Jack Pappas, Eric Taucher, Anh-Dung Phan

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

/// More syntax constructors, and prelogical utilities like matching.
module NHol.basics

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

open NHol
open lib
open fusion
open fusion.Hol_kernel

(* ------------------------------------------------------------------------- *)
(* Create probably-fresh variable                                            *)
(* ------------------------------------------------------------------------- *)

/// Returns a 'fresh' variable with specified type.
let genvar = 
    let gcounter = ref 0
    fun ty -> 
        let count = !gcounter
        gcounter := count + 1
        mk_var("_" + (string count), ty)

(* ------------------------------------------------------------------------- *)
(* Convenient functions for manipulating types.                              *)
(* ------------------------------------------------------------------------- *)

/// Break apart a function type into domain and range.
let dest_fun_ty ty = 
    match ty with
    | Tyapp("fun", [ty1; ty2]) -> (ty1, ty2)
    | _ -> failwith "dest_fun_ty"

/// Tests if one type occurs in another.
let rec occurs_in ty bigty =
    bigty = ty || is_type bigty && exists (occurs_in ty) (snd(dest_type bigty))

/// The call tysubst [ty1',ty1; ... ; tyn',tyn] ty will systematically traverse the type ty
/// and replace the topmost instances of any tyi encountered with the corresponding tyi'.
/// In the (usual) case where all the tyi are type variables, this is the same as type_subst,
/// but also works when they are not.
let rec tysubst alist ty = 
    try 
        rev_assoc ty alist
    with
    | Failure _ -> 
        if is_vartype ty then ty
        else 
            let tycon, tyvars = dest_type ty
            mk_type(tycon, map (tysubst alist) tyvars)

(* ------------------------------------------------------------------------- *)
(* A bit more syntax.                                                        *)
(* ------------------------------------------------------------------------- *)

/// Returns the bound variable of an abstraction.
let bndvar tm = 
    try 
        fst(dest_abs tm)
    with
    | Failure _ -> failwith "bndvar: Not an abstraction"

/// Returns the body of an abstraction.
let body tm = 
    try 
        snd(dest_abs tm)
    with
    | Failure _ -> failwith "body: Not an abstraction"

/// Iteratively constructs combinations (function applications).
let list_mk_comb(h, t) = rev_itlist (C(curry mk_comb)) t h
/// Iteratively constructs abstractions.
let list_mk_abs(vs, bod) = itlist (curry mk_abs) vs bod
/// Iteratively breaks apart combinations (function applications).
let strip_comb = rev_splitlist dest_comb
/// Iteratively breaks apart abstractions.
let strip_abs = splitlist dest_abs

(* ------------------------------------------------------------------------- *)
(* Generic syntax to deal with some binary operators.                        *)
(*                                                                           *)
(* Note that "mk_binary" only works for monomorphic functions.               *)
(* ------------------------------------------------------------------------- *)

/// Tests if a term is an application of a named binary operator.
let is_binary s tm = 
    match tm with
    | Comb(Comb(Const(s', _), _), _) -> s' = s
    | _ -> false

/// Breaks apart an instance of a binary operator with given name.
let dest_binary s tm = 
    match tm with
    | Comb(Comb(Const(s', _), l), r) when s' = s -> (l, r)
    | _ -> failwith "dest_binary"

/// Constructs an instance of a named monomorphic binary operator.
let mk_binary s = 
    let c = mk_const(s, [])
    fun (l, r) -> 
        try 
            mk_comb(mk_comb(c, l), r)
        with
        | Failure _ -> failwith "mk_binary"

(* ------------------------------------------------------------------------- *)
(* Produces a sequence of variants, considering previous inventions.         *)
(* ------------------------------------------------------------------------- *)

/// Pick a list of variants of variables, avoiding a list of variables and each other.
let rec variants av vs = 
    if vs = [] then []
    else 
        let vh = variant av (hd vs)
        vh :: (variants (vh :: av) (tl vs))

(* ------------------------------------------------------------------------- *)
(* Gets all variables (free and/or bound) in a term.                         *)
(* ------------------------------------------------------------------------- *)

/// Determines the variables used, free or bound, in a given term.
let variables = 
    let rec vars(acc, tm) = 
        if is_var tm then insert tm acc
        elif is_const tm then acc
        elif is_abs tm then 
            let v, bod = dest_abs tm
            vars(insert v acc, bod)
        else 
            let l, r = dest_comb tm
            vars(vars(acc, l), r)
    fun tm -> vars([], tm)

(* ------------------------------------------------------------------------- *)
(* General substitution (for any free expression).                           *)
(* ------------------------------------------------------------------------- *)

/// Substitute terms for other terms inside a term.
let subst = 
    let rec ssubst ilist tm = 
        if ilist = [] then tm
        else 
            try 
                fst(find ((aconv tm) << snd) ilist)
            with
            | Failure _ -> 
                match tm with
                | Comb(f, x) -> 
                    let f' = ssubst ilist f
                    let x' = ssubst ilist x
                    if f' == f && x' == x then tm
                    else mk_comb(f', x')
                | Abs(v, bod) -> 
                    let ilist' = filter (not << (vfree_in v) << snd) ilist
                    mk_abs(v, ssubst ilist' bod)
                | _ -> tm
    fun ilist -> 
        let theta = filter (fun (s, t) -> compare s t <> 0) ilist
        if theta = [] then (fun tm -> tm)
        else 
            let ts, xs = unzip theta
            fun tm -> 
                let gs = variants (variables tm) (map (genvar << type_of) xs)
                let tm' = ssubst (zip gs xs) tm
                if tm' == tm then tm
                else vsubst (zip ts gs) tm'

(* ------------------------------------------------------------------------- *)
(* Alpha conversion term operation.                                          *)
(* ------------------------------------------------------------------------- *)

/// Changes the name of a bound variable.
let alpha v tm = 
    let v0, bod = 
        try 
            dest_abs tm
        with
        | Failure _ -> failwith "alpha: Not an abstraction"
    if v = v0 then tm
    elif type_of v = type_of v0 && not(vfree_in v bod) then mk_abs(v, vsubst [v, v0] bod)
    else failwith "alpha: Invalid new variable"

(* ------------------------------------------------------------------------- *)
(* Type matching.                                                            *)
(* ------------------------------------------------------------------------- *)

/// Computes a type instantiation to match one type to another.
let rec type_match vty cty sofar = 
    if is_vartype vty then 
        try 
            if rev_assoc vty sofar = cty then sofar
            else failwith "type_match"
        with
        | Failure "find" -> (cty, vty) :: sofar
    else 
        let vop, vargs = dest_type vty
        let cop, cargs = dest_type cty
        if vop = cop then itlist2 type_match vargs cargs sofar
        else failwith "type_match"

(* ------------------------------------------------------------------------- *)
(* Conventional matching version of mk_const (but with a sanity test).       *)
(* ------------------------------------------------------------------------- *)

/// Constructs a constant with type matching.
let mk_mconst(c, ty) = 
    try 
        let uty = get_const_type c
        let mat = type_match uty ty []
        let con = mk_const(c, mat)
        if type_of con = ty then con
        else fail()
    with
    | Failure _ -> failwith "mk_const: generic type cannot be instantiated"

(* ------------------------------------------------------------------------- *)
(* Like mk_comb, but instantiates type variables in rator if necessary.      *)
(* ------------------------------------------------------------------------- *)

/// Makes a combination, instantiating types in rator if necessary.
let mk_icomb(tm1, tm2) = 
    match dest_type(type_of tm1) with
    | "fun", [ty; _] ->
        let tyins = type_match ty (type_of tm2) []
        mk_comb(inst tyins tm1, tm2)
    | _ -> failwith "mk_icomb: Unhandled case."

(* ------------------------------------------------------------------------- *)
(* Instantiates types for constant c and iteratively makes combination.      *)
(* ------------------------------------------------------------------------- *)

/// Applies constant to list of arguments, instantiating constant type as needed.
let list_mk_icomb cname args = 
    let atys, _ = nsplit dest_fun_ty args (get_const_type cname)
    let tyin = itlist2 (fun g a -> type_match g (type_of a)) atys args []
    list_mk_comb(mk_const(cname, tyin), args)

(* ------------------------------------------------------------------------- *)
(* Free variables in assumption list and conclusion of a theorem.            *)
(* ------------------------------------------------------------------------- *)

/// Returns a list of the variables free in a theorem's assumptions and conclusion.
let thm_frees th = 
    let asl, c = dest_thm th
    itlist (union << frees) asl (frees c)

(* ------------------------------------------------------------------------- *)
(* Is one term free in another?                                              *)
(* ------------------------------------------------------------------------- *)

/// Tests if one term is free in another.
let rec free_in tm1 tm2 = 
    if aconv tm1 tm2 then true
    elif is_comb tm2 then 
        let l, r = dest_comb tm2
        free_in tm1 l || free_in tm1 r
    elif is_abs tm2 then 
        let bv, bod = dest_abs tm2
        not(vfree_in bv tm1) && free_in tm1 bod
    else false

(* ------------------------------------------------------------------------- *)
(* Searching for terms.                                                      *)
(* ------------------------------------------------------------------------- *)

/// Searches a term for a subterm that satises a given predicate.
let rec find_term p tm = 
    if p tm then tm
    elif is_abs tm then find_term p (body tm)
    elif is_comb tm then 
        let l, r = dest_comb tm
        try 
            find_term p l
        with
        | Failure _ -> find_term p r
    else failwith "find_term"

/// Searches a term for all subterms that satisfy a predicate.
let find_terms = 
    let rec accum tl p tm = 
        let tl' = 
            if p tm then insert tm tl
            else tl
        if is_abs tm then accum tl' p (body tm)
        elif is_comb tm then accum (accum tl' p (rator tm)) p (rand tm)
        else tl'
    accum []

(* ------------------------------------------------------------------------- *)
(* General syntax for binders.                                               *)
(*                                                                           *)
(* NB! The "mk_binder" function expects polytype "A", which is the domain.   *)
(* ------------------------------------------------------------------------- *)

/// Tests if a term is a binder construct with named constant.
let is_binder s tm = 
    match tm with
    | Comb(Const(s', _), Abs(_, _)) -> s' = s
    | _ -> false

/// Breaks apart a "binder".
let dest_binder s tm = 
    match tm with
    | Comb(Const(s', _), Abs(x, t)) when s' = s -> (x, t)
    | _ -> failwith "dest_binder"

/// Constructs a term with a named constant applied to an abstraction.
let mk_binder op = 
    let c = mk_const(op, [])
    fun (v, tm) -> mk_comb(inst [type_of v, aty] c, mk_abs(v, tm))

(* ------------------------------------------------------------------------- *)
(* Syntax for binary operators.                                              *)
(* ------------------------------------------------------------------------- *)

/// Tests if a term is an application of the given binary operator.
let is_binop op tm = 
    match tm with
    | Comb(Comb(op', _), _) -> op' = op
    | _ -> false

/// Breaks apart an application of a given binary operator to two arguments.
let dest_binop op tm = 
    match tm with
    | Comb(Comb(op', l), r) when op' = op -> (l, r)
    | _ -> failwith "dest_binop"

/// The call 'mk_binop op l r' returns the term '(op l) r'.
let mk_binop op tm1 = 
    let f = mk_comb(op, tm1)
    fun tm2 -> mk_comb(f, tm2)

/// Makes an iterative application of a binary operator.
let list_mk_binop op = end_itlist(mk_binop op)
/// Repeatedly breaks apart an iterated binary operator into components.
let binops op = striplist(dest_binop op)

(* ------------------------------------------------------------------------- *)
(* Some common special cases                                                 *)
(* ------------------------------------------------------------------------- *)

/// Tests a term to see if it is a conjunction.
let is_conj = is_binary "/\\"
/// Term destructor for conjunctions.
let dest_conj = dest_binary "/\\"
/// Iteratively breaks apart a conjunction.
let conjuncts = striplist dest_conj
/// Tests if a term is an application of implication.
let is_imp = is_binary "==>"
/// Breaks apart an implication into antecedent and consequent.
let dest_imp = dest_binary "==>"
/// Tests a term to see if it is a universal quantification.
let is_forall = is_binder "!"
/// Breaks apart a universally quantified term into quantified variable and body.
let dest_forall = dest_binder "!"
/// Iteratively breaks apart universal quantifications.
let strip_forall = splitlist dest_forall
/// Tests a term to see if it as an existential quantification.
let is_exists = is_binder "?"
/// Breaks apart an existentially quantified term into quantified variable and body.
let dest_exists = dest_binder "?"
/// Iteratively breaks apart existential quantifications.
let strip_exists = splitlist dest_exists
/// Tests a term to see if it is a disjunction.
let is_disj = is_binary "\\/"
/// Breaks apart a disjunction into the two disjuncts.
let dest_disj = dest_binary "\\/"
/// Iteratively breaks apart a disjunction.
let disjuncts = striplist dest_disj

/// Tests a term to see if it is a logical negation.
let is_neg tm = 
    try 
        fst(dest_const(rator tm)) = "~"
    with
    | Failure _ -> false

/// Breaks apart a negation, returning its body.
let dest_neg tm = 
    try 
        let n, p = dest_comb tm
        if fst(dest_const n) = "~" then p
        else fail()
    with
    | Failure _ -> failwith "dest_neg"

/// Tests if a term is of the form `there exists a unique ...'
let is_uexists = is_binder "?!"
/// Breaks apart a unique existence term.
let dest_uexists = dest_binder "?!"
/// Breaks apart a `CONS pair' into head and tail.
let dest_cons = dest_binary "CONS"
/// Tests a term to see if it is an application of CONS.
let is_cons = is_binary "CONS"

/// Iteratively breaks apart a list term.
let dest_list tm = 
    try 
        let tms, nil = splitlist dest_cons tm
        if fst(dest_const nil) = "NIL" then tms
        else fail()
    with
    | Failure _ -> failwith "dest_list"

/// Tests a term to see if it is a list.
let is_list = can dest_list

(* ------------------------------------------------------------------------- *)
(* Syntax for numerals.                                                      *)
(* ------------------------------------------------------------------------- *)

/// Converts a HOL numeral term to unlimited-precision integer.
let dest_numeral = 
    let rec dest_num tm = 
        if try 
               fst(dest_const tm) = "_0"
           with
           | Failure _ -> false
        then num_0
        else 
            let l, r = dest_comb tm
            let n = num_2 * dest_num r
            let cn = fst(dest_const l)
            if cn = "BIT0" then n
            elif cn = "BIT1" then n + num_1
            else fail()
    fun tm -> 
        try 
            let l, r = dest_comb tm
            if fst(dest_const l) = "NUMERAL" then dest_num r
            else fail()
        with
        | Failure _ -> failwith "dest_numeral"

(* ------------------------------------------------------------------------- *)
(* Syntax for generalized abstractions.                                      *)
(*                                                                           *)
(* These are here because they are used by the preterm->term translator;     *)
(* preterms regard generalized abstractions as an atomic notion. This is     *)
(* slightly unclean --- for example we need locally some operations on       *)
(* universal quantifiers --- but probably simplest. It has to go somewhere!  *)
(* ------------------------------------------------------------------------- *)

/// Breaks apart a generalized abstraction into abstracted varstruct and body.
let dest_gabs = 
    let dest_geq = dest_binary "GEQ"
    fun tm -> 
        try 
            if is_abs tm then dest_abs tm
            else 
                let l, r = dest_comb tm
                if not(fst(dest_const l) = "GABS") then fail()
                else 
                    let ltm, rtm = dest_geq(snd(strip_forall(body r)))
                    rand ltm, rtm
        with
        | Failure _ -> failwith "dest_gabs: Not a generalized abstraction"

/// Tests if a term is a basic or generalized abstraction.
let is_gabs = can dest_gabs

/// Constructs a generalized abstraction.
let mk_gabs = 
    let mk_forall(v, t) = 
        let cop = mk_const("!", [type_of v, aty])
        mk_comb(cop, mk_abs(v, t))
    let list_mk_forall(vars, bod) = itlist (curry mk_forall) vars bod
    let mk_geq(t1, t2) = 
        let p = mk_const("GEQ", [type_of t1, aty])
        mk_comb(mk_comb(p, t1), t2)
    fun (tm1, tm2) -> 
        if is_var tm1 then mk_abs(tm1, tm2)
        else 
            let fvs = frees tm1
            let fty = mk_fun_ty (type_of tm1) (type_of tm2)
            let f = variant (frees tm1 @ frees tm2) (mk_var("f", fty))
            let bod = mk_abs(f, list_mk_forall(fvs, mk_geq(mk_comb(f, tm1), tm2)))
            mk_comb(mk_const("GABS", [fty, aty]), bod)

/// Iteratively makes a generalized abstraction.
let list_mk_gabs(vs, bod) = itlist (curry mk_gabs) vs bod
/// Breaks apart an iterated generalized or basic abstraction.
let strip_gabs = splitlist dest_gabs

(* ------------------------------------------------------------------------- *)
(* Syntax for let terms.                                                     *)
(* ------------------------------------------------------------------------- *)

/// Breaks apart a let-expression.
let dest_let tm = 
    try 
        let l, aargs = strip_comb tm
        if fst(dest_const l) <> "LET" then fail()
        else 
            let vars, lebod = strip_gabs(hd aargs)
            let eqs = zip vars (tl aargs)
            let le, bod = dest_comb lebod
            if fst(dest_const le) = "LET_END" then eqs, bod
            else fail()
    with
    | Failure _ -> failwith "dest_let: not a let-term"

/// Tests a term to see if it is a let-expression.
let is_let = can dest_let

/// Constructs a let-expression.
let mk_let(assigs, bod) = 
    let lefts, rights = unzip assigs
    let lend = mk_comb(mk_const("LET_END", [type_of bod, aty]), bod)
    let lbod = list_mk_gabs(lefts, lend)
    let ty1, ty2 = dest_fun_ty(type_of lbod)
    let ltm = 
        mk_const("LET", [ty1, aty;
                         ty2, bty])
    list_mk_comb(ltm, lbod :: rights)

(* ------------------------------------------------------------------------- *)
(* Useful function to create stylized arguments using numbers.               *)
(* ------------------------------------------------------------------------- *)

/// Make a list of terms with stylized variable names.
let make_args = 
    let rec margs n s avoid tys = 
        if tys = [] then []
        else 
            let v = variant avoid (mk_var(s + (string n), hd tys))
            v :: (margs (n + 1) s (v :: avoid) (tl tys))
    fun s avoid tys -> 
        if length tys = 1 then [variant avoid (mk_var(s, hd tys))]
        else margs 0 s avoid tys

(* ------------------------------------------------------------------------- *)
(* Director strings down a term.                                             *)
(* ------------------------------------------------------------------------- *)

/// Returns a path to some subterm satisfying a predicate.
let find_path = 
    let rec find_path p tm = 
        if p tm then []
        elif is_abs tm then "b" :: (find_path p (body tm))
        else 
            try 
                "r" :: (find_path p (rand tm))
            with
            | Failure _ -> "l" :: (find_path p (rator tm))
    fun p tm -> implode(find_path p tm)

/// Find the subterm of a given term indicated by a path.
let follow_path = 
    let rec follow_path s tm = 
        match s with
        | [] -> tm
        | "l" :: t -> follow_path t (rator tm)
        | "r" :: t -> follow_path t (rand tm)
        | _ :: t -> follow_path t (body tm)
    fun s tm -> follow_path (explode s) tm
