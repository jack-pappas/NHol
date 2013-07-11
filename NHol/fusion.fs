(*

Copyright 1998 University of Cambridge
Copyright 1998-2007 John Harrison
Copyright 2013 Jack Pappas, Anh-Dung Phan, Eric Taucher

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

/// Complete HOL kernel of types, terms and theorems.
module NHol.fusion

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

open NHol
open lib

[<AutoOpen>]
module Hol_kernel = 
    type hol_type = 
        | Tyvar of string
        | Tyapp of string * hol_type list
    
    type term = 
        | Var of string * hol_type
        | Const of string * hol_type
        | Comb of term * term
        | Abs of term * term
    
    type thm = 
        | Sequent of (term list * term)
    
    (* ------------------------------------------------------------------------- *)
    (* List of current type constants with their arities.                        *)
    (*                                                                           *)
    (* Initially we just have the boolean type and the function space            *)
    (* constructor. Later on we add as primitive the type of individuals.        *)
    (* All other new types result from definitional extension.                   *)
    (* ------------------------------------------------------------------------- *)

    let the_type_constants = 
        ref ["bool", 0;
             "fun", 2]
    
    (* ------------------------------------------------------------------------- *)
    (* Return all the defined types.                                             *)
    (* ------------------------------------------------------------------------- *)

    /// Lists all the types presently declared.
    let types() = !the_type_constants

    (* ------------------------------------------------------------------------- *)
    (* Lookup function for type constants. Returns arity if it succeeds.         *)
    (* ------------------------------------------------------------------------- *)

    /// Returns the arity of a type constructor.
    let get_type_arity s = assoc s (!the_type_constants)
    
    (* ------------------------------------------------------------------------- *)
    (* Declare a new type.                                                       *)
    (* ------------------------------------------------------------------------- *)

    /// Declares a new type or type constructor.
    let new_type(name, arity) = 
        if can get_type_arity name then failwith("new_type: type " + name + " has already been declared")
        else the_type_constants := (name, arity) :: (!the_type_constants)
    
    (* ------------------------------------------------------------------------- *)
    (* Basic type constructors.                                                  *)
    (* ------------------------------------------------------------------------- *)

    /// Constructs a type (other than a variable type).
    let mk_type(tyop, args) = 
        let arity = 
            try 
                get_type_arity tyop
            with
            | Failure _ -> failwith("mk_type: type " + tyop + " has not been defined")
        if arity = length args then Tyapp(tyop, args)
        else failwith("mk_type: wrong number of arguments to " + tyop)
    
    /// Constructs a type variable of the given name.
    let mk_vartype v = Tyvar(v)
    
    (* ------------------------------------------------------------------------- *)
    (* Basic type destructors.                                                   *)
    (* ------------------------------------------------------------------------- *)

    /// Breaks apart a type (other than a variable type).
    let dest_type = function 
        | (Tyapp(s, ty)) -> s, ty
        | (Tyvar _) -> failwith "dest_type: type variable not a constructor"
    
    /// Breaks a type variable down to its name.
    let dest_vartype = function 
        | (Tyapp(_, _)) -> failwith "dest_vartype: type constructor not a variable"
        | (Tyvar s) -> s
    
    (* ------------------------------------------------------------------------- *)
    (* Basic type discriminators.                                                *)
    (* ------------------------------------------------------------------------- *)

    /// Tests whether a type is an instance of a type constructor.
    let is_type = can dest_type
    /// Tests a type to see if it is a type variable.
    let is_vartype = can dest_vartype
    
    (* ------------------------------------------------------------------------- *)
    (* Return the type variables in a type and in a list of types.               *)
    (* ------------------------------------------------------------------------- *)

    /// Returns a list of the type variables in a type.
    let rec tyvars = function 
        | (Tyapp(_, args)) -> itlist (union << tyvars) args []
        | (Tyvar v as tv) -> [tv]
    
    (* ------------------------------------------------------------------------- *)
    (* Substitute types for type variables.                                      *)
    (*                                                                           *)
    (* NB: non-variables in subst list are just ignored (a check would be        *)
    (* repeated many times), as are repetitions (first possibility is taken).    *)
    (* ------------------------------------------------------------------------- *)

    /// Substitute chosen types for type variables in a type.
    let rec type_subst i ty = 
        match ty with
        | Tyapp(tycon, args) -> 
            let args' = qmap (type_subst i) args
            if args' == args then ty
            else Tyapp(tycon, args')
        | _ -> rev_assocd ty i ty
    
    /// The type ':bool'.
    let bool_ty = Tyapp("bool", [])
    /// The type variable ':A'.
    let aty = Tyvar "A"
    
    (* ------------------------------------------------------------------------- *)
    (* List of term constants and their types.                                   *)
    (*                                                                           *)
    (* We begin with just equality (over all types). Later, the Hilbert choice   *)
    (* operator is added. All other new constants are defined.                   *)
    (* ------------------------------------------------------------------------- *)

    let the_term_constants = 
        ref ["=", Tyapp("fun", [aty;
                                Tyapp("fun", [aty; bool_ty])])]
    
    (* ------------------------------------------------------------------------- *)
    (* Return all the defined constants with generic types.                      *)
    (* ------------------------------------------------------------------------- *)

    /// Returns a list of the constants currently dened.
    let constants() = !the_term_constants

    (* ------------------------------------------------------------------------- *)
    (* Gets type of constant if it succeeds.                                     *)
    (* ------------------------------------------------------------------------- *)

    /// Gets the generic type of a constant from the name of the constant.
    let get_const_type s = assoc s (!the_term_constants)
    
    (* ------------------------------------------------------------------------- *)
    (* Declare a new constant.                                                   *)
    (* ------------------------------------------------------------------------- *)

    /// Declares a new constant.
    let new_constant(name, ty) = 
        if can get_const_type name then failwith("new_constant: constant " + name + " has already been declared")
        else the_term_constants := (name, ty) :: (!the_term_constants)
    
    (* ------------------------------------------------------------------------- *)
    (* Finds the type of a term (assumes it is well-typed).                      *)
    (* ------------------------------------------------------------------------- *)

    /// Returns the type of a term.
    let rec type_of tm = 
        match tm with
        | Var(_, ty) -> ty
        | Const(_, ty) -> ty
        | Comb(s, _) -> hd(tl(snd(dest_type(type_of s))))
        | Abs(Var(_, ty), t) -> 
            Tyapp("fun", [ty;
                          type_of t])
        | _ -> failwith "type_of: not a type of a term"
    
    (* ------------------------------------------------------------------------- *)
    (* Primitive discriminators.                                                 *)
    (* ------------------------------------------------------------------------- *)

    /// Tests a term to see if it is a variable.
    let is_var = 
        function 
        | (Var(_, _)) -> true
        | _ -> false
    
    /// Tests a term to see if it is a constant.
    let is_const = 
        function 
        | (Const(_, _)) -> true
        | _ -> false
    
    /// Tests a term to see if it is an abstraction.
    let is_abs = 
        function 
        | (Abs(_, _)) -> true
        | _ -> false
    
    /// Tests a term to see if it is a combination (function application).
    let is_comb = 
        function 
        | (Comb(_, _)) -> true
        | _ -> false
    
    (* ------------------------------------------------------------------------- *)
    (* Primitive constructors.                                                   *)
    (* ------------------------------------------------------------------------- *)

    /// Constructs a variable of given name and type.
    let mk_var(v, ty) = Var(v, ty)
    
    /// Produce constant term by applying an instantiation to its generic type.
    let mk_const(name, theta) = 
        let uty = 
            try 
                get_const_type name
            with
            | Failure _ -> failwith "mk_const: not a constant name"
        Const(name, type_subst theta uty)
    
    /// Constructs an abstraction.
    let mk_abs(bvar, bod) = 
        match bvar with
        | Var(_, _) -> Abs(bvar, bod)
        | _ -> failwith "mk_abs: not a variable"
    
    /// Constructs a combination.
    let mk_comb(f, a) = 
        match type_of f with
        | Tyapp("fun", [ty; _]) when compare ty (type_of a) = 0 -> Comb(f, a)
        | _ -> failwith "mk_comb: types do not agree"
    
    (* ------------------------------------------------------------------------- *)
    (* Primitive destructors.                                                    *)
    (* ------------------------------------------------------------------------- *)

    /// Breaks apart a variable into name and type.
    let dest_var = 
        function 
        | (Var(s, ty)) -> s, ty
        | _ -> failwith "dest_var: not a variable"
    
    /// Breaks apart a constant into name and type.
    let dest_const = 
        function 
        | (Const(s, ty)) -> s, ty
        | _ -> failwith "dest_const: not a constant"
    
    /// Breaks apart a combination (function application) into rator and rand.
    let dest_comb = 
        function 
        | (Comb(f, x)) -> f, x
        | _ -> failwith "dest_comb: not a combination"
    
    /// Breaks apart an abstraction into abstracted variable and body.
    let dest_abs = 
        function 
        | (Abs(v, b)) -> v, b
        | _ -> failwith "dest_abs: not an abstraction"
    
    (* ------------------------------------------------------------------------- *)
    (* Finds the variables free in a term (list of terms).                       *)
    (* ------------------------------------------------------------------------- *)

    /// Returns a list of the variables free in a term.
    let rec frees tm = 
        match tm with
        | Var(_, _) -> [tm]
        | Const(_, _) -> []
        | Abs(bv, bod) -> subtract (frees bod) [bv]
        | Comb(s, t) -> union (frees s) (frees t)
    
    /// Returns a list of the free variables in a list of terms.
    let freesl tml = itlist (union << frees) tml []
    
    (* ------------------------------------------------------------------------- *)
    (* Whether all free variables in a term appear in a list.                    *)
    (* ------------------------------------------------------------------------- *)
    /// Tests if all free variables of a term appear in a list.
    let rec freesin acc tm = 
        match tm with
        | Var(_, _) -> mem tm acc
        | Const(_, _) -> true
        | Abs(bv, bod) -> freesin (bv :: acc) bod
        | Comb(s, t) -> freesin acc s && freesin acc t
    
    (* ------------------------------------------------------------------------- *)
    (* Whether a variable (or constant in fact) is free in a term.               *)
    (* ------------------------------------------------------------------------- *)

    /// Tests whether a variable (or constant) occurs free in a term.
    let rec vfree_in v tm = 
        match tm with
        | Abs(bv, bod) -> v <> bv && vfree_in v bod
        | Comb(s, t) -> vfree_in v s || vfree_in v t
        | _ -> compare tm v = 0
    
    (* ------------------------------------------------------------------------- *)
    (* Finds the type variables (free) in a term.                                *)
    (* ------------------------------------------------------------------------- *)

    /// Returns the set of type variables used in a term.
    let rec type_vars_in_term tm = 
        match tm with
        | Var(_, ty) -> tyvars ty
        | Const(_, ty) -> tyvars ty
        | Comb(s, t) -> union (type_vars_in_term s) (type_vars_in_term t)
        | Abs(Var(_, ty), t) -> union (tyvars ty) (type_vars_in_term t)
        | _ -> failwith "type_vars_in_term: not a type variable"
    
    (* ------------------------------------------------------------------------- *)
    (* For name-carrying syntax, we need this early.                             *)
    (* ------------------------------------------------------------------------- *)

    /// Modifies a variable name to avoid clashes.
    let rec variant avoid v = 
        if not(exists (vfree_in v) avoid) then v
        else 
            match v with
            | Var(s, ty) -> variant avoid (Var(s + "'", ty))
            | _ -> failwith "variant: not a variable"
    
    (* ------------------------------------------------------------------------- *)
    (* Substitution primitive (substitution for variables only!)                 *)
    (* ------------------------------------------------------------------------- *)

    /// Substitute terms for variables inside a term.
    let vsubst = 
        let rec vsubst ilist tm = 
            match tm with
            | Var(_, _) -> rev_assocd tm ilist tm
            | Const(_, _) -> tm
            | Comb(s, t) -> 
                let s' = vsubst ilist s
                let t' = vsubst ilist t
                if s' == s && t' == t then tm
                else Comb(s', t')
            | Abs(v, s) -> 
                let ilist' = filter (fun (t, x) -> x <> v) ilist
                if ilist' = [] then tm
                else 
                    let s' = vsubst ilist' s
                    if s' == s then tm
                    elif exists (fun (t, x) -> vfree_in v t && vfree_in x s) ilist' then 
                        let v' = variant [s'] v
                        Abs(v', vsubst ((v', v) :: ilist') s)
                    else Abs(v, s')
        fun theta -> 
            if theta = [] then (fun tm -> tm)
            elif forall (fun (t, x) -> type_of t = snd(dest_var x)) theta then vsubst theta
            else failwith "vsubst: Bad substitution list"
    
    (* ------------------------------------------------------------------------- *)
    (* Type instantiation primitive.                                             *)
    (* ------------------------------------------------------------------------- *)

    exception Clash of term
    
    /// Instantiate type variables in a term.
    let inst = 
        let rec inst env tyin tm = 
            match tm with
            | Var(n, ty) -> 
                let ty' = type_subst tyin ty
                let tm' = 
                    if ty' == ty then tm
                    else Var(n, ty')
                if compare (rev_assocd tm' env tm) tm = 0 then tm'
                else raise(Clash tm')
            | Const(c, ty) -> 
                let ty' = type_subst tyin ty
                if ty' == ty then tm
                else Const(c, ty')
            | Comb(f, x) -> 
                let f' = inst env tyin f
                let x' = inst env tyin x
                if f' == f && x' == x then tm
                else Comb(f', x')
            | Abs(y, t) -> 
                let y' = inst [] tyin y
                let env' = (y, y') :: env
                try 
                    let t' = inst env' tyin t
                    if y' == y && t' == t then tm
                    else Abs(y', t')
                with
                | (Clash(w') as ex) -> 
                    if w' <> y' then raise ex
                    else 
                        let ifrees = map (inst [] tyin) (frees t)
                        let y'' = variant ifrees y'
                        let z = Var(fst(dest_var y''), snd(dest_var y))
                        inst env tyin (Abs(z, vsubst [z, y] t))
        fun tyin -> 
            if tyin = [] then fun tm -> tm
            else inst [] tyin
    
    (* ------------------------------------------------------------------------- *)
    (* A few bits of general derived syntax.                                     *)
    (* ------------------------------------------------------------------------- *)

    /// Returns the operator from a combination (function application).
    let rator tm = 
        match tm with
        | Comb(l, r) -> l
        | _ -> failwith "rator: Not a combination"
    
    /// Returns the operand from a combination (function application).
    let rand tm = 
        match tm with
        | Comb(l, r) -> r
        | _ -> failwith "rand: Not a combination"
    
    (* ------------------------------------------------------------------------- *)
    (* Syntax operations for equations.                                          *)
    (* ------------------------------------------------------------------------- *)

    let safe_mk_eq l r = 
        let ty = type_of l
        Comb(Comb(Const("=", Tyapp("fun", [ty;
                                           Tyapp("fun", [ty; bool_ty])])), l), r)
    
    /// Term destructor for equality.
    let dest_eq tm = 
        match tm with
        | Comb(Comb(Const("=", _), l), r) -> l, r
        | _ -> failwith "dest_eq"
    
    (* ------------------------------------------------------------------------- *)
    (* Useful to have term union modulo alpha-conversion for assumption lists.   *)
    (* ------------------------------------------------------------------------- *)

    let rec ordav env x1 x2 = 
        match env with
        | [] -> compare x1 x2
        | (t1, t2) :: oenv -> 
            if compare x1 t1 = 0 then 
                if compare x2 t2 = 0 then 0
                else -1
            elif compare x2 t2 = 0 then 1
            else ordav oenv x1 x2
    
    let rec orda env tm1 tm2 = 
        if tm1 == tm2 && forall (fun (x, y) -> x = y) env then 0
        else 
            match (tm1, tm2) with
            | Var(x1, ty1), Var(x2, ty2) -> ordav env tm1 tm2
            | Const(x1, ty1), Const(x2, ty2) -> compare tm1 tm2
            | Comb(s1, t1), Comb(s2, t2) -> 
                let c = orda env s1 s2
                if c <> 0 then c
                else orda env t1 t2
            | Abs(Var(_, ty1) as x1, t1), Abs(Var(_, ty2) as x2, t2) -> 
                let c = compare ty1 ty2
                if c <> 0 then c
                else orda ((x1, x2) :: env) t1 t2
            | Const(_, _), _ -> -1
            | _, Const(_, _) -> 1
            | Var(_, _), _ -> -1
            | _, Var(_, _) -> 1
            | Comb(_, _), _ -> -1
            | _, Comb(_, _) -> 1
            | _ -> failwith "orda: unexpacted pattern"
    
    /// Total ordering on terms respecting alpha-equivalence.
    let alphaorder = orda []
    
    /// Union of two sets of terms up to alpha-equivalence.
    let rec term_union l1 l2 = 
        match (l1, l2) with
        | ([], l2) -> l2
        | (l1, []) -> l1
        | (h1 :: t1, h2 :: t2) -> 
            let c = alphaorder h1 h2
            if c = 0 then h1 :: (term_union t1 t2)
            elif c < 0 then h1 :: (term_union t1 l2)
            else h2 :: (term_union l1 t2)
    
    let rec term_remove t l = 
        match l with
        | s :: ss -> 
            let c = alphaorder t s
            if c > 0 then 
                let ss' = term_remove t ss
                if ss' == ss then l
                else s :: ss'
            elif c = 0 then ss
            else l
        | [] -> l
    
    let rec term_image f l = 
        match l with
        | h :: t -> 
            let h' = f h
            let t' = term_image f t
            if h' == h && t' == t then l
            else term_union [h'] t'
        | [] -> l
    
    (* ------------------------------------------------------------------------- *)
    (* Basic theorem destructors.                                                *)
    (* ------------------------------------------------------------------------- *)

    /// Breaks a theorem into assumption list and conclusion.
    let dest_thm(Sequent(asl, c)) = (asl, c)
    /// Returns the hypotheses of a theorem.
    let hyp(Sequent(asl, c)) = asl
    /// Returns the conclusion of a theorem.
    let concl(Sequent(asl, c)) = c
    (* ------------------------------------------------------------------------- *)
    (* Basic equality properties; TRANS is derivable but included for efficiency *)
    (* ------------------------------------------------------------------------- *)

    /// Returns theorem expressing reflexivity of equality.
    let REFL tm = Sequent([], safe_mk_eq tm tm)
    
    /// Uses transitivity of equality on two equational theorems.
    let TRANS (Sequent(asl1, c1)) (Sequent(asl2, c2)) = 
        match (c1, c2) with
        | Comb((Comb(Const("=", _), _) as eql), m1), Comb(Comb(Const("=", _), m2), r) when alphaorder m1 m2 = 0 -> 
            Sequent(term_union asl1 asl2, Comb(eql, r))
        | _ -> failwith "TRANS"
    
    (* ------------------------------------------------------------------------- *)
    (* Congruence properties of equality.                                        *)
    (* ------------------------------------------------------------------------- *)

    /// Proves equality of combinations constructed from equal functions and operands.
    let MK_COMB(Sequent(asl1, c1), Sequent(asl2, c2)) = 
        match (c1, c2) with
        | Comb(Comb(Const("=", _), l1), r1), Comb(Comb(Const("=", _), l2), r2) -> 
            (match type_of l1 with
             | Tyapp("fun", [ty; _]) when compare ty (type_of l2) = 0 -> 
                 Sequent(term_union asl1 asl2, safe_mk_eq (Comb(l1, l2)) (Comb(r1, r2)))
             | _ -> failwith "MK_COMB: types do not agree")
        | _ -> failwith "MK_COMB: not both equations"
    
    /// Abstracts both sides of an equation.
    let ABS v (Sequent(asl, c)) = 
        match (v, c) with
        | Var(_, _), Comb(Comb(Const("=", _), l), r) when not(exists (vfree_in v) asl) -> 
            Sequent(asl, safe_mk_eq (Abs(v, l)) (Abs(v, r)))
        | _ -> failwith "ABS"
    
    (* ------------------------------------------------------------------------- *)
    (* Trivial case of lambda calculus beta-conversion.                          *)
    (* ------------------------------------------------------------------------- *)

    /// Special primitive case of beta-reduction.
    let BETA tm = 
        match tm with
        | Comb(Abs(v, bod), arg) when compare arg v = 0 -> Sequent([], safe_mk_eq tm bod)
        | _ -> failwith "BETA: not a trivial beta-redex"
    
    (* ------------------------------------------------------------------------- *)
    (* Rules connected with deduction.                                           *)
    (* ------------------------------------------------------------------------- *)

    /// Introduces an assumption.
    let ASSUME tm = 
        if compare (type_of tm) bool_ty = 0 then Sequent([tm], tm)
        else failwith "ASSUME: not a proposition"
    
    /// Equality version of the Modus Ponens rule.
    let EQ_MP (Sequent(asl1, eq)) (Sequent(asl2, c)) = 
        match eq with
        | Comb(Comb(Const("=", _), l), r) when alphaorder l c = 0 -> Sequent(term_union asl1 asl2, r)
        | _ -> failwith "EQ_MP"
    
    /// Deduces logical equivalence from deduction in both directions.
    let DEDUCT_ANTISYM_RULE (Sequent(asl1, c1)) (Sequent(asl2, c2)) = 
        let asl1' = term_remove c2 asl1
        let asl2' = term_remove c1 asl2
        Sequent(term_union asl1' asl2', safe_mk_eq c1 c2)
    
    (* ------------------------------------------------------------------------- *)
    (* Type and term instantiation.                                              *)
    (* ------------------------------------------------------------------------- *)

    /// Instantiates types in a theorem.
    let INST_TYPE theta (Sequent(asl, c)) = 
        let inst_fn = inst theta
        Sequent(term_image inst_fn asl, inst_fn c)
    
    /// Instantiates free variables in a theorem.
    let INST theta (Sequent(asl, c)) = 
        let inst_fun = vsubst theta
        Sequent(term_image inst_fun asl, inst_fun c)
    
    (* ------------------------------------------------------------------------- *)
    (* Handling of axioms.                                                       *)
    (* ------------------------------------------------------------------------- *)

    let the_axioms = ref([] : thm list)
    /// Returns the current set of axioms.
    let axioms() = !the_axioms
    
    /// Sets up a new axiom.
    let new_axiom tm = 
        if compare (type_of tm) bool_ty = 0 then 
            let th = Sequent([], tm)
            (the_axioms := th :: (!the_axioms)
             th)
        else failwith "new_axiom: Not a proposition"
    
    (* ------------------------------------------------------------------------- *)
    (* Handling of (term) definitions.                                           *)
    (* ------------------------------------------------------------------------- *)

    /// List of all definitions introduced so far.
    let the_definitions = ref([] : thm list)
    /// Returns the current set of primitive definitions.
    let definitions() = !the_definitions
    
    /// Makes a simple new definition of the form 'c = t'.
    let new_basic_definition tm = 
        match tm with
        | Comb(Comb(Const("=", _), Var(cname, ty)), r) -> 
            if not(freesin [] r) then failwith "new_definition: term not closed"
            elif not(subset (type_vars_in_term r) (tyvars ty)) then 
                failwith "new_definition: Type variables not reflected in constant"
            else 
                let c = 
                    new_constant(cname, ty)
                    Const(cname, ty)
                let dth = Sequent([], safe_mk_eq c r)
                the_definitions := dth :: (!the_definitions)
                dth
        | _ -> failwith "new_basic_definition"
    
    (* ------------------------------------------------------------------------- *)
    (* Handling of type definitions.                                             *)
    (*                                                                           *)
    (* This function now involves no logical constants beyond equality.          *)
    (*                                                                           *)
    (*             |- P t                                                        *)
    (*    ---------------------------                                            *)
    (*        |- abs(rep a) = a                                                  *)
    (*     |- P r = (rep(abs r) = r)                                             *)
    (*                                                                           *)
    (* Where "abs" and "rep" are new constants with the nominated names.         *)
    (* ------------------------------------------------------------------------- *)

    /// Introduces a new type in bijection with a nonempty subset of an existing type.
    let new_basic_type_definition tyname (absname, repname) (Sequent(asl, c)) = 
        if exists (can get_const_type) [absname; repname] then 
            failwith "new_basic_type_definition: Constant(s) already in use"
        elif not(asl = []) then failwith "new_basic_type_definition: Assumptions in theorem"
        else 
            let P, x = 
                try 
                    dest_comb c
                with
                | Failure _ -> failwith "new_basic_type_definition: Not a combination"
            if not(freesin [] P) then failwith "new_basic_type_definition: Predicate is not closed"
            else 
                let tyvars = sort (<=) (type_vars_in_term P)
                let _ = 
                    try 
                        new_type(tyname, length tyvars)
                    with
                    | Failure _ -> failwith "new_basic_type_definition: Type already defined"
                let aty = Tyapp(tyname, tyvars)
                let rty = type_of x
                let absty = Tyapp("fun", [rty; aty])
                let repty = Tyapp("fun", [aty; rty])
                let abs = 
                    (new_constant(absname, absty)
                     Const(absname, absty))
                let rep = 
                    (new_constant(repname, repty)
                     Const(repname, repty))
                let a = Var("a", aty)
                let r = Var("r", rty)
                Sequent([], safe_mk_eq (Comb(abs, mk_comb(rep, a))) a), 
                Sequent([], safe_mk_eq (Comb(P, r)) (safe_mk_eq (mk_comb(rep, mk_comb(abs, r))) r))

(* ------------------------------------------------------------------------- *)
(* Stuff that didn't seem worth putting in.                                  *)
(* ------------------------------------------------------------------------- *)

/// Construct a function type.
let mk_fun_ty ty1 ty2 = mk_type("fun", [ty1; ty2])
/// The type variable ':B'.
let bty = mk_vartype "B"

/// Tests a term to see if it is an equation.
let is_eq tm = 
    match tm with
    | Comb(Comb(Const("=", _), _), _) -> true
    | _ -> false

/// Constructs an equation.
let mk_eq = 
    let eq = mk_const("=", [])
    fun (l, r) -> 
        try 
            let ty = type_of l
            let eq_tm = inst [ty, aty] eq
            mk_comb(mk_comb(eq_tm, l), r)
        with
        | Failure _ -> failwith "mk_eq"

(* ------------------------------------------------------------------------- *)
(* Tests for alpha-convertibility (equality ignoring names in abstractions). *)
(* ------------------------------------------------------------------------- *)

/// Tests for alpha-convertibility of terms.
let aconv s t =
    alphaorder s t = 0

(* ------------------------------------------------------------------------- *)
(* Comparison function on theorems. Currently the same as equality, but      *)
(* it's useful to separate because in the proof-recording version it isn't.  *)
(* ------------------------------------------------------------------------- *)

/// Equality test on theorems.
let equals_thm th th' =
    dest_thm th = dest_thm th'
