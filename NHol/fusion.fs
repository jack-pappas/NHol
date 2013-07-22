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

#if INTERACTIVE
#else
/// Complete HOL kernel of types, terms and theorems.
module NHol.fusion

open System

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

open NHol
open lib
#endif

[<AutoOpen>]
module Hol_kernel = 
    type hol_type = 
        | Tyvar of string
        | Tyapp of string * hol_type list
        override this.ToString() = 
            match this with
            | Tyvar s -> "Tyvar \"" + s + "\""
            | Tyapp(s, htlist) -> "Tyapp (\"" + s + "\", " + htlist.ToString() + ")"
    
    type term = 
        | Var of string * hol_type
        | Const of string * hol_type
        | Comb of term * term
        | Abs of term * term
        override this.ToString() = 
            match this with
            | Var(s, t) -> "Var (\"" + s + "\", " + t.ToString() + ")"
            | Const(s, t) -> "Const (\"" + s + "\", " + t.ToString() + ")"
            | Comb(t1, t2) -> "Comb (" + t1.ToString() + ", " + t2.ToString() + ")"
            | Abs(t1, t2) -> 
                "Abs (\"" + t1.ToString() + "\", " + t2.ToString() + ")"
    
    type thm0 = 
        | Sequent of (term list * term)
        override this.ToString() = 
            match this with
            | Sequent(tlist, t) -> 
                "Sequent (" + tlist.ToString() + ", " + t.ToString() + ")"

    type thm = Choice<thm0, exn>
    
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
    let get_type_arity s =
        match assoc s !the_type_constants with
        | Some result -> Choice.succeed result
        | None -> Choice.failwith "find"
    
    (* ------------------------------------------------------------------------- *)
    (* Declare a new type.                                                       *)
    (* ------------------------------------------------------------------------- *)

    /// Declares a new type or type constructor.
    let new_type(name, arity) =
        if Choice.isResult <| get_type_arity name then failwith("new_type: type " + name + " has already been declared")
        else the_type_constants := (name, arity) :: (!the_type_constants)
    
    (* ------------------------------------------------------------------------- *)
    (* Basic type constructors.                                                  *)
    (* ------------------------------------------------------------------------- *)

    /// Constructs a type (other than a variable type).
    let mk_type(tyop, args) =  
        let arity = get_type_arity tyop
        arity 
        |> Choice.bind (fun arity ->      
            if arity = length args then Choice.succeed <| Tyapp(tyop, args)
            else Choice.failwith ("mk_type: wrong number of arguments to " + tyop))
        |> Choice.bindError (fun e -> Choice.nestedFailwith e ("mk_type: type " + tyop + " has not been defined"))
    
    /// Constructs a type variable of the given name.
    let mk_vartype v = Tyvar(v)
    
    (* ------------------------------------------------------------------------- *)
    (* Basic type destructors.                                                   *)
    (* ------------------------------------------------------------------------- *)

    /// Breaks apart a type (other than a variable type).
    let dest_type = function 
        | (Tyapp(s, ty)) ->
            Choice.succeed (s, ty)
        | (Tyvar _) ->
            Choice.failwith "dest_type: type variable not a constructor"
    
    /// Breaks a type variable down to its name.
    let dest_vartype = function 
        | (Tyvar s) ->
            Choice.succeed s
        | (Tyapp(_, _)) ->
            Choice.failwith "dest_vartype: type constructor not a variable"
            
    (* ------------------------------------------------------------------------- *)
    (* Basic type discriminators.                                                *)
    (* ------------------------------------------------------------------------- *)

    /// Tests whether a type is an instance of a type constructor.
    let is_type = Choice.isResult << dest_type

    /// Tests a type to see if it is a type variable.
    let is_vartype = Choice.isResult << dest_vartype
    
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
        ref ["=", Tyapp("fun", [aty; Tyapp("fun", [aty; bool_ty])])]
    
    (* ------------------------------------------------------------------------- *)
    (* Return all the defined constants with generic types.                      *)
    (* ------------------------------------------------------------------------- *)

    /// Returns a list of the constants currently dened.
    let constants() = !the_term_constants

    (* ------------------------------------------------------------------------- *)
    (* Gets type of constant if it succeeds.                                     *)
    (* ------------------------------------------------------------------------- *)

    /// Gets the generic type of a constant from the name of the constant.
    let get_const_type s =
        match assoc s !the_term_constants with
        | Some result -> Choice.succeed result
        | None -> Choice.failwith "find"
    
    (* ------------------------------------------------------------------------- *)
    (* Declare a new constant.                                                   *)
    (* ------------------------------------------------------------------------- *)

    /// Declares a new constant.
    let new_constant(name, ty) =
        if Choice.isResult <| get_const_type name then failwith("new_constant: constant " + name + " has already been declared")
        else the_term_constants := (name, ty) :: (!the_term_constants)
    
    (* ------------------------------------------------------------------------- *)
    (* Finds the type of a term (assumes it is well-typed).                      *)
    (* ------------------------------------------------------------------------- *)

    /// Returns the type of a term.
    let type_of tm = 
        let rec type_of tm = 
            match tm with
            | Var(_, ty) -> ty
            | Const(_, ty) -> ty
            | Comb(s, _) -> hd(tl(snd(Choice.get <| dest_type(type_of s))))
            | Abs(Var(_, ty), t) -> 
                Tyapp("fun", [ty; type_of t])
            | _ -> failwith "type_of: not a type of a term"
        try
            Choice.succeed <| type_of tm
        with Failure s ->
            Choice.failwith s
    
    (* ------------------------------------------------------------------------- *)
    (* Primitive discriminators.                                                 *)
    (* ------------------------------------------------------------------------- *)

    /// Tests a term to see if it is a variable.
    let is_var = 
        function 
        | Var(_, _) -> true
        | _ -> false
    
    /// Tests a term to see if it is a constant.
    let is_const = 
        function 
        | Const(_, _) -> true
        | _ -> false
    
    /// Tests a term to see if it is an abstraction.
    let is_abs = 
        function 
        | Abs(_, _) -> true
        | _ -> false
    
    /// Tests a term to see if it is a combination (function application).
    let is_comb = 
        function 
        | Comb(_, _) -> true
        | _ -> false
    
    (* ------------------------------------------------------------------------- *)
    (* Primitive constructors.                                                   *)
    (* ------------------------------------------------------------------------- *)

    /// Constructs a variable of given name and type.
    let mk_var(v, ty) = Var(v, ty)
    
    /// Produce constant term by applying an instantiation to its generic type.
    let mk_const(name, theta) = 
        let uty = get_const_type name
        uty
        |> Choice.map (fun uty -> Const(name, type_subst theta uty))
        |> Choice.bindError (fun e -> 
            Choice.nestedFailwith e "mk_const: not a constant name")
    
    /// Constructs an abstraction.
    let mk_abs(bvar, bod) = 
        match bvar with
        | Var(_, _) -> Choice.succeed <| Abs(bvar, bod)
        | _ -> Choice.failwith "mk_abs: not a variable"
    
    /// Constructs a combination.
    let mk_comb(f, a) = 
        type_of f 
        |> Choice.bind (fun ty0 -> 
            match ty0 with
            | Tyapp("fun", [ty; _]) ->
                type_of a
                |> Choice.bind (fun ta ->
                    if compare ty ta = 0 then Choice.succeed <| Comb(f, a)
                    else Choice.failwith "mk_comb: types do not agree")
            | _ -> Choice.failwith "mk_comb: types do not agree")

    (* ------------------------------------------------------------------------- *)
    (* Primitive destructors.                                                    *)
    (* ------------------------------------------------------------------------- *)

    /// Breaks apart a variable into name and type.
    let dest_var = 
        function 
        | Var(s, ty) -> Choice.succeed (s, ty)
        | _ -> Choice.failwith "dest_var: not a variable"
    
    /// Breaks apart a constant into name and type.
    let dest_const = 
        function 
        | Const(s, ty) -> Choice.succeed (s, ty)
        | _ -> Choice.failwith "dest_const: not a constant"
    
    /// Breaks apart a combination (function application) into Choice.get <| rator and Choice.get <| rand.
    let dest_comb = 
        function 
        | Comb(f, x) -> Choice.succeed (f, x)
        | _ -> Choice.failwith "dest_comb: not a combination"
    
    /// Breaks apart an abstraction into abstracted variable and body.
    let dest_abs = 
        function 
        | Abs(v, b) -> Choice.succeed (v, b)
        | _ -> Choice.failwith "dest_abs: not an abstraction"
    
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
    let type_vars_in_term tm = 
        let rec type_vars_in_term tm = 
            match tm with
            | Var(_, ty) -> tyvars ty
            | Const(_, ty) -> tyvars ty
            | Comb(s, t) -> union (type_vars_in_term s) (type_vars_in_term t)
            | Abs(Var(_, ty), t) -> union (tyvars ty) (type_vars_in_term t)
            | _ -> failwith "type_vars_in_term: not a type variable"
        try
            Choice.succeed <| type_vars_in_term tm
        with Failure s ->
            Choice.failwith s

    (* ------------------------------------------------------------------------- *)
    (* For name-carrying syntax, we need this early.                             *)
    (* ------------------------------------------------------------------------- *)

    /// Modifies a variable name to avoid clashes.
    let rec variant avoid v = 
        if not(exists (vfree_in v) avoid) then Choice.succeed v
        else 
            match v with
            | Var(s, ty) -> variant avoid (Var(s + "'", ty))
            | _ -> Choice.failwith "variant: not a variable"
    
    (* ------------------------------------------------------------------------- *)
    (* Substitution primitive (substitution for variables only!)                 *)
    (* ------------------------------------------------------------------------- *)

    /// Substitute terms for variables inside a term.
    let vsubst = 
        let vsubst ilist tm = 
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
                            let v' = Choice.get <| variant [s'] v
                            Abs(v', vsubst ((v', v) :: ilist') s)
                        else Abs(v, s')
            try
                Choice.succeed <| vsubst ilist tm
            with Failure s ->
                Choice.failwith s

        fun theta -> 
            if theta = [] then Choice.succeed
            elif forall (fun (t, x) -> 
                    match type_of t, dest_var x with
                    | Success r1, Success r2 -> r1 = snd r2
                    | _ -> false) theta then vsubst theta
            else fun tm -> Choice.failwith "vsubst: Bad substitution list"
    
    (* ------------------------------------------------------------------------- *)
    (* Type instantiation primitive.                                             *)
    (* ------------------------------------------------------------------------- *)

    exception Clash of term
    
    /// Instantiate type variables in a term.
    let inst = 
        let inst env tyin tm =
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
                    | Clash(w') as ex -> 
                        if w' <> y' then raise ex
                        else 
                            let ifrees = map (inst [] tyin) (frees t)
                            let y'' = Choice.get <| variant ifrees y'
                            let z = Var(fst(Choice.get <| dest_var y''), snd(Choice.get <| dest_var y))
                            inst env tyin (Abs(z, Choice.get <| vsubst [z, y] t))
            try
                Choice.succeed <| inst env tyin tm
            with 
            | :? Clash as ex ->
                Choice2Of2 (ex :> exn)
            | Failure s ->
                Choice.failwith s

        fun tyin -> 
            if tyin = [] then Choice.succeed
            else inst [] tyin
    
    (* ------------------------------------------------------------------------- *)
    (* A few bits of general derived syntax.                                     *)
    (* ------------------------------------------------------------------------- *)

    /// Returns the operator from a combination (function application).
    let rator tm = 
        match tm with
        | Comb(l, r) -> Choice.succeed l
        | _ -> Choice.failwith "rator: Not a combination"
    
    /// Returns the operand from a combination (function application).
    let rand tm = 
        match tm with
        | Comb(l, r) -> Choice.succeed r
        | _ -> Choice.failwith "rand: Not a combination"
    
    (* ------------------------------------------------------------------------- *)
    (* Syntax operations for equations.                                          *)
    (* ------------------------------------------------------------------------- *)

    let safe_mk_eq l r = 
        type_of l
        |> Choice.map (fun ty ->
            Comb(Comb(Const("=", Tyapp("fun", [ty; Tyapp("fun", [ty; bool_ty])])), l), r))
    
    /// Term destructor for equality.
    let dest_eq tm = 
        match tm with
        | Comb(Comb(Const("=", _), l), r) -> Choice.succeed (l, r)
        | _ -> Choice.failwith "dest_eq"
    
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
            | _ -> failwith "orda: unexpected pattern"
    
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
    let REFL tm = 
        safe_mk_eq tm tm
        |> Choice.map (fun tm' -> Sequent([], tm'))

    /// Uses transitivity of equality on two equational theorems.
    let TRANS thm1 thm2 = 
        let TRANS (Sequent(asl1, c1)) (Sequent(asl2, c2)) =
            match (c1, c2) with
            | Comb((Comb(Const("=", _), _) as eql), m1), Comb(Comb(Const("=", _), m2), r) when alphaorder m1 m2 = 0 -> 
                Choice.succeed <| Sequent(term_union asl1 asl2, Comb(eql, r))
            | _ -> Choice.failwith "TRANS"
        Choice.bind2 TRANS thm1 thm2
    
    (* ------------------------------------------------------------------------- *)
    (* Congruence properties of equality.                                        *)
    (* ------------------------------------------------------------------------- *)

    /// Proves equality of combinations constructed from equal functions and operands.
    let MK_COMB(thm1, thm2) =
        let MK_COMB(Sequent(asl1, c1), Sequent(asl2, c2)) = 
            match (c1, c2) with
            | Comb(Comb(Const("=", _), l1), r1), Comb(Comb(Const("=", _), l2), r2) ->
                match type_of l1, type_of l2 with
                | Success ty1, Success ty2 -> 
                    match ty1 with
                    | Tyapp("fun", [ty; _]) when compare ty ty2 = 0 -> 
                        safe_mk_eq (Comb(l1, l2)) (Comb(r1, r2))
                        |> Choice.map (fun tm -> Sequent(term_union asl1 asl2, tm))
                    | _ -> Choice.failwith "MK_COMB: types do not agree"
                | _ -> Choice.failwith "MK_COMB: not both equations"
            | _ -> Choice.failwith "MK_COMB: not both equations"
        Choice.bind2 (curry MK_COMB) thm1 thm2
    
    /// Abstracts both sides of an equation.
    let ABS v thm =
        let ABS v (Sequent(asl, c)) = 
            match (v, c) with
            | Var(_, _), Comb(Comb(Const("=", _), l), r) when not(exists (vfree_in v) asl) ->
                safe_mk_eq (Abs(v, l)) (Abs(v, r))
                |> Choice.map (fun tm -> Sequent(asl, tm))
            | _ -> Choice.failwith "ABS"
        Choice.bind (ABS v) thm
    
    (* ------------------------------------------------------------------------- *)
    (* Trivial case of lambda calculus beta-conversion.                          *)
    (* ------------------------------------------------------------------------- *)

    /// Special primitive case of beta-reduction.
    let BETA tm =
        match tm with
        | Comb(Abs(v, bod), arg) when compare arg v = 0 -> 
            safe_mk_eq tm bod
            |> Choice.map (fun tm -> Sequent([], tm))
        | _ -> Choice.failwith "BETA: not a trivial beta-redex"
    
    (* ------------------------------------------------------------------------- *)
    (* Rules connected with deduction.                                           *)
    (* ------------------------------------------------------------------------- *)

    /// Introduces an assumption.
    let ASSUME tm = 
        type_of tm 
        |> Choice.bind (fun ty ->
            if compare ty bool_ty = 0 then Choice.succeed <| Sequent([tm], tm)
            else Choice.failwith "ASSUME: not a proposition")
    
    /// Equality version of the Modus Ponens rule.
    let EQ_MP thm1 thm2 =
        let EQ_MP (Sequent(asl1, eq)) (Sequent(asl2, c)) = 
            match eq with
            | Comb(Comb(Const("=", _), l), r) when alphaorder l c = 0 -> 
                Choice.succeed <| Sequent(term_union asl1 asl2, r)
            | _ -> Choice.failwith "EQ_MP"
        Choice.bind2 EQ_MP thm1 thm2
    
    /// Deduces logical equivalence from deduction in both directions.
    let DEDUCT_ANTISYM_RULE thm1 thm2 =
        let DEDUCT_ANTISYM_RULE (Sequent(asl1, c1)) (Sequent(asl2, c2)) = 
            let asl1' = term_remove c2 asl1
            let asl2' = term_remove c1 asl2
            safe_mk_eq c1 c2
            |> Choice.map (fun tm -> Sequent(term_union asl1' asl2', tm))
        Choice.bind2 DEDUCT_ANTISYM_RULE thm1 thm2
    
    (* ------------------------------------------------------------------------- *)
    (* Type and term instantiation.                                              *)
    (* ------------------------------------------------------------------------- *)

    /// Instantiates types in a theorem.
    let INST_TYPE theta thm =
        // TODO: revise this
        let INST_TYPE theta (Sequent(asl, c)) = 
            try
                let inst_fn = Choice.get << inst theta
                Choice.succeed <| Sequent(term_image inst_fn asl, inst_fn c)
            with Failure s ->
                Choice.failwith s
        Choice.bind (INST_TYPE theta) thm
    
    /// Instantiates free variables in a theorem.
    let INST theta thm =
        // TODO: revise this
        let INST theta (Sequent(asl, c)) = 
            try
                let inst_fun = Choice.get << vsubst theta
                Choice.succeed <| Sequent(term_image inst_fun asl, inst_fun c)
            with Failure s ->
                Choice.failwith s
        Choice.bind (INST theta) thm
    
    (* ------------------------------------------------------------------------- *)
    (* Handling of axioms.                                                       *)
    (* ------------------------------------------------------------------------- *)

    let the_axioms = ref([] : thm list)

    /// Returns the current set of axioms.
    let axioms() = !the_axioms
    
    /// Sets up a new axiom.
    let new_axiom tm = 
        type_of tm
        |> Choice.bind (fun ty ->
            if compare ty bool_ty = 0 then 
                let th = Choice.succeed <| Sequent([], tm)
                the_axioms := th :: (!the_axioms)
                th
            else Choice.failwith "new_axiom: Not a proposition")
    
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
            if not(freesin [] r) then Choice.failwith "new_definition: term not closed"
            else
                type_vars_in_term r
                |> Choice.bind (fun ty' ->
                    if not(subset ty' (tyvars ty)) then 
                        Choice.failwith "new_definition: Type variables not reflected in constant"
                    else 
                        let c = 
                            new_constant(cname, ty)
                            Const(cname, ty)
                        let dth = safe_mk_eq c r |> Choice.map (fun tm -> Sequent([], tm))
                        the_definitions := dth :: (!the_definitions)
                        dth)
        | _ -> Choice.failwith "new_basic_definition"
    
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
    let new_basic_type_definition tyname (absname, repname) thm =
        match thm with
        | Success (Sequent(asl, c)) ->
            /// Tests for failure.
            let can f x = 
                try f x |> ignore; true
                with Failure _ -> false

            if exists (can get_const_type) [absname; repname] then 
                Choice.failwithPair "new_basic_type_definition: Constant(s) already in use"
            elif not(asl = []) then Choice.failwithPair "new_basic_type_definition: Assumptions in theorem"
            else 
                let P, x = 
                    try 
                        Choice.get <| dest_comb c
                    with
                    | Failure _ as e ->
                        nestedFailwith e "new_basic_type_definition: Not a combination"
                if not(freesin [] P) then Choice.failwithPair "new_basic_type_definition: Predicate is not closed"
                else 
                    let tyvars = sort (<=) (Choice.get <| type_vars_in_term P)
                    let _ = 
                        try 
                            new_type(tyname, length tyvars)
                        with
                        | Failure _ as e ->
                            nestedFailwith e "new_basic_type_definition: Type already defined"
                    let aty = Tyapp(tyname, tyvars)
                    let rty = Choice.get <| type_of x
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
                    safe_mk_eq (Comb(abs, Choice.get <| mk_comb(rep, a))) a |> Choice.map (fun tm -> Sequent([], tm)),
                    (safe_mk_eq (Choice.get <| mk_comb(rep, Choice.get <| mk_comb(abs, r))) r)
                    |> Choice.bind (fun tm -> safe_mk_eq (Comb(P, r)) tm
                                              |> Choice.map (fun tm' -> Sequent([], tm')))
        | Error _ ->
            Choice.failwithPair "new_basic_type_definition: Erroneous theorem"

(* ------------------------------------------------------------------------- *)
(* Stuff that didn't seem worth putting in.                                  *)
(* ------------------------------------------------------------------------- *)

/// Construct a function type.
let mk_fun_ty ty1 ty2 = Choice.get <| mk_type ("fun", [ty1; ty2])

/// The type variable ':B'.
let bty = mk_vartype "B"

/// Tests a term to see if it is an equation.
let is_eq tm = 
    match tm with
    | Comb(Comb(Const("=", _), _), _) -> true
    | _ -> false

/// Constructs an equation.
let mk_eq = 
    let eq = Choice.get <| mk_const("=", [])
    fun (l, r) -> 
        try 
            let ty = Choice.get <| type_of l
            let eq_tm = Choice.get <| inst [ty, aty] eq
            Choice.get <| mk_comb(Choice.get <| mk_comb(eq_tm, l), r)
        with
        | Failure _ as e ->
            nestedFailwith e "mk_eq"

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
