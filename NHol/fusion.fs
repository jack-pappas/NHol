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

#if USE
#else
/// Complete HOL kernel of types, terms and theorems.
module NHol.fusion

open System

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num
open ExtCore.Control
open ExtCore.Control.Collections

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
        | Sequent of term list * term
        override this.ToString() =
            match this with
            | Sequent(tlist, t) -> 
                "Sequent (" + tlist.ToString() + ", " + t.ToString() + ")"

    type thm = Protected<thm0>
    
    (* ------------------------------------------------------------------------- *)
    (* List of current type constants with their arities.                        *)
    (*                                                                           *)
    (* Initially we just have the boolean type and the function space            *)
    (* constructor. Later on we add as primitive the type of individuals.        *)
    (* All other new types result from definitional extension.                   *)
    (* ------------------------------------------------------------------------- *)

    let the_type_constants = 
        ref ["bool", 0; "fun", 2]
    
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
        | Some result ->
            Choice.result result
        | None ->
            Choice.failwith "find"
    
    (* ------------------------------------------------------------------------- *)
    (* Declare a new type.                                                       *)
    (* ------------------------------------------------------------------------- *)

    /// Declares a new type or type constructor.
    let new_type(name, arity) =
        if Choice.isResult <| get_type_arity name then
            let msg = sprintf "new_type: type %s has already been declared" name
            Choice.failwith msg
        else
            the_type_constants := (name, arity) :: !the_type_constants
            Choice.result ()
    
    (* ------------------------------------------------------------------------- *)
    (* Basic type constructors.                                                  *)
    (* ------------------------------------------------------------------------- *)

    /// Constructs a type (other than a variable type).
    let mk_type(tyop, args) : Protected<hol_type> =
        choice {
        let! arity = get_type_arity tyop
        if arity = length args then
            return Tyapp(tyop, args)
        else
            return! Choice.failwith ("mk_type: wrong number of arguments to " + tyop)
        }
        |> Choice.mapError (fun ex ->
            nestedFailure ex ("mk_type: type " + tyop + " has not been defined"))

    /// Constructs a type variable of the given name.
    let mk_vartype v = Tyvar(v)
    
    (* ------------------------------------------------------------------------- *)
    (* Basic type destructors.                                                   *)
    (* ------------------------------------------------------------------------- *)

    /// Breaks apart a type (other than a variable type).
    let dest_type = function 
        | (Tyapp(s, ty)) ->
            Choice.result (s, ty)
        | (Tyvar _) ->
            Choice.failwith "dest_type: type variable not a constructor"
    
    /// Breaks a type variable down to its name.
    let dest_vartype = function 
        | (Tyvar s) ->
            Choice.result s
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

    /// Returns a list of the constants currently defined.
    let constants() = !the_term_constants

    (* ------------------------------------------------------------------------- *)
    (* Gets type of constant if it succeeds.                                     *)
    (* ------------------------------------------------------------------------- *)

    /// Gets the generic type of a constant from the name of the constant.
    let get_const_type s : Protected<hol_type> =
        choice {
        match assoc s !the_term_constants with
        | Some result -> 
            return result
        | None -> 
            return! Choice.failwith "find"
        }
    
    (* ------------------------------------------------------------------------- *)
    (* Declare a new constant.                                                   *)
    (* ------------------------------------------------------------------------- *)

    /// Declares a new constant.
    let new_constant(name, ty) : Protected<unit> =
        if Choice.isResult <| get_const_type name then 
            Choice.failwith("new_constant: constant " + name + " has already been declared")
        else 
            Choice.result (the_term_constants := (name, ty) :: (!the_term_constants))
    
    (* ------------------------------------------------------------------------- *)
    (* Finds the type of a term (assumes it is well-typed).                      *)
    (* ------------------------------------------------------------------------- *)

    /// Returns the type of a term.
    // OPTIMIZE : Use ChoiceCont from ExtCore here to recurse in bounded stack space.
    let type_of tm : Protected<hol_type> =
        let rec type_of tm =
            choice {
            match tm with
            | Var(_, ty) ->
                return ty
            | Const(_, ty) ->
                return ty
            | Comb(s, _) ->
                let! type_of_s = type_of s
                let! dest_type_of_s = dest_type type_of_s
                return hd (tl (snd dest_type_of_s))
            | Abs(Var(_, ty), t) ->
                let! type_of_t = type_of t
                return Tyapp("fun", [ty; type_of_t])
            | _ ->
                return! Choice.failwith "type_of: not a type of a term"
            }

        type_of tm
    
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
    let mk_const(name, theta) : Protected<term> = 
        choice {
            let! uty = get_const_type name
            return Const(name, type_subst theta uty)
        }
        |> Choice.mapError (fun e -> 
            nestedFailure e "mk_const: not a constant name")
    
    /// Constructs an abstraction.
    let mk_abs(bvar, bod) : Protected<term> =
        choice {
        match bvar with
        | Var(_, _) ->
            return Abs(bvar, bod)
        | _ ->
            return! Choice.failwith "mk_abs: not a variable"
        }    
    
    /// Constructs a combination.
    let mk_comb(f, a) : Protected<term> =
        choice {
        let! ty0 = type_of f
        match ty0 with
        | Tyapp("fun", [ty; _]) ->
            let! ta = type_of a
            if compare ty ta = 0 then
                return Comb(f, a)
            else
                return! Choice.failwith "mk_comb: types do not agree"
        | _ ->
            return! Choice.failwith "mk_comb: types do not agree"
        }

    (* ------------------------------------------------------------------------- *)
    (* Primitive destructors.                                                    *)
    (* ------------------------------------------------------------------------- *)

    /// Breaks apart a variable into name and type.
    let dest_var tm : Protected<string * hol_type> = 
        match tm with
        | Var(s, ty) -> 
            Choice.result (s, ty)
        | _ -> 
            Choice.failwith "dest_var: not a variable"
    
    /// Breaks apart a constant into name and type.
    let dest_const tm : Protected<string * hol_type> = 
        match tm with
        | Const(s, ty) -> 
            Choice.result (s, ty)
        | _ -> 
            Choice.failwith "dest_const: not a constant"
    
    /// Breaks apart a combination (function application) into rator and rand.
    let dest_comb tm : Protected<term * term> = 
        match tm with
        | Comb(f, x) -> 
            Choice.result (f, x)
        | _ -> 
            Choice.failwith "dest_comb: not a combination"
    
    /// Breaks apart an abstraction into abstracted variable and body.
    let dest_abs tm : Protected<term * term> = 
        match tm with
        | Abs(v, b) -> 
            Choice.result (v, b)
        | _ -> 
            Choice.failwith "dest_abs: not an abstraction"
    
    (* ------------------------------------------------------------------------- *)
    (* Finds the variables free in a term (list of terms).                       *)
    (* ------------------------------------------------------------------------- *)

    /// Returns a list of the variables free in a term.
    let rec frees tm =
        match tm with
        | Const(_, _) ->
            []
        | Var(_, _) ->
            [tm]
        | Abs(bv, bod) ->
            subtract (frees bod) [bv]
        | Comb(s, t) ->
            union (frees s) (frees t)
    
    /// Returns a list of the free variables in a list of terms.
    let freesl tml = itlist (union << frees) tml []
    
    (* ------------------------------------------------------------------------- *)
    (* Whether all free variables in a term appear in a list.                    *)
    (* ------------------------------------------------------------------------- *)
    /// Tests if all free variables of a term appear in a list.
    let rec freesin acc tm =
        match tm with
        | Const(_, _) ->
            true
        | Var(_, _) ->
            mem tm acc
        | Abs(bv, bod) ->
            freesin (bv :: acc) bod
        | Comb(s, t) ->
            freesin acc s && freesin acc t
    
    (* ------------------------------------------------------------------------- *)
    (* Whether a variable (or constant in fact) is free in a term.               *)
    (* ------------------------------------------------------------------------- *)

    /// Tests whether a variable (or constant) occurs free in a term.
    let rec vfree_in v tm =
        match tm with
        | Abs(bv, bod) ->
            v <> bv && vfree_in v bod
        | Comb(s, t) ->
            vfree_in v s || vfree_in v t
        | _ ->
            compare tm v = 0
    
    (* ------------------------------------------------------------------------- *)
    (* Finds the type variables (free) in a term.                                *)
    (* ------------------------------------------------------------------------- *)

    /// Returns the set of type variables used in a term.
    let rec type_vars_in_term tm : Protected<hol_type list> =
        choice {
            match tm with
            | Var(_, ty) -> 
                return tyvars ty
            | Const(_, ty) -> 
                return tyvars ty
            | Comb(s, t) -> 
                let! l = type_vars_in_term s
                let! r = type_vars_in_term t
                return union l r
            | Abs(Var(_, ty), t) -> 
                let l = tyvars ty
                let! r = type_vars_in_term t
                return union l r
            | _ -> 
                return! Choice.failwith "type_vars_in_term: not a type variable"
        }

    (* ------------------------------------------------------------------------- *)
    (* For name-carrying syntax, we need this early.                             *)
    (* ------------------------------------------------------------------------- *)

    /// Modifies a variable name to avoid clashes.
    let rec variant avoid v : Protected<term> =
        choice {
        if not(exists (vfree_in v) avoid) then
            return v
        else 
            match v with
            | Var(s, ty) ->
                return! variant avoid (Var(s + "'", ty))
            | _ ->
                return! Choice.failwith "variant: not a variable"
        }

    (* ------------------------------------------------------------------------- *)
    (* Substitution primitive (substitution for variables only!)                 *)
    (* ------------------------------------------------------------------------- *)

    // CLEAN : Change the name of the 'ilist' parameter here to 'theta' if it makes sense,
    // or change the the 'theta' parameter in the vsubst function to 'ilist' -- either way,
    // the code would be more readable if they had the same name.
    let rec private vsubstRec ilist tm : Protected<term> =
        choice {
        match tm with
        | Const(_, _) ->
            return tm
        | Var(_, _) ->
            return rev_assocd tm ilist tm
        | Comb(s, t) -> 
            let! s' = vsubstRec ilist s
            let! t' = vsubstRec ilist t
            if s' == s && t' == t then
                return tm
            else
                return Comb(s', t')
        | Abs(v, s) -> 
            let ilist' = filter (fun (t, x) -> x <> v) ilist
            if ilist' = [] then
                return tm
            else 
                let! s' = vsubstRec ilist' s
                if s' == s then
                    return tm
                elif exists (fun (t, x) -> vfree_in v t && vfree_in x s) ilist' then 
                    let! v' = variant [s'] v
                    // CLEAN : Replace the name of this value with something sensible.
                    let! foo1 = vsubstRec ((v', v) :: ilist') s
                    return Abs(v', foo1)
                else
                    return Abs(v, s')
        }

    // CLEAN : Replace the name of this function with something more descriptive.
    let private checkTermAndVarTypesMatch theta =
        theta
        |> forall (fun (t, x) ->
            match type_of t, dest_var x with
            | Success r1, Success r2 ->
                r1 = snd r2
            | _ -> false)

    /// Substitute terms for variables inside a term.
    // CLEAN : Unless it offers a _specific_ performance benefit, it would simplify the code if we
    // added an extra parameter 'tm : term' to this function instead of returning a closure.
    let vsubst theta : (term -> Protected<term>) =
        if theta = [] then
            Choice.result
        elif checkTermAndVarTypesMatch theta then
            vsubstRec theta
        else
            fun (_ : term) ->
                Choice.failwith "vsubst: Bad substitution list"
    
    (* ------------------------------------------------------------------------- *)
    (* Type instantiation primitive.                                             *)
    (* ------------------------------------------------------------------------- *)

    (* NOTE :   The original hol-light code defined an exception "Clash of term" for use
                by the 'inst' function below. Instead of using exceptions, the F# code below
                uses Choice<_,_,_> values; in this future, this should be modified to use
                nested Choice<_,_> values instead (so Clash would be (Choice1Of2 << Choice2Of2)
                so we can make better use of workflows. *)

    let rec private instRec env tyin tm : Choice<term, term, exn> =
        // These helper functions simplify some of the code below.
        let inline result x = Choice1Of3 x
        let inline clash x = Choice2Of3 x
        let inline error x = Choice3Of3 x
        let inline (|Result|Clash|Err|) value =
            match value with
            | Choice1Of3 tm -> Result tm
            | Choice2Of3 tm -> Clash tm
            | Choice3Of3 ex -> Err ex

        match tm with
        | Var(n, ty) ->
            let tm' =
                let ty' = type_subst tyin ty
                if ty' == ty then tm
                else Var(n, ty')
            if compare (rev_assocd tm' env tm) tm = 0 then
                result tm'
            else
                clash tm'
        | Const(c, ty) -> 
            let ty' = type_subst tyin ty
            if ty' == ty then
                result tm
            else
                result <| Const(c, ty')
        | Comb(f, x) ->
            match instRec env tyin f with
            | Err ex ->
                error ex
            | Clash tm ->
                clash tm
            | Result f' ->
                match instRec env tyin x with
                | Err ex ->
                    error ex
                | Clash tm ->
                    clash tm
                | Result x' ->
                    if f' == f && x' == x then
                        result tm
                    else
                        result <| Comb(f', x')
            
        | Abs(y, t) ->
            match instRec [] tyin y with
            | Err ex ->
                error ex
            | Clash tm ->
                clash tm
            | Result y' ->
                let env' = (y, y') :: env
                match instRec env' tyin t with
                | Err ex ->
                    error ex
                | Clash w' ->
                    if w' <> y' then
                        // At this point, we assume the clash cannot be fixed and return an error.
                        // TODO : Provide a better error message; perhaps include the clashing terms.
                        error <| exn "instRec: clash"
                    else
                        let ifrees =
                            // Original code: map (instRec [] tyin) (frees t)
                            // This is similar to Choice.List.map in ExtCore, except it uses Choice<_,_,_>.
                            (Choice1Of3 [], frees t)
                            ||> List.fold (fun state tm ->
                                match state with
                                | Err ex ->
                                    error ex
                                | Clash tm ->
                                    clash tm
                                | Result lst ->
                                    match instRec [] tyin tm with
                                    | Err ex ->
                                        error ex
                                    | Clash tm ->
                                        clash tm
                                    | Result tm ->
                                        result (tm :: lst))
                            |> function
                                | Err ex ->
                                    error ex
                                | Clash tm ->
                                    clash tm
                                | Result lst ->
                                    result (List.rev lst)

                        match ifrees with
                        | Err ex ->
                            error ex
                        | Clash tm ->
                            clash tm
                        | Result ifrees ->
                            match variant ifrees y' with
                            | Error ex ->
                                error ex
                            | Success y'' ->
                                match dest_var y'' with
                                | Error ex ->
                                    error ex
                                | Success dest_y'' ->
                                    match dest_var y with
                                    | Error ex ->
                                        error ex
                                    | Success dest_var_y ->
                                        let z = Var(fst dest_y'', snd dest_var_y)
                                        match vsubst [z, y] t with
                                        | Error ex ->
                                            error ex
                                        | Success vsubst_zy_t ->
                                            instRec env tyin (Abs(z, vsubst_zy_t))
                | Result t' ->
                    if y' == y && t' == t then
                        result tm
                    else
                        result <| Abs(y', t')

    let private instImpl env tyin tm =
        match instRec env tyin tm with
        | Choice1Of3 result ->
            Choice.result result
        | Choice2Of3 clashTerm ->
            // This handles the "Clash" case.
            // TODO : Improve this error message; include the clashing term.
            // NOTE : This case probably shouldn't ever be matched -- 'instRec' attempts to handle
            // clashes, and finally returns an error (Choice3Of3) if a clash can't be handled.
            Choice.failwith "instImpl: Clash"
        | Choice3Of3 ex ->
            Choice.error ex
    
    /// Instantiate type variables in a term.
    // CLEAN : Unless it offers a _specific_ performance benefit, it would simplify the code if we
    // added an extra parameter 'tm : term' to this function instead of returning a closure.
    let inst tyin : (term -> Protected<term>) = 
        if tyin = [] then Choice.result
        else instImpl [] tyin
    
    (* ------------------------------------------------------------------------- *)
    (* A few bits of general derived syntax.                                     *)
    (* ------------------------------------------------------------------------- *)

    /// Returns the operator from a combination (function application).
    let rator tm : Protected<term> =
        choice {
        match tm with
        | Comb(l, r) -> 
            return l
        | _ -> 
            return! Choice.failwith "rator: Not a combination"
        }
    
    /// Returns the operand from a combination (function application).
    let rand tm : Protected<term> =
        choice {
        match tm with
        | Comb(l, r) -> 
            return r
        | _ -> 
            return! Choice.failwith "rand: Not a combination"
        }
    
    (* ------------------------------------------------------------------------- *)
    (* Syntax operations for equations.                                          *)
    (* ------------------------------------------------------------------------- *)

    let safe_mk_eq l r : Protected<term> =
        choice {
        let! ty = type_of l
        return Comb(Comb(Const("=", Tyapp("fun", [ty; Tyapp("fun", [ty; bool_ty])])), l), r)
        }
    
    /// Term destructor for equality.
    let dest_eq tm : Protected<term * term> =
        choice {
        match tm with
        | Comb(Comb(Const("=", _), l), r) -> 
            return l, r
        | _ -> 
            return! Choice.failwith "dest_eq"
        }
    
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
    let REFL tm : Protected<thm0> =
        choice {
        let! tm' = safe_mk_eq tm tm
        return Sequent([], tm')
        }

    /// Uses transitivity of equality on two equational theorems.
    let TRANS (thm1 : Protected<thm0>) (thm2 : Protected<thm0>) : Protected<thm0> = 
        let TRANS (Sequent(asl1, c1)) (Sequent(asl2, c2)) =
            choice {
            match (c1, c2) with
            | Comb((Comb(Const("=", _), _) as eql), m1), Comb(Comb(Const("=", _), m2), r) when alphaorder m1 m2 = 0 -> 
                return Sequent(term_union asl1 asl2, Comb(eql, r))
            | _ ->
                return! Choice.failwith "TRANS"
            }
        Choice.bind2 TRANS thm1 thm2
    
    (* ------------------------------------------------------------------------- *)
    (* Congruence properties of equality.                                        *)
    (* ------------------------------------------------------------------------- *)

    /// Proves equality of combinations constructed from equal functions and operands.
    let MK_COMB(thm1 : Protected<thm0>, thm2 : Protected<thm0>) : Protected<thm0> =
        let MK_COMB(Sequent(asl1, c1), Sequent(asl2, c2)) = 
            choice {
                match (c1, c2) with
                | Comb(Comb(Const("=", _), l1), r1), Comb(Comb(Const("=", _), l2), r2) ->
                    let! ty1 = type_of l1
                    let! ty2 = type_of l2
                    match ty1 with
                    | Tyapp("fun", [ty; _]) when compare ty ty2 = 0 -> 
                        let! tm = safe_mk_eq (Comb(l1, l2)) (Comb(r1, r2))
                        return Sequent(term_union asl1 asl2, tm)
                    | _ -> 
                        return! Choice.failwith "MK_COMB: types do not agree"
                | _ -> 
                    return! Choice.failwith "MK_COMB: not both equations"
            }
            |> Choice.mapError (fun e -> nestedFailure e "MK_COMB: not both equations")
        Choice.bind2 (curry MK_COMB) thm1 thm2
    
    /// Abstracts both sides of an equation.
    let ABS v (thm : Protected<thm0>) : Protected<thm0> =
        let ABS v (Sequent(asl, c)) = 
            choice {
                match (v, c) with
                | Var(_, _), Comb(Comb(Const("=", _), l), r) when not(exists (vfree_in v) asl) ->
                    let! tm = safe_mk_eq (Abs(v, l)) (Abs(v, r))
                    return Sequent(asl, tm)
                | _ -> 
                    return! Choice.failwith "ABS"
            }
        Choice.bind (ABS v) thm
    
    (* ------------------------------------------------------------------------- *)
    (* Trivial case of lambda calculus beta-conversion.                          *)
    (* ------------------------------------------------------------------------- *)

    /// Special primitive case of beta-reduction.
    let BETA tm : Protected<thm0> =
        choice {
        match tm with
        | Comb(Abs(v, bod), arg) when compare arg v = 0 -> 
            let! tm = safe_mk_eq tm bod
            return Sequent([], tm)
        | _ -> 
            return! Choice.failwith "BETA: not a trivial beta-redex"
        }

    (* ------------------------------------------------------------------------- *)
    (* Rules connected with deduction.                                           *)
    (* ------------------------------------------------------------------------- *)

    /// Introduces an assumption.
    let ASSUME tm : Protected<thm0> =
        choice {
        let! ty = type_of tm
        if compare ty bool_ty = 0 then
            return Sequent([tm], tm)
        else
            return! Choice.failwith "ASSUME: not a proposition"
        }
    
    /// Equality version of the Modus Ponens rule.
    let EQ_MP (thm1 : Protected<thm0>) (thm2 : Protected<thm0>) : Protected<thm0> =
        let EQ_MP (Sequent(asl1, eq)) (Sequent(asl2, c)) =
            choice {
            match eq with
            | Comb(Comb(Const("=", _), l), r) when alphaorder l c = 0 -> 
                return Sequent(term_union asl1 asl2, r)
            | _ ->
                return! Choice.failwith "EQ_MP"
            }
        Choice.bind2 EQ_MP thm1 thm2
    
    /// Deduces logical equivalence from deduction in both directions.
    let DEDUCT_ANTISYM_RULE (thm1 : Protected<thm0>) (thm2 : Protected<thm0>) : Protected<thm0> =
        let DEDUCT_ANTISYM_RULE (Sequent(asl1, c1)) (Sequent(asl2, c2)) =
            choice {
            let asl1' = term_remove c2 asl1
            let asl2' = term_remove c1 asl2
            let! tm = safe_mk_eq c1 c2
            return Sequent(term_union asl1' asl2', tm)
            }
        Choice.bind2 DEDUCT_ANTISYM_RULE thm1 thm2
    
    (* ------------------------------------------------------------------------- *)
    (* Type and term instantiation.                                              *)
    (* ------------------------------------------------------------------------- *)

    /// Instantiates types in a theorem.
    let INST_TYPE (theta : (hol_type * hol_type) list) (thm : Protected<thm0>) : Protected<thm0> =
        // TODO: revise this
        let INST_TYPE theta (Sequent(asl, c)) : thm =
            Choice.attempt <| fun () ->
                let inst_fun : term -> term = Choice.get << inst theta
                Sequent(term_image inst_fun asl, inst_fun c)
        Choice.bind (INST_TYPE theta) thm
    
    /// Instantiates free variables in a theorem.
    let INST theta (thm : Protected<thm0>) : Protected<thm0> =
        // TODO: revise this
        let INST theta (Sequent(asl, c)) : thm =
            Choice.attempt <| fun () ->
                let inst_fun : term -> term = Choice.get << vsubst theta
                Sequent(term_image inst_fun asl, inst_fun c)
        Choice.bind (INST theta) thm
    
    (* ------------------------------------------------------------------------- *)
    (* Handling of axioms.                                                       *)
    (* ------------------------------------------------------------------------- *)

    let the_axioms = ref([] : thm0 list)

    /// Returns the current set of axioms.
    let axioms() = !the_axioms
    
    /// Sets up a new axiom.
    let new_axiom tm : Protected<thm0> =
        choice {
        let! ty = type_of tm
        if compare ty bool_ty = 0 then 
            let th = Sequent([], tm)
            the_axioms := th :: (!the_axioms)
            return th
        else
            return! Choice.failwith "new_axiom: Not a proposition"
        }
    
    (* ------------------------------------------------------------------------- *)
    (* Handling of (term) definitions.                                           *)
    (* ------------------------------------------------------------------------- *)

    /// List of all definitions introduced so far.
    let the_definitions = ref([] : thm0 list)

    /// Returns the current set of primitive definitions.
    let definitions() = !the_definitions
    
    /// Makes a simple new definition of the form 'c = t'.
    let new_basic_definition tm : Protected<thm0> =
        choice {
        match tm with
        | Comb(Comb(Const("=", _), Var(cname, ty)), r) ->
            if not(freesin [] r) then
                return! Choice.failwith "new_definition: term not closed"
            else
                let! ty' = type_vars_in_term r
                if not(subset ty' (tyvars ty)) then 
                    return! Choice.failwith "new_definition: Type variables not reflected in constant"
                else
                    do! new_constant(cname, ty)
                    let c = Const(cname, ty)
                    let! dth =
                        choice {
                        let! tm = safe_mk_eq c r
                        return Sequent([], tm)
                        }
                    the_definitions := dth :: (!the_definitions)
                    return dth
        | _ ->
            return! Choice.failwith "new_basic_definition"
        }

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
    let new_basic_type_definition tyname (absname, repname) (thm : Protected<thm0>) : Protected<thm0> * Protected<thm0> =
        match thm with
        | Success (Sequent(asl, c)) ->
            if exists (Choice.isResult << get_const_type) [absname; repname] then 
                Choice.failwithPair "new_basic_type_definition: Constant(s) already in use"
            elif not(asl = []) then 
                Choice.failwithPair "new_basic_type_definition: Assumptions in theorem"
            else
                match dest_comb c with
                | Error e -> 
                    Choice.nestedFailwithPair e "new_basic_type_definition: Not a combination"
                | Success(P, x) ->
                    if not(freesin [] P) then 
                        Choice.failwithPair "new_basic_type_definition: Predicate is not closed"
                    else 
                        match type_vars_in_term P with
                        | Success tvs ->
                            let tyvars = sort (<=) tvs
                            match new_type(tyname, length tyvars) with
                            | Success _ ->
                                let aty = Tyapp(tyname, tyvars)
                                match type_of x with
                                | Success rty ->
                                    let absty = Tyapp("fun", [rty; aty])
                                    let repty = Tyapp("fun", [aty; rty])
                                    match new_constant(absname, absty), new_constant(repname, repty) with
                                    | Success _, Success _ ->
                                        let abs = Const(absname, absty)
                                        let rep = Const(repname, repty)
                                        let a = Var("a", aty)
                                        let r = Var("r", rty)
                                        (mk_comb(rep, a) 
                                         |> Choice.bind (fun b -> safe_mk_eq (Comb(abs, b)) a) 
                                         |> Choice.map (fun tm -> Sequent([], tm))),
                                        (mk_comb(abs, r)
                                         |> Choice.bind (fun b1 -> mk_comb(rep, b1) |> Choice.bind (fun b2 -> safe_mk_eq b2 r))
                                         |> Choice.bind (fun tm -> safe_mk_eq (Comb(P, r)) tm |> Choice.map (fun tm' -> Sequent([], tm'))))
                                    | _ -> Choice.failwithPair "new_basic_type_definition: Erroneous theorem"
                                | Error ex -> 
                                    (Choice2Of2 ex, Choice2Of2 ex)
                            | Error _ -> 
                                Choice.failwithPair "new_basic_type_definition: Type already defined"
                        | Error ex -> 
                            (Choice2Of2 ex, Choice2Of2 ex)
        | Error _ ->
            Choice.failwithPair "new_basic_type_definition: Erroneous theorem"

(* ------------------------------------------------------------------------- *)
(* Stuff that didn't seem worth putting in.                                  *)
(* ------------------------------------------------------------------------- *)

/// Construct a function type.
let mk_fun_ty ty1 ty2 = mk_type ("fun", [ty1; ty2])

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
        choice {
        let! eq = eq
        let! ty = type_of l
        let! eq_tm = inst [ty, aty] eq
        let! l = mk_comb(eq_tm, l)
        return! mk_comb(l, r)
        }
        |> Choice.mapError (fun e -> nestedFailure e "mk_eq")
        : Protected<term>

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
