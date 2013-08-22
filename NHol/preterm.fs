(*

Copyright 1998 University of Cambridge
Copyright 1998-2007 John Harrison
Copyright 2012 Marco Maggesi
Copyright 2012 Vincent Aravantinos
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
/// Preterms and pretypes; typechecking; translation to types and terms.
module NHol.preterm

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
#endif

infof "Entering preterm.fs"

(* ------------------------------------------------------------------------- *)
(* Flag to say whether to treat varstruct "\const. bod" as variable.         *)
(* ------------------------------------------------------------------------- *)

/// Interpret a simple varstruct as a variable, even if there is a constant of that name.
let ignore_constant_varstruct = ref true

(* ------------------------------------------------------------------------- *)
(* Flags controlling the treatment of invented type variables in quotations. *)
(* It can be treated as an error, result in a warning, or neither of those.  *)
(* ------------------------------------------------------------------------- *)

/// Determines if user is warned about invented type variables.
let type_invention_warning = ref true

/// Determines if invented type variables are treated as an error.
let type_invention_error = ref false

(* ------------------------------------------------------------------------- *)
(* Implicit types or type schemes for non-constants.                         *)
(* ------------------------------------------------------------------------- *)

/// Restrict variables to a particular type or type scheme.
let the_implicit_types = ref([] : (string * hol_type) list)

(* ------------------------------------------------------------------------- *)
(* Overloading and interface mapping.                                        *)
(* ------------------------------------------------------------------------- *)

/// Makes a symbol overloadable within the specified type skeleton.
let make_overloadable s gty : Protected<unit> =
    match assoc s !the_overload_skeletons with
    | Some x ->
        if x = gty then
            Choice.result ()
        else
            Choice.failwith "make_overloadable: differs from existing skeleton"
    | None ->
        the_overload_skeletons := (s, gty) :: !the_overload_skeletons
        Choice.result ()

/// Remove all overload/interface mappings for an identifier.
let remove_interface sym =
    let ``interface`` = filter ((<>) sym << fst) !the_interface
    the_interface := ``interface``

/// Remove a specific overload/interface mapping for an identifier.
let reduce_interface(sym, tm) : Protected<_> =
    choice {
    let! namty = 
        dest_const tm
        |> Choice.bindError (function Failure _ -> dest_var tm | e -> Choice.error e)
    the_interface := filter ((<>)(sym, namty)) !the_interface
    return ()
    }

/// Map identifier to specific underlying constant.
let override_interface(sym, tm) : Protected<_> =
    choice {
    let! namty =
        dest_const tm
        |> Choice.bindError (function Failure _ -> dest_var tm | e -> Choice.error e)
    let ``interface`` = filter ((<>) sym << fst) !the_interface
    the_interface := (sym, namty) :: ``interface``
    return ()
    }

/// Overload a symbol so it may denote a particular underlying constant.
let overload_interface(sym, tm) : Protected<_> =
    choice {
    let! gty =
        choice {
        match assoc sym !the_overload_skeletons with
        | Some x ->
            return x
        | None ->
            let msg = Microsoft.FSharp.Core.Printf.sprintf "symbol \"%s\" is not overloadable" sym
            return! Choice.failwith msg
        }

    let! ((name, ty) as namty) =
        dest_const tm
        |> Choice.bindError (function Failure _ -> dest_var tm | e -> Choice.error e)

    let! _ =
        type_match gty ty []
        |> Choice.mapError (fun ex ->
            nestedFailure ex "Not an instance of type skeleton")

    let ``interface`` = filter ((<>)(sym, namty)) !the_interface
    the_interface := (sym, namty) :: ``interface``
    return ()
    }

/// Give overloaded constants involving a given type priority in operator overloading.
let prioritize_overload ty : Protected<unit> =
    !the_overload_skeletons
    |> Choice.List.iter (fun (s, gty) ->
        choice {
        let! var_tm =
            !the_interface
            |> Choice.List.tryFind (fun (s', (n, t)) ->
                choice {
                let! tys = type_match gty t []
                return s' = s && mem ty (map fst tys)
                })
            |> Choice.bind (Option.toChoiceWithError "find")
            |> Choice.map (snd >> mk_var)

        return! overload_interface(s, var_tm)
        }
        |> Choice.bindError (function 
            | Failure _ ->
                // NOTE: currently do nothing to handle failures
                System.Diagnostics.Debug.WriteLine "An unhandled error occurred in the 'prioritize_overload' function."
                Choice.result ()
            | e -> Choice.error e))

(* ------------------------------------------------------------------------- *)
(* Type abbreviations.                                                       *)
(* ------------------------------------------------------------------------- *)

let private the_type_abbreviations = ref([] : (string * hol_type) list)

/// Removes use of name as a type abbreviation.
let remove_type_abbrev s =
    the_type_abbreviations := filter (fun (s', _) -> s' <> s) !the_type_abbreviations

/// Sets up a new type abbreviation.
let new_type_abbrev(s, ty) =
    remove_type_abbrev s
    the_type_abbreviations := merge (<) [s, ty] !the_type_abbreviations

/// Lists all current type abbreviations.
let type_abbrevs() = !the_type_abbreviations

(* ------------------------------------------------------------------------- *)
(* Handle constant hiding.                                                   *)
(* ------------------------------------------------------------------------- *)

let private hcs : string list ref = ref []

/// Restores recognition of a constant by the quotation parser.
let hide_constant c =
    hcs := union [c] !hcs

/// Disables recognition of a constant by the quotation parser.
let unhide_constant c =
    hcs := subtract !hcs [c]

/// Determines whether a constant is hidden.
let is_hidden c =
    mem c !hcs

(* ------------------------------------------------------------------------- *)
(* The type of pretypes.                                                     *)
(* ------------------------------------------------------------------------- *)

/// The type of pretypes.
type pretype =
    /// User type variable.
    | Utv of string
    /// Type constructor.
    | Ptycon of string * pretype list
    /// System type variable.
    | Stv of int

(* ------------------------------------------------------------------------- *)
(* Dummy pretype for the parser to stick in before a proper typing pass.     *)
(* ------------------------------------------------------------------------- *)

/// Dummy pretype.
let dpty = Ptycon("", [])

(* ------------------------------------------------------------------------- *)
(* Convert type to pretype.                                                  *)
(* ------------------------------------------------------------------------- *)

/// Converts a type into a pretype.
let rec pretype_of_type ty : Protected<pretype> = 
    choice {
    let! con, args = dest_type ty
    let! ps = Choice.List.map pretype_of_type args
    return Ptycon(con, ps)
    }
    |> Choice.bindError (function Failure _ -> dest_vartype ty |> Choice.map Utv | e -> Choice.error e)

(* ------------------------------------------------------------------------- *)
(* Preterm syntax.                                                           *)
(* ------------------------------------------------------------------------- *)

/// Preterm syntax.
type preterm =
    /// <summary>Variable (<c>v</c>)</summary>
    | Varp of string * pretype
    /// <summary>Constant (<c>c</c>)</summary>
    | Constp of string * pretype
    /// <summary>Combination (<c>f x</c>)</summary>
    | Combp of preterm * preterm
    /// <summary>Lambda-abstraction (<c>\x. t</c>)</summary>
    | Absp of preterm * preterm
    /// <summary>Type constraint (<c>t : ty</c>)</summary>
    | Typing of preterm * pretype

(* ------------------------------------------------------------------------- *)
(* Convert term to preterm.                                                  *)
(* ------------------------------------------------------------------------- *)

/// Converts a term into a preterm.
let rec preterm_of_term tm : Protected<preterm> = 
    choice {
        let! n, ty = dest_var tm
        let! pt = pretype_of_type ty
        return Varp(n, pt)
    }
    |> Choice.bindError (function
        | Failure _ ->
            choice {
                let! n, ty = dest_const tm
                let! pt = pretype_of_type ty
                return Constp(n, pt)
            }
        | e -> Choice.error e)
    |> Choice.bindError (function
        | Failure _ ->
            choice {
                let! v, bod = dest_abs tm
                let! pb = preterm_of_term bod
                let! pv = preterm_of_term v
                return Absp(pv, pb)
            }
        | e -> Choice.error e)
    |> Choice.bindError (function
        | Failure _ ->
            choice {
                let! l, r = dest_comb tm
                let! l' = preterm_of_term l
                let! r' = preterm_of_term r  
                return Combp(l', r')
            }
        | e -> Choice.error e)

(* ------------------------------------------------------------------------- *)
(* Main pretype->type, preterm->term and retypechecking functions.           *)
(* ------------------------------------------------------------------------- *)

// type_of_pretype: Converts a pretype to a type.
// term_of_preterm: Converts a preterm into a term.
// retypecheck: Typecheck a term, iterating over possible overload resolutions.
let (type_of_pretype : _ -> Protected<_>), (term_of_preterm : _ -> Protected<_>), (retypecheck : _ -> _ -> Protected<_>) = 
    let tyv_num = ref 0

    let new_type_var() = 
        let n = !tyv_num
        tyv_num := n + 1
        Stv n
    
    let pmk_cv(s, pty) =
        match get_const_type s with
        | Success _ ->
            Constp(s, pty)
        | Error _ ->
            Varp(s, pty)

    let pmk_numeral = 
        let num_pty = Ptycon("num", [])
        let NUMERAL = Constp("NUMERAL", Ptycon("fun", [num_pty; num_pty]))
        let BIT0 = Constp("BIT0", Ptycon("fun", [num_pty; num_pty]))
        let BIT1 = Constp("BIT1", Ptycon("fun", [num_pty; num_pty]))
        let t_0 = Constp("_0", num_pty)
        let rec pmk_numeral n =
            if n =/ num_0 then t_0
            else
                let m = quo_num n (num_2)
                let b = mod_num n (num_2)
                let op = if b =/ num_0 then BIT0 else BIT1
                Combp(op, pmk_numeral m)
        fun n ->
            Combp(NUMERAL, pmk_numeral n)

    (* ----------------------------------------------------------------------- *)
    (* Pretype substitution for a pretype resulting from translation of type.  *)
    (* ----------------------------------------------------------------------- *)

    let rec pretype_subst th ty = 
        match ty with
        | Ptycon(tycon, args) ->
            Ptycon(tycon, map (pretype_subst th) args)
        | Utv v ->
            rev_assocd ty th ty
        | _ ->
            failwith "pretype_subst: Unexpected form of pretype"

    (* ----------------------------------------------------------------------- *)
    (* Convert type to pretype with new Stvs for all type variables.           *)
    (* ----------------------------------------------------------------------- *)

    let pretype_instance ty : Protected<pretype> =
        choice {
        let! gty = pretype_of_type ty
        let! tyvs = Choice.List.map pretype_of_type (tyvars ty)
        let subs = map (fun tv -> new_type_var(), tv) tyvs
        return pretype_subst subs gty
        }

    (* ----------------------------------------------------------------------- *)
    (* Get a new instance of a constant's generic type modulo interface.       *)
    (* ----------------------------------------------------------------------- *)

    let get_generic_type cname = 
        match filter ((=) cname << fst) !the_interface with
        | [] ->
            get_const_type cname
        | [_, (c, ty)] ->
            Choice.result ty
        | _ :: _ :: _ ->
            !the_overload_skeletons
            |> assoc cname
            |> Option.toChoiceWithError "find"

    (* ----------------------------------------------------------------------- *)
    (* Get the implicit generic type of a variable.                            *)
    (* ----------------------------------------------------------------------- *)

    let get_var_type vname =
        assoc vname !the_implicit_types
        |> Option.toChoiceWithError "find"

    (* ----------------------------------------------------------------------- *)
    (* Unravel unifications and apply them to a type.                          *)
    (* ----------------------------------------------------------------------- *)

    let rec solve env pty =
        choice {
            match pty with
            | Ptycon(f, args) ->
                let! tys = Choice.List.map (solve env) args
                return Ptycon(f, tys)
            | Stv i ->
                if defined env i then
                    let! pty = apply env i |> Option.toChoiceWithError "apply"
                    return! solve env pty
                else
                    return pty
            | _ ->
                return pty
        }

    (* ----------------------------------------------------------------------- *)
    (* Functions for display of preterms and pretypes, by converting them      *)
    (* to terms and types then re-using standard printing functions.           *)
    (* ----------------------------------------------------------------------- *)

    let free_stvs =
        let rec free_stvs =
            function
            | Stv n -> [n]
            | Utv _ -> []
            | Ptycon(_, args) -> flat(map free_stvs args)
        setify << free_stvs

    let string_of_pretype stvs : _ -> Protected<_> =
        let rec type_of_pretype' ns pt : Protected<_> =
            choice {
                match pt with
                | Stv n ->
                    return mk_vartype (if mem n ns then "?" + string n else "_")
                | Utv v ->
                    return mk_vartype v
                | Ptycon(con, args) ->
                    let! tms = Choice.List.map (type_of_pretype' ns) args
                    return! mk_type(con, tms)
            }

        fun pt ->
            Choice.map string_of_type (type_of_pretype' stvs pt)

    let string_of_preterm =
        let rec untyped_t_of_pt pt = 
            choice {
                match pt with 
                | Varp(s, pty) -> 
                    return mk_var(s, aty)
                | Constp(s, pty) -> 
                    let! ty1 = get_const_type s
                    return! mk_mconst(s, ty1)
                | Combp(l, r) -> 
                    let! l' = untyped_t_of_pt l
                    let! r' = untyped_t_of_pt r
                    return! mk_comb(l', r')
                | Absp(v, bod) -> 
                    let! v' = untyped_t_of_pt v
                    let! bod' = untyped_t_of_pt bod
                    return! mk_gabs(v', bod')
                | Typing(ptm, pty) -> 
                    return! untyped_t_of_pt ptm
            }

        fun pt ->
            Choice.map string_of_term (untyped_t_of_pt pt)

    let string_of_ty_error env po =
        let string_of_ty_error env po =
            choice {
                match po with
                | None ->
                    return "unify: types cannot be unified " + "(you should not see this message, please report)"
                | Some(t, ty1, ty2) ->
                    let! ty1 = solve env ty1
                    let! ty2 = solve env ty2
                    let! sty1 = string_of_pretype (free_stvs ty2) ty1
                    let! sty2 = string_of_pretype (free_stvs ty1) ty2
                    let default_msg s = " " + s + " cannot have type " + sty1 + " and " + sty2 + " simultaneously"

                    match t with
                    | Constp(s, _) ->
                        let! ty1 = get_const_type s
                        return " " + s + " has type " + string_of_type ty1 + ", " + "it cannot be used with type " + sty2
                    | Varp(s, _) ->
                        return default_msg s
                    | t ->
                        let! s1 = string_of_preterm t
                        return default_msg s1
            }

        string_of_ty_error env po

    (* ----------------------------------------------------------------------- *)
    (* Unification of types                                                    *)
    (* ----------------------------------------------------------------------- *)

    let rec istrivial ptm env x v =
        choice {
        match v with 
        | Stv y as t ->
            if y = x then 
                return true
            else
                if defined env y then
                    // Option.get is safe to use here
                    return! istrivial ptm env x (Option.get <| apply env y)
                else
                    return false
        | Ptycon(f, args) as t
            when Choice.List.exists (istrivial ptm env x) args = Choice1Of2 true ->
            let! errorString = string_of_ty_error env ptm
            return! Choice.failwith errorString
        | Ptycon _
        | Utv _ ->
            return false
        } : Protected<bool>

    let unify ptm env ty1 ty2 : Protected<_> = 
        let rec unify env v = 
            choice {
            match v with 
            | [] -> 
                return env
            | (ty1, ty2, _) :: oth when ty1 = ty2 ->
                return! unify env oth
            | (Ptycon(f, fargs), Ptycon(g, gargs), ptm) :: oth -> 
                if f = g && length fargs = length gargs then
                    return! unify env (map2 (fun x y -> x, y, ptm) fargs gargs @ oth)
                else
                    let! errorString = string_of_ty_error env ptm
                    return! Choice.failwith errorString
            | (Stv x, t, ptm) :: oth -> 
                if defined env x then
                    // Option.get is safe to use here
                    return! unify env ((Option.get <| apply env x, t, ptm) :: oth)
                else
                    let! cond = istrivial ptm env x t  
                    return! unify (if cond  then env else (x |-> t) env) oth
            | (t, Stv x, ptm) :: oth ->
                return! unify env ((Stv x, t, ptm) :: oth)
            | (_, _, ptm) :: oth ->
                let! errorString = string_of_ty_error env ptm
                return! Choice.failwith errorString
            }

        unify env [ty1, ty2, Option.map (fun t -> t, ty1, ty2) ptm]

    (* ----------------------------------------------------------------------- *)
    (* Attempt to attach a given type to a term, performing unifications.      *)
    (* ----------------------------------------------------------------------- *)

    let rec typify ty (ptm, venv, uenv) : Protected<_> =
        choice {
            //printfn "typify --> %A:%A:%A:%A" ty ptm venv uenv 
            // OPTIMIZE : Create active patterns for the first two cases which memoize
            // the result of the (possibly) costly function called both in the guard and the body.
            match ptm with
            | Varp(s, _) when Option.isSome <| assoc s venv ->
                let! ty' =
                    assoc s venv
                    |> Option.toChoiceWithError "find"
                let! fn = unify (Some ptm) uenv ty' ty
                return Varp(s, ty'), [], fn

            | Varp(s, _) when Choice.isResult <| num_of_string s -> 
                let t = pmk_numeral(Choice.get <| num_of_string s)
                let ty' = Ptycon("num", [])
                let! fn = unify (Some ptm) uenv ty' ty
                return t, [], fn
            
            | Varp(s, _) -> 
                warn (s <> "" && isnum s) "Non-numeral begins with a digit"
                // OPTIMIZE : Use a pattern match here instead of && so 'get_generic_type' isn't called twice.
                if not(is_hidden s) && Choice.isResult <| get_generic_type s then
                    let! foo1 = get_generic_type s
                    let! pty = pretype_instance foo1
                    let ptm = Constp(s, pty)
                    let! fn = unify (Some ptm) uenv pty ty
                    return ptm, [], fn
                else 
                    let ptm = Varp(s, ty)
                    match get_var_type s with
                    | Error _ ->
                        return ptm, [s, ty], uenv
                    | Success ty1 ->
                        let! pty = pretype_instance ty1
                        let! fn = unify (Some ptm) uenv pty ty
                        return ptm, [s, ty], fn

            | Combp(f, x) -> 
                let ty'' = new_type_var()
                let ty' = Ptycon("fun", [ty''; ty])
                let! f', venv1, uenv1 = typify ty' (f, venv, uenv)
                let! x', venv2, uenv2 = typify ty'' (x, venv1 @ venv, uenv1)
                return Combp(f', x'), (venv1 @ venv2), uenv2
            
            | Typing(tm, pty) ->
                let! fn = unify (Some tm) uenv ty pty
                return! typify ty (tm, venv, fn)
            
            | Absp(v, bod) -> 
                let ty', ty'' = 
                    match ty with
                    | Ptycon("fun", [ty'; ty'']) -> ty', ty''
                    | _ -> new_type_var(), new_type_var()
                let ty''' = Ptycon("fun", [ty'; ty''])
                let! uenv0 = unify (Some ptm) uenv ty''' ty
                let! v', venv1, uenv1 = 
                    choice {
                    let! v', venv1, uenv1 = typify ty' (v, [], uenv0)
                    match v' with
                    | Constp(s, _) when !ignore_constant_varstruct ->
                        return Varp(s, ty'), [s, ty'], uenv0
                    | _ ->
                        return v', venv1, uenv1
                    }
                let! bod', venv2, uenv2 = typify ty'' (bod, venv1 @ venv, uenv1)
                return Absp(v', bod'), venv2, uenv2
            
            | _ ->
                return! Choice.failwith "typify: unexpected constant at this stage"
        }

    (* ----------------------------------------------------------------------- *)
    (* Further specialize type constraints by resolving overloadings.          *)
    (* ----------------------------------------------------------------------- *)

    // TODO : Re-implement this function to use the ChoiceCont or ReaderChoiceCont workflow from ExtCore.
    let resolve_interface ptm cont env : Protected<_> =
        let rec resolve_interface ptm cont env = 
            match ptm with
            | Combp(f, x) ->
                resolve_interface f (resolve_interface x cont) env
            | Absp(v, bod) ->
                resolve_interface v (resolve_interface bod cont) env
            | Varp(_, _) ->
                cont env
            | Constp(s, ty) ->
                let maps = filter (fun (s', _) -> s' = s) !the_interface
                if List.isEmpty maps then
                    cont env
                else
                    maps
                    |> List.tryPick (fun (_, (_, ty')) ->
                        match pretype_instance ty' with
                        | Error _ ->
                            None
                        | Success ty' ->
                            // TODO: revise this
                            match unify (Some ptm) env ty' ty with
                            | Success x -> Some (cont x)
                            | Error _ -> None)
                    |> Option.toChoiceWith "tryfind"
                    // TEMP : Until this function is modified to use Choice.
                    |> ExtCore.Choice.bindOrFail
            | _ ->
                failwith "resolve_interface: Unhandled case."

        Choice.attempt <| fun () ->
            resolve_interface ptm cont env

    (* ----------------------------------------------------------------------- *)
    (* Hence apply throughout a preterm.                                       *)
    (* ----------------------------------------------------------------------- *)

    let rec solve_preterm env ptm : Protected<preterm> = 
        choice {
        match ptm with
        | Varp(s, ty) -> 
            let! pt1 = solve env ty
            return Varp(s, pt1)
        | Combp(f, x) -> 
            let! f' = solve_preterm env f
            let! x' = solve_preterm env x
            return Combp(f', x')
        | Absp(v, bod) -> 
            let! v' = solve_preterm env v
            let! bod' = solve_preterm env bod
            return Absp(v', bod')
        | Constp(s, ty) -> 
            let! tys = solve env ty
            return!
                choice { 
                    let! _, (c', _) =
                        !the_interface
                        |> List.tryFind (fun (s', (c', ty')) ->
                            s = s' && Choice.isResult <| unify None env (Choice.get <| pretype_instance ty') ty)
                        |> Option.toChoiceWithError "find"

                    return pmk_cv(c', tys)
                }
                |> Choice.bindError (function Failure _ -> Choice.result <| Constp(s, tys) | e -> Choice.error e)
        | _ -> 
            return! Choice.failwith "solve_preterm: Unhandled case."
        }

    (* ----------------------------------------------------------------------- *)
    (* Flag to indicate that Stvs were translated to real type variables.      *)
    (* ----------------------------------------------------------------------- *)

    let stvs_translated = ref false

    (* ----------------------------------------------------------------------- *)
    (* Pretype <-> type conversion; -> flags system type variable translation. *)
    (* ----------------------------------------------------------------------- *)

    let rec type_of_pretype ty : Protected<hol_type> =
        choice {
            match ty with
            | Stv n -> 
                stvs_translated := true
                let s = "?" + (string n)
                return mk_vartype s
            | Utv v -> 
                return mk_vartype v
            | Ptycon(con, args) -> 
                let! tms = Choice.List.map type_of_pretype args
                return! mk_type(con, tms)
        }

    (* ----------------------------------------------------------------------- *)
    (* Maps preterms to terms.                                                 *)
    (* ----------------------------------------------------------------------- *)

    let term_of_preterm = 
        let rec term_of_preterm ptm = 
            choice {
            match ptm with
            | Varp(s, pty) -> 
                let! pt1 = type_of_pretype pty
                return mk_var(s, pt1)
            | Constp(s, pty) -> 
                let! pt1 = type_of_pretype pty
                return! mk_mconst(s, pt1)
            | Combp(l, r) -> 
                let! l' = term_of_preterm l
                let! r' = term_of_preterm r
                return! mk_comb(l', r')
            | Absp(v, bod) -> 
                let! v' = term_of_preterm v
                let! bod' = term_of_preterm bod
                return! mk_gabs(v', bod')
            | Typing(ptm, pty) -> 
                return! term_of_preterm ptm
            }

        let report_type_invention() = 
            choice {
            if !stvs_translated then 
                if !type_invention_error then 
                    do! Choice.failwith "typechecking error (cannot infer type of variables)"
                else 
                    warn !type_invention_warning "inventing type variables"
            }

        fun ptm -> 
            choice {
            stvs_translated := false
            let! tm = term_of_preterm ptm
            do! report_type_invention()
            return tm
            } : Protected<_>

    (* ----------------------------------------------------------------------- *)
    (* Overall typechecker: initial typecheck plus overload resolution pass.   *)
    (* ----------------------------------------------------------------------- *)

    let retypecheck venv ptm =
        choice {
        let ty = new_type_var()

        let! ptm', _, env = 
            typify ty (ptm, venv, undefined)
            |> Choice.mapError (fun e ->
                nestedFailure e "typechecking error (initial type assignment)")

        let! env' = 
            resolve_interface ptm' id env
            |> Choice.mapError (fun e ->
                nestedFailure e "typechecking error (overload resolution)")

        return! solve_preterm env' ptm'
        } : Protected<_>

    type_of_pretype, term_of_preterm, retypecheck
