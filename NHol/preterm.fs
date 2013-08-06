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
open lib
open fusion
open fusion.Hol_kernel
open basics
open nets
open printer
#endif

(* ------------------------------------------------------------------------- *)
(* Flag to say whether to treat varstruct "\const. bod" as variable.         *)
(* ------------------------------------------------------------------------- *)

/// Interpret a simple varstruct as a variable, even if there is a constant of that name.
let ignore_constant_varstruct = ref true

(* ------------------------------------------------------------------------- *)
(* Flags controlling the treatment of invented type variables in quotations. *)
(* It can be treated as an error, result in a warning, or neither of those.  *)
(* ------------------------------------------------------------------------- *)

/// Determined if user is warned about invented type variables.
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
    let namty = 
        dest_const tm
        |> Choice.bindError (fun _ -> dest_var tm)
    match namty with
    | Success namty ->
        the_interface := filter ((<>)(sym, namty)) !the_interface
        Choice.result ()
    | Error ex ->
        Choice.error ex

/// Map identifier to specific underlying constant.
let override_interface(sym, tm) : Protected<_> =
    let namty =
        dest_const tm
        |> Choice.bindError (fun _ -> dest_var tm)

    match namty with
    | Success namty ->
        let ``interface`` = filter ((<>) sym << fst) !the_interface
        the_interface := (sym, namty) :: ``interface``
        Choice.result ()
    | Error ex ->
        Choice.error ex

/// Overload a symbol so it may denote a particular underlying constant.
let overload_interface(sym, tm) : Protected<_> =
    let gty =
        match assoc sym !the_overload_skeletons with
        | Some x ->
            Choice.result x
        | None ->
            let msg = Microsoft.FSharp.Core.Printf.sprintf "symbol \"%s\" is not overloadable" sym
            Choice.failwith msg

    gty
    |> Choice.bind (fun gty ->
        match dest_const tm |> Choice.bindError (fun _ -> dest_var tm) with
        | Success ((name, ty) as namty) ->
            match type_match gty ty [] with
            | Error ex ->
                Choice.nestedFailwith ex  "Not an instance of type skeleton"
            | Success _ ->
                let ``interface`` = filter ((<>)(sym, namty)) !the_interface
                the_interface := (sym, namty) :: ``interface``
                Choice.result ()
        | Error ex ->
            Choice.error ex)

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
        |> Choice.bindError (fun _ ->
            // NOTE: currently do nothing to handle failures
            System.Diagnostics.Debug.WriteLine "An unhandled error occurred in the 'prioritize_overload' function."
            Choice.result ()))

(* ------------------------------------------------------------------------- *)
(* Type abbreviations.                                                       *)
(* ------------------------------------------------------------------------- *)

// new_type_abbrev: Sets up a new type abbreviation.
// remove_type_abbrev: Removes use of name as a type abbreviation.
// type_abbrevs: Lists all current type abbreviations.
let new_type_abbrev, remove_type_abbrev, type_abbrevs = 
    let the_type_abbreviations = ref([] : (string * hol_type) list)
    let remove_type_abbrev s =
        the_type_abbreviations := filter (fun (s', _) -> s' <> s) !the_type_abbreviations
    let new_type_abbrev(s, ty) =
        remove_type_abbrev s
        the_type_abbreviations := merge (<) [s, ty] !the_type_abbreviations
    let type_abbrevs() = !the_type_abbreviations
    new_type_abbrev, remove_type_abbrev, type_abbrevs

(* ------------------------------------------------------------------------- *)
(* Handle constant hiding.                                                   *)
(* ------------------------------------------------------------------------- *)

// hide_constant: Restores recognition of a constant by the quotation parser.
// unhide_constant: Disables recognition of a constant by the quotation parser.
// is_hidden: Determines whether a constant is hidden.
let hide_constant, unhide_constant, is_hidden = 
    let hcs = ref([] : string list)
    let hide_constant c = hcs := union [c] !hcs
    let unhide_constant c = hcs := subtract !hcs [c]
    let is_hidden c = mem c !hcs
    hide_constant, unhide_constant, is_hidden

(* ------------------------------------------------------------------------- *)
(* The type of pretypes.                                                     *)
(* ------------------------------------------------------------------------- *)

type pretype = 
    | Utv of string                     (* User type variable         *)
    | Ptycon of string * pretype list   (* Type constructor           *)
    | Stv of int                        (* System type variable       *)

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
    |> Choice.bindError (fun _ -> dest_vartype ty |> Choice.map Utv)

(* ------------------------------------------------------------------------- *)
(* Preterm syntax.                                                           *)
(* ------------------------------------------------------------------------- *)

type preterm = 
    | Varp of string * pretype      (* Variable           - v      *)
    | Constp of string * pretype    (* Constant           - c      *)
    | Combp of preterm * preterm    (* Combination        - f x    *)
    | Absp of preterm * preterm     (* Lambda-abstraction - \x. t  *)
    | Typing of preterm * pretype   (* Type constraint    - t : ty *)

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
    |> Choice.bindError (fun _ ->
        choice {
            let! n, ty = dest_const tm
            let! pt = pretype_of_type ty
            return Constp(n, pt)
        })
    |> Choice.bindError (fun _ ->
        choice {
            let! v, bod = dest_abs tm
            let! pb = preterm_of_term bod
            let! pv = preterm_of_term v
            return Absp(pv, pb)
        })
    |> Choice.bindError (fun _ ->
        choice {
            let! l, r = dest_comb tm
            let! l' = preterm_of_term l
            let! r' = preterm_of_term r  
            return Combp(l', r')
        })

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
        Stv(n)
    
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

    let pretype_instance ty = 
        let gty = Choice.get <| pretype_of_type ty
        // TODO : Modify this to use Choice.List.map.
        let tyvs = map (Choice.get << pretype_of_type) (tyvars ty)
        let subs = map (fun tv -> new_type_var(), tv) tyvs
        pretype_subst subs gty

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

    let string_of_pretype stvs =
        let rec type_of_pretype' ns pt =
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

    let rec istrivial ptm env x = function 
        | Stv y as t ->
            y = x || defined env y && istrivial ptm env x (Option.get <| apply env y)
        | Ptycon(f, args) as t when exists (istrivial ptm env x) args ->
            let errorString = ExtCore.Choice.bindOrRaise <| string_of_ty_error env ptm
            failwith errorString
        | (Ptycon _ | Utv _) ->
            false

    let unify ptm env ty1 ty2 = 
        let unify ptm env ty1 ty2 = 
            let rec unify env = function 
                | [] -> env
                | (ty1, ty2, _) :: oth when ty1 = ty2 ->
                    unify env oth
                | (Ptycon(f, fargs), Ptycon(g, gargs), ptm) :: oth -> 
                    if f = g && length fargs = length gargs then
                        unify env (map2 (fun x y -> x, y, ptm) fargs gargs @ oth)
                    else
                        let errorString = ExtCore.Choice.bindOrRaise <| string_of_ty_error env ptm
                        failwith errorString
                | (Stv x, t, ptm) :: oth -> 
                    if defined env x then
                        unify env ((Option.get <| apply env x, t, ptm) :: oth)
                    else 
                        unify (if istrivial ptm env x t then env
                               else (x |-> t) env) oth
                | (t, Stv x, ptm) :: oth ->
                    unify env ((Stv x, t, ptm) :: oth)
                | (_, _, ptm) :: oth ->
                    let errorString = ExtCore.Choice.bindOrRaise <| string_of_ty_error env ptm
                    failwith errorString

            unify env [ty1, ty2, Option.map (fun t -> t, ty1, ty2) ptm]

        // NOTE: remove this when istrivial is converted                            
        Choice.attempt <| fun () ->
            unify ptm env ty1 ty2

    (* ----------------------------------------------------------------------- *)
    (* Attempt to attach a given type to a term, performing unifications.      *)
    (* ----------------------------------------------------------------------- *)

    let typify ty (ptm, venv, uenv) =
        let rec typify ty (ptm, venv, uenv) =
            //printfn "typify --> %A:%A:%A:%A" ty ptm venv uenv 
            match ptm with
            | Varp(s, _) when Option.isSome <| assoc s venv ->
                let ty' =
                    assoc s venv
                    |> Option.getOrFailWith "find"
                Varp(s, ty'), [], Choice.get <| unify (Some ptm) uenv ty' ty

            | Varp(s, _) when Choice.isResult <| num_of_string s -> 
                let t = pmk_numeral(Choice.get <| num_of_string s)
                let ty' = Ptycon("num", [])
                t, [], Choice.get <| unify (Some ptm) uenv ty' ty
            
            | Varp(s, _) -> 
                warn (s <> "" && isnum s) "Non-numeral begins with a digit"
                if not(is_hidden s) && Choice.isResult <| get_generic_type s then 
                    let pty = pretype_instance(Choice.get <| get_generic_type s)
                    let ptm = Constp(s, pty)
                    ptm, [], Choice.get <| unify (Some ptm) uenv pty ty
                else 
                    let ptm = Varp(s, ty)
                    if Choice.isError <| get_var_type s then
                        ptm, [s, ty], uenv
                    else 
                        let pty = pretype_instance(Choice.get <| get_var_type s)
                        ptm, [s, ty], Choice.get <| unify (Some ptm) uenv pty ty

            | Combp(f, x) -> 
                let ty'' = new_type_var()
                let ty' = Ptycon("fun", [ty''; ty])
                let f', venv1, uenv1 = typify ty' (f, venv, uenv)
                let x', venv2, uenv2 = typify ty'' (x, venv1 @ venv, uenv1)
                Combp(f', x'), (venv1 @ venv2), uenv2
            
            | Typing(tm, pty) ->
                typify ty (tm, venv, Choice.get <| unify (Some tm) uenv ty pty)
            
            | Absp(v, bod) -> 
                let ty', ty'' = 
                    match ty with
                    | Ptycon("fun", [ty'; ty'']) -> ty', ty''
                    | _ -> new_type_var(), new_type_var()
                let ty''' = Ptycon("fun", [ty'; ty''])
                let uenv0 = Choice.get <| unify (Some ptm) uenv ty''' ty
                let v', venv1, uenv1 = 
                    let v', venv1, uenv1 = typify ty' (v, [], uenv0)
                    match v' with
                    | Constp(s, _) when !ignore_constant_varstruct ->
                        Varp(s, ty'), [s, ty'], uenv0
                    | _ ->
                        v', venv1, uenv1
                let bod', venv2, uenv2 = typify ty'' (bod, venv1 @ venv, uenv1)
                Absp(v', bod'), venv2, uenv2
            
            | _ ->
                failwith "typify: unexpected constant at this stage"
        
        Choice.attempt <| fun () ->
            typify ty (ptm, venv, uenv)

    (* ----------------------------------------------------------------------- *)
    (* Further specialize type constraints by resolving overloadings.          *)
    (* ----------------------------------------------------------------------- *)

    // TODO : Re-implement this function to use the ChoiceCont or ReaderChoiceCont workflow from ExtCore.
    let resolve_interface ptm cont env =
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
                    |> tryfind (fun (_, (_, ty')) -> 
                        let ty' = pretype_instance ty'
                        // TODO: revise this
                        match unify (Some ptm) env ty' ty with
                        | Success x -> Some (cont x)
                        | Error _ -> None)
                    |> Option.getOrFailWith "tryfind"
            | _ ->
                failwith "resolve_interface: Unhandled case."

        Choice.attempt <| fun () ->
            resolve_interface ptm cont env

    (* ----------------------------------------------------------------------- *)
    (* Hence apply throughout a preterm.                                       *)
    (* ----------------------------------------------------------------------- *)

    let rec solve_preterm env ptm = 
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
                            find (fun (s', (c', ty')) -> 
                                s = s' && Choice.isResult <| unify None env (pretype_instance ty') ty) !the_interface
                            |> Option.toChoiceWithError "find"

                        return pmk_cv(c', tys)
                    }
                    |> Choice.bindError (fun _ -> Choice.result <| Constp(s, tys))
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

    let rec type_of_pretype ty =
        choice {
            match ty with
            | Stv n -> 
                stvs_translated := true
                let s = "?" + (string n)
                return mk_vartype(s)
            | Utv(v) -> 
                return mk_vartype(v)
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
            }

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
        }

    type_of_pretype, term_of_preterm, retypecheck

