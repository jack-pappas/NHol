﻿(*

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
/// Simplistic HOL Light prettyprinter, using the OCaml "Format" library.
module NHol.printer

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
#endif

infof "Entering printer.fs"

(* ------------------------------------------------------------------------- *)
(* Character discrimination.                                                 *)
(* ------------------------------------------------------------------------- *)

//
let private ctable =
    // OPTIMIZE :   Make sure these strings are compiled into literals.
    //              They may need to be lifted out of this function into the module for that.
    let spaces = " \t\n\r"
    let separators = ",;"
    let brackets = "()[]{}"
    let symbs = "\\!@#$%^&*-+|\\<=>/?~.:"
    let alphas = "'abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    let nums = "0123456789"
    
    let ctable =
        let inline maxAsciiCode str =
            // OPTIMIZE : Use String.mapReduce from a future version of ExtCore, instead of String.fold.
            String.fold (fun x c -> max x (int c)) 0 str

        maxAsciiCode spaces
        |> max (maxAsciiCode separators)
        |> max (maxAsciiCode brackets)
        |> max (maxAsciiCode symbs)
        |> max (maxAsciiCode alphas)
        |> max (maxAsciiCode nums)
        |> max (int System.Byte.MaxValue)
        |> Array.zeroCreate

    String.iter (fun c -> Array.set ctable (int c) 1) spaces
    String.iter (fun c -> Array.set ctable (int c) 2) separators
    String.iter (fun c -> Array.set ctable (int c) 4) brackets
    String.iter (fun c -> Array.set ctable (int c) 8) symbs
    String.iter (fun c -> Array.set ctable (int c) 16) alphas
    String.iter (fun c -> Array.set ctable (int c) 32) nums
    ctable

/// Returns the ASCII code for the first (0th) character in a string.
let inline private charcode (s : string) =
//    #if DEBUG
//    if String.length s <> 1 then
//        logger.Debug ("NHol.printer.charcode: The string should contain exactly one (1) character, but it contains {0} characters. (s = {1})",
//            String.length s, s)
//    #endif
    // Note: In F# 65536 retuns 0, so the max is 65535 in F#.
    // int <| Checked.byte s.[0]
    int s.[0]

/// Checks that a string contains exactly one (1) character,
/// and raises an exception if otherwise.
let private checkStringIsSingleChar c =
    if String.length c <> 1 then
        let msg = sprintf "The string should contain exactly one (1) character, but it contains %i characters. (c = %s)" (String.length c) c
        invalidArg "c" msg

/// Tests if a one-character string is some kind of space.
let isspace c =
    // Preconditions
    //checkStringIsSingleChar c

    Array.get ctable (charcode c) = 1

/// Tests if a one-character string is a separator.
let issep c =
    // Preconditions
    //checkStringIsSingleChar c

    Array.get ctable (charcode c) = 2

/// Tests if a one-character string is some kind of bracket.
let isbra c =
    // Preconditions
    //checkStringIsSingleChar c

    Array.get ctable (charcode c) = 4

/// Tests if a one-character string is a symbol other than bracket or separator.
let issymb c =
    // Preconditions
    //checkStringIsSingleChar c

    Array.get ctable (charcode c) = 8

/// Tests if a one-character string is alphabetic.
let isalpha c =
    // Preconditions
    //checkStringIsSingleChar c

    Array.get ctable (charcode c) = 16

/// Tests if a one-character string is a decimal digit.
let isnum c =
    // Preconditions
    //checkStringIsSingleChar c

    Array.get ctable (charcode c) = 32

/// Tests if a one-character string is alphanumeric.
let isalnum c =
    // Preconditions
    //checkStringIsSingleChar c

    Array.get ctable (charcode c) >= 16


(* ------------------------------------------------------------------------- *)
(* Reserved words.                                                           *)
(* ------------------------------------------------------------------------- *)

let private reswords = 
    ref [
        "(";
        ")";
        "[";
        "]";
        "{";
        "}";
        ":";
        ";";
        ".";
        "|";
        "let";
        "in";
        "and";
        "if";
        "then";
        "else";
        "match";
        "with";
        "function";
        "->";
        "when"]

/// Add given strings to the set of reserved words.
let reserve_words ns =
    reswords := union !reswords ns

/// Remove given strings from the set of reserved words.
let unreserve_words ns =
    reswords := subtract !reswords ns

/// Tests if a string is one of the reserved words.
let is_reserved_word n =
    mem n !reswords

/// Returns the list of reserved words.
let reserved_words () =
    !reswords


(* ------------------------------------------------------------------------- *)
(* Functions to access the global tables controlling special parse status.   *)
(*                                                                           *)
(*  << List of binders;                                                       *)
(*                                                                           *)
(*  << List of prefixes (right-associated unary functions like negation).     *)
(*                                                                           *)
(*  << List of infixes with their precedences and associations.               *)
(*                                                                           *)
(* Note that these tables are independent of constant/variable status or     *)
(* whether an identifier is symbolic.                                        *)
(* ------------------------------------------------------------------------- *)

let private binder_list : string list ref = ref []

/// Stops the quotation parser from treating a name as a binder.
let unparse_as_binder n =
    binder_list := subtract !binder_list [n]

/// Makes the quotation parser treat a name as a binder.
let parse_as_binder n =
    binder_list := union !binder_list [n]

/// Tests if a string has binder status in the parser.
let parses_as_binder n =
    mem n !binder_list

/// Lists the binders.
let binders () =
    !binder_list


let private prefix_list : string list ref = ref []

/// Removes prefix status for an identifier.
let unparse_as_prefix n =
    prefix_list := subtract !prefix_list [n]

/// Gives an identifier prefix status.
let parse_as_prefix n =
    prefix_list := union !prefix_list [n]

/// Tests if an identifier has prefix status.
let is_prefix n =
    mem n !prefix_list

/// <summary>
/// Certain identifiers <c>c</c> have prefix status, meaning that combinations of the form
/// <c>c f x</c> will be parsed as <c>c (f x)</c> rather than the usual <c>(c f) x</c>.
/// The call <c>prefixes()</c> returns the list of all such identifiers.
/// </summary>
let prefixes () =
    !prefix_list


//
let private infix_list : (string * (int * string)) list ref = ref []

/// Removes string from the list of infix operators.
let unparse_as_infix n =
    infix_list := filter (((<>) n) << fst) !infix_list

//
let private infix_cmp (s, (x, a)) (t, (y, b)) =
    x < y || x = y && a > b || x = y && a = b && s < t

/// Adds identifier to list of infixes, with given precedence and associativity.
let parse_as_infix (n, d) =
    infix_list := sort infix_cmp ((n, d) :: (filter (((<>) n) << fst) !infix_list))

/// Get the precedence and associativity of an infix operator.
let get_infix_status n =
    assoc n !infix_list

/// Lists the infixes currently recognized by the parser.
let infixes () =
    !infix_list


(* ------------------------------------------------------------------------- *)
(* Interface mapping.                                                        *)
(* ------------------------------------------------------------------------- *)

/// List of active interface mappings.
let the_interface : (string * (string * hol_type)) list ref = ref []

/// List of overload skeletons for all overloadable identifiers.
let the_overload_skeletons : (string * hol_type) list ref = ref []

open FSharp.Compatibility.OCaml.Format

set_max_boxes 100

(* ------------------------------------------------------------------------- *)
(* Flag determining whether interface/overloading is reversed on printing.   *)
(* ------------------------------------------------------------------------- *)

/// Determines whether interface map is printed on output (default 'true').
let reverse_interface_mapping = ref true

(* ------------------------------------------------------------------------- *)
(* Determine binary operators that print without surrounding spaces.         *)
(* ------------------------------------------------------------------------- *)

/// Determines which binary operators are printed with surrounding spaces.
let unspaced_binops =
    ref [","; ".."; "$"]

(* ------------------------------------------------------------------------- *)
(* Binary operators to print at start of line when breaking.                 *)
(* ------------------------------------------------------------------------- *)

/// Determines which binary operators are line-broken to the left.
let prebroken_binops =
    ref ["==>"]

(* ------------------------------------------------------------------------- *)
(* Force explicit indications of bound variables in set abstractions.        *)
(* ------------------------------------------------------------------------- *)

/// Determines whether bound variables in set abstractions are made explicit.
let print_unambiguous_comprehensions = ref false

(* ------------------------------------------------------------------------- *)
(* Print the universal set UNIV:A->bool as "(:A)".                           *)
(* ------------------------------------------------------------------------- *)

/// Determines whether the universe set on a type is printed just as the type.
let typify_universal_set = ref true

(* ------------------------------------------------------------------------- *)
(* Flag controlling whether hypotheses print.                                *)
(* ------------------------------------------------------------------------- *)

/// Flag determining whether the assumptions of theorems are printed explicitly.
let print_all_thm = ref true

(* ------------------------------------------------------------------------- *)
(* Get the name of a constant or variable.                                   *)
(* ------------------------------------------------------------------------- *)

/// Gets the name of a constant or variable.
let name_of tm =
    match tm with
    | Var(x, _)
    | Const(x, _) -> x
    | _ -> ""

(* ------------------------------------------------------------------------- *)
(* Printer for types.                                                        *)
(* ------------------------------------------------------------------------- *)

//
let private soc sep flag ss =
    if List.isEmpty ss then ""
    else 
        let s = end_itlist (fun s1 s2 -> s1 + sep + s2) ss
        if flag then "(" + s + ")"
        else s

//
let rec private sot pr ty : Protected<string> =
    dest_vartype ty
    |> Choice.bindError (fun _ ->
        dest_type ty
        |> Choice.mapError (fun e ->
            nestedFailure e "sot: malformed type")
        |> Choice.bind (fun ty' ->
            choice {
            match ty' with
            | con, [] ->
                return con
            | "fun", [ty1; ty2] ->
                let! sot_ty1 = sot 1 ty1
                let! sot_ty2 = sot 0 ty2
                return
                    soc "->" (pr > 0) [sot_ty1;
                                        sot_ty2]
            | "sum", [ty1; ty2] ->
                let! sot_ty1 = sot 3 ty1
                let! sot_ty2 = sot 2 ty2
                return
                    soc "+" (pr > 2) [sot_ty1;
                                        sot_ty2]
            | "prod", [ty1; ty2] ->
                let! sot_ty1 = sot 5 ty1
                let! sot_ty2 = sot 4 ty2
                return
                    soc "#" (pr > 4) [sot_ty1;
                                        sot_ty2]
            | "cart", [ty1; ty2] ->
                let! sot_ty1 = sot 6 ty1
                let! sot_ty2 = sot 7 ty2
                return
                    soc "^" (pr > 6) [sot_ty1;
                                        sot_ty2]
            | con, args ->
                let! foo1 = Choice.List.map (sot 0) args
                return (soc "," true foo1) + con
            }))

/// Prints a type (without colon or quotes) to formatter.
let pp_print_type fmt ty =
    pp_print_string fmt (Choice.get <| sot 0 ty)

/// Prints a type with initial colon and surrounding quotes to formatter.
let pp_print_qtype fmt ty =
    pp_print_string fmt ("`:" + (Choice.get <| sot 0 ty) + "`")


(* ------------------------------------------------------------------------- *)
(* Allow the installation of user printers. Must fail quickly if N/A.        *)
(* ------------------------------------------------------------------------- *)

// TODO :   This should (eventually) be modified to have the type (string * (term -> Protected<unit>)) list ref.
let private user_printers : (string * (term -> unit)) list ref = ref []

/// Install a user-defined printing function into the HOL Light term printer.
let install_user_printer pr =
    user_printers := pr :: !user_printers

/// Remove user-defined printer from the HOL Light term printing.
let delete_user_printer s =
    // TODO :   This function should be modified to remove the use of Option.get -- this function
    //          will currently fail (raise an exn) if 's' is not in the list of user printers.
    user_printers := snd(Option.get <| remove (fun (s', _) -> s = s') !user_printers)

/// Try user-defined printers on a term.
let try_user_printer tm : Protected<unit> =
    !user_printers
    |> tryfind (fun (_, pr) ->
        // TODO : wrong use of Some, need to change this
        Some <| pr tm)
    |> Option.toChoiceWithError "find"


(* ------------------------------------------------------------------------- *)
(* Printer for terms.                                                        *)
(* ------------------------------------------------------------------------- *)

//
module internal PP_print_term =
    let reverse_interface(s0, ty0) =
        if not !reverse_interface_mapping then s0
        else
            match find (fun (s, (s', ty)) -> s' = s0 && Choice.isResult <| type_match ty ty0 []) !the_interface with
            | Some(s0', _) -> s0'
            | None -> s0

    let rec DEST_BINARY c tm =
        choice {
            let! il, r = dest_comb tm
            let! i, l = dest_comb il
            let! ci = dest_const i
            let! cc = dest_const c
            if i = c || (is_const i && is_const c && reverse_interface ci = reverse_interface cc) then
                return l, r
            else
                return! Choice.fail()
        }
        |> Choice.mapError (fun e -> nestedFailure e "DEST_BINARY")

    and ARIGHT s =
        choice {
        match get_infix_status s with
        | Some (_, "right") ->
            return true
        | Some _ ->
            return false
        // Add this to ensure the original meaning
        | None ->
            return! Choice.nestedFailwith (exn "find") "ARIGHT"
        }

    let rec powerof10 n = 
        if abs_num n </ Int 1 then false
        elif n =/ Int 1 then true
        else powerof10(n / Int 10)

    let bool_of_term t =
        choice {
        match t with
        | Const("T", _) ->
            return true
        | Const("F", _) ->
            return false
        | _ ->
            return! Choice.failwith "bool_of_term"
        }

    let code_of_term t =
        let f, tms = strip_comb t
        // Choice.get is safe to use here
        // OPTIMIZE : Use pattern-matching here instead of 'length' -- it's faster because length is O(n).
        if not(is_const f && fst(Choice.get <| dest_const f) = "ASCII") || not(length tms = 8) then
            failwith "code_of_term"
        else
            itlist (fun b f ->
                if b then 1 + 2 * f else 2 * f)
                    (map (Choice.get << bool_of_term) (rev tms)) 0

    let rec dest_clause tm = 
        choice {
            let! tm' = body tm
            let! tm'' = body tm'
            let pbod = snd(strip_exists tm'')
            let s, args = strip_comb pbod
            // OPTIMIZE : Use pattern-matching here instead of 'length' -- it's faster because length is O(n).
            if name_of s = "_UNGUARDED_PATTERN" && length args = 2 then
                let! tm1 = rator(hd args)
                let! tm2 = rator(hd(tl args))                
                return! Choice.List.map id [rand tm1; rand tm2]
            elif name_of s = "_GUARDED_PATTERN" && length args = 3 then
                let! tm1 = rator(hd args)
                let! tm2 = rator(hd(tl(tl args)))
                return! Choice.List.map id [rand tm1; Choice.result <| hd(tl args); rand tm2]
            else 
                return! Choice.failwith "dest_clause"
        }

    let rec dest_clauses tm = 
        choice {
            let s, args = strip_comb tm
            // TODO : Use pattern-patching here to check length of args instead of calling 'length' (which is O(n)).
            if name_of s = "_SEQPATTERN" && length args = 2 then
                let! cl = dest_clause(hd args)
                let! cls = dest_clauses(hd(tl args))
                return (cl :: cls)
            else
                let! cl = dest_clause tm
                return [cl]
        }

    let rec print_term fmt prec tm =
            (* OPTIMIZE: Modify these functions to use option -- these heavily-nested
                         try-catch blocks are extremely slow. *)
            match try_user_printer tm with
            | Success _ -> ()
            | Error _ -> 
                match dest_numeral tm with
                | Success tm ->
                    pp_print_string fmt (string_of_num tm)
                | Error _ -> 
                    match dest_list tm with
                    | Success tms ->
                         try
                            // CLEAN : Rename this value to something sensible.
                            let foo1 =
                                type_of tm
                                |> Choice.bind dest_type
                                |> Choice.bind (snd >> hd >> dest_type)
                                |> Choice.map fst
                                |> ExtCore.Choice.bindOrRaise
                            if foo1 <> "char" then fail()
                            else 
                                let ccs = map (String.make 1 << Char.chr << code_of_term) tms
                                let s = "\"" + String.escaped(implode ccs) + "\""
                                pp_print_string fmt s
                         with
                         | Failure _ -> 
                             pp_print_string fmt "["
                             print_term_sequence fmt "; " 0 tms
                             pp_print_string fmt "]"
                    | Error _ -> 
                        if is_gabs tm then print_binder fmt prec tm
                        else 
                            let hop, args = strip_comb tm
                            let s0 = name_of hop
                            let ty0 = Choice.get <| type_of hop
                            let s = reverse_interface(s0, ty0)
                            
                            if s = "EMPTY" && is_const tm && args = [] then pp_print_string fmt "{}"
                            else 
                                try 
                                    if s = "UNIV" && !typify_universal_set && is_const tm && args = [] then 
                                        let ty = fst(Choice.get <| dest_fun_ty(Choice.get <| type_of tm))
                                        (pp_print_string fmt "(:"
                                         pp_print_type fmt ty
                                         pp_print_string fmt ")")
                                    else fail()
                                with
                                | Failure _ -> 
                                    try 
                                        if s <> "INSERT" then fail()
                                        else 
                                            let mems, oth = splitlist (Choice.toOption << dest_binary "INSERT") tm
                                            // Choice.get is safe to use here
                                            if is_const oth && fst(Choice.get <| dest_const oth) = "EMPTY" then 
                                                (pp_print_string fmt "{"
                                                 print_term_sequence fmt ", " 14 mems
                                                 pp_print_string fmt "}")
                                            else fail()
                                    with
                                    | Failure _ -> 
                                        try 
                                            if not(s = "GSPEC") then fail()
                                            else 
                                                let evs, bod = strip_exists(Choice.get <| body(Choice.get <| rand tm))
                                                let bod1, fabs = Choice.get <| dest_comb bod
                                                let bod2, babs = Choice.get <| dest_comb bod1
                                                let c = Choice.get <| rator bod2
                                                if fst(Choice.get <| dest_const c) <> "SETSPEC" then fail()
                                                else 
                                                    pp_print_string fmt "{"
                                                    print_term fmt 0 fabs
                                                    pp_print_string fmt " | "
                                                    (let fvs = frees fabs
                                                     let bvs = frees babs
                                                     if not(!print_unambiguous_comprehensions) 
                                                        && set_eq evs (if (length fvs <= 1 || bvs = []) then fvs
                                                                       else intersect fvs bvs)
                                                     then ()
                                                     else 
                                                         (print_term_sequence fmt "," 14 evs
                                                          pp_print_string fmt " | "))
                                                    print_term fmt 0 babs
                                                    pp_print_string fmt "}"
                                        with
                                        | Failure _ -> 
                                            try 
                                                let eqs, bod = Choice.get <| dest_let tm
                                                (if prec = 0 then pp_open_hvbox fmt 0
                                                 else 
                                                     (pp_open_hvbox fmt 1
                                                      pp_print_string fmt "(")
                                                 pp_print_string fmt "let "
                                                 print_term fmt 0 (Choice.get <| mk_eq(hd eqs))
                                                 do_list (fun (v, t) -> 
                                                         pp_print_break fmt 1 0
                                                         pp_print_string fmt "and "
                                                         print_term fmt 0 (Choice.get <| mk_eq(v, t))) (tl eqs)
                                                 pp_print_string fmt " in"
                                                 pp_print_break fmt 1 0
                                                 print_term fmt 0 bod
                                                 if prec = 0 then ()
                                                 else pp_print_string fmt ")"
                                                 pp_close_box fmt ())
                                            with
                                            | Failure _ -> 
                                                try 
                                                    if s <> "DECIMAL" then fail()
                                                    else 
                                                        let n_num = Choice.get <| dest_numeral(hd args)
                                                        let n_den = Choice.get <| dest_numeral(hd(tl args))
                                                        if not(powerof10 n_den) then fail()
                                                        else 
                                                            let s_num = string_of_num(quo_num n_num n_den)
                                                            let s_den = 
                                                                implode
                                                                    (tl
                                                                         (explode
                                                                              (string_of_num
                                                                                   (n_den +/ (mod_num n_num n_den)))))
                                                            pp_print_string fmt ("#" + s_num + (if n_den = Int 1 then ""
                                                                                                else ".") + s_den)
                                                with
                                                | Failure _ -> 
                                                    try 
                                                        if s <> "_MATCH" || length args <> 2 then failwith ""
                                                        else 
                                                            let cls = Choice.get <| dest_clauses(hd(tl args))
                                                            (if prec = 0 then ()
                                                             else pp_print_string fmt "("
                                                             pp_open_hvbox fmt 0
                                                             pp_print_string fmt "match "
                                                             print_term fmt 0 (hd args)
                                                             pp_print_string fmt " with"
                                                             pp_print_break fmt 1 2
                                                             print_clauses fmt cls
                                                             pp_close_box fmt ()
                                                             if prec = 0 then ()
                                                             else pp_print_string fmt ")")
                                                    with
                                                    | Failure _ -> 
                                                        try 
                                                            if s <> "_FUNCTION" || length args <> 1 then failwith ""
                                                            else 
                                                                let cls = Choice.get <| dest_clauses(hd args)
                                                                (if prec = 0 then ()
                                                                 else pp_print_string fmt "("
                                                                 pp_open_hvbox fmt 0
                                                                 pp_print_string fmt "function"
                                                                 pp_print_break fmt 1 2
                                                                 print_clauses fmt cls
                                                                 pp_close_box fmt ()
                                                                 if prec = 0 then ()
                                                                 else pp_print_string fmt ")")
                                                        with
                                                        | Failure _ ->
                                                            if s = "COND" && length args = 3 then 
                                                                (if prec = 0 then ()
                                                                 else pp_print_string fmt "("
                                                                 pp_open_hvbox fmt (-1)
                                                                 pp_print_string fmt "if "
                                                                 print_term fmt 0 (hd args)
                                                                 pp_print_break fmt 0 0
                                                                 pp_print_string fmt " then "
                                                                 print_term fmt 0 (hd(tl args))
                                                                 pp_print_break fmt 0 0
                                                                 pp_print_string fmt " else "
                                                                 print_term fmt 0 (hd(tl(tl args)))
                                                                 pp_close_box fmt ()
                                                                 if prec = 0 then ()
                                                                 else pp_print_string fmt ")")
                                                            elif is_prefix s && length args = 1 then 
                                                                (if prec = 1000 then pp_print_string fmt "("
                                                                 else ()
                                                                 pp_print_string fmt s
                                                                 (if isalnum s 
                                                                     || s = "--" && length args = 1 
                                                                        && (try 
                                                                                let l, r = Choice.get <| dest_comb(hd args)
                                                                                let s0 = name_of l
                                                                                let ty0 = Choice.get <| type_of l
                                                                                reverse_interface(s0, ty0) = "--" 
                                                                                || mem (fst(Choice.get <| dest_const l)) 
                                                                                       ["real_of_num";
                                                                                        "int_of_num"]
                                                                            with
                                                                            | Failure _ -> false) 
                                                                     || s = "~" && length args = 1 && is_neg(hd args)
                                                                  then pp_print_string fmt " "
                                                                  else ())
                                                                 print_term fmt 999 (hd args)
                                                                 if prec = 1000 then pp_print_string fmt ")"
                                                                 else ())
                                                            elif parses_as_binder s && length args = 1 && is_gabs(hd args) then
                                                                print_binder fmt prec tm
                                                            elif Option.isSome <| get_infix_status s && length args = 2 then 
                                                                let bargs = 
                                                                    if Choice.get <| ARIGHT s then 
                                                                        let tms, tmt = splitlist (Choice.toOption << DEST_BINARY hop) tm
                                                                        tms @ [tmt]
                                                                    else 
                                                                        let tmt, tms = 
                                                                            rev_splitlist (Choice.toOption << DEST_BINARY hop) tm
                                                                        tmt :: tms
                                                                let newprec = fst(Option.get <| get_infix_status s)
                                                                (if newprec <= prec then 
                                                                     (pp_open_hvbox fmt 1
                                                                      pp_print_string fmt "(")
                                                                 else pp_open_hvbox fmt 0
                                                                 print_term fmt newprec (hd bargs)
                                                                 do_list (fun x -> 
                                                                         if mem s (!unspaced_binops) then ()
                                                                         elif mem s (!prebroken_binops) then 
                                                                             pp_print_break fmt 1 0
                                                                         else pp_print_string fmt " "
                                                                         pp_print_string fmt s
                                                                         if mem s (!unspaced_binops) then 
                                                                             pp_print_break fmt 0 0
                                                                         elif mem s (!prebroken_binops) then 
                                                                             pp_print_string fmt " "
                                                                         else pp_print_break fmt 1 0
                                                                         print_term fmt newprec x) (tl bargs)
                                                                 if newprec <= prec then pp_print_string fmt ")"
                                                                 else ()
                                                                 pp_close_box fmt ())
                                                            elif (is_const hop || is_var hop) && args = [] then 
                                                                let s' = 
                                                                    if parses_as_binder s || Option.isSome <| get_infix_status s || is_prefix s then "(" + s + ")"
                                                                    else s
                                                                pp_print_string fmt s'
                                                            else 
                                                                let l, r = Choice.get <| dest_comb tm
                                                                (pp_open_hvbox fmt 0
                                                                 if prec = 1000 then pp_print_string fmt "("
                                                                 else ()
                                                                 print_term fmt 999 l
                                                                 // TODO: this converted form is a bit non-sense
                                                                 match dest_const l with
                                                                 | Success(s, _) -> 
                                                                    if not <| mem s ["real_of_num"; "int_of_num"] then
                                                                        pp_print_space fmt ()
                                                                 | Error _ -> pp_print_space fmt ()
                                                                 print_term fmt 1000 r
                                                                 if prec = 1000 then pp_print_string fmt ")"
                                                                 else ()
                                                                 pp_close_box fmt ())

    and print_term_sequence fmt sep prec tms =
        if not <| List.isEmpty tms then
            print_term fmt prec (hd tms)
            let ttms = tl tms
            if not <| List.isEmpty ttms then
                pp_print_string fmt sep
                print_term_sequence fmt sep prec ttms

    and print_binder fmt prec tm =
            let absf = is_gabs tm
            let s = 
                if absf then "\\"
                else name_of(Choice.get <| rator tm)
            let rec collectvs tm = 
                if absf then 
                    if is_abs tm then 
                        let v, t = Choice.get <| dest_abs tm
                        let vs, bod = collectvs t
                        (false, v) :: vs, bod
                    elif is_gabs tm then 
                        let v, t = Choice.get <| dest_gabs tm
                        let vs, bod = collectvs t
                        (true, v) :: vs, bod
                    else [], tm
                // Choice.get is safe to use here
                elif is_comb tm && name_of(Choice.get <| rator tm) = s then 
                    if is_abs(Choice.get <| rand tm) then 
                        let v, t = Choice.get <| dest_abs(Choice.get <| rand tm)
                        let vs, bod = collectvs t
                        (false, v) :: vs, bod
                    elif is_gabs(Choice.get <| rand tm) then 
                        let v, t = Choice.get <| dest_gabs(Choice.get <| rand tm)
                        let vs, bod = collectvs t
                        (true, v) :: vs, bod
                    else [], tm
                else [], tm
            let vs, bod = collectvs tm
            ((if prec = 0 then pp_open_hvbox fmt 4
              else (pp_open_hvbox fmt 5; pp_print_string fmt "("))
             pp_print_string fmt s
             (if isalnum s then pp_print_string fmt " " else ())
             do_list (fun (b, x) -> 
                (if b then pp_print_string fmt "(" else ())
                print_term fmt 0 x
                (if b then pp_print_string fmt ")" else ())
                pp_print_string fmt " ") (butlast vs)
             (if fst(last vs) then pp_print_string fmt "(" else ())
             print_term fmt 0 (snd(last vs))
             (if fst(last vs) then pp_print_string fmt ")" else ())
             pp_print_string fmt "."
             (if length vs = 1 then pp_print_string fmt " " else pp_print_space fmt ())
             print_term fmt 0 bod
             (if prec = 0 then () else pp_print_string fmt ")")
             pp_close_box fmt ())

    and print_clauses fmt cls = 
        match cls with
        | [c] ->
            print_clause fmt c
        | c :: cs -> 
            print_clause fmt c
            pp_print_break fmt 1 0
            pp_print_string fmt "| "
            print_clauses fmt cs
        | _ ->
            failwith "print_clauses: Unhandled case."

    and print_clause fmt cl = 
        match cl with
        | [p; g; r] -> 
            print_term fmt 1 p
            pp_print_string fmt " when "
            print_term fmt 1 g
            pp_print_string fmt " -> "
            print_term fmt 1 r
        | [p; r] -> 
            print_term fmt 1 p
            pp_print_string fmt " -> "
            print_term fmt 1 r
        | _ ->
            failwith "print_clause: Unhandled case."


/// Prints a term (without quotes) to formatter.
let pp_print_term fmt tm =
    try
        PP_print_term.print_term fmt 0 tm
    with Failure _ as ex ->
        (* NOTE :   We currently suppress certain exceptions which may be raised during
                    printing; however, we do log them for diagnostics purposes. *)
        logger.DebugException ("Suppressed exception in 'pp_print_term'.", ex)

        // NOTE: suppress all exceptions in printing
        ()

(* ------------------------------------------------------------------------- *)
(* Print term with quotes.                                                   *)
(* ------------------------------------------------------------------------- *)

/// Prints a term with surrounding quotes to formatter.
let pp_print_qterm fmt tm =
    pp_print_string fmt "`"
    pp_print_term fmt tm
    pp_print_string fmt "`"

(* ------------------------------------------------------------------------- *)
(* Printer for theorems.                                                     *)
(* ------------------------------------------------------------------------- *)

/// Prints a theorem to formatter.
let pp_print_thm fmt th =
    let asl, tm = dest_thm th
    if not <| List.isEmpty asl then
        if !print_all_thm then
            pp_print_term fmt (hd asl)
            do_list (fun x ->
                pp_print_string fmt ","
                pp_print_space fmt ()
                pp_print_term fmt x) (tl asl)
        else
            pp_print_string fmt "..."
        pp_print_space fmt ()
    
    pp_open_hbox fmt ()
    pp_print_string fmt "|- "
    pp_print_term fmt tm
    pp_close_box fmt ()

(* ------------------------------------------------------------------------- *)
(* Print on standard output.                                                 *)
(* ------------------------------------------------------------------------- *)

/// Prints a type (without colon or quotes) to standard output.
let print_type = pp_print_type std_formatter

/// Prints a type with colon and surrounding quotes to standard output.
let print_qtype = pp_print_qtype std_formatter

/// Prints a HOL term (without quotes) to the standard output.
let print_term = pp_print_term std_formatter

/// Prints a HOL term with surrounding quotes to standard output.
let print_qterm = pp_print_qterm std_formatter

/// Prints a HOL theorem to the standard output.
let print_thm = pp_print_thm std_formatter

(* ------------------------------------------------------------------------- *)
(* Conversions to string.                                                    *)
(* ------------------------------------------------------------------------- *)

/// Modifies a formatting printing function to return its output as a string.
let print_to_string printer =
    let sbuff = ref ""
    let rec output s m n =
        sbuff := !sbuff + (String.sub s m n)
    let flush() = ()
    let fmt = make_formatter output flush
    pp_set_max_boxes fmt 100 |> ignore
    fun i ->
        printer fmt i |> ignore
        pp_print_flush fmt () |> ignore
        let s = !sbuff
        sbuff := ""
        s

/// Converts a HOL type to a string representation.
let string_of_type = print_to_string pp_print_type

/// Converts a HOL term to a string representation.
let string_of_term = print_to_string pp_print_term

/// Converts a HOL theorem to a string representation.
let string_of_thm = print_to_string pp_print_thm

/// Prints a term list to formatter.
let pp_print_list_term fmt (al : term list) =
    // CLEAN : Use List.iter instead of a recursive function here.
    let rec pp_print_list_termInner fmt al =
        match al with
        | [] -> ()
        | typa :: tl ->
            pp_print_term fmt typa
            pp_print_break fmt 0 0
            pp_print_list_termInner fmt tl
        
    if List.isEmpty al then
        pp_print_string fmt "No items"
    else
        pp_open_hvbox fmt 0
        pp_print_list_termInner fmt al
        pp_close_box fmt ()

/// Prints a term list to the standard output.
let print_list_term = pp_print_list_term std_formatter

/// Converts a term list to a string representation.
let string_of_list_term = print_to_string pp_print_list_term

/// Prints a ((hol_type * hol_type) list) to formatter.
let pp_print_list_typtyp fmt (al : (hol_type * hol_type) list) =
    // CLEAN : Use List.iter instead of a recursive function here.
    let rec pp_print_list_typtypInner fmt al =
        match al with
        | [] -> ()
        | (typa, typb) :: tl ->
            pp_print_type fmt typa
            pp_print_string fmt ", "
            pp_print_type fmt typb
            pp_print_break fmt 0 0
            pp_print_list_typtypInner fmt tl
        
    if List.isEmpty al then
        pp_print_string fmt "No items"
    else
        pp_open_hvbox fmt 0
        pp_print_list_typtypInner fmt al
        pp_close_box fmt ()

/// Prints a ((hol_type * hol_type) list) to the standard output.
let print_list_typtyp = pp_print_list_typtyp std_formatter

/// Converts a ((hol_type * hol_type) list) to a string representation.
let string_of_list_typtyp = print_to_string pp_print_list_typtyp

(* ------------------------------------------------------------------------- *)
(* Prints the type after each variable.  Useful for "debugging" type issues. *)
(* This code is from the TipsAndTricks section of the Flyspeck project wiki. *)
(* ------------------------------------------------------------------------- *)

let print_varandtype tm =
    choice {
    let hop, args = strip_comb tm
    let s = name_of hop
    let! ty = type_of hop
    if is_var hop && List.isEmpty args then
        let fmt = std_formatter
        pp_print_string fmt "("
        pp_print_string fmt s
        pp_print_string fmt ":"
        pp_print_type fmt ty
        pp_print_string fmt ")"
    else
        return! Choice.failwith "print_varandtype"
    }

let [<Literal>] private showTypesPrinterName = "Show Types"

let show_types () =
    install_user_printer (showTypesPrinterName, print_varandtype >> Choice.get)

let hide_types () =
    try delete_user_printer showTypesPrinterName
    with Failure _ as e ->
        nestedFailwith e "hide_types: Types are already hidden."


(* ------------------------------------------------------------------------- *)
(* Install all the printers.                                                 *)
(* ------------------------------------------------------------------------- *)

#if INTERACTIVE
fsi.AddPrinter string_of_type
fsi.AddPrinter string_of_term
fsi.AddPrinter string_of_thm
#endif
