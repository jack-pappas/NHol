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
/// Simplistic HOL Light prettyprinter, using the OCaml "Format" library.
module NHol.printer

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
#endif

(* ------------------------------------------------------------------------- *)
(* Character discrimination.                                                 *)
(* ------------------------------------------------------------------------- *)

// isspace: Tests if a one-character string is some kind of space.
// issep: Tests if a one-character string is a separator.
// isbra: Tests if a one-character string is some kind of bracket.
// issymb: Tests if a one-character string is a symbol other than bracket or separator.
// isalpha: Tests if a one-character string is alphabetic.
// isnum: Tests if a one-character string is a decimal digit.
// isalnum: Tests if a one-character string is alphanumeric.
let isspace, issep, isbra, issymb, isalpha, isnum, isalnum = 
    let charcode s = Char.code(String.get s 0)
    let spaces = " \t\n\r"
    let separators = ",;"
    let brackets = "()[]{}"
    let symbs = "\\!@#$%^&*-+|\\<=>/?~.:"
    let alphas = "'abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    let nums = "0123456789"
    let allchars = spaces + separators + brackets + symbs + alphas + nums
    let csetsize = itlist (max << charcode) (explode allchars) 256
    let ctable = Array.make csetsize 0
    do_list (fun c -> Array.set ctable (charcode c) 1) (explode spaces)
    do_list (fun c -> Array.set ctable (charcode c) 2) (explode separators)
    do_list (fun c -> Array.set ctable (charcode c) 4) (explode brackets)
    do_list (fun c -> Array.set ctable (charcode c) 8) (explode symbs)
    do_list (fun c -> Array.set ctable (charcode c) 16) (explode alphas)
    do_list (fun c -> Array.set ctable (charcode c) 32) (explode nums)
    let isspace c = Array.get ctable (charcode c) = 1
    let issep c = Array.get ctable (charcode c) = 2
    let isbra c = Array.get ctable (charcode c) = 4
    let issymb c = Array.get ctable (charcode c) = 8
    let isalpha c = Array.get ctable (charcode c) = 16
    let isnum c = Array.get ctable (charcode c) = 32
    let isalnum c = Array.get ctable (charcode c) >= 16
    isspace, issep, isbra, issymb, isalpha, isnum, isalnum

(* ------------------------------------------------------------------------- *)
(* Reserved words.                                                           *)
(* ------------------------------------------------------------------------- *)

// reserve_words: Add given strings to the set of reserved words.
// unreserve_words: Remove given strings from the set of reserved words.
// is_reserved_word: Tests if a string is one of the reserved words.
// reserved_words: Returns the list of reserved words.
let reserve_words, unreserve_words, is_reserved_word, reserved_words = 
    let reswords = 
        ref ["(";
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
    (fun ns -> reswords := union (!reswords) ns), (fun ns -> reswords := subtract (!reswords) ns), 
    (fun n -> mem n (!reswords)), (fun () -> !reswords)

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

// unparse_as_binder: Stops the quotation parser from treating a name as a binder.
// parse_as_binder: Makes the quotation parser treat a name as a binder.
// parses_as_binder: Tests if a string has binder status in the parser.
// binders: Lists the binders.
let unparse_as_binder, parse_as_binder, parses_as_binder, binders = 
    let binder_list = ref([] : string list)
    (fun n -> binder_list := subtract (!binder_list) [n]), (fun n -> binder_list := union (!binder_list) [n]), 
    (fun n -> mem n (!binder_list)), (fun () -> !binder_list)

// unparse_as_prefix: Removes prefix status for an identifier.
// parse_as_prefix: Gives an identifier prefix status.
// is_prefix: Tests if an identifier has prefix status.
// prefixes: Certain identifiers 'c' have prefix status, meaning that combinations of the form 'c f x' will
//           be parsed as 'c (f x)' rather than the usual '(c f) x'. The call 'prefixes()' returns the list
//           of all such identifiers.
let unparse_as_prefix, parse_as_prefix, is_prefix, prefixes = 
    let prefix_list = ref([] : string list)
    (fun n -> prefix_list := subtract (!prefix_list) [n]), (fun n -> prefix_list := union (!prefix_list) [n]), 
    (fun n -> mem n (!prefix_list)), (fun () -> !prefix_list)

// unparse_as_infix: Removes string from the list of infix operators.
// parse_as_infix: Adds identifier to list of infixes, with given precedence and associativity.
// get_infix_status: Get the precedence and associativity of an infix operator.
// infixes: Lists the infixes currently recognized by the parser.
let unparse_as_infix, parse_as_infix, get_infix_status, infixes = 
    let cmp (s, (x, a)) (t, (y, b)) = x < y || x = y && a > b || x = y && a = b && s < t
    let infix_list = ref([] : (string * (int * string)) list)
    (fun n -> infix_list := filter (((<>) n) << fst) (!infix_list)), 
    (fun (n, d) -> infix_list := sort cmp ((n, d) :: (filter (((<>) n) << fst) (!infix_list)))), 
    (fun n -> assoc n !infix_list),
    (fun () -> !infix_list)

(* ------------------------------------------------------------------------- *)
(* Interface mapping.                                                        *)
(* ------------------------------------------------------------------------- *)

/// List of active interface mappings.
let the_interface = ref([] : (string * (string * hol_type)) list)

/// List of overload skeletons for all overloadable identifiers.
let the_overload_skeletons = ref([] : (string * hol_type) list)

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
let prebroken_binops = ref ["==>"]

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
    | Var(x, ty) | Const(x, ty) -> x
    | _ -> ""

(* ------------------------------------------------------------------------- *)
(* Printer for types.                                                        *)
(* ------------------------------------------------------------------------- *)

// pp_print_type: Prints a type (without colon or quotes) to formatter.
// pp_print_qtype: Prints a type with initial colon and surrounding quotes to formatter.
let pp_print_type, pp_print_qtype = 
    let soc sep flag ss = 
        if ss = [] then ""
        else 
            let s = end_itlist (fun s1 s2 -> s1 + sep + s2) ss
            if flag then "(" + s + ")"
            else s
    let rec sot pr ty = 
        match dest_vartype ty with
        | Success s -> s
        | Error _ -> 
            match dest_type ty with
            | Success ty' ->
                match ty' with
                | con, [] -> con
                | "fun", [ty1; ty2] -> 
                    soc "->" (pr > 0) [sot 1 ty1;
                                       sot 0 ty2]
                | "sum", [ty1; ty2] -> 
                    soc "+" (pr > 2) [sot 3 ty1;
                                      sot 2 ty2]
                | "prod", [ty1; ty2] -> 
                    soc "#" (pr > 4) [sot 5 ty1;
                                      sot 4 ty2]
                | "cart", [ty1; ty2] -> 
                    soc "^" (pr > 6) [sot 6 ty1;
                                      sot 7 ty2]
                | con, args -> (soc "," true (map (sot 0) args)) + con
            | Error _ -> "malformed type"
    (fun fmt ty -> pp_print_string fmt (sot 0 ty)), (fun fmt ty -> pp_print_string fmt ("`:" + sot 0 ty + "`"))

(* ------------------------------------------------------------------------- *)
(* Allow the installation of user printers. Must fail quickly if N/A.        *)
(* ------------------------------------------------------------------------- *)

// install_user_printer: Install a user-defined printing function into the HOL Light term printer.
// delete_user_printer: Remove user-defined printer from the HOL Light term printing.
// try_user_printer: Try user-defined printers on a term.
let install_user_printer, delete_user_printer, try_user_printer = 
    let user_printers = ref([] : (string * (term -> unit)) list)
    (fun pr -> user_printers := pr :: (!user_printers)), 
    (fun s -> user_printers := snd(Option.get <| remove (fun (s', _) -> s = s') (!user_printers))),
    // TODO: this function doesn't seem correct 
    (fun tm -> tryfind (fun (_, pr) -> Some <| pr tm) (!user_printers) 
               |> Option.toChoiceWithError "find")

(* ------------------------------------------------------------------------- *)
(* Printer for terms.                                                        *)
(* ------------------------------------------------------------------------- *)

/// Prints a term (without quotes) to formatter.
let pp_print_term =
    let reverse_interface(s0, ty0) =
        if not(!reverse_interface_mapping) then s0
        else 
            match find (fun (s, (s', ty)) -> s' = s0 && Choice.isResult <| type_match ty ty0 []) (!the_interface) with
            | Some(s0', _) -> s0'
            | None -> s0

    let rec DEST_BINARY c tm = 
        choice { 
            let! il, r = dest_comb tm
            let! i, l = dest_comb il
            let! ci = dest_const i
            let! cc = dest_const c
            if i = c || (is_const i && is_const c && reverse_interface ci = reverse_interface cc) then 
                return (l, r)
            else return! Choice.fail()
        }        
        |> Choice.bindError (fun e -> Choice.nestedFailwith e "DEST_BINARY")

    and ARIGHT s = 
        match get_infix_status s with
        | Some (_, "right") -> true
        | Some _ -> false
        // Add this to ensure the original meaning
        | None -> failwith "find"

    let rec powerof10 n = 
        if abs_num n </ Int 1 then false
        elif n =/ Int 1 then true
        else powerof10(n / Int 10)

    let bool_of_term t = 
        match t with
        | Const("T", _) -> true
        | Const("F", _) -> false
        | _ -> failwith "bool_of_term"

    let code_of_term t = 
        let f, tms = strip_comb t
        if not(is_const f && fst(Choice.get <| dest_const f) = "ASCII") || not(length tms = 8) then 
            failwith "code_of_term"
        else 
            itlist (fun b f -> 
                if b then 1 + 2 * f else 2 * f) 
                    (map bool_of_term (rev tms)) 0

    let rec dest_clause tm = 
        choice {
            let! tm' = body tm
            let! tm'' = body tm'
            let pbod = snd(strip_exists tm'')
            let s, args = strip_comb pbod
            if name_of s = "_UNGUARDED_PATTERN" && length args = 2 then
                let! tm1 = rator(hd args)
                let! tm2 = rator(hd(tl args))                
                return! Choice.List.map id [rand tm1; rand tm2]
            elif name_of s = "_GUARDED_PATTERN" && length args = 3 then
                let! tm1 = rator(hd args)
                let! tm2 = rator(hd(tl(tl args)))
                return! Choice.List.map id [rand tm1; Choice.succeed <| hd(tl args); rand tm2]
            else 
                return! Choice.failwith "dest_clause"
        }

    let rec dest_clauses tm = 
        choice {
            let s, args = strip_comb tm
            if name_of s = "_SEQPATTERN" && length args = 2 then
                let! cl = dest_clause(hd args)
                let! cls = dest_clauses(hd(tl args))
                return (cl :: cls)
            else
                let! cl = dest_clause tm
                return [cl]
        }

    fun fmt ->
        let rec print_term prec tm =
            (* OPTIMIZE: Modify these functions to use option -- these heavily-nested
                         try-catch blocks are extremely slow. *)
            match try_user_printer tm with
            | Success _ -> ()
            | Error _ -> 
                match dest_numeral tm with
                | Success tm -> pp_print_string fmt (string_of_num tm)
                | Error _ -> 
                    match dest_list tm with
                    | Success tms ->
                         try 
                             if fst(Choice.get <| dest_type(hd(snd(Choice.get <| dest_type(Choice.get <| type_of tm))))) <> "char" then fail()
                             else 
                                 let ccs = map (String.make 1 << Char.chr << code_of_term) tms
                                 let s = "\"" + String.escaped(implode ccs) + "\""
                                 pp_print_string fmt s
                         with
                         | Failure _ -> 
                             pp_print_string fmt "["
                             print_term_sequence "; " 0 tms
                             pp_print_string fmt "]"
                    | Error _ -> 
                        if is_gabs tm then print_binder prec tm
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
                                            if is_const oth && fst(Choice.get <| dest_const oth) = "EMPTY" then 
                                                (pp_print_string fmt "{"
                                                 print_term_sequence ", " 14 mems
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
                                                    print_term 0 fabs
                                                    pp_print_string fmt " | "
                                                    (let fvs = frees fabs
                                                     let bvs = frees babs
                                                     if not(!print_unambiguous_comprehensions) 
                                                        && set_eq evs (if (length fvs <= 1 || bvs = []) then fvs
                                                                       else intersect fvs bvs)
                                                     then ()
                                                     else 
                                                         (print_term_sequence "," 14 evs
                                                          pp_print_string fmt " | "))
                                                    print_term 0 babs
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
                                                 print_term 0 (Choice.get <| mk_eq(hd eqs))
                                                 do_list (fun (v, t) -> 
                                                         pp_print_break fmt 1 0
                                                         pp_print_string fmt "and "
                                                         print_term 0 (Choice.get <| mk_eq(v, t))) (tl eqs)
                                                 pp_print_string fmt " in"
                                                 pp_print_break fmt 1 0
                                                 print_term 0 bod
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
                                                             print_term 0 (hd args)
                                                             pp_print_string fmt " with"
                                                             pp_print_break fmt 1 2
                                                             print_clauses cls
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
                                                                 print_clauses cls
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
                                                                 print_term 0 (hd args)
                                                                 pp_print_break fmt 0 0
                                                                 pp_print_string fmt " then "
                                                                 print_term 0 (hd(tl args))
                                                                 pp_print_break fmt 0 0
                                                                 pp_print_string fmt " else "
                                                                 print_term 0 (hd(tl(tl args)))
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
                                                                 print_term 999 (hd args)
                                                                 if prec = 1000 then pp_print_string fmt ")"
                                                                 else ())
                                                            elif parses_as_binder s && length args = 1 
                                                                 && is_gabs(hd args) then print_binder prec tm
                                                            elif Option.isSome <| get_infix_status s && length args = 2 then 
                                                                let bargs = 
                                                                    if ARIGHT s then 
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
                                                                 print_term newprec (hd bargs)
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
                                                                         print_term newprec x) (tl bargs)
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
                                                                 print_term 999 l
                                                                 // TODO: this converted form is a bit non-sense
                                                                 match dest_const l with
                                                                 | Success(s, _) -> 
                                                                         mem s ["real_of_num"; "int_of_num"] |> ignore
                                                                 | Error _ -> pp_print_space fmt ()
                                                                 print_term 1000 r
                                                                 if prec = 1000 then pp_print_string fmt ")"
                                                                 else ()
                                                                 pp_close_box fmt ())

        and print_term_sequence sep prec tms = 
            if tms = [] then ()
            else 
                (print_term prec (hd tms)
                 let ttms = tl tms
                 if ttms = [] then ()
                 else 
                     (pp_print_string fmt sep
                      print_term_sequence sep prec ttms))

        and print_binder prec tm = 
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
              else 
                  (pp_open_hvbox fmt 5
                   pp_print_string fmt "("))
             pp_print_string fmt s
             (if isalnum s then pp_print_string fmt " "
              else ())
             do_list (fun (b, x) -> 
                     (if b then pp_print_string fmt "("
                      else ())
                     print_term 0 x
                     (if b then pp_print_string fmt ")"
                      else ())
                     pp_print_string fmt " ") (butlast vs)
             (if fst(last vs) then pp_print_string fmt "("
              else ())
             print_term 0 (snd(last vs))
             (if fst(last vs) then pp_print_string fmt ")"
              else ())
             pp_print_string fmt "."
             (if length vs = 1 then pp_print_string fmt " "
              else pp_print_space fmt ())
             print_term 0 bod
             (if prec = 0 then ()
              else pp_print_string fmt ")")
             pp_close_box fmt ())

        and print_clauses cls = 
            match cls with
            | [c] -> print_clause c
            | c :: cs -> 
                (print_clause c
                 pp_print_break fmt 1 0
                 pp_print_string fmt "| "
                 print_clauses cs)
            | _ -> failwith "print_clauses: Unhandled case."

        and print_clause cl = 
            match cl with
            | [p; g; r] -> 
                (print_term 1 p
                 pp_print_string fmt " when "
                 print_term 1 g
                 pp_print_string fmt " -> "
                 print_term 1 r)
            | [p; r] -> 
                (print_term 1 p
                 pp_print_string fmt " -> "
                 print_term 1 r)
            | _ -> failwith "print_clause: Unhandled case."

        fun tm ->
            try
                print_term 0 tm
            with Failure s ->
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
    (if not(asl = []) then 
         (if !print_all_thm then 
              (pp_print_term fmt (hd asl)
               do_list (fun x -> 
                       pp_print_string fmt ","
                       pp_print_space fmt ()
                       pp_print_term fmt x) (tl asl))
          else pp_print_string fmt "..."
          pp_print_space fmt ())
     else ()
     pp_open_hbox fmt ()
     pp_print_string fmt "|- "
     pp_print_term fmt tm
     pp_close_box fmt ())

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
    let rec output s m n = sbuff := (!sbuff) + (String.sub s m n)
    let flush() = ()
    let fmt = make_formatter output flush
    ignore(pp_set_max_boxes fmt 100)
    fun i -> 
        ignore(printer fmt i)
        ignore(pp_print_flush fmt ())
        let s = !sbuff
        sbuff := ""
        s

/// Converts a HOL type to a string representation.
let string_of_type = print_to_string pp_print_type

/// Converts a HOL term to a string representation.
let string_of_term = print_to_string pp_print_term

/// Converts a HOL theorem to a string representation.
let string_of_thm = print_to_string pp_print_thm

(* ------------------------------------------------------------------------- *)
(* Install all the printers.                                                 *)
(* ------------------------------------------------------------------------- *)

#if INTERACTIVE
fsi.AddPrinter string_of_type
fsi.AddPrinter string_of_term
fsi.AddPrinter string_of_thm
#endif
