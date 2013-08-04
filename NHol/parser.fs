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
/// Lexical analyzer, type and preterm parsers.
module NHol.parser

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
#endif

(* TODO :   Re-name operators and functions for parser-combinators (below) to the
            equivalents from fparsec:
                http://www.quanttec.com/fparsec/reference/primitives.html
            When the renaming is complete, we can attempt to simplify the parser
            implementation by transitioning the code below to actually use fparsec. *)

(* ------------------------------------------------------------------------- *)
(* Need to have this now for set enums, since "," isn't a reserved word.     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix(",", (14, "right"))

(* ------------------------------------------------------------------------- *)
(* Basic parser combinators.                                                 *)
(* ------------------------------------------------------------------------- *)

//
exception Noparse

/// Produce alternative composition of two parsers.
// NOTE : This is called (||) in the original hol-light code.
let (<|>) parser1 parser2 input = 
    try 
        parser1 input
    with
    | Noparse -> parser2 input

/// Sequentially compose two parsers.
// NOTE : This is called (++) in the original hol-light code.
let (.>>.) parser1 parser2 input = 
    let result1, rest1 = parser1 input
    let result2, rest2 = parser2 rest1
    (result1, result2), rest2

/// Parses zero or more successive items using given parser.
let rec many prs input = 
    try 
        let result, next = prs input
        let results, rest = many prs next
        (result :: results), rest
    with
    | Noparse -> [], input

/// Apply function to parser result.
// NOTE : This is called (>>) in the original hol-light code.
let (|>>) prs treatment input = 
    let result, rest = prs input
    treatment result, rest

/// Applies parser and fails if it raises Noparse.
let fix err prs input = 
    try 
        prs input
    with
    | Noparse -> failwith(err + " expected")

/// Parses a separated list of items.
let rec listof prs sep err =
    prs .>>. many(sep .>>. (fix err prs) |>> snd) |>> (fun (h, t) -> h :: t)

/// Trivial parser that parses nothing.
let nothing input = [], input

/// Parses a possibly empty separated list of items.
let elistof prs sep err =
    listof prs sep err <|> nothing

/// Parses iterated left-associated binary operator.
let leftbin prs sep cons err = 
    prs .>>. many(sep .>>. fix err prs) |>> (fun (x, opxs) -> 
        let ops, xs = unzip opxs
        itlist2 (fun op y x -> cons op x y) (rev ops) (rev xs) x)

/// Parses iterated right-associated binary operator.
let rightbin prs sep cons err = 
    prs .>>. many(sep .>>. fix err prs) |>> (fun (x, opxs) -> 
        if opxs = [] then x
        else 
            let ops, xs = unzip opxs
            itlist2 cons ops (x :: butlast xs) (last xs))

/// Attempts to parse, returning empty list of items in case of failure.
let possibly prs input = 
    try 
        let x, rest = prs input
        [x], rest
    with
    | Noparse -> [], input

/// Parses any single item satisfying a predicate.
let some p = 
    function 
    | [] -> raise Noparse
    | h :: t -> 
        if p h then h, t
        else raise Noparse

/// Parser that requires a specific item.
let a tok = some(fun item -> item = tok)

/// Parses at least a given number of successive items using given parser.
let rec atleast n prs i = 
    (if n <= 0 then many prs
     else (prs .>>. atleast (n - 1) prs) |>> (fun (h, t) -> h :: t)) i

/// Parser that checks emptiness of the input.
let finished input = 
    if input = [] then 0, input
    else failwith "Unparsed input"

(* ------------------------------------------------------------------------- *)
(* The basic lexical classes: identifiers, strings and reserved words.       *)
(* ------------------------------------------------------------------------- *)

type lexcode = 
    | Ident of string
    | Resword of string

(* ------------------------------------------------------------------------- *)
(* Lexical analyzer. Apart from some special bracket symbols, each           *)
(* identifier is made up of the longest string of alphanumerics or           *)
(* the longest string of symbolics.                                          *)
(* ------------------------------------------------------------------------- *)

reserve_words ["//"]

/// HOL Light comment token.
let comment_token = ref(Resword "//")

/// Lexically analyze an input string.
let lex = 
    let collect(h, t) = end_itlist (+) (h :: t)
    let reserve = 
        function 
        | (Ident n as tok) -> 
            if is_reserved_word n then Resword(n)
            else tok
        | t -> t
    let stringof p = atleast 1 p |>> end_itlist (+)
    let simple_ident = stringof(some isalnum) <|> stringof(some issymb)
    let undertail = stringof(a "_") .>>. possibly simple_ident |>> collect
    let ident = (undertail <|> simple_ident) .>>. many undertail |>> collect
    let septok = stringof(some issep)
    let escapecode i = 
        match i with
        | "\\" :: rst -> "\\", rst
        | "\"" :: rst -> "\"", rst
        | "\'" :: rst -> "\'", rst
        | "n" :: rst -> "\n", rst
        | "r" :: rst -> "\r", rst
        | "t" :: rst -> "\t", rst
        | "b" :: rst -> "\b", rst
        | " " :: rst -> " ", rst
        | "x" :: h :: l :: rst -> String.make 1 (Char.chr(int_of_string("0x" + h + l))), rst
        | a :: b :: c :: rst when forall isnum [a; b; c] -> String.make 1 (Char.chr(int_of_string(a + b + c))), rst
        | _ -> failwith "lex:unrecognized OCaml-style escape in string"
    let stringchar = some(fun i -> i <> "\\" && i <> "\"") <|> (a "\\" .>>. escapecode |>> snd)
    let string = a "\"" .>>. many stringchar .>>. a "\"" |>> (fun ((_, s), _) -> "\"" + implode s + "\"")
    let rawtoken = (string <|> some isbra <|> septok <|> ident) |>> (fun x -> Ident x)
    let simptoken = many(some isspace) .>>. rawtoken |>> (reserve << snd)
    let rec tokens i = 
        try 
            let (t, rst) = simptoken i
            if t = !comment_token then 
                (many(fun i -> 
                         if i <> [] && hd i <> "\n" then 1, tl i
                         else raise Noparse) .>>. tokens |>> snd) rst
            else 
                let toks, rst1 = tokens rst
                t :: toks, rst1
        with
        | Noparse -> [], i
    fst << (tokens .>>. many(some isspace) .>>. finished |>> (fst << fst))

(* ------------------------------------------------------------------------- *)
(* Parser for pretypes. Concrete syntax:                                     *)
(*                                                                           *)
(* TYPE        :: SUMTYPE -> TYPE                                            *)
(*              | SUMTYPE                                                    *)
(*                                                                           *)
(* SUMTYPE     :: PRODTYPE + SUMTYPE                                         *)
(*              | PRODTYPE                                                   *)
(*                                                                           *)
(* PRODTYPE    :: POWTYPE # PRODTYPE                                         *)
(*              | POWTYPE                                                    *)
(*                                                                           *)
(* POWTYPE     :: APPTYPE ^ POWTYPE                                          *)
(*              | APPTYPE                                                    *)
(*                                                                           *)
(* APPTYPE     :: ATOMICTYPES type-constructor  [Provided arity matches]     *)
(*              | ATOMICTYPES                   [Provided only 1 ATOMICTYPE] *)
(*                                                                           *)
(* ATOMICTYPES :: type-constructor              [Provided arity zero]        *)
(*              | type-variable                                              *)
(*              | ( TYPE )                                                   *)
(*              | ( TYPE LIST )                                              *)
(*                                                                           *)
(* TYPELIST    :: TYPE , TYPELIST                                            *)
(*              | TYPE                                                       *)
(*                                                                           *)
(* Two features make this different from previous HOL type syntax:           *)
(*                                                                           *)
(*  o Any identifier not in use as a type constant will be parsed as a       *)
(*    type variable; a ' is not needed and a * is not allowed.               *)
(*                                                                           *)
(*  o Antiquotation is not supported.                                        *)
(* ------------------------------------------------------------------------- *)

/// Parses a pretype.
let parse_pretype = 
    let btyop n n' x y = Ptycon(n, [x; y])
    let mk_apptype = 
        function 
        | [s], [] -> s
        | tys, [c] -> Ptycon(c, tys)
        | _ -> failwith "Bad type construction"
    let type_atom input = 
        match input with
        | (Ident s) :: rest -> 
            let result =
                try
                    assoc s (type_abbrevs())
                    |> Option.toChoiceWithError "find"
                    |> Choice.bind pretype_of_type
                    |> Choice.get
                with
                | Failure _ -> 
                    if (match get_type_arity s with
                        | Success 0 -> true
                        | _ -> false)
                    then Ptycon(s, [])
                    else Utv(s)
            result, rest
        | _ -> raise Noparse
    let type_constructor input = 
        match input with
        | (Ident s) :: rest -> 
            if (match get_type_arity s with
                | Success i -> i > 0
                | Error _ -> false)
            then s, rest
            else raise Noparse
        | _ -> raise Noparse
    let rec pretype i = rightbin sumtype (a(Resword "->")) (btyop "fun") "type" i
    and sumtype i = rightbin prodtype (a(Ident "+")) (btyop "sum") "type" i
    and prodtype i = rightbin carttype (a(Ident "#")) (btyop "prod") "type" i
    and carttype i = leftbin apptype (a(Ident "^")) (btyop "cart") "type" i
    and apptype i = (atomictypes .>>. ((type_constructor |>> (fun x -> [x])) <|> nothing) |>> mk_apptype) i
    and atomictypes i = 
        (((a(Resword "(")) .>>. typelist .>>. (a(Resword ")")) |>> (snd << fst)) <|> (type_atom |>> (fun x -> [x]))) i
    and typelist i = (listof pretype (a(Ident ",")) "type") i
    pretype

(* ------------------------------------------------------------------------- *)
(* Hook to allow installation of user parsers.                               *)
(* ------------------------------------------------------------------------- *)

// install_parser: Install a user parser.
// delete_parser: Uninstall a user parser.
// installed_parsers: List the user parsers currently installed.
// try_user_parser: Try all user parsing functions.
let install_parser, delete_parser, installed_parsers, try_user_parser = 
    let rec try_parsers ps i = 
        match ps with
        | [] -> raise Noparse
        | hd :: tl -> 
            try 
                (snd hd) i
            with
            | Noparse -> try_parsers tl i
    let parser_list = ref([] : (string * (lexcode list -> preterm * lexcode list)) list)
    (fun dat -> parser_list := dat :: (!parser_list)), 
    (fun key -> 
        match remove (fun (key', _) -> key = key') (!parser_list) with
        | Some (_, p) -> parser_list := p
        | None -> ()), 
    (fun () -> !parser_list), 
    (fun i -> try_parsers (!parser_list) i)

(* ------------------------------------------------------------------------- *)
(* Initial preterm parsing. This uses binder and precedence/associativity/   *)
(* prefix status to guide parsing and preterm construction, but treats all   *)
(* identifiers as variables.                                                 *)
(*                                                                           *)
(* PRETERM            :: APPL_PRETERM binop APPL_PRETERM                     *)
(*                     | APPL_PRETERM                                        *)
(*                                                                           *)
(* APPL_PRETERM       :: APPL_PRETERM : type                                 *)
(*                     | APPL_PRETERM BINDER_PRETERM                         *)
(*                     | BINDER_PRETERM                                      *)
(*                                                                           *)
(* BINDER_PRETERM     :: binder VARSTRUCT_PRETERMS . PRETERM                 *)
(*                     | let PRETERM and ... and PRETERM in PRETERM          *)
(*                     | ATOMIC_PRETERM                                      *)
(*                                                                           *)
(* VARSTRUCT_PRETERMS :: TYPED_PRETERM VARSTRUCT_PRETERMS                    *)
(*                     | TYPED_PRETERM                                       *)
(*                                                                           *)
(* TYPED_PRETERM      :: TYPED_PRETERM : type                                *)
(*                     | ATOMIC_PRETERM                                      *)
(*                                                                           *)
(* ATOMIC_PRETERM     :: ( PRETERM )                                         *)
(*                     | if PRETERM then PRETERM else PRETERM                *)
(*                     | [ PRETERM; .. ; PRETERM ]                           *)
(*                     | { PRETERM, .. , PRETERM }                           *)
(*                     | { PRETERM | PRETERM }                               *)
(*                     | identifier                                          *)
(*                                                                           *)
(* Note that arbitrary preterms are allowed as varstructs. This allows       *)
(* more general forms of matching and considerably regularizes the syntax.   *)
(* ------------------------------------------------------------------------- *)

/// Parses a preterm.
let parse_preterm =
  let rec pairwise r l =
    match l with
      [] -> true
    | h::t -> forall (r h) t && pairwise r t

  let rec pfrees ptm acc =
    match ptm with
      Varp(v,pty) ->
        if v = "" && pty = dpty then acc
        elif Choice.isResult <| get_const_type v || Choice.isResult <| num_of_string v || exists (fun (w,_) -> v = w) (!the_interface) then acc
        else insert ptm acc
    | Constp(_,_) -> acc
    | Combp(p1,p2) -> pfrees p1 (pfrees p2 acc)
    | Absp(p1,p2) -> subtract (pfrees p2 acc) (pfrees p1 [])
    | Typing(p,_) -> pfrees p acc

  let pdest_eq =
      function
      | (Combp(Combp(Varp(("="|"<=>"),_),l),r)) -> (l,r)
      | _ -> failwith "pdest_eq: Unhandled case."

  let pmk_let (letbindings,body) =
    let vars,tms = unzip (map pdest_eq letbindings)
    do warn(not (pairwise (fun s t -> intersect(pfrees s []) (pfrees t []) = []) vars)) "duplicate names on left of let-binding: latest is used"
    let lend = Combp(Varp("LET_END",dpty), body)
    let abs = itlist (fun v t -> Absp(v,t)) vars lend
    let labs = Combp(Varp("LET",dpty),abs)
    rev_itlist (fun x f -> Combp(f,x)) tms labs

  let pmk_vbinder(n,v,bod) =
    if n = "\\" then Absp(v,bod)
    else Combp(Varp(n,dpty),Absp(v,bod))

  let pmk_binder(n,vs,bod) = itlist (fun v b -> pmk_vbinder(n,v,b)) vs bod

  let pmk_set_enum ptms = itlist (fun x t -> Combp(Combp(Varp("INSERT",dpty),x),t)) ptms (Varp("EMPTY",dpty))

  let pgenvar =
    let gcounter = ref 0
    fun () ->
        let count = !gcounter
        gcounter := count + 1
        Varp("GEN%PVAR%"+(string count),dpty)

  let pmk_exists(v,ptm) = Combp(Varp("?",dpty),Absp(v,ptm))

  let pmk_list els = itlist (fun x y -> Combp(Combp(Varp("CONS",dpty),x),y)) els (Varp("NIL",dpty))

  let pmk_bool =
    let tt = Varp("T",dpty)
    let ff = Varp("F",dpty)
    fun b ->
        if b then tt else ff

  let pmk_char c =
    let lis = map (fun i -> pmk_bool((c / (1 <<< i)) % 2 = 1)) (0--7)
    itlist (fun x y -> Combp(y,x)) lis (Varp("ASCII",dpty))

  let pmk_string s =
    let ns = map (fun i -> Char.code(String.get s i)) (0--(String.length s - 1))
    pmk_list(map pmk_char ns)

  let pmk_setcompr (fabs,bvs,babs) =
    let v = pgenvar()
    let bod = itlist (curry pmk_exists) bvs (Combp(Combp(Combp(Varp("SETSPEC",dpty),v),babs),fabs))
    Combp(Varp("GSPEC",dpty),Absp(v,bod))

  let pmk_setabs (fabs,babs) =
    let evs =
      let fvs = pfrees fabs []
      let bvs = pfrees babs []
      if length fvs <= 1 || bvs = [] then fvs
      else intersect fvs bvs
    pmk_setcompr (fabs,evs,babs)

  let rec mk_precedence infxs prs inp =
    match infxs with
      (s,(p,at))::_ ->
          let fun1 lc x y =
              match lc with
              | (Ident op) -> Combp(Combp(Varp(op,dpty),x),y) 
              | _ -> failwith "mk_precedence.fun1: Unhandled case."
          let topins,rest = partition (fun (s',pat') -> pat' = (p,at)) infxs
          (if at = "right" then rightbin else leftbin)
           (mk_precedence rest prs)
            (end_itlist (<|>) (map (fun (s,_) -> a (Ident s)) topins)) 
             fun1 "term after binary operator" inp
    | _ -> prs inp

  let pmk_geq s t = Combp(Combp(Varp("GEQ",dpty),s),t)

  let pmk_pattern ((pat,guards),res) =
    let x = pgenvar()
    let y = pgenvar()
    let vs = pfrees pat []
    let bod =
     if guards = [] then
       Combp(Combp(Varp("_UNGUARDED_PATTERN",dpty),pmk_geq pat x), pmk_geq res y)
     else
       Combp(Combp(Combp(Varp("_GUARDED_PATTERN",dpty),pmk_geq pat x), hd guards), pmk_geq res y)
    Absp(x,Absp(y,itlist (curry pmk_exists) vs bod))

  let pretype = parse_pretype

  let rec string inp = 
      match inp with
      | Ident s :: rst when String.length s >= 2 && String.sub s 0 1 = "\"" && String.sub s (String.length s - 1) 1 = "\"" -> 
          String.sub s 1 (String.length s - 2), rst
      | _ -> raise Noparse
  
  and singleton1 x = [x]
  
  and lmk_ite(((((_, b), _), l), _), r) = Combp(Combp(Combp(Varp("COND", dpty), b), l), r)
  
  and lmk_typed = 
      function 
      | (p, []) -> p
      | (p, [ty]) -> Typing(p, ty)
      | _ -> fail()
  
  and lmk_let(((_, bnds), _), ptm) = pmk_let(bnds, ptm)
  
  and lmk_binder((((s, h), t), _), p) = pmk_binder(s, h :: t, p)
  
  and lmk_setenum(l, _) = pmk_set_enum l
  
  and lmk_setabs(((l, _), r), _) = pmk_setabs(l, r)
  
  and lmk_setcompr(((((f, _), vs), _), b), _) = pmk_setcompr(f, pfrees vs [], b)
  
  and lmk_decimal((_, l0), ropt) = 
      let l, r = 
          if ropt = [] then l0, "1"
          else 
              let r0 = hd ropt
              let n_l = Choice.get <| num_of_string l0
              let n_r = Choice.get <| num_of_string r0
              let n_d = power_num (Int 10) (Int(String.length r0))
              let n_n = n_l */ n_d +/ n_r
              string_of_num n_n, string_of_num n_d
      Combp(Combp(Varp("DECIMAL", dpty), Varp(l, dpty)), Varp(r, dpty))
  
  and lmk_univ((_, pty), _) = 
      Typing(Varp("UNIV", dpty), Ptycon("fun", [pty; Ptycon("bool", [])]))
  
  and any_identifier = 
      function 
      | ((Ident s) :: rest) -> s, rest
      | _ -> raise Noparse
  
  and identifier x = 
    match x with
    | ((Ident s) :: rest) -> 
          if Option.isSome <| get_infix_status s || is_prefix s || parses_as_binder s then raise Noparse
          else s, rest
    | _ -> raise Noparse
  
  and binder = 
      function 
      | ((Ident s) :: rest) -> 
          if parses_as_binder s then s, rest
          else raise Noparse
      | _ -> raise Noparse
  
  and pre_fix = 
      function 
      | ((Ident s) :: rest) -> 
          if is_prefix s then s, rest
          else raise Noparse
      | _ -> raise Noparse
  
  let rec preterm i = mk_precedence (infixes()) typed_appl_preterm i
  
  and nocommapreterm i = 
      let infs = filter (fun (s, _) -> s <> ",") (infixes())
      mk_precedence infs typed_appl_preterm i
  
  and typed_appl_preterm i = (appl_preterm .>>. possibly(a(Resword ":") .>>. pretype |>> snd) |>> lmk_typed) i
  
  and appl_preterm i = 
      (pre_fix .>>. appl_preterm |>> (fun (x, y) -> Combp(Varp(x, dpty), y)) <|> binder_preterm .>>. many binder_preterm 
       |>> (fun (h, t) -> itlist (fun x y -> Combp(y, x)) (rev t) h)) i
  
  and binder_preterm i = 
      (a(Resword "let") .>>. leftbin (preterm |>> singleton1) (a(Resword "and")) (K (@)) "binding" .>>. a(Resword "in") 
       .>>. preterm |>> lmk_let 
       <|> (binder .>>. typed_apreterm .>>. many typed_apreterm .>>. a(Resword ".") .>>. preterm |>> lmk_binder) 
       <|> atomic_preterm) i
  
  and typed_apreterm i = (atomic_preterm .>>. possibly(a(Resword ":") .>>. pretype |>> snd) |>> lmk_typed) i

  and atomic_preterm i =
    (try_user_parser
      <|> ((a (Resword "(") .>>. a (Resword ":")) .>>. pretype .>>. a (Resword ")") |>> lmk_univ)
      <|> (string |>> pmk_string)
      <|> ((a (Resword "(")) .>>. (any_identifier |>> (fun s -> Varp(s,dpty))) .>>. a (Resword ")") |>> (snd << fst))
      <|> ((a (Resword "(")) .>>. preterm .>>. a (Resword ")") |>> (snd << fst))
      <|> ((a (Resword "if")) .>>. preterm .>>. a (Resword "then") .>>. preterm .>>. a (Resword "else") .>>. preterm |>> lmk_ite)
      <|> ((a (Resword "[")) .>>. elistof preterm (a (Resword ";")) "term" .>>. a (Resword "]") |>> (pmk_list << snd << fst))
      <|> ((a (Resword "{")) .>>.
            (elistof nocommapreterm (a (Ident ",")) "term" .>>.  a (Resword "}") |>> lmk_setenum
              <|> preterm .>>. a (Resword "|") .>>. preterm .>>. a (Resword "}") |>> lmk_setabs
              <|> preterm .>>. a (Resword "|") .>>. preterm .>>. a (Resword "|") .>>. preterm .>>. a (Resword "}") |>> lmk_setcompr) |>> snd)
      <|> ((a (Resword "match")) .>>. preterm .>>. a (Resword "with") .>>. clauses |>> (fun (((_,e),_),c) -> Combp(Combp(Varp("_MATCH",dpty),e),c)))
      <|> ((a (Resword "function")) .>>. clauses |>> (fun (_,c) -> Combp(Varp("_FUNCTION",dpty),c)))
      <|> ((a (Ident "#")) .>>. identifier .>>. possibly (a (Resword ".") .>>. identifier |>> snd) |>> lmk_decimal)
      <|> (identifier |>> (fun s -> Varp(s,dpty)))) i

  and pattern i = (preterm .>>. possibly(a(Resword "when") .>>. preterm |>> snd)) i
  
  and clause i = ((pattern .>>. (a(Resword "->") .>>. preterm |>> snd)) |>> pmk_pattern) i
  
  and clauses i = 
      ((possibly(a(Resword "|")) .>>. listof clause (a(Resword "|")) "pattern-match clause" |>> snd) 
       |>> end_itlist(fun s t -> Combp(Combp(Varp("_SEQPATTERN", dpty), s), t))) i

  (function
    | [Ident s] -> Varp(s,dpty),[]
    | inp -> preterm inp)

(* ------------------------------------------------------------------------- *)
(* Type and term parsers.                                                    *)
(* ------------------------------------------------------------------------- *)

/// Parses a string into a HOL type.
let parse_type s =
//    printfn "parsing type %s" s 
    let pty, l = (parse_pretype << lex << explode) s
    //printfn "pty, l <-- %A, %A" pty l
    if l = [] then Choice.get <| type_of_pretype pty
    else failwith "Unparsed input following type"

let tryParseType s : Protected<_> =
    try
        Choice.result <| parse_type s
    with e ->
        Choice.nestedFailwith e "parse_type"

/// Parses a string into a HOL term.
let parse_term s = 
//    printfn "parsing term %s" s
    let ptm, l = (parse_preterm << lex << explode) s
    //printfn "l <-- %A" l
    if l = [] then (Choice.get << term_of_preterm << (Choice.get << retypecheck [])) ptm
    else failwith "Unparsed input following term"

let tryParseTerm s : Protected<_> =
    try
        Choice.result <| parse_term s
    with e ->
        Choice.nestedFailwith e "parse_term"


