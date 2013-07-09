(*

Copyright 2013 Jack Pappas, Anh-Dung Phan, Domenico D. D. Masini

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

#I "./../packages"

#r "FSharp.Compatibility.OCaml.0.1.10/lib/net40/FSharp.Compatibility.OCaml.dll"
#r "FSharp.Compatibility.OCaml.Format.0.1.10/lib/net40/FSharp.Compatibility.OCaml.Format.dll"
#r "FSharp.Compatibility.OCaml.System.0.1.10/lib/net40/FSharp.Compatibility.OCaml.System.dll"

#I "./../NHol"

// Disable "Incomplete pattern matches on this expression." warnings.
// Some of these are true warnings, but should be fixed in the code.
// No sense in seeing these warnings when using F# interactive.
#nowarn "25"

// Disable "Uppercase variable identifiers should not generally be used in patterns, and may indicate a misspelt pattern name."
#nowarn "49"

// Disable ML compatibility warnings
#nowarn "62"

(* ------------------------------------------------------------------------- *)  
(* Various tweaks to OCaml and general library functions.                    *)  
(* ------------------------------------------------------------------------- *)   
#load "system.fs"       (* Set up proper parsing and load bignums            *)   
#load "lib.fs"          (* Various useful general library functions          *)  
(* ------------------------------------------------------------------------- *)  
(* The logical core.                                                         *)   
(* ------------------------------------------------------------------------- *)  
#load "fusion.fs"    
(* ------------------------------------------------------------------------- *)  
(* Some extra support stuff needed outside the core.                         *)  
(* ------------------------------------------------------------------------- *)  
#load "basics.fs"       (* Additional syntax operations and other utilities  *)  
#load "nets.fs"         (* Term nets for fast matchability-based lookup      *)  
(* ------------------------------------------------------------------------- *)  
(* The interface.                                                            *)  
(* ------------------------------------------------------------------------- *)  
#load "printer.fs"      (* Crude prettyprinter                               *)  
#load "preterm.fs"      (* Preterms and their interconversion with terms     *)  
#load "parser.fs"       (* Lexer and parser                                  *)  
(* ------------------------------------------------------------------------- *)  
(* Higher level deductive system.                                            *)  
(* ------------------------------------------------------------------------- *)  
#load "equal.fs"        (* Basic equality reasoning and conversionals        *)  
#load "bool.fs"         (* Boolean theory and basic derived rules            *)  
#load "drule.fs"        (* Additional derived rules                          *)  
#load "tactics.fs"      (* Tactics, tacticals and goal stack                 *)  
#load "itab.fs"         (* Toy prover for intuitionistic logic               *)  
#load "simp.fs"         (* Basic rewriting and simplification tools.         *)  
#load "theorems.fs"     (* Additional theorems (mainly for quantifiers) etc. *)  
#load "ind_defs.fs"     (* Derived rules for inductive definitions           *)  
#load "class.fs"        (* Classical reasoning: Choice and Extensionality    *)  
#load "trivia.fs"       (* Some very basic theories, e.g. type ":1"          *)  
#load "canon.fs"        (* Tools for putting terms in canonical forms        *)  
#load "meson.fs"        (* First order automation: MESON (model elimination) *)  
#load "quot.fs"         (* Derived rules for defining quotient types         *)  
(* ------------------------------------------------------------------------- *)  
(* Mathematical theories and additional proof tools.                         *)  
(* ------------------------------------------------------------------------- *)  
//#load "pair.fs"         (* Theory of pairs                                   *)  
//#load "nums.fs"         (* Axiom of Infinity, definition of natural numbers  *)  
//#load "recursion.fs"    (* Tools for primitive recursion on inductive types  *)  
//#load "arith.fs"        (* Natural number arithmetic                         *)  
//#load "wf.fs"           (* Theory of wellfounded relations                   *)  
//#load "calc_num.fs"     (* Calculation with natural numbers                  *)  
//#load "normalizer.fs"   (* Polynomial normalizer for rings and semirings     *)  
//#load "grobner.fs"      (* Groebner basis procedure for most semirings.      *)  
//#load "ind_types.fs"    (* Tools for defining inductive types                *)  
//#load "lists.fs"        (* Theory of lists                                   *)  
//#load "realax.fs"       (* Definition of real numbers                        *)  
//#load "calc_int.fs"     (* Calculation with integer-valued reals             *)  
//#load "realarith.fs"    (* Universal linear real decision procedure          *)  
//#load "real.fs"         (* Derived properties of reals                       *)  
//#load "calc_rat.fs"     (* Calculation with rational-valued reals            *)  
//#load "int.fs"          (* Definition of integers                            *)  
//#load "sets.fs"         (* Basic set theory.                                 *)  
//#load "iterate.fs"      (* Iterated operations                               *)  
//#load "cart.fs"         (* Finite Cartesian products                         *)  
//#load "define.fs"       (* Support for general recursive definitions         *)  
//(* ------------------------------------------------------------------------- *)  
//(* The help system.                                                          *)  
//(* ------------------------------------------------------------------------- *)  
//#load "help.fs"         (* Online help using the entries in Help directory   *)  
//#load "database.fs"     (* List of name-theorem pairs for search system      *)  
