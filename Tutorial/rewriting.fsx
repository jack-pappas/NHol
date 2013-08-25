(*

Copyright 2013 Domenico Masini

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
#r "ExtCore.0.8.33/lib/net40/ExtCore.dll"

#I "./../NHol"
#r @"bin/Debug/NHol.dll"

#nowarn "25"
#nowarn "40"
#nowarn "49"
#nowarn "62"

open FSharp.Compatibility.OCaml;;
open FSharp.Compatibility.OCaml.Num;;

open NHol
open NHol.lib
open NHol.fusion
open NHol.basics
open NHol.nets
open NHol.printer
open NHol.preterm
open NHol.parser
open NHol.equal
open NHol.bool
open NHol.drule
open NHol.tactics
open NHol.itab
open NHol.simp
open NHol.theorems

fsi.AddPrinter string_of_type;;
fsi.AddPrinter string_of_term;;
fsi.AddPrinter string_of_thm;;

BETA_RULE;;                 // forces equal module evaluation: maybe not needed
mk_iff;;                    // forces bool module evaluation
MK_CONJ;;                   // forces drule module evaluation

_FALSITY_;;                 // forces tactics module evaluation

// for some reason it seems that it is better to call this after the tactics module evaluation
fsi.AddPrinter string_of_justification;;
fsi.AddPrinter string_of_refinement;;
fsi.AddPrinter string_of_tactic;;
fsi.AddPrinter string_of_thm_tactic;;
fsi.AddPrinter string_of_thm_tactical;;
fsi.AddPrinter string_of_goal;;
fsi.AddPrinter string_of_goalstack;;
fsi.AddPrinter string_of_goalstate;;

ITAUT_TAC;;                 // forces itab module evaluation: maybe not needed
mk_rewrites;;               // forces simp module evaluation

let betaTh:Choice<thm0,exn> = 
    Choice1Of2 (Sequent ([], parse_term @"(\x:A. (f:A->B) x) (y:A) = (f:A->B) (y:A)"));;         // |- (\x. f x) y = f y

let t1 = REWR_CONV betaTh (parse_term @"(\x. t1) t2");;                         // this in OCaml would be enough to prove ABS_SIMP while here fails

// Trying manual instantiation

let manualInst:instantiation = 
    (
        [(1, parse_term @"f:E->C")], 
        [(parse_term @"\z:E. t1:C", parse_term @"f:E->C"); (parse_term @"t2:E", parse_term @"y:E")], 
        [(Tyvar "C", Tyvar "B"); (Tyvar "E", Tyvar "A")]
    );;

let newManualTh = INSTANTIATE manualInst betaTh;; // also this fails while in OCaml succeeds

// Another more simple test on INSTANTIATE function

let th1:Choice<thm0,exn> = 
    Choice1Of2 (Sequent ([], parse_term @"p /\ q"));;

let instns:instantiation = 
        Choice.get (term_match [] (parse_term @"p:bool") (parse_term @"~a:bool"))

let newTh = INSTANTIATE instns th1;; // this simple test succeeds

// Another test

let insts2:instantiation = Choice.get (term_match [] (parse_term @"(\x:A. (f:A->B) x) (y:A)") (parse_term @"(\z:E. t1:C) t2"))
let newManualTh2 = INSTANTIATE insts2 betaTh;; // also this fails while in OCaml succeeds



let tm = (lhs (parse_term @"(\x. f x) y = f y"))        // `(\x. f x) y`
let insts = term_match [] (parse_term @"(\x. f x) y") (parse_term @"(\x. t1) t2");;

open ExtCore.Control
open ExtCore.Control.Collections

choice {
    let! tm = (lhs (parse_term @"(\x. f x) y = f y")) 
    let fTm = parse_term "f:A->B"
    let absTm = parse_term @"\x. t1:A"
    let t2Tm = parse_term "t2:B"
    let yTm = parse_term "y:A"
    let ty374 = Tyvar "?374"
    let ty368 = Tyvar "?368"
    let ty375 = Tyvar "?375"
    let ty373 = Tyvar "?373"
    let insts = [(1, fTm)], [(absTm, fTm); (t2Tm, yTm)], [(ty374, ty368); (ty375, ty373)] // term_match [] tm (parse_term @"(\x. t1) t2")
//    return insts
    return INSTANTIATE insts betaTh
}


