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

#load @".\ProofGUI1.fsx"

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
open FSharp.Compatibility.OCaml.Format;;

open ExtCore.Control;;
open ExtCore.Control.Collections;;

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
open NHol.ind_defs
open NHol.``class``
open NHol.trivia
open NHol.canon
open NHol.meson

BETA_RULE;;                 // forces equal module evaluation: maybe not needed
mk_iff;;                    // forces bool module evaluation
MK_CONJ;;                   // forces drule module evaluation
_FALSITY_;;                 // forces tactics module evaluation
ITAUT_TAC;;                 // forces itab module evaluation: maybe not needed
mk_rewrites;;               // forces simp module evaluation
EQ_REFL;;                   // forces theorems module evaluation
EXISTS_EQUATION;;           // forces ind_defs module evaluation
ETA_AX;;                    // forces class module evaluation
o_DEF;;                     // forces trivia module evaluation
CONJ_ACI_RULE;;             // forces canon module evaluation
ASM_MESON_TAC;;             // forces meson module evaluation

fsi.AddPrinter string_of_type;;
fsi.AddPrinter string_of_term;;
fsi.AddPrinter string_of_thm;;
fsi.AddPrinter string_of_justification;;
fsi.AddPrinter string_of_refinement;;
fsi.AddPrinter string_of_tactic;;
fsi.AddPrinter string_of_thm_tactic;;
fsi.AddPrinter string_of_thm_tactical;;
fsi.AddPrinter string_of_goal;;
fsi.AddPrinter string_of_goalstack;;
fsi.AddPrinter string_of_goalstate;;

open ProofGUI1

proofGUI()

// Start Snippet from https://github.com/xcthulhu/flyspeck/emacs/print-types.ml to get term types

let suppressed = 
    ref ["==>";"?";"!";"/\\";"\\/";",";"~";"APPEND";"CONS";"HD";"LAST";
     "NIL";"=";"real_lt";"real_gt";"real_le";"real_ge";"BIT0";"BIT1";"NUMERAL";
     "real_of_num";"_0";"_1";"real_div";"real_mul";"real_pow";"COND"];;

let suppress s = suppressed := s :: !suppressed;;

let unsuppress s = suppressed := List.filter ((!=) s) (!suppressed);;

let rec get_type_list tm = 
    match tm with       
        Var(s,t) -> if mem s !suppressed then [] else [(s,t)] 
        | Const(s,t) -> if mem s !suppressed then [] else [(s,t)] 
        | Comb (t1,t2) -> get_type_list t1 @ get_type_list t2 
        | Abs (t1,t2) -> get_type_list t1 @ get_type_list t2;;

let print_atom_type : string * hol_type -> unit =
    fun (s,t) -> 
        (
            printfn "(\"%A\")" s;
            printfn "%A" t;
            printfn "%A)\n" ""
        );;

let setify_types tm = ((sort (<)) << setify << get_type_list) tm;;

let print_term_types = List.iter print_atom_type << setify_types;;

let print_thm_types tm = print_term_types (concl tm);;

let tm = (parse_term @"! t:A. P t ==> ? u:A. P u");;
let tys = setify_types tm;;
print_term_types tm;;

// End Snippet from https://github.com/xcthulhu/flyspeck/emacs/print-types.ml to get term types

///////***************************

g (parse_term @"! t:A. P t ==> ? u:A. P u");;
e STRIP_TAC;;
e STRIP_TAC;;
e (EXISTS_TAC (parse_term @"t:A"));;
e (ACCEPT_TAC (ASSUME (parse_term @"((P:A->bool) t)")));;




