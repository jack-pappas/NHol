(*

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

#I "./../packages"

#r "FSharp.Compatibility.OCaml.0.1.10/lib/net40/FSharp.Compatibility.OCaml.dll"
#r "FSharp.Compatibility.OCaml.Format.0.1.10/lib/net40/FSharp.Compatibility.OCaml.Format.dll"
#r "FSharp.Compatibility.OCaml.System.0.1.10/lib/net40/FSharp.Compatibility.OCaml.System.dll"
#r "ExtCore.0.8.29/lib/net40/ExtCore.dll"

// Disable "Incomplete pattern matches on this expression." warnings.
// Some of these are true warnings, but should be fixed in the code.
// No sense in seeing these warnings when using F# interactive.
#nowarn "25"

// Disable "This and other recursive references to the object(s) being defined will be checked
// for initialization-soundness at runtime through the use of a delayed reference. 
// This is because you are defining one or more recursive objects, rather than recursive functions."
#nowarn "40"

// Disable "Uppercase variable identifiers should not generally be used in patterns, and may indicate a misspelt pattern name."
#nowarn "49"

// Disable ML compatibility warnings
#nowarn "62"

open FSharp.Compatibility.OCaml;;
open FSharp.Compatibility.OCaml.Num;;

(*

Gc.set { (Gc.get()) with Gc.stack_limit = 16777216 }

(* ------------------------------------------------------------------------- *)
(* Make sure user interrupts generate an exception, not kill the process.    *)
(* ------------------------------------------------------------------------- *)

Sys.catch_break true

(* ------------------------------------------------------------------------- *)
(* Set up a quotation expander for the `...` quotes.                         *)
(* This includes the case `;...` to support miz3, even if that isn't loaded. *)
(* ------------------------------------------------------------------------- *)

let quotexpander s = 
    if s = "" then failwith "Empty quotation"
    else 
        let c = String.sub s 0 1
        if c = ":" then "parse_type \"" + (String.escaped(String.sub s 1 (String.length s - 1))) + "\""
        elif c = ";" then "parse_qproof \"" + (String.escaped s) + "\""
        else "parse_term \"" + (String.escaped s) + "\""

Quotation.add "tot" (Quotation.ExStr(fun x -> quotexpander))

(* ------------------------------------------------------------------------- *)
(* Modify the lexical analysis of uppercase identifiers.                     *)
(* ------------------------------------------------------------------------- *)

set_jrh_lexer

(* ------------------------------------------------------------------------- *)
(* Load in the bignum library and set up printing in the toplevel.           *)
(* ------------------------------------------------------------------------- *)

#load "nums.cma"

include Num

let print_num n = 
    Format.open_hbox()
    Format.print_string(string_of_num n)
    Format.close_box()

fsi.AddPrinter print_num

*)
