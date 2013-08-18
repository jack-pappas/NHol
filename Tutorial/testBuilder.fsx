//#region "License"

(*

Copyright 2013 Eric Taucher

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

//#endregion

//#region "Source Directory"

// Note: This script is for assisting in creating test 
// by avoiding compile cycles before adding them as a NUnit test.

// Note: This script is in the tutorial directory, so 
// __SOURCE_DIRECTORY__ is NHol\Tutorial
printfn "%s" __SOURCE_DIRECTORY__;;

//#endregion 

//#region "Preprocessor Directives"

// To ensure we know the active preprocessor directives.

#if USE
// Use is used by Command prompt HOL Light for use with fsi.exe --use option.
// The use option comes from OCaml and F# Interactive should support it but doesn't.
// There are indications in the source code that they were working on it,
// but it was never enabled.
//
// Since we cannot use #use from F# Interactive we do it via the fsi.exe option.

printfn "defined USE";;
#endif

#if INTERACTIVE
// INTERACTIVE is a F# compiler directive that is defined with using F# Interactive or fsi.exe.

printfn "defined INTERACTIVE";;
#endif

#if COMPILED
// COMPILED is a F# compiler directive that is defined with using compiled F# code.

printfn "defined COMPILED";;
#endif

#if BUGGY
// If BUGGY directive is defined, an exception could be raised
// otherwise, we just ignore the choice value.

printfn "defined BUGGY";;
#endif

#if DEBUG
// TRACE is a .NET compiler directive that allows .NET debugging to be performed on the output.

printfn "defined DEBUG";;
#endif

#if TRACE
// TRACE is a .NET compiler directive that allows .NET trace statements to be compiled into the output.

printfn "defined TRACE";;
#endif

#if FSI_VER_2
// FSI_VER_2 needs to be set when using F# Interactive version 2.x that comes with Visual Studio 2010.
// Visual Studio 2012 comes with F# Interactive version 11.x.

printfn "defined FSI_VER2";;
#endif

#if CODE_COVERAGE
// Used for special cases when using code coverage i.e. dotCover does not do inline code.

printfn "defined CODE_COVERAGE";;
#endif

//System.Environment.CurrentDirectory;;
//System.Environment.UserDomainName;;
//System.Environment.UserName;;

//#endregion

//#region "References"

// Note: To use this with F# Interactive within Visual Studio 2010
// In Visual Studio menu: Tool -> Options -> F# Tools -> F# Interactive
// For F# Interactive Options add --define:FSI_VER_2
#if FSI_VER_2
#r @"./../packages/ExtCore.0.8.32/lib/net40/ExtCore.dll"
#r @"./../packages/NLog.2.0.1.2/lib/net40/NLog.dll"
//#r @"./../packages/NUnit.2.6.2/lib/nunit.framework.dll"
//#r @"./../packages/FsUnit.1.2.1.0/Lib/Net40/FsUnit.NUnit.dll"
#r @"./../packages/FSharp.Compatibility.OCaml.0.1.10/lib/net40/FSharp.Compatibility.OCaml.dll"
#r @"./../NHol.Tests/bin/Debug/NHol.Tests.dll"
#else
#I "./../packages"

#r @"ExtCore.0.8.32/lib/net40/ExtCore.dll"
#r @"NLog.2.0.1.2/lib/net40/NLog.dll"
//#r @"NUnit.2.6.2/lib/nunit.framework.dll"
//#r @"FsUnit.1.2.1.0/Lib/Net40/FsUnit.NUnit.dll"
#r @"FSharp.Compatibility.OCaml.0.1.10/lib/net40/FSharp.Compatibility.OCaml.dll"

#I "./../NHol.Tests"
#r @"bin/Debug/NHol.Tests.dll"
#endif

//#endregion

//open NUnit.Framework
//open FsUnit

open ExtCore
open FSharp.Compatibility.OCaml
open TestHelpers

#nowarn "62"

//#region "Logging"

#load "./../NHol/Logging.fs";;
open NHol.Logging;;

//Logging.printNLogConfig ();;
//
//logger.Trace("trace message");;
//
//logger.Info(Logging.alignedNameValue "Name" "Value");;

//#endregion

//#region "system"

#if FSI_VER_2
//#r "./../packages/FSharp.Compatibility.OCaml.0.1.10/lib/net40/FSharp.Compatibility.OCaml.dll"
#r "./../packages/FSharp.Compatibility.OCaml.Format.0.1.10/lib/net40/FSharp.Compatibility.OCaml.Format.dll"
#r "./../packages/FSharp.Compatibility.OCaml.System.0.1.10/lib/net40/FSharp.Compatibility.OCaml.System.dll"
#else
#I "./../packages"

//#r "FSharp.Compatibility.OCaml.0.1.10/lib/net40/FSharp.Compatibility.OCaml.dll"
#r "FSharp.Compatibility.OCaml.Format.0.1.10/lib/net40/FSharp.Compatibility.OCaml.Format.dll"
#r "FSharp.Compatibility.OCaml.System.0.1.10/lib/net40/FSharp.Compatibility.OCaml.System.dll"
#endif

#load "./../NHol/system.fs";;
open NHol.system;;

//#endregion

//#region "test access to libs"

let ExtCoreTest = ExtCore.Operators.swap (1, 2);;
logger.Trace("Entering testBuilder.fsx");;
let OCamlTest = FSharp.Compatibility.OCaml.Num.Num.Zero;;
let OCamlFormatTest = FSharp.Compatibility.OCaml.Format.print_string "Hi";;
let OCamlSystemTest = FSharp.Compatibility.OCaml.Sys.getcwd ();;

//#endregion

//#region "lib"

#load "./../NHol/lib.fs";;
open NHol.lib;;

let sum ((x : int), (y : int)) : int =
    x + y;;

let add1 = curry sum 1;;
add1 2;;

let sum2 = (fun ((x : int), (y : int)) -> x + y)

let add12 = curry sum2 1;;

add12 5;;




//#endregion
(*
//#region "fusion"

#load "./../NHol/fusion.fs";;
open NHol.fusion;;

types ();;

//#endregion

//#region "basics"

#load "./../NHol/basics.fs";;
open NHol.basics;;

let ty = Tyvar("a");;
genvar ty;;

dest_fun_ty;;


//#endregion

//#region "nets"

#load "./../NHol/nets.fs";;
open NHol.nets;;

// TODO: Make this work
enter [] ("Name", "Value") empty_net;;

//#endregion

//#region "printer"

#load "./../NHol/printer.fs";;
open NHol.printer;;

issep ";";;

//#endregion

//#region "preterm"

#load "./../NHol/preterm.fs";;
open NHol.preterm;;

pretype_of_type (Tyvar("a"));;

//#endregion

//#region "parser"

#load "./../NHol/parser.fs";;
open NHol.parser;;

some (fun item -> item = "1") ["1"; "+"; "2"];;

parse_term "x = y";;

parse_term "x";;

printfn "%A" (parse_term "x");;
printfn "%A" (parse_term "A /\ B");;
let temp = parse_term "x + y";;
printfn "%A" temp;;

//#endregion

//#region "equal"

#load "./../NHol/equal.fs";;
open NHol.equal;;

let tha = REFL (parse_term "x = y");;
SYM tha;;

//#endregion

//#region "bool"

#load "./../NHol/bool.fs";;
open NHol.bool;;

let c = parse_term "P /\ Q";;
let d = parse_term "A /\ B";;

mk_iff (c, d);;

//#endregion

//#region "drule"

#load "./../NHol/drule.fs";;
open NHol.drule;;

let e = REFL (parse_term "P = Q");;
let f = REFL (parse_term "A = B");;

MK_CONJ e f;;

//#endregion
*)