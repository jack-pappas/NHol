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

#if INTERACTIVE

// Code here goes into init.fsx

#else

module NHol.system

let configureNLog () =
  printfn "entering configureNLog"
  let projectPath = __SOURCE_DIRECTORY__
  let configPath = projectPath + @"\NLog.config"
  printfn "NLog config path: %s" configPath
  let xmlConfig = new NLog.Config.XmlLoggingConfiguration(configPath)
  NLog.LogManager.Configuration <- xmlConfig

let configureNLogPrgramatically () =
  let config = new NLog.Config.LoggingConfiguration()
  let fileTarget = new NLog.Targets.FileTarget()
  let projectPath = __SOURCE_DIRECTORY__
  let filePath = projectPath + @"\log.txt"
  let layout = new NLog.Layouts.SimpleLayout(filePath)
  fileTarget.Name <- "file"
  fileTarget.FileName <- layout
  fileTarget.AutoFlush <- true
  config.AddTarget("file", fileTarget)
  let rule1 = new NLog.Config.LoggingRule("*",NLog.LogLevel.Trace,fileTarget)
  config.LoggingRules.Add(rule1)
  NLog.LogManager.Configuration <- config

let NLogConfigToString () = 
  let targets = NLog.LogManager.Configuration.AllTargets
  let out = ""
  let out = Seq.fold (fun out target -> out + (sprintf "%A\n" target)) out targets
  let rules = NLog.LogManager.Configuration.LoggingRules
  let out = Seq.fold (fun out rule -> out + (sprintf "%A\n" rule)) out rules
  out

let printNLogConfig () = 
  Printf.printfn "%s" (NLogConfigToString ())

configureNLog ()
printNLogConfig ()

// Setup logger
let logger = NLog.LogManager.GetLogger("file")

logger.Trace("NLog message from system.fs")

#endif

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


