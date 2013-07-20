(*

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

// Change from package to NHol solution. Not NHol project.
#I @"./../../NHol"
#r @"./NHol/bin/Debug/NLog.dll"     // Use part of directory in name to help VS Intellisense.

// Configure and intialize NLog for logging

let configureNLog () =
  let projectPath = __SOURCE_DIRECTORY__
  let configPath = projectPath + @"\NLog.config"   // Read NLog.config from NHol project directory not NHol solution directory.
  printfn "NLog.config path: %s" configPath
  let xmlConfig = new NLog.Config.XmlLoggingConfiguration(configPath)
  NLog.LogManager.Configuration <- xmlConfig

let configureNLogPrgramatically () =
  let config = new NLog.Config.LoggingConfiguration()
  let fileTarget = new NLog.Targets.FileTarget()
  let projectPath = __SOURCE_DIRECTORY__
  let filePath = projectPath + @"\NHol_Log.txt"          // Log to file named NHol_Log.txt in NHol project directory, not NHol solution directory.
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
  let out = "NLog configuration:\n"
  let out = Seq.fold (fun out target -> out + (sprintf "%A\n" target)) out targets
  let rules = NLog.LogManager.Configuration.LoggingRules
  let out = Seq.fold (fun out rule -> out + (sprintf "%A\n" rule)) out rules
  out

let printNLogConfig () = 
  Printf.printfn "%s" (NLogConfigToString ())

configureNLog ()

// Setup logger
let logger = NLog.LogManager.GetLogger("file")
logger.Trace("NLog message from init.fsx")