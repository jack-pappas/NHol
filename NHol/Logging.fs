(*

Copyright 2013 Jack Pappas, Anh-Dung Phan, Eric Taucher, Domenico Masini

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

[<AutoOpen>]
module NHol.Logging

#endif

// Log support functions
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Logging =
    open System.Diagnostics
    open System.IO
    open Microsoft.FSharp.Core.Printf
    open NLog

    //
    let configureNLog () =
        // If you copy or move this be sure to verify directory path is correct
        // because __SOURCE_DIRECTORY__ may change.
        let configPath =
            let projectPath = __SOURCE_DIRECTORY__ + ".\..\NHol"
            projectPath + @"\NLog.config"

        if not <| File.Exists configPath then
            // TODO : Print message about config path not being found, so it doesn't just fail silently.
            false
        else
            Debug.WriteLine (
                sprintf "NLog config path: %s" configPath, "Logging")
            LogManager.Configuration <-
                Config.XmlLoggingConfiguration (configPath)
            true

    // Note: How to set Layout property in F#
    // If you look at C# examples of setting the layout property it will look like
    // fileTarget.Layout = "${time} ${message}"
    // which in F# would be
    // fileTarget.Layout <- "${time} ${message}"
    // but this does not work with F# as you will get
    // The type 'string' is not compatible with the type 'NLog.Layouts.Layout'
    // To do this property you have to construct a SimpleLayout with the text as a parameter
    // then convert the SimpleLayout to a Layout before assiging.

    // Note: __SOURCE_DIRECTORY__ can cause problems if you don't understand
    // how it works.
    //
    // If used from F# Interactive window in VS you will get something like
    // C:\Users\Eric.Windows7Ult\AppData\Local\Temp
    //
    // If sent to F# Interactive window in VS from fsx script you will get the 
    // directory the where the fsx script is located.
    //
    // If used in fsi.exe, running fsi.exe from a command prompt, you will get
    // the directory where fsi.exe is located.
    //
    // If fsi.exe is started from a Windows Explorer search, you will get
    // C:\Windows\system32
    //
    // Since we are using __SOURCE_DIRECTORY__ to locate a config file 
    // then depending on where __SOURCE_DIRECTORY__ is located, or 
    // how fsi.exe is started, the value returned can change.
    // 
    // So if you move a file or reaname a file or directory in the path
    // or copy a function with __SOURCE_DIRECTORY__ in it, 
    // don't be surpised if the function fails related to the
    // __SOURCE_DIRECTORY__ value changing.

    let configureNLogProgramatically () =
        Debug.WriteLine (
            sprintf "configureNLogProgramatically called in NLogExample.fsx.", "Logging")

        LogManager.Configuration <-
            /// The logging configuration object.
            let config = Config.LoggingConfiguration()

            // Log to file
            // TODO : Should this value be bound using 'use' instead of 'let'?
            let fileTarget =
                let fileTarget = new Targets.FileTarget()
        
                fileTarget.Name <- "file"
                fileTarget.AutoFlush <- true
                fileTarget.FileName <-
                    let solutionPath = __SOURCE_DIRECTORY__  + @".\..\"
                    let filePath = solutionPath + @"NHol.run.Nlog.txt" 
                    new Layouts.SimpleLayout(filePath)
                fileTarget.Layout <-
                    Layouts.SimpleLayout "${time} ${callsite} ${level} ${message}"
                    :> Layouts.Layout

                fileTarget

            config.AddTarget ("file", fileTarget)
            Config.LoggingRule ("*", LogLevel.Debug, fileTarget)
            |> config.LoggingRules.Add

            // Log to console
            // TODO : Should this value be bound using 'use' instead of 'let'?
            let consoleTarget =
                let consoleTarget = new Targets.ConsoleTarget()
                consoleTarget.Name <- "console"
                consoleTarget.Layout <-
                    Layouts.SimpleLayout "${time} ${callsite} ${level} ${message}"
                    :> Layouts.Layout
                consoleTarget

            config.AddTarget ("console", consoleTarget)
            Config.LoggingRule ("*", LogLevel.Trace, consoleTarget)
            |> config.LoggingRules.Add
    
            // Return the configuration object.
            config

    let inline private toStringWithDefault defaultString (value : ^T) =
        if isNull value then defaultString
        else value.ToString ()

    let printNLogConfig () =
      // TODO : Use 'sprintf' below for formatting strings.
      // Joining several (3+) strings should be done with the String.join/joins functions from ExtCore.
      let rec processTargets targets acc =
        match targets with
        | [] ->
            List.rev acc
        | (target : Targets.Target) :: tl ->
          match target with
          | :? Targets.FileTarget as fileTarget ->
              let name = "name: " + target.Name
              let layout = "layout: " + toStringWithDefault "None" fileTarget.Layout
              let header = "header: " + toStringWithDefault "None" fileTarget.Header
              let footer = "footer: " + toStringWithDefault "None" fileTarget.Footer
              let autoFlush = "autoFlush: " + fileTarget.AutoFlush.ToString()
              let createDirs = "createDirs: " + fileTarget.CreateDirs.ToString()
              let encoding = "encoding: " + fileTarget.Encoding.ToString()
              let filename = "filename: " + fileTarget.FileName.ToString()
              let keepFileOpen = "keepFileOpen: " + fileTarget.KeepFileOpen.ToString()
              let lineEnding = "lineEnding: " + fileTarget.LineEnding.ToString()
              let acc = ("[" + name + ", " + layout + ", " + header + ", " + footer + ", " + autoFlush + ", " + createDirs + ", " + encoding + ", " + filename + ", " + keepFileOpen + ", " + lineEnding + "]") :: acc
              processTargets tl acc
          | :? Targets.ConsoleTarget as consoleTarget ->
              let name = "name: " + target.Name
              let layout = "layout: " + toStringWithDefault "None" consoleTarget.Layout
              let header = "header: " + toStringWithDefault "None" consoleTarget.Header
              let footer = "footer: " + toStringWithDefault "None" consoleTarget.Footer
              let error = consoleTarget.Error.ToString()
              let acc = ("[" + name + ", " + layout + ", " + header + ", " + footer + ", " + error + "]") :: acc
              processTargets tl acc
          | :? Targets.TargetWithLayoutHeaderAndFooter as targetWithHeaders ->
              let name = "name: " + target.Name
              let layout = "layout: " + toStringWithDefault "None" targetWithHeaders.Layout
              let header = "header: " + toStringWithDefault "None" targetWithHeaders.Header
              let footer = "footer: " + toStringWithDefault "None" targetWithHeaders.Footer
              let acc = ("[" + name + ", " + layout + ", " + header + ", " + footer + "]") :: acc
              processTargets tl acc
          | :? Targets.TargetWithLayout as targetWithLayout ->
              let name = "name: " + target.Name
              let layout = "layout: " + toStringWithDefault "None" targetWithLayout.Layout
              let acc = ("[" + name + ", " + layout + "]") :: acc
              processTargets tl acc
          | _ ->
              let name = target.Name
              let acc = ("[" + name + "]") :: acc
              processTargets tl acc

      let listToString (list : string list) =
          let rec processList list acc =
            match list with
            | [] -> "[" + acc + "]"
            | (item : string) :: tl ->
                match acc with
                | "" -> 
                    let acc = item
                    processList tl acc
                | _ -> 
                    let acc = acc + ", " + item
                    processList tl acc
        
          processList list ""

      let rec processRules rules acc =
        match rules with
        | [] -> List.rev acc
        | (rule : Config.LoggingRule) :: tl ->
            let name = "name: " + rule.LoggerNamePattern
            let levels = "levels: " + (rule.Levels 
                |> Seq.map (fun (level : LogLevel) -> level.Name)
                |> Seq.toList
                |> listToString)
            let targets = "targets: " + (rule.Targets 
                |> Seq.map (fun (target : Targets.Target) -> target.Name)
                |> Seq.toList
                |> listToString)
            let filters = "filters: " + (rule.Filters 
                |> Seq.map (fun (filter : Filters.Filter) -> filter.Action.ToString())
                |> Seq.toList
                |> listToString)
            let final = "final: " + rule.Final.ToString()
            let acc = ("[" + name + ", " + levels + ", " + targets + ", " + filters + ", " + final + "]") :: acc
            processRules tl acc
    
      let targets = LogManager.Configuration.AllTargets
      let targetList =  Seq.toList targets
      let targetTextList = processTargets targetList [] |> listToString

      let rules = LogManager.Configuration.LoggingRules
      let ruleList = Seq.toList rules
      let ruleTextList = processRules ruleList [] |> listToString
      
      Debug.WriteLine (
        sprintf "targets: %A" targetTextList)
      Debug.WriteLine (
        sprintf "rules: %A" ruleTextList)

    // Configure NLog
    let configure () =
        if not <| configureNLog () then
            Debug.WriteLine ("Configuring NLog programmatically.", "Logging")
            configureNLogProgramatically ()

    let alignedNameValue (name : string) (value : string) : string =
        let nameFieldWidth = 15
        let padding = String.replicate (nameFieldWidth - name.Length) " "
        Printf.sprintf "%s: %s %s" name padding value

    // Pause for user to press any key to resume.
    // Show optional message
    let pause msg =
        if not <| String.isEmpty (msg)
        then printfn "%s" msg
        printfn "%s" "Press any key to continue."
        System.Console.ReadKey() |> ignore

//
[<AutoOpen>]
module Logger =
    open Microsoft.FSharp.Core.Printf
    open NLog

    // When this module is opened, configure the logger.
    do
        Logging.configure ()

    /// The standard logger for NHol.
    let logger =
        LogManager.GetLogger "file"

    //
    let inline debugf fmt : 'T =
        ksprintf logger.Debug fmt

    //
    let inline tracef fmt : 'T =
        ksprintf logger.Trace fmt

    //
    let inline infof fmt : 'T =
        ksprintf logger.Info fmt

    //
    let inline warnf fmt : 'T =
        ksprintf logger.Warn fmt

    //
    let inline errorf fmt : 'T =
        ksprintf logger.Error fmt

    //
    let inline fatalf fmt : 'T =
        ksprintf logger.Fatal fmt
