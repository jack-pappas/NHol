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
    open NLog.Layouts
    open NLog.Targets


    /// <summary>Configures NLog by loading an NLog configuration file (NLog.config).</summary>
    /// <returns><c>true</c> if the configuration file was loaded successfully; otherwise, <c>false</c>.</returns>
    let configureNLog () =
        // If you copy or move this be sure to verify directory path is correct
        // because __SOURCE_DIRECTORY__ may change.
        let configFilename =
            let configRelativeFilename =
                Path.Combine (__SOURCE_DIRECTORY__, "NLog.config")

            // Remove .\..\ from path
            Path.GetFullPath configRelativeFilename

        if not <| File.Exists configFilename then
#if INTERACTIVE
            // TODO: Should we fail here (with "failwith") instead of just printing a message?
            // It is difficult to debug the code when running in F# Interactive, so the log is
            // fairly important; it may be better to be slightly less user-friendly up front to
            // make sure we can fix any more serious problems the user might run into later.
            //failwith "Error: Unable to find the NLog configuration file (NLog.config)."
            printfn "Warning: Unable to find the NLog configuration file (NLog.config)."
            printfn "The expected path to the file was: \"%s\"" configFilename
#else
            Debug.WriteLine (
                sprintf "Unable to find the NLog configuration file (NLog.config). \
                         The expected path to the file was: \"%s\"" configFilename, "NHol")
#endif
            // Return false to indicate the configuration wasn't loaded.
            false

        else
#if INTERACTIVE
            printfn "NLog config path: %s" configFilename
#else
            Debug.WriteLine (
                sprintf "NLog config path: %s" configFilename, "NHol")
#endif
            // Load the configuration from the configuration file.
            LogManager.Configuration <-
                Config.XmlLoggingConfiguration configFilename
            true

    (* NOTE :   How to set the Layout property in F#.

                If you look at C# examples of setting the layout property it will look like:
                    fileTarget.Layout = "${time} ${message}"
                which in F# would be:
                    fileTarget.Layout <- "${time} ${message}"

                This does not work in F#; you will get a compiler error like:
                    The type 'string' is not compatible with the type 'NLog.Layouts.Layout'

                To remedy this, pass the string to Layouts.Layout.FromString like this:
                    fileTarget.Layout <- Layouts.Layout.FromString "${time} ${callsite} ${level} ${message}"
    *)

    (* NOTE :   __SOURCE_DIRECTORY__ can cause problems if you don't understand how it works.
    
                If used from F# Interactive window in VS you will get something like
                    C:\Users\Eric.Windows7Ult\AppData\Local\Temp
    
                If sent to F# Interactive window in VS from fsx script you will get the
                directory the where the fsx script is located.
    
                If used in fsi.exe, running fsi.exe from a command prompt, you will get
                the directory where fsi.exe is located.
    
                If fsi.exe is started from a Windows Explorer search, you will get
                    C:\Windows\system32
    
                Since we are using __SOURCE_DIRECTORY__ to locate a config file then depending on where
                __SOURCE_DIRECTORY__ is located, or how fsi.exe is started, the value returned can change.
     
                So if you move a file or reaname a file or directory in the path or copy a function
                with __SOURCE_DIRECTORY__ in it,  don't be surpised if the function fails related to
                the __SOURCE_DIRECTORY__ value changing.
    *)

    //
    let [<Literal>] private standardLayout = "${time} ${pad: padding=-50 :inner=${callsite}} ${level} ${message}"
    //
    let [<Literal>] private sessionLogFilename = "NHol.Session.log"

    //
    let private createDefaultNLogConfig () =
        /// The logging configuration object.
        let config = Config.LoggingConfiguration ()

        do
            // Log to file
            let sessionFileTarget =
                new FileTarget (
                    Name = "SessionLogFile",
                    FileName = Layout.FromString (Path.Combine (__SOURCE_DIRECTORY__, @"\..\", sessionLogFilename)),
                    Layout = Layout.FromString standardLayout,
                    AutoFlush = true)

            config.AddTarget ("SessionLogFile", sessionFileTarget)
            Config.LoggingRule ("*", LogLevel.Debug, sessionFileTarget)
            |> config.LoggingRules.Add

        do
            // Log to console
            let consoleTarget =
                new ColoredConsoleTarget (
                    Name = "UserConsole",
                    Layout = Layout.FromString standardLayout,
                    UseDefaultRowHighlightingRules = true)

            config.AddTarget ("UserConsole", consoleTarget)
            Config.LoggingRule ("*", LogLevel.Info, consoleTarget)
            |> config.LoggingRules.Add
    
        // Return the configuration object.
        config

    //
    let inline private toStringWithDefault defaultString (value : ^T) =
        if isNull value then defaultString
        else value.ToString ()

    //
    let private listToString (list : string list) =
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

    //
    let rec private processTargets acc targets =
        // TODO : Use 'sprintf' below for formatting strings.
        // Joining several (3+) strings should be done with the String.join/joins functions from ExtCore.
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
                processTargets acc tl
            | :? Targets.ConsoleTarget as consoleTarget ->
                let name = "name: " + target.Name
                let layout = "layout: " + toStringWithDefault "None" consoleTarget.Layout
                let header = "header: " + toStringWithDefault "None" consoleTarget.Header
                let footer = "footer: " + toStringWithDefault "None" consoleTarget.Footer
                let error = consoleTarget.Error.ToString()
                let acc = ("[" + name + ", " + layout + ", " + header + ", " + footer + ", " + error + "]") :: acc
                processTargets acc tl
            | :? Targets.TargetWithLayoutHeaderAndFooter as targetWithHeaders ->
                let name = "name: " + target.Name
                let layout = "layout: " + toStringWithDefault "None" targetWithHeaders.Layout
                let header = "header: " + toStringWithDefault "None" targetWithHeaders.Header
                let footer = "footer: " + toStringWithDefault "None" targetWithHeaders.Footer
                let acc = ("[" + name + ", " + layout + ", " + header + ", " + footer + "]") :: acc
                processTargets acc tl
            | :? Targets.TargetWithLayout as targetWithLayout ->
                let name = "name: " + target.Name
                let layout = "layout: " + toStringWithDefault "None" targetWithLayout.Layout
                let acc = ("[" + name + ", " + layout + "]") :: acc
                processTargets acc tl
            | _ ->
                let name = target.Name
                let acc = ("[" + name + "]") :: acc
                processTargets acc tl

    //
    let rec private processRules acc rules =
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
            processRules acc tl

    //
    let printNLogConfig () =
        let targetTextList =
            LogManager.Configuration.AllTargets
            |> Seq.toList
            |> processTargets []
            |> listToString
      
        let ruleTextList =
            LogManager.Configuration.LoggingRules
            |> Seq.toList
            |> processRules []
            |> listToString
      
#if INTERACTIVE
        printfn "targets: %s" targetTextList
        printfn "rules: %s" ruleTextList
#else
        Debug.WriteLine (
            sprintf "targets: %A" targetTextList)
        Debug.WriteLine (
            sprintf "rules: %A" ruleTextList)
#endif

    /// Configures NLog.
    let configure () =
        if not <| configureNLog () then
#if INTERACTIVE
            printfn "Configuring NLog programmatically."
#else
            Debug.WriteLine ("Configuring NLog programmatically.", "NHol")
#endif
            LogManager.Configuration <- createDefaultNLogConfig ()

    //
    let alignedNameValue (name : string) (value : string) : string =
        // OPTIMIZE : Use String.PadLeft (or .PadRight) here instead of String.replicate.
        // TODO : This function will currently crash if name.Length > 15 -- this should be handled
        // in a better way; either add a precondition to check the string length, or modify the implementation
        // so it handles strings of any length (or a combination of these).
        let nameFieldWidth = 15
        let padding = String.replicate (nameFieldWidth - name.Length) " "
#if INTERACTIVE
        sprintf "%s: %s %s\n" name padding value
#else
        Printf.sprintf "%s: %s %s" name padding value
#endif

    /// Pause for user to press any key to resume.
    /// Optionally displays a message to the user.
    let pause msg =
        // TODO: Figure out if console attached to call correct routine.
        // Perhaps use the System.Environment.UserInteractive to determine this.
#if USE
        // Note: We have a console so ReadKey will work.
        if not <| String.isEmpty msg then
            printfn "%s" msg
            printfn "%s" "Press any key to continue."
            System.Console.ReadKey() |> ignore
#else
#if INTERACTIVE
        // Note: We don't have a console so ReadKey will not work.
        if not <| String.isEmpty msg then
            printfn "%s" msg
            printfn "%s" "Press Enter to continue."
            printfn "Note: Cursor must be on next line for this to work."
            System.Console.ReadLine () |> ignore
#else
        ()  // Don't pause if running as a program.
#endif
#endif


/// Logging-related helper functions.
/// This module also provides access to the process-global logger instance.
[<AutoOpen>]
module Logger =
    open Microsoft.FSharp.Core.Printf
    open NLog

    // When this module is opened, configure the logger.
    do
        Logging.configure ()

    /// The standard logger for NHol.
    let logger =
        // NOTE : This doesn't "get" a logger with the specified name, it actually creates one.
        LogManager.GetLogger "NHolSession"

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

    //
    let logEntryExit (functionName : string) (body : unit -> 'T) =
        // Preconditions
        checkNonNull "functionName" functionName
        if String.isEmpty functionName then
            invalidArg "functionName" "The function name is empty."

        logger.Trace ("Entering {0}.", functionName)
        
        // TODO : Should we wrap this in a try/with (where the 'with' reraises the exn) so we can
        // provide a better exit message in case the function raises an exception?
        let result = body ()
        logger.Trace ("Exiting {0}.", functionName)
        result

    //
    let logEntryExitProtected (functionName : string) (body : unit -> Choice<'T, 'Error>) =
        // Preconditions
        checkNonNull "functionName" functionName
        if String.isEmpty functionName then
            invalidArg "functionName" "The function name is empty."

        logger.Trace ("Entering {0}.", functionName)
        
        let result = body ()
        match result with
        | Choice1Of2 _ ->
            logger.Trace ("Exiting {0}, returning a result value.", functionName)
        | Choice2Of2 _ ->
            logger.Trace ("Exiting {0}, returning an error value.", functionName)
        result

