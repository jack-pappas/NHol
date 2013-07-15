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

// This was done as a quick check to find conversion problems realted to the functions parse_term and parse_type.
// It is by no means complete, but does identify problems that need attention.
// Currently this only works with F# Interactive in Visual Studio.
// To use just Ctrl-A to select all then Alt-Enter to send all lines to F# Interactive.
// Check the F# Interactive window for messages.

#if INTERACTIVE

#I @"./../NHol"

#r @"bin/Debug/FSharp.Compatibility.OCaml.dll"
#r @"bin/Debug/FSharp.Compatibility.OCaml.Format.dll"
#r @"bin/Debug/FSharp.Compatibility.OCaml.System.dll"

#r @"bin/Debug/NHol.dll"

#else

module NHol.util

#endif

open System.Text.RegularExpressions

/// Convert a path to a list of absolute file names.
// A path can be absolute or relative, a directory or file, or empty.
let getFiles (path : string) : string list =
    let toAbsolutePath path =
        if System.String.IsNullOrWhiteSpace(path)
        then __SOURCE_DIRECTORY__                                                            // empty path
        elif System.IO.Path.IsPathRooted path   
        then path                                                                            // absolute path
        else __SOURCE_DIRECTORY__ + System.IO.Path.DirectorySeparatorChar.ToString() + path  // relative path
    let toFileList absolutePath =
        if (System.IO.Directory.Exists absolutePath)
        then Array.toList (System.IO.Directory.GetFiles absolutePath)
        elif System.IO.File.Exists(absolutePath)
        then [ absolutePath ]
        else failwith ("path is not a directory or file: " + absolutePath)
    path
    |> toAbsolutePath 
    |> toFileList

let printGroup (g : Group) =
    printfn "Group Index:        %d" g.Index 
    printfn "Group Length:       %d" g.Length 
    printfn "Group Success:      %b" g.Success 
    printfn "Group Value length: %d" g.Value.Length
    printfn "Group Value:        '%s'" g.Value 
    printfn "Group Capute count: %d" g.Captures.Count

let printCapture (c : Capture) =
    printfn "Capture Index:        %d" c.Index 
    printfn "Capture Length:       %d" c.Length 
    printfn "Capture Value length: %d" c.Value.Length
    printfn "Capture Value:        '%s'" c.Value 

let printMatch (m : Match) =
    printfn "Match Index:        %d" m.Index 
    printfn "Match Length:       %d" m.Length 
    printfn "Match Success:      %b" m.Success
    printfn "Match Value length: %d" m.Value.Length
    printfn "Match Value:        '%s'" m.Value 
    printfn "Match Capute count: %d" m.Captures.Count
    Seq.iter printCapture (Seq.cast m.Captures )
    printfn "Match Groups count: %d" m.Groups.Count
    Seq.iter printGroup (Seq.cast m.Groups)
    printfn "-----------------------------------------"

/// Create a map with key as line number and value as line end offset from start of file.
let lineEndingMap (fileName : string) : Map<int, (int * int)> = 
    // Don't add more match patterns as that will throw the line count off.
    // i.e. 2 match patterns will return 2x matches which will create 2x entries for line numbers 
    // and thus be incorrect.
    // Don't match \r|\n|\r\n or \r\n|\r|\n as this will match twice for \r\n
    let pattern = @"(?<linebreak>(\r?\n))" 
    let regex = new Regex(pattern, RegexOptions.Multiline)
    let getMatches fileName pattern =
        let fileText = (System.IO.File.ReadAllText fileName)
        regex.Matches(fileText)
        |> Seq.cast 
        |> Seq.toList 
    let rec processMatchList lineNumber start acc matches=
        match matches with
        | (hd : Match) :: tl ->
            let lineEndOffset = hd.Captures.[0].Index
            let acc = (lineNumber, (start, lineEndOffset)) :: acc
            let start = lineEndOffset + hd.Length 
            processMatchList (lineNumber + 1) start acc tl 
        | [] -> List.rev  acc
    getMatches fileName pattern
    |> processMatchList 1 0 [(0, (0, 0))] 
    |> Map.ofList

/// Given an offset in a file return the line number, start offset, end offset.
// Note: This processes the map sequentially. 
// Could probably be enhanced using a differnt data structure
// or using a binary search algorithm.
let lineNumberLookup (lineNumberMap : Map<int, (int * int)>) (offset : int) : (int * int * int) =
    let rec findLine offset checkLineNumber =
        match Map.tryFind checkLineNumber lineNumberMap with
        | Some(lineStartOffset, lineEndOffset) ->
            if offset > lineEndOffset
            then findLine offset (checkLineNumber + 1)
            else 
                (checkLineNumber, lineStartOffset, lineEndOffset)
        | None -> (0, 0, 0)
    findLine offset 1

/// Returns tuple of (filename, linenumber, Match) for all matches against all filesnames for all patterns.
let getMatches (filenames : string list) (patterns : string list) : (string * int * int * Match) list =                
    let rec processFiles (pattern : string) (filenames : string list) acc =
        match filenames with
        | fileName :: tl ->
            let lineEndings = lineEndingMap fileName
            let fileText = (System.IO.File.ReadAllText fileName)
            let regex = new Regex(pattern, RegexOptions.Multiline)
            let matches = regex.Matches(fileText)
            let matchesList = matches |> Seq.cast |> Seq.toList
            let rec addInfo list (acc : (string * int * int * Match) list) =
                match list with
                | (hd : Match) :: tl ->
                    let offsetFromFileStart = (hd.Captures.[0].Index)
                    let (lineNumber, lineStartOffset, lineEndOffset) = lineNumberLookup lineEndings offsetFromFileStart
                    let offsetFromLineStart = offsetFromFileStart - lineStartOffset
                    addInfo tl ((fileName, lineNumber, offsetFromLineStart, hd) :: acc)
                | [] -> acc
            let newItems = addInfo matchesList []
            processFiles pattern tl (acc @ (List.rev newItems))
        | [] -> acc
    let rec processPatterns patterns filenames acc =
        match patterns with
        | hd :: tl ->
            let acc = processFiles hd filenames acc
            processPatterns tl filenames acc
        | [] -> acc
    processPatterns patterns filenames []

/// Prints the list of filename linenumber message and match string.
let printInfo (info : (string * int * int * Match * string * string) list) =
    let printMatchCollection (item : (string * int * int * Match * string * string)) =
        let (fileName, lineNumber, offset, regexMatch, matchString, msg) = item
        printfn @"%s(%d,%d): %s ""%s""" fileName lineNumber offset msg matchString 
    let rec printMatchInfoList (list : (string * int * int * Match * string * string) list) =
        match list with
        | hd :: tl -> 
            printMatchCollection hd
            printMatchInfoList tl
        | [] -> ()
    printMatchInfoList info

/// Adds a message to the list if there is no @ before the string for a parse_term or parse_type.
let atSignCondition (item : (string * int * int * Match)) acc : (string * int * int * Match * string * string) list =
    let (fileName, lineNumber, offset, regexMatch) = item
    let atSignString = regexMatch.Groups.["atSign"].Value
    let atStringCondition = not (atSignString.Contains("@"))
    if atStringCondition 
    then 
        let parseString = regexMatch.Groups.["parseString"].Value
        let msg = "Missing @ before string."
        (fileName, lineNumber, offset, regexMatch, parseString, msg) :: acc
    else acc
    
/// Adds a message to the list if the substring occurs in the string for a parse_term or parse_type.
let substringFoundCondtion (item : (string * int * int * Match)) (substring : string) acc : (string * int * int * Match * string * string) list =
    let (fileName, lineNumber, offset, regexMatch) = item
    let parseString = regexMatch.Groups.["parseString"].Value
    let parseStringCondition = parseString.Contains(substring)
    if  parseStringCondition 
    then
        let msg = "String contains: " + substring
        (fileName, lineNumber, offset, regexMatch, parseString, msg) :: acc
    else acc
    
/// Adds a message to the list if "|>" occurs in the string for a parse_term or parse_type.
let invalidTextCondition (item : (string * int * int * Match)) acc : (string * int * int * Match * string * string) list =
    substringFoundCondtion (item : (string * int * int * Match)) "|>" acc

/// Adds a message to the list if linebreak occurs in the string for a parse_term or parse_type.
let containsLinebreakCondition (item : (string * int * int * Match)) acc : (string * int * int * Match * string * string) list =
    let substring = "\n"
    let (fileName, lineNumber, offset, regexMatch) = item
    let parseString = regexMatch.Groups.["parseString"].Value
    let parseStringCondition = parseString.Contains(substring)
    if  parseStringCondition 
    then
        let msg = "String contains line break: " + substring
        (fileName, lineNumber, offset, regexMatch, parseString, msg) :: acc
    else acc
    
/// Adds a message to the list if a parsing error occurs for a parse_term or parse_type.
let parsingErrorCondition (item : (string * int * int * Match)) acc : (string * int * int * Match * string * string) list =
    let (fileName, lineNumber, offset, regexMatch) = item
    let parseFunction = regexMatch.Groups.["parse_function"].Value
    let parseString = regexMatch.Groups.["parseString"].Value
    try
        if parseFunction = "parse_term"
        then NHol.parser.parse_term parseString |> ignore
        elif parseFunction = "parse_type"
        then NHol.parser.parse_type parseString |> ignore
        else failwith ("Unknow parse function: " + parseFunction)
        acc
    with
    | _ ->        
        let msg = "Error during " + parseFunction + "."
        if parseFunction = "parse_term"
        then (fileName, lineNumber, offset, regexMatch, parseString, msg) :: acc
        elif parseFunction = "parse_type"
        then (fileName, lineNumber, offset, regexMatch, parseString, msg) :: acc
        else failwith ("Unknow parse function: " + parseFunction)
        
/// Adds a message to the list if a successful parse occurs for a parse_term or parse_type.
let parsingSuccessCondition (item : (string * int * int * Match)) acc : (string * int * int * Match * string * string) list =
    let (fileName, lineNumber, offset, regexMatch) = item
    let parseFunction = regexMatch.Groups.["parse_function"].Value
    let parseString = regexMatch.Groups.["parseString"].Value
    try
        if parseFunction = "parse_term"
        then NHol.parser.parse_term parseString |> ignore
        elif parseFunction = "parse_type"
        then NHol.parser.parse_type parseString |> ignore
        else failwith ("Unknow parse function: " + parseFunction)
        let msg = parseFunction + " successful."
        (fileName, lineNumber, offset, regexMatch, parseString, msg) :: acc
    with
    | _ -> acc

/// Use to pass functionName with no condtions.
let functionNameAlwaysCondition (item : (string * int * int * Match)) acc : (string * int * int * Match * string * string) list =
    let (fileName, lineNumber, offset, regexMatch) = item
    let functionName = regexMatch.Groups.["functionName"].Value
    (fileName, lineNumber, offset, regexMatch, functionName, "") :: acc
    
/// Adds a message to the list if a HOL Light name is found.
let holLightNameCondition (item : (string * int * int * Match)) acc : (string * int * int * Match * string * string) list =
    let (fileName, lineNumber, offset, regexMatch) = item
    let functionName = regexMatch.Groups.["functionName"].Value
    let functionNameCondition = 
//        functionName.ToUpper() = functionName &&
        offset = 0 &&
        Regex.IsMatch(functionName, @"^[A-Z0-9_]+$")
    if functionNameCondition 
    then (fileName, lineNumber, offset, regexMatch, functionName, "") :: acc
    else acc

/// Process the matches to build a list of messages based on the condtions.
let processConditions conditions info  : (string * int * int * Match * string * string) list =
    let rec processConditions (item : (string * int * int * Match)) conditions acc : (string * int * int * Match * string * string) list =
        match conditions with
        | condition :: tl ->
            let acc = condition item acc
            processConditions item tl acc
        | [] -> acc
    let rec prcessInfo (info : (string * int * int * Match) list) conditions acc : (string * int * int * Match * string * string) list =
        match info with
        | hd :: tl -> 
            let acc = processConditions hd conditions acc
            prcessInfo tl conditions acc
        | [] -> List.rev acc
    prcessInfo info conditions []
   
/// Prints a list of messages based on the filenames, patterns and condtions.
let printMessages filenames patterns conditions =
    getMatches filenames patterns
    |> processConditions conditions
    |> printInfo 

// I made this list to correspond with the compilation order to see if the 
// order mattered when parsing.
/// List of absolute filenames for HOL Light source code files in this project.
let projectFiles : string list = 
    let projectCodeFiles =
        [@"lib.fs";
        @"fusion.fs";
        @"basics.fs";
        @"nets.fs";
        @"printer.fs";
        @"preterm.fs";
        @"parser.fs";
        @"equal.fs";
        @"bool.fs";
        @"drule.fs";
        @"tactics.fs";
        @"itab.fs";
        @"simp.fs";
        @"theorems.fs";
        @"ind_defs.fs";
        @"class.fs";
        @"trivia.fs";
        @"canon.fs";
        @"meson.fs";
        @"quot.fs";
        @"pair.fs";
        @"nums.fs";
        @"recursion.fs";
        @"arith.fs";
        @"wf.fs";
        @"calc_num.fs";
        @"normalizer.fs";
        @"grobner.fs";
        @"ind_types.fs";
        @"lists.fs";
        @"realax.fs";
        @"calc_int.fs";
        @"realarith.fs";
        @"real.fs";
        @"calc_rat.fs";
        @"int.fs";
        @"sets.fs";
        @"iterate.fs";
        @"cart.fs";
        @"define.fs";
        @"help.fs";
        @"database.fs"]
    let rec convertFiles filenames acc =
        match filenames with
        | hd :: tl -> 
            let absoluteFileName = __SOURCE_DIRECTORY__ + System.IO.Path.DirectorySeparatorChar.ToString() + hd
            let acc = absoluteFileName :: acc
            convertFiles tl acc
        | [] -> List.rev acc
    convertFiles projectCodeFiles []

// "(?<parse_function>parse_term)(?:[ ]?)(?<atSign>[@]?)(?:\x22)(?<parseString>[^""]*)(?:\x22)"
// Regex options used: RegexOptions.Multiline
// A parse_term in code should macth
// (?<parse_function>parse_term) - the named group parse_function which is the function name parse_term
// (?:[ ]?)                      - an optional space
// (?<atSign>[@]?)               - the named group atSign which is an @ before opening ". It is optional here to match were we missed adding @.
// (?:\x22)                      - a starting " here as \x22
// (?<parseString>[^""]*)        - the named group parseString which is any characters upto the next "
// (?:\x22)                      - a ending " here as \x22

// "(?<parse_function>parse_type)(?:[ ]?)(?<atSign>[@]?)(?:\x22)(?<parseString>[^""]*)(?:\x22)"
// Regex options used: RegexOptions.Multiline
// A parse_type in code should macth
// (?<parse_function>parse_type) - the named group parse_function which is the function name parse_type
// (?:[ ]?)                      - an optional space
// (?<atSign>[@]?)               - the named group atSign which is an @ before opening ". It is optional here to match were we missed adding @.
// (?:\x22)                      - a starting " here as \x22
// (?<parseString>[^""]*)        - the named group parseString which is any characters upto the next "
// (?:\x22)                      - a ending " here as \x22

//let test001 =
////    let path = @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol"
////    let path = @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\bool.fs"
////    let path = ""
////    let path = @"theorems.fs"
////    let fileList = getFiles path
//
//    let parseTermPattern = @"(?<parse_function>parse_term)(?:[ ]?)(?<atSign>[@]?)(?:\x22)(?<parseString>[^""]*)(?:\x22)"
//    let parseTypePattern = @"(?<parse_function>parse_type)(?:[ ]?)(?<atSign>[@]?)(?:\x22)(?<parseString>[^""]*)(?:\x22)"
//    let patterns = [parseTermPattern; parseTypePattern]
//
////    let conditions = [atSignCondition; invalidTextCondition; parsingErrorCondition; parsingSuccessCondition; containsLinebreakCondition]
//    let conditions = [containsLinebreakCondition; parsingErrorCondition; parsingSuccessCondition]
//
//    printMessages projectFiles patterns conditions

let test002 =
    let letWithoutArgsPattern = @"(?:let)(?:( )+)(?<functionName>[^ ]*)(?:( )+)(?:=)"
    let patterns = [letWithoutArgsPattern]
    let conditions = [holLightNameCondition]

    printMessages projectFiles patterns conditions