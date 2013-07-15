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

//printfn "result as AST:  %A" result
//printfn "result as term: %s" (NHol.printer.string_of_term result)


// A path can be absolute or relative, a directory or file, or empty.
let getFiles (path : string) : string list =
    let toAbsolutePath path =
        if System.String.IsNullOrWhiteSpace(path)
        then __SOURCE_DIRECTORY__                                                            // empty path
        elif System.IO.Path.IsPathRooted path   
        then path                                                                            // absolute path
        else  __SOURCE_DIRECTORY__ + System.IO.Path.DirectorySeparatorChar.ToString() + path // relative path
    let toFileList absolutePath =
        if (System.IO.Directory.Exists absolutePath)
        then Array.toList (System.IO.Directory.GetFiles absolutePath)
        elif System.IO.File.Exists(absolutePath)
        then [ absolutePath ]
        else failwith ("path is not a directory or file: " + absolutePath)
    path
    |> toAbsolutePath 
    |> toFileList

let lineEndingMap (fileName : string) = 
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
    let rec processMatchList lineNumber acc matches=
        match matches with
        | (hd : Match) :: tl ->
            let acc = (lineNumber, hd.Captures.[0].Index) :: acc
            processMatchList (lineNumber + 1) acc tl 
        | [] -> List.rev  acc
    getMatches fileName pattern
    |> processMatchList 1 [(0,0)] 
    |> Map.ofList

let lineNumberLookup map offset : int =
    let rec findLine offset checkLineNumber =
        match Map.tryFind checkLineNumber map with
        | Some(lineEnd) ->
            if offset > lineEnd
            then findLine offset (checkLineNumber + 1)
            else checkLineNumber
        | None -> 0
    findLine offset 1

let getMatches (fileNames : string list) (patterns : string list) : (string * int * Match) list =                
    let rec processPattern (pattern : string) (fileNames : string list) acc =
        match fileNames with
        | fileName :: tl ->
            let lineEndings = lineEndingMap fileName
            let fileText = (System.IO.File.ReadAllText fileName)
            let matches = Regex.Matches(fileText, pattern)
            let matchesList = matches |> Seq.cast |> Seq.toList
            let rec addInfo list (acc : (string * int * Match) list) =
                match list with
                | (hd : Match) :: tl ->
                    let offset = (hd.Captures.[0].Index)
                    let lineNumber = lineNumberLookup lineEndings offset
                    addInfo tl ((fileName, lineNumber, hd) :: acc)
                | [] -> acc
            let newItems = addInfo matchesList []
            processPattern pattern tl (acc @ (List.rev newItems))
        | [] -> acc
    let rec processPatterns patterns fileNames acc =
        match patterns with
        | hd :: tl ->
            let acc = processPattern hd fileNames acc
            processPatterns tl fileNames acc
        | [] -> acc
    processPatterns patterns fileNames []

let printInfo (info : (string * int * Match * string * string) list) =
    let printMatchCollection (item : (string * int * Match * string * string)) =
        let (fileName, lineNumber, regexMatch, matchString, msg) = item
        printfn @"%s(%d): %s ""%s""" fileName lineNumber msg matchString 
    let rec printMatchInfoList (list : (string * int * Match * string * string) list) =
        match list with
        | hd :: tl -> 
            printMatchCollection hd
            printMatchInfoList tl
        | [] -> ()
    printMatchInfoList info

let atSignCondition (item : (string * int * Match)) acc : (string * int * Match * string * string) list =
    let (fileName, lineNumber, regexMatch) = item
    let atSignString = regexMatch.Groups.["atSign"].Value
    let atStringCondition = not (atSignString.Contains("@"))
    if atStringCondition 
    then 
        let parseString = regexMatch.Groups.["parseString"].Value
        let msg = "Missing @ before string."
        (fileName, lineNumber, regexMatch, parseString, msg) :: acc
    else acc

let substringFoundCondtion (item : (string * int * Match)) (substring : string) acc : (string * int * Match * string * string) list =
    let (fileName, lineNumber, regexMatch) = item
    let parseString = regexMatch.Groups.["parseString"].Value
    let parseStringCondition = parseString.Contains(substring)
    if  parseStringCondition 
    then
        let msg = "String contains: " + substring
        (fileName, lineNumber, regexMatch, parseString, msg) :: acc
    else acc

let invalidTextCondition (item : (string * int * Match)) acc : (string * int * Match * string * string) list =
    substringFoundCondtion (item : (string * int * Match)) "|>" acc

let parsingErrorCondition (item : (string * int * Match)) acc : (string * int * Match * string * string) list =
    let (fileName, lineNumber, regexMatch) = item
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
        then (fileName, lineNumber, regexMatch, parseString, msg) :: acc
        elif parseFunction = "parse_type"
        then (fileName, lineNumber, regexMatch, parseString, msg) :: acc
        else failwith ("Unknow parse function: " + parseFunction)

let parsingSuccessCondition (item : (string * int * Match)) acc : (string * int * Match * string * string) list =
    let (fileName, lineNumber, regexMatch) = item
    let parseFunction = regexMatch.Groups.["parse_function"].Value
    let parseString = regexMatch.Groups.["parseString"].Value
    try
        if parseFunction = "parse_term"
        then NHol.parser.parse_term parseString |> ignore
        elif parseFunction = "parse_type"
        then NHol.parser.parse_type parseString |> ignore
        else failwith ("Unknow parse function: " + parseFunction)
        let msg = parseFunction + " successful."
        (fileName, lineNumber, regexMatch, parseString, msg) :: acc
    with
    | _ -> acc
        
// Note: If any condition matches, a new item is added to the output.
let filterInfo info filters  : (string * int * Match * string * string) list =
    let rec filtersItem (item : (string * int * Match)) filters acc : (string * int * Match * string * string) list =
        match filters with
        | filter :: tl ->
            let acc = filter item acc
            filtersItem item tl acc
        | [] -> acc
    let rec filterList (info : (string * int * Match) list) filters acc : (string * int * Match * string * string) list =
        match info with
        | hd :: tl -> 
            let acc = filtersItem hd filters acc
            filterList tl filters acc
        | [] -> List.rev acc
    filterList info filters []
   
let identifyParseStringProblems fileNames patterns =
    let info = (getMatches fileNames patterns)
    let info = filterInfo info [atSignCondition; invalidTextCondition; parsingErrorCondition;parsingSuccessCondition]
    printInfo info

let filters =
    [atSignCondition; invalidTextCondition; parsingErrorCondition]

// "(?<parse_function>parse_term)(?:[ ]?)(?<atSign>[@]?)(?:\x22)(?<parseString>.*?)(?:\x22)"
// A parse_term in code should macth
// (?<parse_function>parse_term) - the named group parse_function which is the function name parse_term
// (?:[ ]?)                      - an optional space
// (?<atSign>[@]?)               - the named group atSign which is an @ before opening ". It is optional here to match were we missed adding @.
// (?:\x22)                      - a starting " here as \x22
// (?<parseString>.*?)           - the named group parseString which is any non greedy characters upto the next "
// (?:\x22)                      - a ending " here as \x22

// "(?<parse_function>parse_type)(?:[ ]?)(?<atSign>[@]?)(?:\x22)(?<parseString>.*?)(?:\x22)"
// A parse_type in code should macth
// (?<parse_function>parse_type) - the named group parse_function which is the function name parse_type
// (?:[ ]?)                      - an optional space
// (?<atSign>[@]?)               - the named group atSign which is an @ before opening ". It is optional here to match were we missed adding @.
// (?:\x22)                      - a starting " here as \x22
// (?<parseString>.*?)           - the named group parseString which is any non greedy characters upto the next "
// (?:\x22)                      - a ending " here as \x22

let test001 =
//    let path = @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol"
//    let path = @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\bool.fs"
//    let path = ""
//    let path = @"bool.fs"
//    let fileList = getFiles path

// I made this list to correspond with the compilation order to see if the 
// order mattered when parsing.
    let fileList : string list = 
        [@"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\lib.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\fusion.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\basics.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\nets.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\printer.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\preterm.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\parser.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\equal.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\bool.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\drule.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\tactics.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\itab.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\simp.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\theorems.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\ind_defs.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\class.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\trivia.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\canon.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\meson.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\quot.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\pair.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\nums.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\recursion.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\arith.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\wf.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\calc_num.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\normalizer.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\grobner.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\ind_types.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\lists.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\realax.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\calc_int.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\realarith.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\real.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\calc_rat.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\int.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\sets.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\iterate.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\cart.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\define.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\util.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\help.fs";
        @"E:\Projects\Visual Studio 2012\Github\Harrison\NHol\NHol\database.fs"]

    let parseTermPattern = @"(?<parse_function>parse_term)(?:[ ]?)(?<atSign>[@]?)(?:\x22)(?<parseString>.*?)(?:\x22)"
    let parseTypePattern = @"(?<parse_function>parse_type)(?:[ ]?)(?<atSign>[@]?)(?:\x22)(?<parseString>.*?)(?:\x22)"
    let patterns = [parseTermPattern; parseTypePattern]

    identifyParseStringProblems fileList patterns