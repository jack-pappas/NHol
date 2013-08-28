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

/// Tests for functions in the NHol.parser module.
module Tests.NHol.parser

open NUnit.Framework

open NHol.parser
open FSharp.Compatibility.OCaml

#if SKIP_MODULE_INIT
#else
/// Performs setup for this test fixture.
/// Executed once prior to running any tests in this fixture.
[<TestFixtureSetUp>]
let fixtureSetup () : unit =
    // TEMP : Until any "real" code is added here (if ever), just emit a message
    // to the NUnit console/log so we'll know this function has been executed.
    SetupHelpers.emitEmptyTestFixtureSetupMessage "parser"

/// Performs setup for each unit test.
/// Executed once prior to running each unit test in this fixture.
[<SetUp>]
let testSetup () : unit =
    // Emit a message to the NUnit console/log to record when this function is called.
    SetupHelpers.emitTestSetupModuleResetMessage "parser"

    // Reset mutable state for this module and those proceeding it before running each unit test.
    // This helps avoid issues with mutable state which arise because unit tests can run in any order.
    ModuleReset.lib ()
    ModuleReset.fusion ()
    ModuleReset.basics ()
    ModuleReset.nets ()
    ModuleReset.printer ()
    ModuleReset.preterm ()
    ModuleReset.parser ()
#endif

// functions to help with test cases.

// Note: HOL Light parsers that work with parsing exceptions expect noparse exception
// and not a user defined exception.

// Create a parser that accepts anything except an empty list.
let anyParser (x : 'a list) : 'a * 'a list =
    match x with
    | h::t -> (h,t)
//    | [] -> failwith "anyParser"
    | [] -> raise Noparse

let isNum x =
    let (result, _) = System.Int32.TryParse x
    result

let isLexcodeNum x =
    match x with
    | Ident y when isNum y ->
//        printfn "x: %A is lexcode num." x
        true
    | _ ->
//        printfn "x: %A is NOT lexcode num." x
        false

// Create a parser that accepts only int values.
let intParser (l : string list) : string * string list =
    match l with
    | h::t when isNum h -> (h,t)
    | _ -> raise Noparse

// Create a parser that accepts only int lexcode values.
let intLexcodeParser (l : lexcode list) : lexcode * lexcode list =
    match l with
    | Ident h::t when isNum h -> (Ident h,t)
    | _ -> raise Noparse

(* (<|>) - OCaml ||  tests *)

(* (.>>.) - OCaml ++  tests *)

(* many  tests *)

// The first string is what humans expect to read
// and the second string list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private manyStringTypeValues : (string * string list * (string list * string list))[] = [|
    (
        // idx 0
        // parser.many.01
        // No input
        "",    // humans read this
        [],    // the NHol.parser.many function reads this
        ([],[])
    );
    (
        // idx 1
        // parser.many.02
        // one char input, one value that matches
        "1",
        ["1"],
        (["1"],[])
    );
    (
        // idx 2
        // parser.many.03
        // one char input, one value that doesn't match
        "a",
        ["a"],
        ([],["a"])
    );
    (
        // idx 3
        // parser.many.04
        // two char input, two values that matches
        "12",
        ["1";"2"],
        (["1"; "2"],[])
    );
    (
        // idx 4
        // parser.many.05
        // two char input, first value doesn't match, second value matches
        "a1",
        ["a";"1"],
        ([],["a";"1"])
    );
    (
        // idx 5
        // parser.many.06
        // two char input, no values match
        "ab",
        ["a";"b"],
        ([],["a";"b"])
    );
    (
        // idx 6
        // parser.many.07
        // three char input, no values match
        "abc",
        ["a";"b";"c"],
        ([],["a";"b";"c"])
    );
    (
        // idx 7
        // parser.many.08
        // three char input, first values matches
        "1bc",
        ["1";"b";"c"],
        (["1"],["b";"c"])
    );
    (
        // idx 8
        // parser.many.09
        // three char input, first two values match
        "12c",
        ["1";"2";"c"],
        (["1";"2"],["c"])
    );
    (
        // idx 9
        // parser.many.10
        // three char input, all values match
        "123",
        ["1";"2";"3"],
        (["1";"2";"3"],[])
    );
    |]

[<Test>]
[<TestCase(0, TestName = "parser.many.01")>]
[<TestCase(1, TestName = "parser.many.02")>]
[<TestCase(2, TestName = "parser.many.03")>]
[<TestCase(3, TestName = "parser.many.04")>]
[<TestCase(4, TestName = "parser.many.05")>]
[<TestCase(5, TestName = "parser.many.06")>]
[<TestCase(6, TestName = "parser.many.07")>]
[<TestCase(7, TestName = "parser.many.08")>]
[<TestCase(8, TestName = "parser.many.09")>]
[<TestCase(9, TestName = "parser.many.010")>]
let ``function many - type string`` idx =
    let (externalForm, _, _) = manyStringTypeValues.[idx]
    let (_, internalForm, _) = manyStringTypeValues.[idx]
    let (_, _, (currentResult , restResult)) = manyStringTypeValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let stringParser : string list -> string list * string list = NHol.parser.many intParser
    let (current, rest) = stringParser internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    Assert.AreEqual(current, currentResult)
    Assert.AreEqual(rest, restResult)

// The first sting is what humans expect to read
// and the second lexcode list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private manyLexcodeTypeValues : (string * lexcode list * (lexcode list * lexcode list))[] = [|
    (
        // idx 0
        // parser.many.101
        // No input
        "",    // humans read this
        [],    // the NHol.parser.many function reads this
        ([],[])
    );
    (
        // idx 1
        // parser.many.102
        // one token input, one value that matches
        "1",
        [Ident "1"],
        ([Ident "1"],[])
    );
    (
        // idx 2
        // parser.many.103
        // one token input, one value that doesn't match
        "a",
        [Ident "a"],
        ([],[Ident "a"])
    );
    (
        // idx 3
        // parser.many.104
        // two token input, one value that matches
        "12",
        [Ident "12"],
        ([Ident "12"],[])
    );
    (
        // idx 4
        // parser.many.105
        // two token input, first value doesn't match, second value matches
        "a 1",
        [Ident "a"; Ident "1"],
        ([],[Ident "a"; Ident "1"])
    );
    (
        // idx 5
        // parser.many.106
        // two token input with space seperator, first value matches second value doesn't match
        "12 a",
        [Ident "12";Ident "a"],
        ([Ident "12"],[Ident "a"])
    );
    (
        // idx 6
        // parser.many.107
        // two token input, first value matches second value doesn't match
        "12#",
        [Ident "12";Ident "#"],
        ([Ident "12"],[Ident "#"])
    );

    (
        // idx 7
        // parser.many.108
        // three token input, no values match
        "a b c",
        [Ident "a";Ident "b";Ident "c"],
        ([],[Ident "a";Ident "b";Ident "c"])
    );
    (
        // idx 8
        // parser.many.109
        // three token input, first values matches
        "1 b c",
        [Ident "1";Ident "b";Ident "c"],
        ([Ident "1"],[Ident "b";Ident "c"])
    );
    (
        // idx 9
        // parser.many.110
        // three token input, first two values match
        "1 2 c",
        [Ident "1";Ident "2";Ident "c"],
        ([Ident "1";Ident "2"],[Ident "c"])
    );
    (
        // idx 10
        // parser.many.111
        // three token input, all values match
        "1 2 3",
        [Ident "1";Ident "2";Ident "3"],
        ([Ident "1";Ident "2";Ident "3"],[])
    );
    |]

[<Test>]
[<TestCase(0, TestName = "parser.many.101")>]
[<TestCase(1, TestName = "parser.many.102")>]
[<TestCase(2, TestName = "parser.many.103")>]
[<TestCase(3, TestName = "parser.many.104")>]
[<TestCase(4, TestName = "parser.many.105")>]
[<TestCase(5, TestName = "parser.many.106")>]
[<TestCase(6, TestName = "parser.many.107")>]
[<TestCase(7, TestName = "parser.many.108")>]
[<TestCase(8, TestName = "parser.many.109")>]
[<TestCase(9, TestName = "parser.many.110")>]
[<TestCase(10, TestName = "parser.many.111")>]
let ``function many - type lexcode`` idx =
    let (externalForm, _, _) = manyLexcodeTypeValues.[idx]
    let (_, internalForm, _) = manyLexcodeTypeValues.[idx]
    let (_, _, (currentResult , restResult)) = manyLexcodeTypeValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = (NHol.parser.lex << NHol.lib.explode) externalForm  // Notice use of lex to convert string to lexcode.
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let lexcodeParser : lexcode list -> lexcode list * lexcode list = NHol.parser.many intLexcodeParser
    let (current, rest) = lexcodeParser internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    Assert.AreEqual(current, currentResult)
    Assert.AreEqual(rest, restResult)

(* (|>>) - OCaml >>  tests *)

(* fix  tests *)

(* listof  tests *)

// The first string is what humans expect to read
// and the second string list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private listofStringTypeValues : (string * string list * (string list -> (string * string list)) * string * (string list * string list))[] = [|
    (
        // idx 0
        // parser.listof.01
        // No input
        // throws NHol.parser.Noparse
        "",    // humans read this
        [],    // the NHol.parser.listof function reads this
        anyParser,
        "|",
        ([],[])  // Dummy value
    );
    (
        // idx 1
        // parser.listof.02
        // No seperator
        "1",    // humans read this
        ["1"],  // the NHol.parser.listof function reads this
        anyParser,
        "",
        (["1"],[])    // Notice "1" accepted because anyParser accepts "1" and did not reach seperator char
    );
    (
        // idx 2
        // parser.listof.03
        // one char that does not match seperator
        "1",
        ["1"],
        anyParser,
        "|",
        (["1"],[])    // Notice "1" accepted because anyParser accepts "1" and did not reach seperator char
    );
    (
        // idx 3
        // parser.listof.04
        // one char that matches seperator
        "|",
        ["|"],
        anyParser,
        "|",
        (["|"],[])    // Notice "|" accepted because anyParser accepts "|"
    );
    (
        // idx 4
        // parser.listof.05
        // two char input that ends with seperator
        // throws System.Excpeiton
        // Notice throws exception because anyParser accepts "1", seperatorParser accepts "|"
        //    anyParser wants another value but doesn't get one.
        "1|",
        ["1";"|";],
        anyParser,
        "|",
        ([],[])  // Dummy value
    );
    (
        // idx 5
        // parser.listof.06
        // example with two values
        "1|2",
        ["1";"|";"2"],
        anyParser,
        "|",
        (["1"; "2"],[])
    );
    (
        // idx 6
        // parser.listof.07
        // example with three values
        "1|2|3",
        ["1";"|";"2";"|";"3"],
        anyParser,
        "|",
        (["1"; "2"; "3"],[])
    );
    (
        // idx 7
        // parser.listof.08
        // example with remaining input
        "1|2|3 4",
        ["1";"|";"2";"|";"3";" ";"4"],
        anyParser,
        "|",
        (["1"; "2"; "3"],[" ";"4"])
    );
    (
        // idx 8
        // parser.listof.09
        // No input
        // throws NHol.parser.Noparse
        "",    // humans read this
        [],    // the NHol.parser.listof function reads this
        intParser,
        "|",
        ([],[])  // Dummy value
    );
    (
        // idx 9
        // parser.listof.10
        // No seperator
        "1",    // humans read this
        ["1"],  // the NHol.parser.listof function reads this
        intParser,
        "",
        (["1"],[])    // Notice "1" accepted because anyParser accepts "1" and did not reach seperator char
    );
    (
        // idx 10
        // parser.listof.11
        // one char that does not match seperator
        "1",
        ["1"],
        intParser,
        "|",
        (["1"],[])    // Notice "1" accepted because anyParser accepts "1" and did not reach seperator char
    );
    (
        // idx 11
        // parser.listof.12
        // one char that matches seperator
        // throws NHol.parser.Noparse
        "|",
        ["|"],
        intParser,
        "|",
        ([],[])  // Dummy value
    );
    (
        // idx 12
        // parser.listof.13
        // two char input that ends with seperator
        // throws System.Excpeiton
        // Notice throws exception because intParser accepts "1", seperatorParser accepts "|"
        //    intParser wants another value but doesn't get one.
        "1|",
        ["1";"|";],
        intParser,
        "|",
        ([],[])  // Dummy value
    );
    (
        // idx 13
        // parser.listof.14
        // example with two values
        "1|2",
        ["1";"|";"2"],
        intParser,
        "|",
        (["1"; "2"],[])
    );
    (
        // idx 14
        // parser.listof.15
        // example with three values
        "1|2|3",
        ["1";"|";"2";"|";"3"],
        intParser,
        "|",
        (["1"; "2"; "3"],[])
    );
    (
        // idx 15
        // parser.listof.16
        // example with remaining input
        "1|2|3 4",
        ["1";"|";"2";"|";"3";" ";"4"],
        intParser,
        "|",
        (["1"; "2"; "3"],[" ";"4"])
    );

    |]

[<Test>]
[<TestCase(0, TestName = "parser.listof.01", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.listof.02")>]
[<TestCase(2, TestName = "parser.listof.03")>]
[<TestCase(3, TestName = "parser.listof.04")>]
[<TestCase(4, TestName = "parser.listof.05", ExpectedException=typeof<System.Exception>, ExpectedMessage = "listof error expected")>]
[<TestCase(5, TestName = "parser.listof.06")>]
[<TestCase(6, TestName = "parser.listof.07")>]
[<TestCase(7, TestName = "parser.listof.08")>]
[<TestCase(8, TestName = "parser.listof.09", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(9, TestName = "parser.listof.10")>]
[<TestCase(10, TestName = "parser.listof.11")>]
[<TestCase(11, TestName = "parser.listof.12", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(12, TestName = "parser.listof.13", ExpectedException=typeof<System.Exception>, ExpectedMessage = "listof error expected")>]
[<TestCase(13, TestName = "parser.listof.14")>]
[<TestCase(14, TestName = "parser.listof.15")>]
[<TestCase(15, TestName = "parser.listof.16")>]
let ``function listof - type string`` idx =
    let (externalForm, _, _, _, _) = listofStringTypeValues.[idx]
    let (_, internalForm, _, _, _) = listofStringTypeValues.[idx]
    let (_, _, valueParser, _, _) = listofStringTypeValues.[idx]
    let (_, _, _, seperator, _) = listofStringTypeValues.[idx]
    let (_, _, _, _, (currentResult , restResult)) = listofStringTypeValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let seperatorParser = a seperator
    let stringParser = NHol.parser.listof valueParser seperatorParser "listof error"
    let (current, rest) = stringParser internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    Assert.AreEqual(current, currentResult)
    Assert.AreEqual(rest, restResult)

// The first lexcode is what humans expect to read
// and the second lexcode list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private listoflexcodeTypeValues : (string * lexcode list * (lexcode list -> (lexcode * lexcode list)) * lexcode * (lexcode list * lexcode list))[] = [|
    (
        // idx 0
        // parser.listof.101
        // No input
        // throws NHol.parser.Noparse
        "",    // humans read this
        [],    // the NHol.parser.listof function reads this
        intLexcodeParser,
        Resword "|",
        ([],[])  // Dummy value
    );
    (
        // idx 1
        // parser.listof.102
        // No seperator
        "1",
        [Ident "1"],
        intLexcodeParser,
        Ident "",
        ([Ident "1"],[])    // Notice "1" accepted because intLexcodeParser accepts "1" and did not reach seperator char
    );
    (
        // idx 2
        // parser.listof.103
        // one char that does not match seperator
        "1",
        [Ident "1"],
        intLexcodeParser,
        Resword "|",
        ([Ident "1"],[])    // Notice "1" accepted because intLexcodeParser accepts "1" and did not reach seperator char
    );
    (
        // idx 3
        // parser.listof.104
        // one char that matches seperator
        // throws NHol.parser.Noparse
        "|",
        [Resword "|"],
        intLexcodeParser,
        Resword "|",
        ([],[])  // Dummy value
    );
    (
        // idx 4
        // parser.listof.105
        // two char input that ends with seperator
        // throws System.Excpetion "listof error expected"
        // Notice throws exception because intLexcodeParser accepts Ident "1", seperatorParser accepts "|"
        //    intLexcodeParser wants another value but doesn't get one.
        "1|",
        [Ident "1"; Resword "|";],
        intLexcodeParser,
        Resword "|",
        ([],[])  // Dummy value
    );
    (
        // idx 5
        // parser.listof.106
        // example with two values
        "1|2",
        [Ident "1"; Resword "|"; Ident "2"],
        intLexcodeParser,
        Resword "|",
        ([Ident "1"; Ident "2"],[])
    );
    (
        // idx 6
        // parser.listof.107
        // example with three values
        "1|2|3",
        [Ident "1"; Resword "|"; Ident "2"; Resword "|"; Ident "3"],
        intLexcodeParser,
        Resword "|",
        ([Ident "1"; Ident "2"; Ident "3"],[])
    );
    (
        // idx 7
        // parser.listof.108
        // example with remaining input
        "1|2|3 4",
        [Ident "1"; Resword "|"; Ident "2"; Resword "|"; Ident "3"; Ident "4"],  // Notice space removed by lex
        intLexcodeParser,
        Resword "|",
        ([Ident "1"; Ident "2"; Ident "3"],[Ident "4"])
    );
    (
        // idx 8
        // parser.listof.109
        // No input
        // throws NHol.parser.Noparse
        "",    // humans read this
        [],    // the NHol.parser.listof function reads this
        intLexcodeParser,
        Ident ",",
        ([],[])  // Dummy value
    );
    (
        // idx 9
        // parser.listof.110
        // No seperator
        "1",
        [Ident "1"],
        intLexcodeParser,
        Ident "",
        ([Ident "1"],[])    // Notice "1" accepted because intLexcodeParser accepts "1" and did not reach seperator char
    );
    (
        // idx 10
        // parser.listof.111
        // one char that does not match seperator
        "1",
        [Ident "1"],
        intLexcodeParser,
        Ident ",",
        ([Ident "1"],[])    // Notice "1" accepted because intLexcodeParser accepts "1" and did not reach seperator char
    );
    (
        // idx 11
        // parser.listof.112
        // one char that matches seperator
        // throws NHol.parser.Noparse
        ",",
        [Ident ","],
        intLexcodeParser,
        Ident ",",
        ([],[])  // Dummy value
    );
    (
        // idx 12
        // parser.listof.113
        // two char input that ends with seperator
        // throws System.Excpetion "listof error expected"
        // Notice throws exception because intLexcodeParser accepts Ident "1", seperatorParser accepts "|"
        //    intLexcodeParser wants another value but doesn't get one.
        "1,",
        [Ident "1"; Ident ",";],
        intLexcodeParser,
        Ident ",",
        ([],[])  // Dummy value
    );
    (
        // idx 13
        // parser.listof.114
        // example with two values
        "1,2",
        [Ident "1"; Ident ","; Ident "2"],
        intLexcodeParser,
        Ident ",",
        ([Ident "1"; Ident "2"],[])
    );
    (
        // idx 14
        // parser.listof.115
        // example with three values
        "1,2,3",
        [Ident "1"; Ident ","; Ident "2"; Ident ","; Ident "3"],
        intLexcodeParser,
        Ident ",",
        ([Ident "1"; Ident "2"; Ident "3"],[])
    );
    (
        // idx 15
        // parser.listof.116
        // example with remaining input
        "1,2,3 4",
        [Ident "1"; Ident ","; Ident "2"; Ident ","; Ident "3"; Ident "4"],  // Notice space removed by lex
        intLexcodeParser,
        Ident ",",
        ([Ident "1"; Ident "2"; Ident "3"],[Ident "4"])
    );
    |]

[<Test>]
[<TestCase(0, TestName = "parser.listof.101", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.listof.102")>]
[<TestCase(2, TestName = "parser.listof.103")>]
[<TestCase(3, TestName = "parser.listof.104", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(4, TestName = "parser.listof.105", ExpectedException=typeof<System.Exception>, ExpectedMessage = "listof error expected")>]
[<TestCase(5, TestName = "parser.listof.106")>]
[<TestCase(6, TestName = "parser.listof.107")>]
[<TestCase(7, TestName = "parser.listof.108")>]
[<TestCase(8, TestName = "parser.listof.109", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(9, TestName = "parser.listof.110")>]
[<TestCase(10, TestName = "parser.listof.111")>]
[<TestCase(11, TestName = "parser.listof.112", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(12, TestName = "parser.listof.113", ExpectedException=typeof<System.Exception>, ExpectedMessage = "listof error expected")>]
[<TestCase(13, TestName = "parser.listof.114")>]
[<TestCase(14, TestName = "parser.listof.115")>]
[<TestCase(15, TestName = "parser.listof.116")>]
let ``function listof - type lexcode`` idx =
    let (externalForm, _, _, _, _) = listoflexcodeTypeValues.[idx]
    let (_, internalForm, _, _, _) = listoflexcodeTypeValues.[idx]
    let (_, _, valueParser, _, _) = listoflexcodeTypeValues.[idx]
    let (_, _, _, seperator, _) = listoflexcodeTypeValues.[idx]
    let (_, _, _, _, (currentResult , restResult)) = listoflexcodeTypeValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = (NHol.parser.lex << NHol.lib.explode) externalForm  // Notice use of lex to convert string to lexcode.
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let seperatorParser = a seperator
    let lexcodeParser = NHol.parser.listof valueParser seperatorParser "listof error"
    let (current, rest) = lexcodeParser internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    Assert.AreEqual(current, currentResult)
    Assert.AreEqual(rest, restResult)

(* nothing  tests *)

(* elistof  tests *)

(* leftbin  tests *)

(* rightbin  tests *)

(* possibly  tests *)

// The first string is what humans expect to read
// and the second string list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private possiblyStringTypeValues : (string * string list * (string list * string list))[] = [|
    (
        // idx 0
        // parser.possibly.01
        // No input
        "",    // humans read this
        [],    // the NHol.parser.possibly function reads this
        ([],[])  // Notice result is a (string list * string list) and not (string * string list)
    );
    (
        // idx 1
        // parser.possibly.02
        // one char input, one value that matches
        "1",
        ["1"],
        (["1"],[])
    );
    (
        // idx 2
        // parser.possibly.03
        // one char input, one value that doesn't match
        "a",
        ["a"],
        ([],["a"])
    );
    (
        // idx 3
        // parser.possibly.04
        // two char input, one value that matches
        "12",
        ["1";"2"],
        (["1"],["2"])
    );
    (
        // idx 4
        // parser.possibly.05
        // two char input, first value doesn't match, second value matches
        "a1",
        ["a";"1"],
        ([],["a";"1"])
    );
    |]

[<Test>]
[<TestCase(0, TestName = "parser.possibly.01")>]
[<TestCase(1, TestName = "parser.possibly.02")>]
[<TestCase(2, TestName = "parser.possibly.03")>]
[<TestCase(3, TestName = "parser.possibly.04")>]
[<TestCase(4, TestName = "parser.possibly.05")>]
let ``function possibly - type string`` idx =
    let (externalForm, _, _) = possiblyStringTypeValues.[idx]
    let (_, internalForm, _) = possiblyStringTypeValues.[idx]
    let (_, _, (currentResult , restResult)) = possiblyStringTypeValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let stringParser : string list -> string list * string list = NHol.parser.possibly intParser
    let (current, rest) = stringParser internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    Assert.AreEqual(current, currentResult)
    Assert.AreEqual(rest, restResult)

// The first sting is what humans expect to read
// and the second lexcode list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private possiblyLexcodeTypeValues : (string * lexcode list * (lexcode list * lexcode list))[] = [|
    (
        // idx 0
        // parser.possibly.101
        // No input
        "",    // humans read this
        [],    // the NHol.parser.possibly function reads this
        ([],[])  // Notice result is a (lexcode list * lexcode list) and not (lexcode * lexcode list)
    );
    (
        // idx 1
        // parser.possibly.102
        // one token input, one value that matches
        "1",
        [Ident "1"],
        ([Ident "1"],[])
    );
    (
        // idx 2
        // parser.possibly.103
        // one token input, one value that doesn't match
        "a",
        [Ident "a"],
        ([],[Ident "a"])
    );
    (
        // idx 3
        // parser.possibly.104
        // one token input, one value that matches
        "12",
        [Ident "12"],
        ([Ident "12"],[])
    );
    (
        // idx 4
        // parser.possibly.105
        // two token input, no values match
        "a1",
        [Ident "a1"],
        ([],[Ident "a1"])
    );
    (
        // idx 5
        // parser.possibly.106
        // one token input, no values match
        "12a",
        [Ident "12a"],
        ([],[Ident "12a"])
    );
    (
        // idx 6
        // parser.possibly.107
        // two token input, first value matches second value doesn't match
        "12#",
        [Ident "12";Ident "#"],
        ([Ident "12"],[Ident "#"])
    );
    |]

[<Test>]
[<TestCase(0, TestName = "parser.possibly.101")>]
[<TestCase(1, TestName = "parser.possibly.102")>]
[<TestCase(2, TestName = "parser.possibly.103")>]
[<TestCase(3, TestName = "parser.possibly.104")>]
[<TestCase(4, TestName = "parser.possibly.105")>]
[<TestCase(5, TestName = "parser.possibly.106")>]
[<TestCase(6, TestName = "parser.possibly.107")>]
let ``function possibly - type lexcode`` idx =
    let (externalForm, _, _) = possiblyLexcodeTypeValues.[idx]
    let (_, internalForm, _) = possiblyLexcodeTypeValues.[idx]
    let (_, _, (currentResult , restResult)) = possiblyLexcodeTypeValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = (NHol.parser.lex << NHol.lib.explode) externalForm  // Notice use of lex to convert string to lexcode.
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let lexcodeParser : lexcode list -> lexcode list * lexcode list = NHol.parser.possibly intLexcodeParser
    let (current, rest) = lexcodeParser internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    Assert.AreEqual(current, currentResult)
    Assert.AreEqual(rest, restResult)

(* some  tests *)

// The first string is what humans expect to read
// and the second string list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private someStringTypeValues : (string * string list * (string * string list))[] = [|
    (
        // idx 0
        // parser.some.01
        // No input
        // throws NHol.parser.Noparse
        "",    // humans read this
        [],    // the NHol.parser.some function reads this
        ("",[])  // dummy value
    );
    (
        // idx 1
        // parser.some.02
        // one char input, one value that matches
        "1",
        ["1"],
        ("1",[])
    );
    (
        // idx 2
        // parser.some.03
        // one char input, one value that doesn't match
        // throws NHol.parser.Noparse
        "a",
        ["a"],
        ("",[])  // dummy value
    );
    (
        // idx 3
        // parser.some.04
        // two char input, one value that matches
        "12",
        ["1";"2"],
        ("1",["2"])
    );
    (
        // idx 4
        // parser.some.05
        // two char input, first value doesn't match, second value matches
        // throws NHol.parser.Noparse
        "a1",
        ["a";"1"],
        ("",[])  // dummy value
    );
    |]

[<Test>]
[<TestCase(0, TestName = "parser.some.01", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.some.02")>]
[<TestCase(2, TestName = "parser.some.03", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(3, TestName = "parser.some.04")>]
[<TestCase(4, TestName = "parser.some.05", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
let ``function some - type string`` idx =
    let (externalForm, _, _) = someStringTypeValues.[idx]
    let (_, internalForm, _) = someStringTypeValues.[idx]
    let (_, _, (currentResult , restResult)) = someStringTypeValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let stringParser : string list -> string * string list = NHol.parser.some isNum
    let (current, rest) = stringParser internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    Assert.AreEqual(current, currentResult)
    Assert.AreEqual(rest, restResult)

// The first sting is what humans expect to read
// and the second lexcode list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private someLexcodeTypeValues : (string * lexcode list * (lexcode * lexcode list))[] = [|
    (
        // idx 0
        // parser.some.101
        // No input
        // throws NHol.parser.Noparse
        "",    // humans read this
        [],    // the NHol.parser.some function reads this
        (Ident "",[])  // dummy value
    );
    (
        // idx 1
        // parser.some.102
        // one token input, one value that matches
        "1",
        [Ident "1"],
        (Ident "1",[])
    );
    (
        // idx 2
        // parser.some.103
        // one token input, one value that doesn't match
        // throws NHol.parser.Noparse
        "a",
        [Ident "a"],
        (Ident "",[])  // dummy value
    );
    (
        // idx 3
        // parser.some.104
        // two token input, one value that matches
        "12",
        [Ident "12"],
        (Ident "12",[])
    );
    (
        // idx 4
        // parser.some.105
        // one token input, no matches
        // throws NHol.parser.Noparse
        "a1",
        [Ident "a1"],
        (Ident "",[])  // dummy value
    );
    (
        // idx 5
        // parser.some.106
        // one token input, no matches
        // throws NHol.parser.Noparse
        // Note: This throws Noparse exception because "12a" is lexed as "12a" and not "12" and "a",
        // so "12a" is not a num.
        "12a",
        [Ident "12a"],
        (Ident "",[])  // dummy value
    );
    (
        // idx 6
        // parser.some.107
        // two token input, first value matches second value doesn't match
        "12#",
        [Ident "12";Ident "#"],
        (Ident "12",[Ident "#"])
    );
    |]

[<Test>]
[<TestCase(0, TestName = "parser.some.101", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.some.102")>]
[<TestCase(2, TestName = "parser.some.103", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(3, TestName = "parser.some.104")>]
[<TestCase(4, TestName = "parser.some.105", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(5, TestName = "parser.some.106", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(6, TestName = "parser.some.107")>]
let ``function some - type lexcode`` idx =
    let (externalForm, _, _) = someLexcodeTypeValues.[idx]
    let (_, internalForm, _) = someLexcodeTypeValues.[idx]
    let (_, _, (currentResult , restResult)) = someLexcodeTypeValues.[idx]

    // Verify function input form and human form match.
//    let test1 = NHol.lib.explode externalForm
//    printfn "test1: %A" test1
//    let test2 = NHol.parser.lex test1
//    printfn "test2: %A" test2

    let convertedForm = (NHol.parser.lex << NHol.lib.explode) externalForm  // Notice use of lex to convert string to lexcode.
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let lexcodeParser : lexcode list -> lexcode * lexcode list = NHol.parser.some isLexcodeNum
    let (current, rest) = lexcodeParser internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    Assert.AreEqual(current, currentResult)
    Assert.AreEqual(rest, restResult)

(* a  tests *)

// The first string is what humans expect to read
// and the second string list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private parseraStringTypeValues : (string * string list * string * (string * string list))[] = [|
    (
        // idx 0
        // parser.a.01
        // No input, non empty value
        // throws NHol.parser.Noparse
        "",    // humans read this
        [],    // the NHol.parser.a function reads this
        "(",
        ("",[])  // dummy value
    );
    (
        // idx 1
        // parser.a.02
        // one char input, empty value
        // throws NHol.parser.Noparse
        "(",
        ["("],
        "",
        ("",[])  // dummy value
    );
    (
        // idx 2
        // parser.a.03
        // one char input, value that matches
        "(",
        ["("],
        "(",
        ("(",[])
    );
    (
        // idx 3
        // parser.a.04
        // one char input, value that doesn't match
        // throws NHol.parser.Noparse
        "(",
        ["("],
        ")",
        ("",[])  // dummy value
    );
    (
        // idx 4
        // parser.a.05
        // multi char input, value that matches
        "(5)",
        ["(";"5";")"],
        "(",
        ("(",["5";")"])
    );
    |]

[<Test>]
[<TestCase(0, TestName = "parser.a.01", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.a.02", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(2, TestName = "parser.a.03")>]
[<TestCase(3, TestName = "parser.a.04", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(4, TestName = "parser.a.05")>]
let ``function a - type string`` idx =
    let (externalForm, _, _, _) = parseraStringTypeValues.[idx]
    let (_, internalForm, _, _) = parseraStringTypeValues.[idx]
    let (_, _, value, _) = parseraStringTypeValues.[idx]
    let (_, _, _, (currentResult , restResult)) = parseraStringTypeValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let stringParser : string list -> string * string list = NHol.parser.a value
    let (current, rest) = stringParser internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    Assert.AreEqual(current, currentResult)
    Assert.AreEqual(rest, restResult)

// The first sting is what humans expect to read
// and the second lexcode list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private parseraLexcodeTypeValues : (string * lexcode list * lexcode * (lexcode * lexcode list))[] = [|
    (
        // idx 0
        // parser.a.101
        // No input, non empty value
        // throws NHol.parser.Noparse
        "",    // humans read this
        [],    // the NHol.parser.a function reads this
        Resword "(",
        (Resword "",[])  // dummy value
    );
    (
        // idx 1
        // parser.a.102
        // one token input, empty value
        // throws NHol.parser.Noparse
        "(",
        [Resword "("],
        Resword "",
        (Resword "",[])  // dummy value
    );
    (
        // idx 2
        // parser.a.103
        // one token input, value that matches
        "(",
        [Resword "("],
        Resword "(",
        (Resword "(",[])
    );
    (
        // idx 3
        // parser.a.104
        // one token input, value that doesn't match
        // throws NHol.parser.Noparse
        "(",
        [Resword "("],
        Resword ")",
        (Resword "",[])  // dummy value
    );
    (
        // idx 4
        // parser.a.105
        // multi token input, value that matches
        "(5)",
        [Resword "(";Ident "5";Resword ")"],
        Resword "(",
        (Resword "(",[Ident "5";Resword ")"])
    );
    |]

[<Test>]
[<TestCase(0, TestName = "parser.a.101", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.a.102", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(2, TestName = "parser.a.103")>]
[<TestCase(3, TestName = "parser.a.104", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(4, TestName = "parser.a.105")>]
let ``function a - type lexcode`` idx =
    let (externalForm, _, _, _) = parseraLexcodeTypeValues.[idx]
    let (_, internalForm, _, _) = parseraLexcodeTypeValues.[idx]
    let (_, _, value, _) = parseraLexcodeTypeValues.[idx]
    let (_, _, _, (currentResult , restResult)) = parseraLexcodeTypeValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = (NHol.parser.lex << NHol.lib.explode) externalForm  // Notice use of lex to convert string to lexcode.
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let lexcodeParser : lexcode list -> lexcode * lexcode list = NHol.parser.a value
    let (current, rest) = lexcodeParser internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    Assert.AreEqual(current, currentResult)
    Assert.AreEqual(rest, restResult)

(* atleast  tests *)

// The first string is what humans expect to read
// and the second string list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private atleastStringTypeValues : (string * string list * int * (string list * string list))[] = [|
    (
        // idx 0
        // parser.atleast.01
        // No input
        // throws noparse
        "",    // humans read this
        [],    // the NHol.parser.atleast function reads this
        1,
        ([],[]) // dummy value
    );
    (
        // idx 1
        // parser.atleast.02
        // required is 0
        "12",
        ["1";"2"],
        0,              // Notice when count is zero this acts the same as many.
        (["1";"2"],[])
    );
    (
        // idx 2
        // parser.atleast.03
        // one char input, one value that matches, required is 1
        "1",
        ["1"],
        1,
        (["1"],[])
    );
    (
        // idx 3
        // parser.atleast.04
        // one char input, one value that doesn't match
        // throws noparse
        "a",
        ["a"],
        1,
        ([],[]) // dummy value
    );
    (
        // idx 4
        // parser.atleast.05
        // two char input, two values that matches, required is 1
        "12",
        ["1";"2"],
        1,
        (["1"; "2"],[])
    );
    (
        // idx 5
        // parser.atleast.06
        // two char input, first value doesn't match, second value matches
        // throws noparse
        "a1",
        ["a";"1"],
        1,
        ([],[]) // dummy value
    );
    (
        // idx 6
        // parser.atleast.07
        // two char input, no values match
        // throws noparse
        "ab",
        ["a";"b"],
        1,
        ([],[]) // dummy value
    );
    (
        // idx 7
        // parser.atleast.08
        // three char input, first values matches, required is 1
        "1bc",
        ["1";"b";"c"],
        1,
        (["1"],["b";"c"])
    );
    (
        // idx 8
        // parser.atleast.09
        // three char input, first two values match, required is 1
        "12c",
        ["1";"2";"c"],
        1,
        (["1";"2"],["c"])
    );
    (
        // idx 9
        // parser.atleast.10
        // three char input, all values match, required is 1
        "123",
        ["1";"2";"3"],
        1,
        (["1";"2";"3"],[])
    );
    (
        // idx 10
        // parser.atleast.11
        // one char input, one value that matches
        // throws noparse
        "1",
        ["1"],
        2,
        ([],[]) // dummy value
    );
    (
        // idx 11
        // parser.atleast.12
        // one char input, one value that doesn't match
        // throws noparse
        "a",
        ["a"],
        2,
        ([],[]) // dummy value
    );
    (
        // idx 12
        // parser.atleast.13
        // two char input, two values that matches, required is 2
        "12",
        ["1";"2"],
        2,
        (["1"; "2"],[])
    );
    (
        // idx 13
        // parser.atleast.14
        // two char input, first value doesn't match, second value matches
        // throws noparse
        "a1",
        ["a";"1"],
        2,
        ([],[]) // dummy value
    );
    (
        // idx 14
        // parser.atleast.15
        // two char input, no values match
        // throws noparse
        "ab",
        ["a";"b"],
        2,
        ([],[]) // dummy value
    );
    (
        // idx 15
        // parser.atleast.16
        // three char input, no values match
        // throws noparse
        "abc",
        ["a";"b";"c"],
        2,
        ([],[]) // dummy value
    );
    (
        // idx 16
        // parser.atleast.17
        // three char input, first values matches
        // throws noparse
        "1bc",
        ["1";"b";"c"],
        2,
        ([],[]) // dummy value
    );
    (
        // idx 17
        // parser.atleast.18
        // three char input, first two values match, required is 2
        "12c",
        ["1";"2";"c"],
        2,
        (["1";"2"],["c"])
    );
    (
        // idx 18
        // parser.atleast.19
        // three char input, all values match, required is 2
        "123",
        ["1";"2";"3"],
        2,
        (["1";"2";"3"],[])
    );
    (
        // idx 19
        // parser.atleast.20
        // one char input, one value that matches
        // throws noparse
        "1",
        ["1"],
        3,
        ([],[]) // dummy value
    );
    (
        // idx 20
        // parser.atleast.21
        // one char input, one value that doesn't match
        // throws noparse
        "a",
        ["a"],
        3,
        ([],[]) // dummy value
    );
    (
        // idx 21
        // parser.atleast.22
        // two char input, two values that matches
        // throws noparse
        "12",
        ["1";"2"],
        3,
        ([],[]) // dummy value
    );
    (
        // idx 22
        // parser.atleast.23
        // two char input, first value doesn't match, second value matches
        // throws noparse
        "a1",
        ["a";"1"],
        3,
        ([],[]) // dummy value
    );
    (
        // idx 23
        // parser.atleast.24
        // two char input, no values match
        // throws noparse
        "ab",
        ["a";"b"],
        3,
        ([],[]) // dummy value
    );
    (
        // idx 24
        // parser.atleast.25
        // three char input, no values match
        // throws noparse
        "abc",
        ["a";"b";"c"],
        3,
        ([],[]) // dummy value
    );
    (
        // idx 25
        // parser.atleast.26
        // three char input, first values matches
        // throws noparse
        "1bc",
        ["1";"b";"c"],
        3,
        ([],[]) // dummy value
    );
    (
        // idx 26
        // parser.atleast.27
        // three char input, first two values match
        // throws noparse
        "12c",
        ["1";"2";"c"],
        3,
        ([],[]) // dummy value
    );
    (
        // idx 27
        // parser.atleast.28
        // three char input, all values match, required is 3
        "123",
        ["1";"2";"3"],
        3,
        (["1";"2";"3"],[])
    );
    |]

[<Test>]
[<TestCase(0, TestName = "parser.atleast.01", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.atleast.02")>]
[<TestCase(2, TestName = "parser.atleast.03")>]
[<TestCase(3, TestName = "parser.atleast.04", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(4, TestName = "parser.atleast.05")>]
[<TestCase(5, TestName = "parser.atleast.06", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(6, TestName = "parser.atleast.07", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(7, TestName = "parser.atleast.08")>]
[<TestCase(8, TestName = "parser.atleast.09")>]
[<TestCase(9, TestName = "parser.atleast.10")>]
[<TestCase(10, TestName = "parser.atleast.11", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(11, TestName = "parser.atleast.12", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(12, TestName = "parser.atleast.13")>]
[<TestCase(13, TestName = "parser.atleast.14", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(14, TestName = "parser.atleast.15", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(15, TestName = "parser.atleast.16", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(16, TestName = "parser.atleast.17", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(17, TestName = "parser.atleast.18")>]
[<TestCase(18, TestName = "parser.atleast.19")>]
[<TestCase(19, TestName = "parser.atleast.20", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(20, TestName = "parser.atleast.21", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(21, TestName = "parser.atleast.22", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(22, TestName = "parser.atleast.23", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(23, TestName = "parser.atleast.24", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(24, TestName = "parser.atleast.25", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(25, TestName = "parser.atleast.26", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(26, TestName = "parser.atleast.27", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(27, TestName = "parser.atleast.28")>]
let ``function atleast - type string`` idx =
    let (externalForm, _, _, _) = atleastStringTypeValues.[idx]
    let (_, internalForm, _, _) = atleastStringTypeValues.[idx]
    let (_, _, count, _) = atleastStringTypeValues.[idx]
    let (_, _, _, (currentResult , restResult)) = atleastStringTypeValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let stringParser : string list -> string list * string list = NHol.parser.atleast count intParser
    let (current, rest) = stringParser internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    Assert.AreEqual(current, currentResult)
    Assert.AreEqual(rest, restResult)

// The first sting is what humans expect to read
// and the second lexcode list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private atleastLexcodeTypeValues : (string * lexcode list * int * (lexcode list * lexcode list))[] = [|
    (
        // idx 0
        // parser.atleast.101
        // No input
        // trows noparse
        "",    // humans read this
        [],    // the NHol.parser.atleast function reads this
        1,
        ([],[])  // dummy value
    );
    (
        // idx 1
        // parser.atleast.102
        // required is 0
        "1 2",
        [Ident "1";Ident "2"],
        0,              // Notice when count is zero this acts the same as many.
        ([Ident "1"; Ident "2"],[])
    );
    (
        // idx 2
        // parser.atleast.103
        // one token input, one value that matches, required is 1
        "1",
        [Ident "1"],
        1,
        ([Ident "1"],[])
    );
    (
        // idx 3
        // parser.atleast.104
        // one token input, one value that doesn't match
        // trows noparse
        "a",
        [Ident "a"],
        1,
        ([],[])  // dummy value
    );
    (
        // idx 4
        // parser.atleast.105
        // two token input, one value that matches, required is 1
        "12",
        [Ident "12"],
        1,
        ([Ident "12"],[])
    );
    (
        // idx 5
        // parser.atleast.106
        // two token input, first value doesn't match, second value matches
        // trows noparse
        "a 1",
        [Ident "a"; Ident "1"],
        1,
        ([],[])  // dummy value
    );
    (
        // idx 6
        // parser.atleast.107
        // two token input with space seperator, first value matches second value doesn't match, required is 1
        "12 a",
        [Ident "12";Ident "a"],
        1,
        ([Ident "12"],[Ident "a"])
    );
    (
        // idx 7
        // parser.atleast.108
        // two token input, first value matches second value doesn't match, required is 1
        "12#",
        [Ident "12";Ident "#"],
        1,
        ([Ident "12"],[Ident "#"])
    );
    (
        // idx 8
        // parser.atleast.109
        // three token input, no values match
        // trows noparse
        "a b c",
        [Ident "a";Ident "b";Ident "c"],
        1,
        ([],[])  // dummy value
    );
    (
        // idx 9
        // parser.atleast.110
        // three token input, first values matches, required is 1
        "1 b c",
        [Ident "1";Ident "b";Ident "c"],
        1,
        ([Ident "1"],[Ident "b";Ident "c"])
    );
    (
        // idx 10
        // parser.atleast.111
        // three token input, first two values match, required is 1
        "1 2 c",
        [Ident "1";Ident "2";Ident "c"],
        1,
        ([Ident "1";Ident "2"],[Ident "c"])
    );
    (
        // idx 11
        // parser.atleast.112
        // three token input, all values match, required is 1
        "1 2 3",
        [Ident "1";Ident "2";Ident "3"],
        1,
        ([Ident "1";Ident "2";Ident "3"],[])
    );


    (
        // idx 12
        // parser.atleast.113
        // one token input, one value that matches
        // throws noparse
        "1",
        [Ident "1"],
        2,
        ([],[])  // dummy value
    );
    (
        // idx 13
        // parser.atleast.114
        // one token input, one value that doesn't match
        // trows noparse
        "a",
        [Ident "a"],
        2,
        ([],[])  // dummy value
    );
    (
        // idx 14
        // parser.atleast.115
        // two token input, one value that matches
        // throws noparse
        "12",
        [Ident "12"],
        2,
        ([],[])  // dummy value
    );
    (
        // idx 15
        // parser.atleast.116
        // two token input, first value doesn't match, second value matches
        // trows noparse
        "a 1",
        [Ident "a"; Ident "1"],
        2,
        ([],[])  // dummy value
    );
    (
        // idx 16
        // parser.atleast.117
        // two token input with space seperator, first value matches second value doesn't match
        // throws noparse
        "12 a",
        [Ident "12";Ident "a"],
        2,
        ([],[])  // dummy value
    );
    (
        // idx 17
        // parser.atleast.118
        // two token input, first value matches second value doesn't match
        // throws noparse
        "12#",
        [Ident "12";Ident "#"],
        2,
        ([],[])  // dummy value
    );
    (
        // idx 18
        // parser.atleast.119
        // two token input, both values match, required is 2
        "12 3",
        [Ident "12";Ident "3"],
        2,
        ([Ident "12";Ident "3"],[])
    );
    (
        // idx 19
        // parser.atleast.120
        // three token input, no values match
        // trows noparse
        "a b c",
        [Ident "a";Ident "b";Ident "c"],
        2,
        ([],[])  // dummy value
    );
    (
        // idx 20
        // parser.atleast.121
        // three token input, first values matches
        // throws noparse
        "1 b c",
        [Ident "1";Ident "b";Ident "c"],
        2,
        ([],[])  // dummy value
    );
    (
        // idx 21
        // parser.atleast.122
        // three token input, first two values match, required is 2
        "1 2 c",
        [Ident "1";Ident "2";Ident "c"],
        2,
        ([Ident "1";Ident "2"],[Ident "c"])
    );
    (
        // idx 22
        // parser.atleast.123
        // three token input, all values match, required is 2
        "1 2 3",
        [Ident "1";Ident "2";Ident "3"],
        2,
        ([Ident "1";Ident "2";Ident "3"],[])
    );
    (
        // idx 23
        // parser.atleast.124
        // one token input, one value that matches
        // throws noparse
        "1",
        [Ident "1"],
        3,
        ([],[])  // dummy value
    );
    (
        // idx 24
        // parser.atleast.125
        // one token input, one value that doesn't match
        // trows noparse
        "a",
        [Ident "a"],
        3,
        ([],[])  // dummy value
    );
    (
        // idx 25
        // parser.atleast.126
        // two token input, one value that matches
        // throws noparse
        "12",
        [Ident "12"],
        3,
        ([],[])  // dummy value
    );
    (
        // idx 26
        // parser.atleast.127
        // two token input, first value doesn't match, second value matches
        // trows noparse
        "a 1",
        [Ident "a"; Ident "1"],
        3,
        ([],[])  // dummy value
    );
    (
        // idx 27
        // parser.atleast.128
        // two token input with space seperator, first value matches second value doesn't match
        // throws noparse
        "12 a",
        [Ident "12";Ident "a"],
        3,
        ([],[])  // dummy value
    );
    (
        // idx 28
        // parser.atleast.129
        // two token input, first value matches second value doesn't match
        // throws noparse
        "12#",
        [Ident "12";Ident "#"],
        3,
        ([],[])  // dummy value
    );
    (
        // idx 29
        // parser.atleast.130
        // two token input, both values match
        // throws noparse
        "12 3",
        [Ident "12";Ident "3"],
        3,
        ([],[])  // dummy value
    );
    (
        // idx 30
        // parser.atleast.131
        // three token input, no values match
        // trows noparse
        "a b c",
        [Ident "a";Ident "b";Ident "c"],
        3,
        ([],[])  // dummy value
    );
    (
        // idx 31
        // parser.atleast.132
        // three token input, first values matches
        // throws noparse
        "1 b c",
        [Ident "1";Ident "b";Ident "c"],
        3,
        ([],[])  // dummy value
    );
    (
        // idx 32
        // parser.atleast.133
        // three token input, first two values match
        // throws noparse
        "1 2 c",
        [Ident "1";Ident "2";Ident "c"],
        3,
        ([],[])  // dummy value
    );
    (
        // idx 33
        // parser.atleast.134
        // three token input, all values match, required is 3
        "1 2 3",
        [Ident "1";Ident "2";Ident "3"],
        3,
        ([Ident "1";Ident "2";Ident "3"],[])
    );
    |]

[<Test>]
[<TestCase(0, TestName = "parser.atleast.101", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.atleast.102")>]
[<TestCase(2, TestName = "parser.atleast.103")>]
[<TestCase(3, TestName = "parser.atleast.104", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(4, TestName = "parser.atleast.105")>]
[<TestCase(5, TestName = "parser.atleast.106", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(6, TestName = "parser.atleast.107")>]
[<TestCase(7, TestName = "parser.atleast.108")>]
[<TestCase(8, TestName = "parser.atleast.109", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(9, TestName = "parser.atleast.110")>]
[<TestCase(10, TestName = "parser.atleast.111")>]
[<TestCase(11, TestName = "parser.atleast.112")>]
[<TestCase(12, TestName = "parser.atleast.113", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(13, TestName = "parser.atleast.114", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(14, TestName = "parser.atleast.115", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(15, TestName = "parser.atleast.116", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(16, TestName = "parser.atleast.117", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(17, TestName = "parser.atleast.118", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(18, TestName = "parser.atleast.119")>]
[<TestCase(19, TestName = "parser.atleast.120", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(20, TestName = "parser.atleast.121", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(21, TestName = "parser.atleast.122")>]
[<TestCase(22, TestName = "parser.atleast.123")>]
[<TestCase(23, TestName = "parser.atleast.124", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(24, TestName = "parser.atleast.125", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(25, TestName = "parser.atleast.126", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(26, TestName = "parser.atleast.127", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(27, TestName = "parser.atleast.128", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(28, TestName = "parser.atleast.129", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(29, TestName = "parser.atleast.130", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(30, TestName = "parser.atleast.131", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(31, TestName = "parser.atleast.132", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(32, TestName = "parser.atleast.133", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(33, TestName = "parser.atleast.134")>]
let ``function atleast - type lexcode`` idx =
    let (externalForm, _, _, _) = atleastLexcodeTypeValues.[idx]
    let (_, internalForm, _, _) = atleastLexcodeTypeValues.[idx]
    let (_, _, count, _) = atleastLexcodeTypeValues.[idx]
    let (_, _, _, (currentResult , restResult)) = atleastLexcodeTypeValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = (NHol.parser.lex << NHol.lib.explode) externalForm  // Notice use of lex to convert string to lexcode.
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let lexcodeParser : lexcode list -> lexcode list * lexcode list = NHol.parser.atleast count intLexcodeParser
    let (current, rest) = lexcodeParser internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    Assert.AreEqual(current, currentResult)
    Assert.AreEqual(rest, restResult)

(* finished  tests *)

(* comment_token  tests *)

(* lex  tests *)

// Note: lex has several parser combinators within it.
// These parser combinators are indvidually tested here.
// To keep the funtions within lex private to lex the
// parser combinators functions are recreated here.
// If lex is ever changed, then these functions and test
// need to be changed accordingly.

let collect((h : string), (t : string list)) : string = NHol.lib.end_itlist (+) (h :: t)

let private collectValues : ((string * string list) * string)[] = [|
    (
        // idx 0
        // parser.lex.collect.01
        ("",[]),
        ""
    );
    (
        // idx 1
        // parser.lex.collect.02
        ("a",[]),
        "a"
    );
    (
        // idx 2
        // parser.lex.collect.03
        ("",["b"]),
        "b"
    );
    (
        // idx 3
        // parser.lex.collect.04
        ("a",["b"]),
        "ab"
    );
    (
        // idx 4
        // parser.lex.collect.05
        ("",["b";"c"]),
        "bc"
    );
    (
        // idx 5
        // parser.lex.collect.06
        ("a",["b";"c"]),
        "abc"
    );
    |]
[<Test>]
[<TestCase(0, TestName = "parser.lex.collect.01")>]
[<TestCase(1, TestName = "parser.lex.collect.02")>]
[<TestCase(2, TestName = "parser.lex.collect.03")>]
[<TestCase(3, TestName = "parser.lex.collect.04")>]
[<TestCase(4, TestName = "parser.lex.collect.05")>]
[<TestCase(5, TestName = "parser.lex.collect.06")>]
let ``function lex.collect`` idx =
    let (input, _) = collectValues.[idx]
    let (_, result) = collectValues.[idx]

    let collectResult = collect input
//    printfn "input: %A" input
//    printfn "expected result: %A" result
//    printfn "function result: %A" collectResult
    collectResult |> assertEqual result

let reserve (v : lexcode) : lexcode =
    match v with
    | (Ident n as tok) ->
        if NHol.printer.is_reserved_word n then Resword(n)
        else tok
    | t -> t

let private reserveValues : (lexcode * lexcode)[] = [|
    (
        // idx 0
        // parser.lex.reserve.01
        // a string that is not is_reserved_word
        Ident "a",
        Ident "a"
    );
    (
        // idx 1
        // parser.lex.reserve.02
        // a single char that is_reserved_word
        Ident "[",
        Resword "["   // Notice Ident changed to Resword for is_reserved_word item.
    );
    (
        // idx 2
        // parser.lex.reserve.03
        // another string that is is_reserved_word
        Ident "->",
        Resword "->"
    );
    (
        // idx 3
        // parser.lex.reserve.04
        // a string that is not is_reserved_word
        Ident "at",
        Ident "at"
    );
    (
        // idx 4
        // parser.lex.reserve.05
        // a string that is already a Resword token
        Resword "if",
        Resword "if"   // Notice Resword stayed a Resword
    );
    |]
[<Test>]
[<TestCase(0, TestName = "parser.lex.reserve.01")>]
[<TestCase(1, TestName = "parser.lex.reserve.02")>]
[<TestCase(2, TestName = "parser.lex.reserve.03")>]
[<TestCase(3, TestName = "parser.lex.reserve.04")>]
[<TestCase(4, TestName = "parser.lex.reserve.05")>]
let ``function lex.reserve`` idx =
    let (input, _) = reserveValues.[idx]
    let (_, result) = reserveValues.[idx]

    let reserveResult = reserve input
//    printfn "input: %A" input
//    printfn "expected result: %A" result
//    printfn "function result: %A" reserveResult
    reserveResult |> assertEqual result

let stringof (p : ('a -> string * 'a)) : ('a -> string * 'a) =
    atleast 1 p |>> NHol.lib.end_itlist (+)

// The first string is what humans expect to read
// and the second string list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private stringofValues : (string * string list * (string list -> string * string list) * (string * string list))[] = [|
    (
        // idx 0
        // parser.lex.stringof.01
        // No input
        // throws noparse
        "",    // humans read this
        [],    // the stringof function reads this
        (some NHol.printer.isnum),
        ("",[])  // dummy value
    );
    (
        // idx 1
        // parser.lex.stringof.02
        // one number
        "1",
        ["1"],
        (some NHol.printer.isnum),
        ("1",[])
    );
    (
        // idx 2
        // parser.lex.stringof.03
        // two numbers
        "12",
        ["1";"2"],
        (some NHol.printer.isnum),
        ("12",[])
    );
    (
        // idx 3
        // parser.lex.stringof.04
        // three numbers
        "123",
        ["1";"2";"3"],
        (some NHol.printer.isnum),
        ("123",[])
    );
    (
        // idx 4
        // parser.lex.stringof.05
        // one number then one letter
        "1a",
        ["1";"a";],
        (some NHol.printer.isnum),
        ("1",["a"])
    );
    (
        // idx 5
        // parser.lex.stringof.06
        // two numbers then one letter
        "12a",
        ["1";"2";"a";],
        (some NHol.printer.isnum),
        ("12",["a"])
    );
    (
        // idx 6
        // parser.lex.stringof.07
        // three numbers then one letter
        "123a",
        ["1";"2";"3";"a";],
        (some NHol.printer.isnum),
        ("123",["a"])
    );
    (
        // idx 7
        // parser.lex.stringof.08
        // one letter then one number
        // thows noparse
        "a1",
        ["a";"1"],
        (some NHol.printer.isnum),
        ("",[])  // dummy value
    );
    (
        // idx 8
        // parser.lex.stringof.09
        // one symbol
        "#",
        ["#"],
        (some NHol.printer.issymb),
        ("#",[])
    );
    (
        // idx 9
        // parser.lex.stringof.10
        // two symbols
        "#=",
        ["#";"="],
        (some NHol.printer.issymb),
        ("#=",[])
    );
    (
        // idx 10
        // parser.lex.stringof.11
        // three symbols
        "#=?",
        ["#";"=";"?"],
        (some NHol.printer.issymb),
        ("#=?",[])
    );
    (
        // idx 11
        // parser.lex.stringof.12
        // one symbol then one letter
        "#a",
        ["#";"a";],
        (some NHol.printer.issymb),
        ("#",["a"])
    );
    (
        // idx 12
        // parser.lex.stringof.13
        // two symbols then one letter
        "#=a",
        ["#";"=";"a";],
        (some NHol.printer.issymb),
        ("#=",["a"])
    );
    (
        // idx 13
        // parser.lex.stringof.14
        // three symbols then one letter
        "#=?a",
        ["#";"=";"?";"a";],
        (some NHol.printer.issymb),
        ("#=?",["a"])
    );
    (
        // idx 14
        // parser.lex.stringof.15
        // one letter then one symbol
        // throws noparse
        "a#",
        ["a";"#"],
        (some NHol.printer.issymb),
        ("",[])  // dummy value
    );
    |]
[<Test>]
[<TestCase(0, TestName = "parser.lex.stringof.01", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.lex.stringof.02")>]
[<TestCase(2, TestName = "parser.lex.stringof.03")>]
[<TestCase(3, TestName = "parser.lex.stringof.04")>]
[<TestCase(4, TestName = "parser.lex.stringof.05")>]
[<TestCase(5, TestName = "parser.lex.stringof.06")>]
[<TestCase(6, TestName = "parser.lex.stringof.07")>]
[<TestCase(7, TestName = "parser.lex.stringof.08", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(8, TestName = "parser.lex.stringof.09")>]
[<TestCase(9, TestName = "parser.lex.stringof.10")>]
[<TestCase(10, TestName = "parser.lex.stringof.11")>]
[<TestCase(11, TestName = "parser.lex.stringof.12")>]
[<TestCase(12, TestName = "parser.lex.stringof.13")>]
[<TestCase(13, TestName = "parser.lex.stringof.14")>]
[<TestCase(14, TestName = "parser.lex.stringof.15", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
let ``function lex.stringof`` idx =
    let (externalForm, _, _, _) = stringofValues.[idx]
    let (_, internalForm, _, _) = stringofValues.[idx]
    let (_, _, parser, _ ) = stringofValues.[idx]
    let (_, _, _, (currentResult , restResult)) = stringofValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    let stringParser = stringof parser
    let (current,rest) = stringParser internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    current |> assertEqual currentResult
    rest |> assertEqual restResult

// Note alnum includes ' and _
let simple_ident : (string list -> string * string list) =
    stringof(some NHol.printer.isalnum) <|> stringof(some NHol.printer.issymb)

// The first string is what humans expect to read
// and the second string list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private simple_identValues : (string * string list * (string * string list))[] = [|
    (
        // idx 0
        // parser.lex.simple_ident.01
        // No input
        // throws noparse
        "",    // humans read this
        [],    // the simple_ident function reads this
        ("",[])  // dummy value
    );
    (
        // idx 1
        // parser.lex.simple_ident.02
        // one number
        "1",
        ["1"],
        ("1",[])
    );
    (
        // idx 2
        // parser.lex.simple_ident.03
        // one letter
        "a",
        ["a"],
        ("a",[])
    );
    (
        // idx 3
        // parser.lex.simple_ident.04
        // one symbol
        "#",
        ["#"],
        ("#",[])
    );
    (
        // idx 4
        // parser.lex.simple_ident.05
        // one fowrad slash
        "/",
        ["/"],
        ("/",[])
    );
    (
        // idx 5
        // parser.lex.simple_ident.06
        // one underscore
        "_",
        ["_"],
        ("_",[])
    );
    (
        // idx 6
        // parser.lex.simple_ident.07
        // one single quote
        "'",
        ["'"],
        ("'",[])
    );
    (
        // idx 7
        // parser.lex.simple_ident.08
        // two numbers
        "12",
        ["1";"2"],
        ("12",[])
    );
    (
        // idx 8
        // parser.lex.simple_ident.09
        // two letters
        "ab",
        ["a";"b"],
        ("ab",[])
    );
    (
        // idx 9
        // parser.lex.simple_ident.10
        // two forward slash
        "//",
        ["/";"/"],
        ("//",[])
    );
    (
        // idx 10
        // parser.lex.simple_ident.11
        // two #s
        "##",
        ["#";"#"],
        ("##",[])
    );
    (
        // idx 11
        // parser.lex.simple_ident.12
        // two underscores
        "__",
        ["_";"_"],
        ("__",[])
    );
    (
        // idx 12
        // parser.lex.simple_ident.13
        // two single quotes
        "''",
        ["'";"'"],
        ("''",[])
    );
    (
        // idx 13
        // parser.lex.simple_ident.14
        // one letter then one number
        "a1",
        ["a";"1"],
        ("a1",[])
    );
    (
        // idx 14
        // parser.lex.simple_ident.15
        // one letter then one #
        "a#",
        ["a";"#"],
        ("a",["#"])
    );
    (
        // idx 15
        // parser.lex.simple_ident.16
        // one letter then one forward slash
        "a/",
        ["a";"/"],
        ("a",["/"])
    );
    (
        // idx 16
        // parser.lex.simple_ident.17
        // one letter then one _
        "a_",
        ["a";"_"],
        ("a_",[])
    );
    (
        // idx 17
        // parser.lex.simple_ident.18
        // one letter then one single quote
        "a'",
        ["a";"'"],
        ("a'",[])
    );
    (
        // idx 18
        // parser.lex.simple_ident.19
        // one number then one letter
        "1a",
        ["1";"a"],
        ("1a",[])
    );
    (
        // idx 19
        // parser.lex.simple_ident.20
        // one number then one #
        "1#",
        ["1";"#"],
        ("1",["#"])
    );
    (
        // idx 20
        // parser.lex.simple_ident.21
        // one number then one forward slash
        "1/",
        ["1";"/"],
        ("1",["/"])
    );
    (
        // idx 21
        // parser.lex.simple_ident.22
        // one number then one underscore
        "1_",
        ["1";"_"],
        ("1_",[])
    );
    (
        // idx 22
        // parser.lex.simple_ident.23
        // one number then one single quote
        "1'",
        ["1";"'"],
        ("1'",[])
    );
    (
        // idx 23
        // parser.lex.simple_ident.24
        // one # then one letter
        "#a",
        ["#";"a"],
        ("#",["a"])
    );
    (
        // idx 24
        // parser.lex.simple_ident.25
        // one # then one number
        "#1",
        ["#";"1"],
        ("#",["1"])
    );
    (
        // idx 25
        // parser.lex.simple_ident.26
        // one # then one forward slash
        "#/",
        ["#";"/"],
        ("#/",[])
    );
    (
        // idx 26
        // parser.lex.simple_ident.27
        // one # then one underscore
        "#_",
        ["#";"_"],
        ("#",["_"])
    );
    (
        // idx 27
        // parser.lex.simple_ident.28
        // one # then one single quote
        "#'",
        ["#";"'"],
        ("#",["'"])
    );
    (
        // idx 28
        // parser.lex.simple_ident.29
        // one forward slash then one letter
        "/a",
        ["/";"a"],
        ("/",["a"])
    );
    (
        // idx 29
        // parser.lex.simple_ident.30
        // one forward slash then one number
        "/1",
        ["/";"1"],
        ("/",["1"])
    );
    (
        // idx 30
        // parser.lex.simple_ident.31
        // one forward slash then one #
        "/#",
        ["/";"#"],
        ("/#",[])
    );
    (
        // idx 31
        // parser.lex.simple_ident.32
        // one forward slash then one underscore
        "/_",
        ["/";"_"],
        ("/",["_"])
    );
    (
        // idx 32
        // parser.lex.simple_ident.33
        // one forward slash then one underscore
        "/'",
        ["/";"'"],
        ("/",["'"])
    );
    (
        // idx 33
        // parser.lex.simple_ident.34
        // one underscore then one letter
        "_a",
        ["_";"a"],
        ("_a",[])
    );
    (
        // idx 34
        // parser.lex.simple_ident.35
        // one underscore then one number
        "_1",
        ["_";"1"],
        ("_1",[])
    );
    (
        // idx 35
        // parser.lex.simple_ident.36
        // one underscore then one #
        "_#",
        ["_";"#"],
        ("_",["#"])
    );
    (
        // idx 36
        // parser.lex.simple_ident.37
        // one underscore then one forward slash
        "_/",
        ["_";"/"],
        ("_",["/"])
    );
    (
        // idx 37
        // parser.lex.simple_ident.38
        // one underscore then one single quote
        "_'",
        ["_";"'"],
        ("_'",[])
    );
    (
        // idx 38
        // parser.lex.simple_ident.39
        // one single quote then one letter
        "'a",
        ["'";"a"],
        ("'a",[])
    );
    (
        // idx 39
        // parser.lex.simple_ident.40
        // one single quote then one number
        "'1",
        ["'";"1"],
        ("'1",[])
    );
    (
        // idx 40
        // parser.lex.simple_ident.41
        // one single quote then one #
        "'#",
        ["'";"#"],
        ("'",["#"])
    );
    (
        // idx 41
        // parser.lex.simple_ident.42
        // one single quote then one forward slash
        "'/",
        ["'";"/"],
        ("'",["/"])
    );
    (
        // idx 42
        // parser.lex.simple_ident.43
        // one single quote then one underscore
        "'_",
        ["'";"_"],
        ("'_",[])
    );
    |]
[<Test>]
[<TestCase(0, TestName = "parser.lex.simple_ident.01", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.lex.simple_ident.02")>]
[<TestCase(2, TestName = "parser.lex.simple_ident.03")>]
[<TestCase(3, TestName = "parser.lex.simple_ident.04")>]
[<TestCase(4, TestName = "parser.lex.simple_ident.05")>]
[<TestCase(5, TestName = "parser.lex.simple_ident.06")>]
[<TestCase(6, TestName = "parser.lex.simple_ident.07")>]
[<TestCase(7, TestName = "parser.lex.simple_ident.08")>]
[<TestCase(8, TestName = "parser.lex.simple_ident.09")>]
[<TestCase(9, TestName = "parser.lex.simple_ident.10")>]
[<TestCase(10, TestName = "parser.lex.simple_ident.11")>]
[<TestCase(11, TestName = "parser.lex.simple_ident.12")>]
[<TestCase(12, TestName = "parser.lex.simple_ident.13")>]
[<TestCase(13, TestName = "parser.lex.simple_ident.14")>]
[<TestCase(14, TestName = "parser.lex.simple_ident.15")>]
[<TestCase(15, TestName = "parser.lex.simple_ident.16")>]
[<TestCase(16, TestName = "parser.lex.simple_ident.17")>]
[<TestCase(17, TestName = "parser.lex.simple_ident.18")>]
[<TestCase(18, TestName = "parser.lex.simple_ident.19")>]
[<TestCase(19, TestName = "parser.lex.simple_ident.20")>]
[<TestCase(20, TestName = "parser.lex.simple_ident.21")>]
[<TestCase(21, TestName = "parser.lex.simple_ident.22")>]
[<TestCase(22, TestName = "parser.lex.simple_ident.23")>]
[<TestCase(23, TestName = "parser.lex.simple_ident.24")>]
[<TestCase(24, TestName = "parser.lex.simple_ident.25")>]
[<TestCase(25, TestName = "parser.lex.simple_ident.26")>]
[<TestCase(26, TestName = "parser.lex.simple_ident.27")>]
[<TestCase(27, TestName = "parser.lex.simple_ident.28")>]
[<TestCase(28, TestName = "parser.lex.simple_ident.29")>]
[<TestCase(29, TestName = "parser.lex.simple_ident.30")>]
[<TestCase(30, TestName = "parser.lex.simple_ident.31")>]
[<TestCase(31, TestName = "parser.lex.simple_ident.32")>]
[<TestCase(32, TestName = "parser.lex.simple_ident.33")>]
[<TestCase(33, TestName = "parser.lex.simple_ident.34")>]
[<TestCase(34, TestName = "parser.lex.simple_ident.35")>]
[<TestCase(35, TestName = "parser.lex.simple_ident.36")>]
[<TestCase(36, TestName = "parser.lex.simple_ident.37")>]
[<TestCase(37, TestName = "parser.lex.simple_ident.38")>]
[<TestCase(38, TestName = "parser.lex.simple_ident.39")>]
[<TestCase(39, TestName = "parser.lex.simple_ident.40")>]
[<TestCase(40, TestName = "parser.lex.simple_ident.41")>]
[<TestCase(41, TestName = "parser.lex.simple_ident.42")>]
[<TestCase(42, TestName = "parser.lex.simple_ident.43")>]
let ``function lex.simple_ident`` idx =
    let (externalForm, _, _) = simple_identValues.[idx]
    let (_, internalForm, _) = simple_identValues.[idx]
    let (_, _, (currentResult , restResult)) = simple_identValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    let (current,rest) = simple_ident internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    current |> assertEqual currentResult
    rest |> assertEqual restResult

let undertail : (string list -> string * string list) = stringof(a "_") .>>. possibly simple_ident |>> collect

// The first string is what humans expect to read
// and the second string list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private undertailValues : (string * string list * (string * string list))[] = [|
    (
        // idx 0
        // parser.lex.undertail.01
        // No input
        // throws noparse
        "",    // humans read this
        [],    // the undertail function reads this
        ("",[])  // dummy value
    );
    (
        // idx 1
        // parser.lex.undertail.02
        // one underscrore then one number
        "_1",
        ["_";"1"],
        ("_1",[])
    );
    (
        // idx 2
        // parser.lex.undertail.03
        // one underscrore then one letter
        "_a",
        ["_";"a"],
        ("_a",[])
    );
    (
        // idx 3
        // parser.lex.undertail.04
        // one underscrore then one symbol
        "_#",
        ["_";"#"],
        ("_#",[])
    );
    (
        // idx 4
        // parser.lex.undertail.05
        // one underscrore then one fowrad slash
        "_/",
        ["_";"/"],
        ("_/",[])
    );
    (
        // idx 5
        // parser.lex.undertail.06
        // two underscrores
        "__",
        ["_";"_"],
        ("__",[])
    );
    (
        // idx 6
        // parser.lex.undertail.07
        // one underscrore then one single quote
        "_'",
        ["_";"'"],
        ("_'",[])
    );
    (
        // idx 7
        // parser.lex.undertail.08
        // one underscrore then two numbers
        "_12",
        ["_";"1";"2"],
        ("_12",[])
    );
    (
        // idx 8
        // parser.lex.undertail.09
        // one underscrore then two letters
        "_ab",
        ["_";"a";"b"],
        ("_ab",[])
    );
    (
        // idx 9
        // parser.lex.undertail.10
        // one underscrore then two forward slash
        "_//",
        ["_";"/";"/"],
        ("_//",[])
    );
    (
        // idx 10
        // parser.lex.undertail.11
        // one underscrore then two #s
        "_##",
        ["_";"#";"#"],
        ("_##",[])
    );
    (
        // idx 11
        // parser.lex.undertail.12
        // one underscrore then two underscores
        "___",
        ["_";"_";"_"],
        ("___",[])
    );
    (
        // idx 12
        // parser.lex.undertail.13
        // one underscrore then two single quotes
        "_''",
        ["_";"'";"'"],
        ("_''",[])
    );
    (
        // idx 13
        // parser.lex.undertail.14
        // one underscrore then one letter then one number
        "_a1",
        ["_";"a";"1"],
        ("_a1",[])
    );
    (
        // idx 14
        // parser.lex.undertail.15
        // one underscrore then one letter then one #
        "_a#",
        ["_";"a";"#"],
        ("_a",["#"])
    );
    (
        // idx 15
        // parser.lex.undertail.16
        // one underscrore then one letter then one forward slash
        "_a/",
        ["_";"a";"/"],
        ("_a",["/"])
    );
    (
        // idx 16
        // parser.lex.undertail.17
        // one underscrore then one letter then one _
        "_a_",
        ["_";"a";"_"],
        ("_a_",[])
    );
    (
        // idx 17
        // parser.lex.undertail.18
        // one underscrore then one letter then one single quote
        "_a'",
        ["_";"a";"'"],
        ("_a'",[])
    );
    (
        // idx 18
        // parser.lex.undertail.19
        // one underscrore then one number then one letter
        "_1a",
        ["_";"1";"a"],
        ("_1a",[])
    );
    (
        // idx 19
        // parser.lex.undertail.20
        // one underscrore then one number then one #
        "_1#",
        ["_";"1";"#"],
        ("_1",["#"])
    );
    (
        // idx 20
        // parser.lex.undertail.21
        // one underscrore then one number then one forward slash
        "_1/",
        ["_";"1";"/"],
        ("_1",["/"])
    );
    (
        // idx 21
        // parser.lex.undertail.22
        // one underscrore then one number then one underscore
        "_1_",
        ["_";"1";"_"],
        ("_1_",[])
    );
    (
        // idx 22
        // parser.lex.undertail.23
        // one underscrore then one number then one single quote
        "_1'",
        ["_";"1";"'"],
        ("_1'",[])
    );
    (
        // idx 23
        // parser.lex.undertail.24
        // one underscrore then one # then one letter
        "_#a",
        ["_";"#";"a"],
        ("_#",["a"])
    );
    (
        // idx 24
        // parser.lex.undertail.25
        // one underscrore then one # then one number
        "_#1",
        ["_";"#";"1"],
        ("_#",["1"])
    );
    (
        // idx 25
        // parser.lex.undertail.26
        // one underscrore then one # then one forward slash
        "_#/",
        ["_";"#";"/"],
        ("_#/",[])
    );
    (
        // idx 26
        // parser.lex.undertail.27
        // one underscrore then one # then one underscore
        "_#_",
        ["_";"#";"_"],
        ("_#",["_"])
    );
    (
        // idx 27
        // parser.lex.undertail.28
        // one underscrore then one # then one single quote
        "_#'",
        ["_";"#";"'"],
        ("_#",["'"])
    );
    (
        // idx 28
        // parser.lex.undertail.29
        // one underscrore then one forward slash then one letter
        "_/a",
        ["_";"/";"a"],
        ("_/",["a"])
    );
    (
        // idx 29
        // parser.lex.undertail.30
        // one underscrore then one forward slash then one number
        "_/1",
        ["_";"/";"1"],
        ("_/",["1"])
    );
    (
        // idx 30
        // parser.lex.undertail.31
        // one underscrore then one forward slash then one #
        "_/#",
        ["_";"/";"#"],
        ("_/#",[])
    );
    (
        // idx 31
        // parser.lex.undertail.32
        // one underscrore then one forward slash then one underscore
        "_/_",
        ["_";"/";"_"],
        ("_/",["_"])
    );
    (
        // idx 32
        // parser.lex.undertail.33
        // one underscrore then one forward slash then one underscore
        "_/'",
        ["_";"/";"'"],
        ("_/",["'"])
    );
    (
        // idx 33
        // parser.lex.undertail.34
        // two underscores then one letter
        "__a",
        ["_";"_";"a"],
        ("__a",[])
    );
    (
        // idx 34
        // parser.lex.undertail.35
        // two underscores then one number
        "__1",
        ["_";"_";"1"],
        ("__1",[])
    );
    (
        // idx 35
        // parser.lex.undertail.36
        // two underscores then one #
        "__#",
        ["_";"_";"#"],
        ("__#",[])    // Notice: change from simple_ident
    );
    (
        // idx 36
        // parser.lex.undertail.37
        // two underscores then one forward slash
        "__/",
        ["_";"_";"/"],
        ("__/",[])    // Notice: change from simple_ident
    );
    (
        // idx 37
        // parser.lex.undertail.38
        // two underscores then one single quote
        "__'",
        ["_";"_";"'"],
        ("__'",[])
    );
    (
        // idx 38
        // parser.lex.undertail.39
        // one underscrore then one single quote then one letter
        "_'a",
        ["_";"'";"a"],
        ("_'a",[])
    );
    (
        // idx 39
        // parser.lex.undertail.40
        // one underscrore then one single quote then one number
        "_'1",
        ["_";"'";"1"],
        ("_'1",[])
    );
    (
        // idx 40
        // parser.lex.undertail.41
        // one underscrore then one single quote then one #
        "_'#",
        ["_";"'";"#"],
        ("_'",["#"])
    );
    (
        // idx 41
        // parser.lex.undertail.42
        // one underscrore then one single quote then one forward slash
        "_'/",
        ["_";"'";"/"],
        ("_'",["/"])
    );
    (
        // idx 42
        // parser.lex.undertail.43
        // one underscrore then one single quote then one underscore
        "_'_",
        ["_";"'";"_"],
        ("_'_",[])
    );
    (
        // idx 43
        // parser.lex.undertail.44
        // one number
        "1",
        ["1"],
        ("_1",[])
    );
    (
        // idx 44
        // parser.lex.undertail.45
        // one letter
        "a",
        ["a"],
        ("_a",[])
    );
    (
        // idx 45
        // parser.lex.undertail.46
        // one symbol
        "#",
        ["#"],
        ("_#",[])
    );
    (
        // idx 46
        // parser.lex.undertail.47
        // one foward slash
        "/",
        ["/"],
        ("_/",[])
    );
    (
        // idx 47
        // parser.lex.undertail.48
        // one single quote
        "'",
        ["'"],
        ("_'",[])
    );

    |]
[<Test>]
[<TestCase(0, TestName = "parser.lex.undertail.01", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.lex.undertail.02")>]
[<TestCase(2, TestName = "parser.lex.undertail.03")>]
[<TestCase(3, TestName = "parser.lex.undertail.04")>]
[<TestCase(4, TestName = "parser.lex.undertail.05")>]
[<TestCase(5, TestName = "parser.lex.undertail.06")>]
[<TestCase(6, TestName = "parser.lex.undertail.07")>]
[<TestCase(7, TestName = "parser.lex.undertail.08")>]
[<TestCase(8, TestName = "parser.lex.undertail.09")>]
[<TestCase(9, TestName = "parser.lex.undertail.10")>]
[<TestCase(10, TestName = "parser.lex.undertail.11")>]
[<TestCase(11, TestName = "parser.lex.undertail.12")>]
[<TestCase(12, TestName = "parser.lex.undertail.13")>]
[<TestCase(13, TestName = "parser.lex.undertail.14")>]
[<TestCase(14, TestName = "parser.lex.undertail.15")>]
[<TestCase(15, TestName = "parser.lex.undertail.16")>]
[<TestCase(16, TestName = "parser.lex.undertail.17")>]
[<TestCase(17, TestName = "parser.lex.undertail.18")>]
[<TestCase(18, TestName = "parser.lex.undertail.19")>]
[<TestCase(19, TestName = "parser.lex.undertail.20")>]
[<TestCase(20, TestName = "parser.lex.undertail.21")>]
[<TestCase(21, TestName = "parser.lex.undertail.22")>]
[<TestCase(22, TestName = "parser.lex.undertail.23")>]
[<TestCase(23, TestName = "parser.lex.undertail.24")>]
[<TestCase(24, TestName = "parser.lex.undertail.25")>]
[<TestCase(25, TestName = "parser.lex.undertail.26")>]
[<TestCase(26, TestName = "parser.lex.undertail.27")>]
[<TestCase(27, TestName = "parser.lex.undertail.28")>]
[<TestCase(28, TestName = "parser.lex.undertail.29")>]
[<TestCase(29, TestName = "parser.lex.undertail.30")>]
[<TestCase(30, TestName = "parser.lex.undertail.31")>]
[<TestCase(31, TestName = "parser.lex.undertail.32")>]
[<TestCase(32, TestName = "parser.lex.undertail.33")>]
[<TestCase(33, TestName = "parser.lex.undertail.34")>]
[<TestCase(34, TestName = "parser.lex.undertail.35")>]
[<TestCase(35, TestName = "parser.lex.undertail.36")>]
[<TestCase(36, TestName = "parser.lex.undertail.37")>]
[<TestCase(37, TestName = "parser.lex.undertail.38")>]
[<TestCase(38, TestName = "parser.lex.undertail.39")>]
[<TestCase(39, TestName = "parser.lex.undertail.40")>]
[<TestCase(40, TestName = "parser.lex.undertail.41")>]
[<TestCase(41, TestName = "parser.lex.undertail.42")>]
[<TestCase(42, TestName = "parser.lex.undertail.43")>]
[<TestCase(43, TestName = "parser.lex.undertail.44", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(44, TestName = "parser.lex.undertail.45", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(45, TestName = "parser.lex.undertail.46", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(46, TestName = "parser.lex.undertail.47", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(47, TestName = "parser.lex.undertail.48", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]

let ``function lex.undertail`` idx =
    let (externalForm, _, _) = undertailValues.[idx]
    let (_, internalForm, _) = undertailValues.[idx]
    let (_, _, (currentResult , restResult)) = undertailValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    let (current,rest) = undertail internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    current |> assertEqual currentResult
    rest |> assertEqual restResult

let ident : (string list -> string * string list)= (undertail <|> simple_ident) .>>. many undertail |>> collect

// The first string is what humans expect to read
// and the second string list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private identValues : (string * string list * (string * string list))[] = [|
    (
        // idx 0
        // parser.lex.ident.01
        // No input
        // throws noparse
        "",    // humans read this
        [],    // the ident function reads this
        ("",[])  // dummy value
    );
    (
        // idx 1
        // parser.lex.ident.02
        // one number
        "1",
        ["1"],
        ("1",[])
    );
    (
        // idx 2
        // parser.lex.ident.03
        // one letter
        "a",
        ["a"],
        ("a",[])
    );
    (
        // idx 3
        // parser.lex.ident.04
        // one symbol
        "#",
        ["#"],
        ("#",[])
    );
    (
        // idx 4
        // parser.lex.ident.05
        // one fowrad slash
        "/",
        ["/"],
        ("/",[])
    );
    (
        // idx 5
        // parser.lex.ident.06
        // one underscore
        "_",
        ["_"],
        ("_",[])
    );
    (
        // idx 6
        // parser.lex.ident.07
        // one single quote
        "'",
        ["'"],
        ("'",[])
    );
    (
        // idx 7
        // parser.lex.ident.08
        // two numbers
        "12",
        ["1";"2"],
        ("12",[])
    );
    (
        // idx 8
        // parser.lex.ident.09
        // two letters
        "ab",
        ["a";"b"],
        ("ab",[])
    );
    (
        // idx 9
        // parser.lex.ident.10
        // two forward slash
        "//",
        ["/";"/"],
        ("//",[])
    );
    (
        // idx 10
        // parser.lex.ident.11
        // two #s
        "##",
        ["#";"#"],
        ("##",[])
    );
    (
        // idx 11
        // parser.lex.ident.12
        // two underscores
        "__",
        ["_";"_"],
        ("__",[])
    );
    (
        // idx 12
        // parser.lex.ident.13
        // two single quotes
        "''",
        ["'";"'"],
        ("''",[])
    );
    (
        // idx 13
        // parser.lex.ident.14
        // one letter then one number
        "a1",
        ["a";"1"],
        ("a1",[])
    );
    (
        // idx 14
        // parser.lex.ident.15
        // one letter then one #
        "a#",
        ["a";"#"],
        ("a",["#"])
    );
    (
        // idx 15
        // parser.lex.ident.16
        // one letter then one forward slash
        "a/",
        ["a";"/"],
        ("a",["/"])
    );
    (
        // idx 16
        // parser.lex.ident.17
        // one letter then one _
        "a_",
        ["a";"_"],
        ("a_",[])
    );
    (
        // idx 17
        // parser.lex.ident.18
        // one letter then one single quote
        "a'",
        ["a";"'"],
        ("a'",[])
    );
    (
        // idx 18
        // parser.lex.ident.19
        // one number then one letter
        "1a",
        ["1";"a"],
        ("1a",[])
    );
    (
        // idx 19
        // parser.lex.ident.20
        // one number then one #
        "1#",
        ["1";"#"],
        ("1",["#"])
    );
    (
        // idx 20
        // parser.lex.ident.21
        // one number then one forward slash
        "1/",
        ["1";"/"],
        ("1",["/"])
    );
    (
        // idx 21
        // parser.lex.ident.22
        // one number then one underscore
        "1_",
        ["1";"_"],
        ("1_",[])
    );
    (
        // idx 22
        // parser.lex.ident.23
        // one number then one single quote
        "1'",
        ["1";"'"],
        ("1'",[])
    );
    (
        // idx 23
        // parser.lex.ident.24
        // one # then one letter
        "#a",
        ["#";"a"],
        ("#",["a"])
    );
    (
        // idx 24
        // parser.lex.ident.25
        // one # then one number
        "#1",
        ["#";"1"],
        ("#",["1"])
    );
    (
        // idx 25
        // parser.lex.ident.26
        // one # then one forward slash
        "#/",
        ["#";"/"],
        ("#/",[])
    );
    (
        // idx 26
        // parser.lex.ident.27
        // one # then one underscore
        "#_",
        ["#";"_"],
        ("#_",[])
    );
    (
        // idx 27
        // parser.lex.ident.28
        // one # then one single quote
        "#'",
        ["#";"'"],
        ("#",["'"])
    );
    (
        // idx 28
        // parser.lex.ident.29
        // one forward slash then one letter
        "/a",
        ["/";"a"],
        ("/",["a"])
    );
    (
        // idx 29
        // parser.lex.ident.30
        // one forward slash then one number
        "/1",
        ["/";"1"],
        ("/",["1"])
    );
    (
        // idx 30
        // parser.lex.ident.31
        // one forward slash then one #
        "/#",
        ["/";"#"],
        ("/#",[])
    );
    (
        // idx 31
        // parser.lex.ident.32
        // one forward slash then one underscore
        "/_",
        ["/";"_"],
        ("/_",[])
    );
    (
        // idx 32
        // parser.lex.ident.33
        // one forward slash then one underscore
        "/'",
        ["/";"'"],
        ("/",["'"])
    );
    (
        // idx 33
        // parser.lex.ident.34
        // one underscore then one letter
        "_a",
        ["_";"a"],
        ("_a",[])
    );
    (
        // idx 34
        // parser.lex.ident.35
        // one underscore then one number
        "_1",
        ["_";"1"],
        ("_1",[])
    );
    (
        // idx 35
        // parser.lex.ident.36
        // one underscore then one #
        "_#",
        ["_";"#"],
        ("_#",[])
    );
    (
        // idx 36
        // parser.lex.ident.37
        // one underscore then one forward slash
        "_/",
        ["_";"/"],
        ("_/",[])
    );
    (
        // idx 37
        // parser.lex.ident.38
        // one underscore then one single quote
        "_'",
        ["_";"'"],
        ("_'",[])
    );
    (
        // idx 38
        // parser.lex.ident.39
        // one single quote then one letter
        "'a",
        ["'";"a"],
        ("'a",[])
    );
    (
        // idx 39
        // parser.lex.ident.40
        // one single quote then one number
        "'1",
        ["'";"1"],
        ("'1",[])
    );
    (
        // idx 40
        // parser.lex.ident.41
        // one single quote then one #
        "'#",
        ["'";"#"],
        ("'",["#"])
    );
    (
        // idx 41
        // parser.lex.ident.42
        // one single quote then one forward slash
        "'/",
        ["'";"/"],
        ("'",["/"])
    );
    (
        // idx 42
        // parser.lex.ident.43
        // one single quote then one underscore
        "'_",
        ["'";"_"],
        ("'_",[])
    );
    (
        // idx 43
        // parser.lex.ident.44
        // one underscore then one number
        "_1",
        ["_";"1"],
        ("_1",[])
    );
    (
        // idx 44
        // parser.lex.ident.45
        // one underscore then one letter
        "_a",
        ["_";"a"],
        ("_a",[])
    );
    (
        // idx 45
        // parser.lex.ident.46
        // one underscore then one symbol
        "_#",
        ["_";"#"],
        ("_#",[])
    );
    (
        // idx 46
        // parser.lex.ident.47
        // one underscore then one fowrad slash
        "_/",
        ["_";"/"],
        ("_/",[])
    );
    (
        // idx 47
        // parser.lex.ident.48
        // one underscore then one single quote
        "_'",
        ["_";"'"],
        ("_'",[])
    );
    (
        // idx 48
        // parser.lex.ident.49
        // one underscore then two numbers
        "_12",
        ["_";"1";"2"],
        ("_12",[])
    );
    (
        // idx 49
        // parser.lex.ident.50
        // one underscore then two letters
        "_ab",
        ["_";"a";"b"],
        ("_ab",[])
    );
    (
        // idx 50
        // parser.lex.ident.51
        // one underscore then two forward slash
        "_//",
        ["_";"/";"/"],
        ("_//",[])
    );
    (
        // idx 51
        // parser.lex.ident.52
        // one underscore then two #s
        "_##",
        ["_";"#";"#"],
        ("_##",[])
    );
    (
        // idx 52
        // parser.lex.ident.53
        // one underscore then two underscores
        "___",
        ["_";"_";"_"],
        ("___",[])
    );
    (
        // idx 53
        // parser.lex.ident.54
        // one underscore then two single quotes
        "_''",
        ["_";"'";"'"],
        ("_''",[])
    );
    (
        // idx 54
        // parser.lex.ident.55
        // one underscore then one letter then one number
        "_a1",
        ["_";"a";"1"],
        ("_a1",[])
    );
    (
        // idx 55
        // parser.lex.ident.56
        // one underscore then one letter then one #
        "_a#",
        ["_";"a";"#"],
        ("_a",["#"])
    );
    (
        // idx 56
        // parser.lex.ident.57
        // one underscore then one letter then one forward slash
        "_a/",
        ["_";"a";"/"],
        ("_a",["/"])
    );
    (
        // idx 57
        // parser.lex.ident.58
        // one underscore then one letter then one _
        "_a_",
        ["_";"a";"_"],
        ("_a_",[])
    );
    (
        // idx 58
        // parser.lex.ident.59
        // one underscore then one letter then one single quote
        "_a'",
        ["_";"a";"'"],
        ("_a'",[])
    );
    (
        // idx 59
        // parser.lex.ident.60
        // one underscore then one number then one letter
        "_1a",
        ["_";"1";"a"],
        ("_1a",[])
    );
    (
        // idx 60
        // parser.lex.ident.61
        // one underscore then one number then one #
        "_1#",
        ["_";"1";"#"],
        ("_1",["#"])
    );
    (
        // idx 61
        // parser.lex.ident.62
        // one underscore then one number then one forward slash
        "_1/",
        ["_";"1";"/"],
        ("_1",["/"])
    );
    (
        // idx 62
        // parser.lex.ident.63
        // one underscore then one number then one underscore
        "_1_",
        ["_";"1";"_"],
        ("_1_",[])
    );
    (
        // idx 63
        // parser.lex.ident.64
        // one underscore then one number then one single quote
        "_1'",
        ["_";"1";"'"],
        ("_1'",[])
    );
    (
        // idx 64
        // parser.lex.ident.65
        // one underscore then one # then one letter
        "_#a",
        ["_";"#";"a"],
        ("_#",["a"])
    );
    (
        // idx 65
        // parser.lex.ident.66
        // one underscore then one # then one number
        "_#1",
        ["_";"#";"1"],
        ("_#",["1"])
    );
    (
        // idx 66
        // parser.lex.ident.67
        // one underscore then one # then one forward slash
        "_#/",
        ["_";"#";"/"],
        ("_#/",[])
    );
    (
        // idx 67
        // parser.lex.ident.68
        // one underscore then one # then one underscore
        "_#_",
        ["_";"#";"_"],
        ("_#_",[])
    );
    (
        // idx 68
        // parser.lex.ident.69
        // one underscore then one # then one single quote
        "_#'",
        ["_";"#";"'"],
        ("_#",["'"])
    );
    (
        // idx 69
        // parser.lex.ident.70
        // one underscore then one forward slash then one letter
        "_/a",
        ["_";"/";"a"],
        ("_/",["a"])
    );
    (
        // idx 70
        // parser.lex.ident.71
        // one underscore then one forward slash then one number
        "_/1",
        ["_";"/";"1"],
        ("_/",["1"])
    );
    (
        // idx 71
        // parser.lex.ident.72
        // one underscore then one forward slash then one #
        "_/#",
        ["_";"/";"#"],
        ("_/#",[])
    );
    (
        // idx 72
        // parser.lex.ident.73
        // one underscore then one forward slash then one underscore
        "_/_",
        ["_";"/";"_"],
        ("_/_",[])
    );
    (
        // idx 73
        // parser.lex.ident.74
        // one underscore then one forward slash then one underscore
        "_/'",
        ["_";"/";"'"],
        ("_/",["'"])
    );
    (
        // idx 74
        // parser.lex.ident.75
        // one underscore then one underscore then one letter
        "__a",
        ["_";"_";"a"],
        ("__a",[])
    );
    (
        // idx 75
        // parser.lex.ident.76
        // one underscore then one underscore then one number
        "__1",
        ["_";"_";"1"],
        ("__1",[])
    );
    (
        // idx 76
        // parser.lex.ident.77
        // one underscore then one underscore then one #
        "__#",
        ["_";"_";"#"],
        ("__#",[])
    );
    (
        // idx 77
        // parser.lex.ident.78
        // one underscore then one underscore then one forward slash
        "__/",
        ["_";"_";"/"],
        ("__/",[])
    );
    (
        // idx 78
        // parser.lex.ident.79
        // one underscore then one underscore then one single quote
        "__'",
        ["_";"_";"'"],
        ("__'",[])
    );
    (
        // idx 79
        // parser.lex.ident.80
        // one underscore then one single quote then one letter
        "_'a",
        ["_";"'";"a"],
        ("_'a",[])
    );
    (
        // idx 80
        // parser.lex.ident.81
        // one underscore then one single quote then one number
        "_'1",
        ["_";"'";"1"],
        ("_'1",[])
    );
    (
        // idx 81
        // parser.lex.ident.82
        // one underscore then one single quote then one #
        "_'#",
        ["_";"'";"#"],
        ("_'",["#"])
    );
    (
        // idx 82
        // parser.lex.ident.83
        // one underscore then one single quote then one forward slash
        "_'/",
        ["_";"'";"/"],
        ("_'",["/"])
    );
    (
        // idx 83
        // parser.lex.ident.84
        // one underscore then one single quote then one underscore
        "_'_",
        ["_";"'";"_"],
        ("_'_",[])
    );

    |]
[<Test>]
[<TestCase(0, TestName = "parser.lex.ident.01", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.lex.ident.02")>]
[<TestCase(2, TestName = "parser.lex.ident.03")>]
[<TestCase(3, TestName = "parser.lex.ident.04")>]
[<TestCase(4, TestName = "parser.lex.ident.05")>]
[<TestCase(5, TestName = "parser.lex.ident.06")>]
[<TestCase(6, TestName = "parser.lex.ident.07")>]
[<TestCase(7, TestName = "parser.lex.ident.08")>]
[<TestCase(8, TestName = "parser.lex.ident.09")>]
[<TestCase(9, TestName = "parser.lex.ident.10")>]
[<TestCase(10, TestName = "parser.lex.ident.11")>]
[<TestCase(11, TestName = "parser.lex.ident.12")>]
[<TestCase(12, TestName = "parser.lex.ident.13")>]
[<TestCase(13, TestName = "parser.lex.ident.14")>]
[<TestCase(14, TestName = "parser.lex.ident.15")>]
[<TestCase(15, TestName = "parser.lex.ident.16")>]
[<TestCase(16, TestName = "parser.lex.ident.17")>]
[<TestCase(17, TestName = "parser.lex.ident.18")>]
[<TestCase(18, TestName = "parser.lex.ident.19")>]
[<TestCase(19, TestName = "parser.lex.ident.20")>]
[<TestCase(20, TestName = "parser.lex.ident.21")>]
[<TestCase(21, TestName = "parser.lex.ident.22")>]
[<TestCase(22, TestName = "parser.lex.ident.23")>]
[<TestCase(23, TestName = "parser.lex.ident.24")>]
[<TestCase(24, TestName = "parser.lex.ident.25")>]
[<TestCase(25, TestName = "parser.lex.ident.26")>]
[<TestCase(26, TestName = "parser.lex.ident.27")>]
[<TestCase(27, TestName = "parser.lex.ident.28")>]
[<TestCase(28, TestName = "parser.lex.ident.29")>]
[<TestCase(29, TestName = "parser.lex.ident.30")>]
[<TestCase(30, TestName = "parser.lex.ident.31")>]
[<TestCase(31, TestName = "parser.lex.ident.32")>]
[<TestCase(32, TestName = "parser.lex.ident.33")>]
[<TestCase(33, TestName = "parser.lex.ident.34")>]
[<TestCase(34, TestName = "parser.lex.ident.35")>]
[<TestCase(35, TestName = "parser.lex.ident.36")>]
[<TestCase(36, TestName = "parser.lex.ident.37")>]
[<TestCase(37, TestName = "parser.lex.ident.38")>]
[<TestCase(38, TestName = "parser.lex.ident.39")>]
[<TestCase(39, TestName = "parser.lex.ident.40")>]
[<TestCase(40, TestName = "parser.lex.ident.41")>]
[<TestCase(41, TestName = "parser.lex.ident.42")>]
[<TestCase(42, TestName = "parser.lex.ident.43")>]
[<TestCase(43, TestName = "parser.lex.ident.44")>]
[<TestCase(44, TestName = "parser.lex.ident.45")>]
[<TestCase(45, TestName = "parser.lex.ident.46")>]
[<TestCase(46, TestName = "parser.lex.ident.47")>]
[<TestCase(47, TestName = "parser.lex.ident.48")>]
[<TestCase(48, TestName = "parser.lex.ident.49")>]
[<TestCase(49, TestName = "parser.lex.ident.50")>]
[<TestCase(50, TestName = "parser.lex.ident.51")>]
[<TestCase(51, TestName = "parser.lex.ident.52")>]
[<TestCase(52, TestName = "parser.lex.ident.53")>]
[<TestCase(53, TestName = "parser.lex.ident.54")>]
[<TestCase(54, TestName = "parser.lex.ident.55")>]
[<TestCase(55, TestName = "parser.lex.ident.56")>]
[<TestCase(56, TestName = "parser.lex.ident.57")>]
[<TestCase(57, TestName = "parser.lex.ident.58")>]
[<TestCase(58, TestName = "parser.lex.ident.59")>]
[<TestCase(59, TestName = "parser.lex.ident.60")>]
[<TestCase(60, TestName = "parser.lex.ident.61")>]
[<TestCase(61, TestName = "parser.lex.ident.62")>]
[<TestCase(62, TestName = "parser.lex.ident.63")>]
[<TestCase(63, TestName = "parser.lex.ident.64")>]
[<TestCase(64, TestName = "parser.lex.ident.65")>]
[<TestCase(65, TestName = "parser.lex.ident.66")>]
[<TestCase(66, TestName = "parser.lex.ident.67")>]
[<TestCase(67, TestName = "parser.lex.ident.68")>]
[<TestCase(68, TestName = "parser.lex.ident.69")>]
[<TestCase(69, TestName = "parser.lex.ident.70")>]
[<TestCase(70, TestName = "parser.lex.ident.71")>]
[<TestCase(71, TestName = "parser.lex.ident.72")>]
[<TestCase(72, TestName = "parser.lex.ident.73")>]
[<TestCase(73, TestName = "parser.lex.ident.74")>]
[<TestCase(74, TestName = "parser.lex.ident.75")>]
[<TestCase(75, TestName = "parser.lex.ident.76")>]
[<TestCase(76, TestName = "parser.lex.ident.77")>]
[<TestCase(77, TestName = "parser.lex.ident.78")>]
[<TestCase(78, TestName = "parser.lex.ident.79")>]
[<TestCase(79, TestName = "parser.lex.ident.80")>]
[<TestCase(80, TestName = "parser.lex.ident.81")>]
[<TestCase(81, TestName = "parser.lex.ident.82")>]
[<TestCase(82, TestName = "parser.lex.ident.83")>]
[<TestCase(83, TestName = "parser.lex.ident.84")>]
let ``function lex.ident`` idx =
    let (externalForm, _, _) = identValues.[idx]
    let (_, internalForm, _) = identValues.[idx]
    let (_, _, (currentResult , restResult)) = identValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    let (current,rest) = ident internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    current |> assertEqual currentResult
    rest |> assertEqual restResult

let septok : (string list -> string * string list) = stringof(some NHol.printer.issep)

// The first string is what humans expect to read
// and the second string list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private septokValues : (string * string list * (string * string list))[] = [|
    (
        // idx 0
        // parser.lex.septok.01
        // No input
        // throws noparse
        "",    // humans read this
        [],    // the septok function reads this
        ("",[])  // dummy value
    );
    (
        // idx 1
        // parser.lex.septok.02
        // one number
        // throws noparse
        "1",
        ["1"],
        ("",[])  // dummy value
    );
    (
        // idx 2
        // parser.lex.septok.03
        // one letter
        // throws noparse
        "a",
        ["a"],
        ("",[])  // dummy value
    );
    (
        // idx 3
        // parser.lex.septok.04
        // one symbol
        // throws noparse
        "#",
        ["#"],
        ("",[])  // dummy value
    );
    (
        // idx 4
        // parser.lex.septok.05
        // one fowrad slash
        // throws noparse
        "/",
        ["/"],
        ("",[])  // dummy value
    );
    (
        // idx 5
        // parser.lex.septok.06
        // one underscore
        // throws noparse
        "_",
        ["_"],
        ("",[])  // dummy value
    );
    (
        // idx 6
        // parser.lex.septok.07
        // one single quote
        // throws noparse
        "'",
        ["'"],
        ("",[])  // dummy value
    );
    (
        // idx 7
        // parser.lex.septok.08
        // one seperator
        ";",
        [";"],
        (";",[])
    );
    (
        // idx 8
        // parser.lex.septok.09
        // two differnt seperators
        ";,",
        [";";","],
        (";,",[])
    );
    (
        // idx 9
        // parser.lex.septok.10
        // three identical seperators
        ",,,",
        [",";",";","],
        (",,,",[])
    );
    (
        // idx 10
        // parser.lex.septok.11
        // one letter then one seperator then one letter
        // throws noparse
        "a,a",
        ["a";",";"a"],
        ("",[])  // dummy value
    );
    (
        // idx 11
        // parser.lex.septok.12
        // one seperator then one letter then one seperator
        ",a,",
        [",";"a";","],
        (",",["a";","])
    );
    |]
[<Test>]
[<TestCase(0, TestName = "parser.lex.septok.01", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.lex.septok.02", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(2, TestName = "parser.lex.septok.03", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(3, TestName = "parser.lex.septok.04", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(4, TestName = "parser.lex.septok.05", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(5, TestName = "parser.lex.septok.06", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(6, TestName = "parser.lex.septok.07", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(7, TestName = "parser.lex.septok.08")>]
[<TestCase(8, TestName = "parser.lex.septok.09")>]
[<TestCase(9, TestName = "parser.lex.septok.10")>]
[<TestCase(10, TestName = "parser.lex.septok.11", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(11, TestName = "parser.lex.septok.12")>]
let ``function lex.septok`` idx =
    let (externalForm, _, _) = septokValues.[idx]
    let (_, internalForm, _) = septokValues.[idx]
    let (_, _, (currentResult , restResult)) = septokValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    let (current,rest) = septok internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    current |> assertEqual currentResult
    rest |> assertEqual restResult

// Language escape sequences.
// OCaml : http://caml.inria.fr/pub/docs/manual-ocaml/lex.html
// F#    : http://msdn.microsoft.com/en-us/library/dd323829.aspx
let escapecode (i : string list) : (string * string list) =
    match i with
    | "\\" :: rst -> "\\", rst
    | "\"" :: rst -> "\"", rst
    | "\'" :: rst -> "\'", rst
    | "n" :: rst -> "\n", rst
    | "r" :: rst -> "\r", rst
    | "t" :: rst -> "\t", rst
    | "b" :: rst -> "\b", rst
    | " " :: rst -> " ", rst
    | "x" :: h :: l :: rst -> String.make 1 (Char.chr(int_of_string("0x" + h + l))), rst
    | a :: b :: c :: rst when NHol.lib.forall NHol.printer.isnum [a; b; c] -> String.make 1 (Char.chr(int_of_string(a + b + c))), rst
    | _ -> failwith "lex:unrecognized OCaml-style escape in string"

// The first string is what humans expect to read
// and the second string list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private escapecodeValues : (string * string list * (string * string list))[] = [|
    (
        // idx 0
        // parser.lex.escapecode.01
        // Empty list
        // throws exception "lex:unrecognized OCaml-style escape in string"
        "",    // humans read this
        [],    // the escapecode function reads this
        ("",[])  // dummy value
    );
    (
        // idx 1
        // parser.lex.escapecode.02
        "\\",
        ["\\"],
        ("\\",[])
    );
    (
        // idx 2
        // parser.lex.escapecode.03
        "\"",
        ["\""],
        ("\"",[])
    );
    (
        // idx 3
        // parser.lex.escapecode.04
        "\'",
        ["\'"],
        ("\'",[])
    );
    (
        // idx 4
        // parser.lex.escapecode.05
        "\n",
        ["n"],
        ("\n",[])
    );
    (
        // idx 5
        // parser.lex.escapecode.06
        "\r",
        ["r"],
        ("\r",[])
    );
    (
        // idx 6
        // parser.lex.escapecode.07
        "\t",
        ["t"],
        ("\t",[])
    );
    (
        // idx 7
        // parser.lex.escapecode.08
        "\b",
        ["b"],
        ("\b",[])
    );
    (
        // idx 8
        // parser.lex.escapecode.09
        "\ ",   // Note: This is not one used by F#, e.g. slash space
        [" "],
        (" ",[])
    );
    (
        // idx 9
        // parser.lex.escapecode.10
        "\065",
        ["0";"6";"5"],
        ("A",[])
    );
    (
        // idx 10
        // parser.lex.escapecode.11
        "\x41",
        ["x";"4";"1"],
        ("A",[])
    );
    (
        // idx 11
        // parser.lex.escapecode.12
        // throws exception "lex:unrecognized OCaml-style escape in string"
        "\c",
        ["c"],
        ("",[])  // dummy value
    );
    |]
[<Test>]
[<TestCase(0, TestName = "parser.lex.escapecode.01", ExpectedException=typeof<System.Exception>, ExpectedMessage = "lex:unrecognized OCaml-style escape in string")>]
[<TestCase(1, TestName = "parser.lex.escapecode.02")>]
[<TestCase(2, TestName = "parser.lex.escapecode.03")>]
[<TestCase(3, TestName = "parser.lex.escapecode.04")>]
[<TestCase(4, TestName = "parser.lex.escapecode.05")>]
[<TestCase(5, TestName = "parser.lex.escapecode.06")>]
[<TestCase(6, TestName = "parser.lex.escapecode.07")>]
[<TestCase(7, TestName = "parser.lex.escapecode.08")>]
[<TestCase(8, TestName = "parser.lex.escapecode.09")>]
[<TestCase(9, TestName = "parser.lex.escapecode.10")>]
[<TestCase(10, TestName = "parser.lex.escapecode.11")>]
[<TestCase(11, TestName = "parser.lex.escapecode.12", ExpectedException=typeof<System.Exception>, ExpectedMessage = "lex:unrecognized OCaml-style escape in string")>]
let ``function lex.escapecode`` idx =
    let (externalForm, _, _) = escapecodeValues.[idx]
    let (_, internalForm, _) = escapecodeValues.[idx]
    let (_, _, (currentResult , restResult)) = escapecodeValues.[idx]

    let (current,rest) = escapecode internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    current |> assertEqual currentResult
    rest |> assertEqual restResult

let stringchar : (string list -> string * string list) = some(fun i -> i <> "\\" && i <> "\"") <|> (a "\\" .>>. escapecode |>> snd)

// The first string is what humans expect to read
// and the second string list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private stringcharValues : (string * string list * (string * string list))[] = [|
    (
        // idx 0
        // parser.lex.stringchar.01
        // No input
        // throws noparse
        "",    // humans read this
        [],    // the stringchar function reads this
        ("",[])  // dummy value
    );
    (
        // idx 1
        // parser.lex.stringchar.02
        // one number
        "1",
        ["1"],
        ("1",[])
    );
    (
        // idx 2
        // parser.lex.stringchar.03
        // one letter
        "a",
        ["a"],
        ("a",[])
    );
    (
        // idx 3
        // parser.lex.stringchar.04
        // one symbol
        "#",
        ["#"],
        ("#",[])
    );
    (
        // idx 4
        // parser.lex.stringchar.05
        // one fowrad slash
        "/",
        ["/"],
        ("/",[])
    );
    (
        // idx 5
        // parser.lex.stringchar.06
        // one underscore
        "_",
        ["_"],
        ("_",[])
    );
    (
        // idx 6
        // parser.lex.stringchar.07
        // one single quote
        "'",
        ["'"],
        ("'",[])
    );
    (
        // idx 7
        // parser.lex.stringchar.08
        // one seperator
        ";",
        [";"],
        (";",[])
    );
    (
        // idx 8
        // parser.lex.stringchar.09
        // two backslash characters
        @"\\",
        [@"\";@"\"],
        ("\\",[])
    );
    (
        // idx 9
        // parser.lex.stringchar.10
        // a tab character
        @"\t",
        [@"\";"t"],
        ("\t",[])
    );
    (
        // idx 10
        // parser.lex.stringchar.11
        // a double quote
        // throws noparse
        "\"",
        ["\""],
        ("",[])   // dummy value
    );
    (
        // idx 11
        // parser.lex.stringchar.12
        // a double quote then a single character
        // throws noparse
        "\"a",
        ["\"";"a"],
        ("",[])   // dummy value
    );
    |]
[<Test>]
[<TestCase(0, TestName = "parser.lex.stringchar.01", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.lex.stringchar.02")>]
[<TestCase(2, TestName = "parser.lex.stringchar.03")>]
[<TestCase(3, TestName = "parser.lex.stringchar.04")>]
[<TestCase(4, TestName = "parser.lex.stringchar.05")>]
[<TestCase(5, TestName = "parser.lex.stringchar.06")>]
[<TestCase(6, TestName = "parser.lex.stringchar.07")>]
[<TestCase(7, TestName = "parser.lex.stringchar.08")>]
[<TestCase(8, TestName = "parser.lex.stringchar.09")>]
[<TestCase(9, TestName = "parser.lex.stringchar.10")>]
[<TestCase(10, TestName = "parser.lex.stringchar.11", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(11, TestName = "parser.lex.stringchar.12", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
let ``function lex.stringchar`` idx =
    let (externalForm, _, _) = stringcharValues.[idx]
    let (_, internalForm, _) = stringcharValues.[idx]
    let (_, _, (currentResult , restResult)) = stringcharValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    let (current,rest) = stringchar internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    current |> assertEqual currentResult
    rest |> assertEqual restResult

let string = a "\"" .>>. many stringchar .>>. a "\"" |>> (fun ((_, s), _) -> "\"" + NHol.lib.implode s + "\"")

// The first string is what humans expect to read
// and the second string list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private stringValues : (string * string list * (string * string list))[] = [|
    (
        // idx 0
        // parser.lex.string.01
        // No input
        // throws noparse
        "",    // humans read this
        [],    // the string function reads this
        ("",[])  // dummy value
    );
    (
        // idx 1
        // parser.lex.string.02
        // one number
        // throws noparse
        "1",
        ["1"],
        ("",[])   // dummy value
    );
    (
        // idx 2
        // parser.lex.string.03
        // one letter
        // throws noparse
        "a",
        ["a"],
        ("",[])   // dummy value
    );
    (
        // idx 3
        // parser.lex.string.04
        // one symbol
        // throws noparse
        "#",
        ["#"],
        ("",[])   // dummy value
    );
    (
        // idx 4
        // parser.lex.string.05
        // one double quote
        // throws noparse
        "\"",
        ["\""],
        ("",[])   // dummy value
    );
    (
        // idx 5
        // parser.lex.string.06
        // two double quotes
        "\"\"",
        ["\"";"\""],
        ("\"\"",[])
    );
    (
        // idx 6
        // parser.lex.string.07
        // one double quote then one character then one double quote
        "\"a\"",
        ["\"";"a";"\""],
        ("\"a\"",[])
    );
    (
        // idx 7
        // parser.lex.string.08
        // one double quote then one character then one double quote then one different character
        "\"a\"b",
        ["\"";"a";"\"";"b"],
        ("\"a\"",["b"])
    );
    (
        // idx 8
        // parser.lex.string.09
        // one character then one double quote then one different character then one double quote
        // throws noparse
        "a\"b\"",
        ["a";"\"";"b";"\""],
        ("",[])   // dummy value
    );
    (
        // idx 9
        // parser.lex.string.10
        // a tab character
        // throws noparse
        @"\t",
        [@"\";"t"],
        ("",[])   // dummy value
    );
    (
        // idx 10
        // parser.lex.string.11
        // a double quote then a single character
        // throws noparse
        "\"a",
        ["\"";"a"],
        ("",[])   // dummy value
    );
    (
        // idx 11
        // parser.lex.string.12
        // a double quote then many characters then a double quote, i.e. a quoted string
        // throws noparse
        "\"abcdeABCDE12345!@#$%\"",
        ["\"";"a";"b";"c";"d";"e";"A";"B";"C";"D";"E";"1";"2";"3";"4";"5";"!";"@";"#";"$";"%";"\""],
        ("\"abcdeABCDE12345!@#$%\"" ,[])   // dummy value
    );
    |]
[<Test>]
[<TestCase(0, TestName = "parser.lex.string.01", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.lex.string.02", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(2, TestName = "parser.lex.string.03", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(3, TestName = "parser.lex.string.04", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(4, TestName = "parser.lex.string.05", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(5, TestName = "parser.lex.string.06")>]
[<TestCase(6, TestName = "parser.lex.string.07")>]
[<TestCase(7, TestName = "parser.lex.string.08")>]
[<TestCase(8, TestName = "parser.lex.string.09", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(9, TestName = "parser.lex.string.10", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(10, TestName = "parser.lex.string.11", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(11, TestName = "parser.lex.string.12")>]
let ``function lex.string`` idx =
    let (externalForm, _, _) = stringValues.[idx]
    let (_, internalForm, _) = stringValues.[idx]
    let (_, _, (currentResult , restResult)) = stringValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    let (current,rest) = string internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    current |> assertEqual currentResult
    rest |> assertEqual restResult

let rawtoken : (string list -> lexcode * string list) = (string <|> some NHol.printer.isbra <|> septok <|> ident) |>> (fun x -> Ident x)

// The first rawtoken is what humans expect to read
// and the second rawtoken list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private rawtokenValues : (string * string list * (lexcode * string list))[] = [|
    (
        // idx 0
        // parser.lex.rawtoken.01
        // No input
        // throws noparse
        "",    // humans read this
        [],    // the rawtoken function reads this
        (Ident "",[])  // dummy value
    );
    (
        // idx 1
        // parser.lex.rawtoken.02
        // single double quote
        "\"",
        ["\""],
        (Ident "",[])
    );
    (
        // idx 2
        // parser.lex.rawtoken.03
        // empty quoted string
        "\"\"",
        ["\"";"\""],
        (Ident "\"\"",[])
    );
    (
        // idx 3
        // parser.lex.rawtoken.04
        // quoted string with one character
        "\"a\"",
        ["\"";"a";"\""],
        (Ident "\"a\"",[])
    );
    (
        // idx 4
        // parser.lex.rawtoken.05
        // quoted string with several characters
        "\"a1#[\t;\"",  // "\"a1#[\t;\",
        ["\""; "a"; "1"; "#"; "["; "\t"; ";"; "\""],
        (Ident "\"a1#[\t;\"",[])
    );
    (
        // idx 5
        // parser.lex.rawtoken.06
        // left paren
        "(",
        ["("],
        (Ident "(",[]) // dummy value
    );
    (
        // idx 6
        // parser.lex.rawtoken.07
        // right paren
        ")",
        [")"],
        (Ident ")",[])
    );
    (
        // idx 7
        // parser.lex.rawtoken.08
        // left square bracket
        "[",
        ["["],
        (Ident "[",[])
    );
    (
        // idx 8
        // parser.lex.rawtoken.09
        // right square bracket
        "]",
        ["]"],
        (Ident "]",[])
    );
    (
        // idx 9
        // parser.lex.rawtoken.10
        // left curly bracket
        "{",
        ["{"],
        (Ident "{",[])
    );
    (
        // idx 10
        // parser.lex.rawtoken.11
        // right curly bracket
        "}",
        ["}"],
        (Ident "}",[])
    );
    (
        // idx 11
        // parser.lex.rawtoken.12
        // comma
        ",",
        [","],
        (Ident ",",[])
    );
    (
        // idx 12
        // parser.lex.rawtoken.13
        // semicolon
        ";",
        [";"],
        (Ident ";",[])
    );
    (
        // idx 13
        // parser.lex.rawtoken.14
        // the lowercase character a
        "a",
        ["a"],
        (Ident "a",[])
    );
    (
        // idx 14
        // parser.lex.rawtoken.15
        // the uppercase character a
        "A",
        ["A"],
        (Ident "A",[])
    );
    (
        // idx 15
        // parser.lex.rawtoken.16
        // the number zero
        "0",
        ["0"],
        (Ident "0",[])
    );
    (
        // idx 16
        // parser.lex.rawtoken.17
        // the underscore character
        "_",
        ["_"],
        (Ident "_",[])
    );
    (
        // idx 17
        // parser.lex.rawtoken.18
        // the single quote character
        "'",
        ["'"],
        (Ident "'",[])
    );
    (
        // idx 18
        // parser.lex.rawtoken.19
        // the reserved word let
        "let",
        ["l";"e";"t"],
        (Ident "let",[])
    );
    (
        // idx 19
        // parser.lex.rawtoken.20
        // two letters
        "ab",
        ["a";"b"],
        (Ident "ab",[])
    );
    (
        // idx 20
        // parser.lex.rawtoken.21
        // two letters then left open paren
        "ab(",
        ["a";"b";"("],
        (Ident "ab",["("])
    );
    (
        // idx 21
        // parser.lex.rawtoken.22
        // two numbers
        "12",
        ["1";"2"],
        (Ident "12",[])
    );
    (
        // idx 22
        // parser.lex.rawtoken.23
        // two numbers then left open paren
        "12(",
        ["1";"2";"("],
        (Ident "12",["("])
    );
    (
        // idx 23
        // parser.lex.rawtoken.24
        // two brackets
        "()",
        ["(";")"],
        (Ident "(",[")"])
    );
    (
        // idx 24
        // parser.lex.rawtoken.25
        // two seperators
        ",;",
        [",";";"],
        (Ident ",;",[])   // Notice two seperators together are treated as a single token
    );
    (
        // idx 25
        // parser.lex.rawtoken.26
        // two seperators seperated by a space
        ", ;",
        [",";" ";";"],
        (Ident ",",[" "; ";"])
    );
    (
        // idx 26
        // parser.lex.rawtoken.27
        // two strings
        "\"11\"\"22\"",
        ["\""; "1"; "1"; "\""; "\""; "2"; "2"; "\""],
        (Ident "\"11\"",["\""; "2"; "2"; "\""])
    );
    (
        // idx 27
        // parser.lex.rawtoken.28
        // two identifiers seperated by a space
        "a b",
        ["a"; " "; "b"],
        (Ident "a",[" "; "b"])
    );
    (
        // idx 28
        // parser.lex.rawtoken.29
        // a string followed by a bracket
        "\"a\"[",
        ["\""; "a"; "\""; "["],
        (Ident "\"a\"",["["])
    );
    (
        // idx 29
        // parser.lex.rawtoken.30
        // a string followed by a seperator
        "\"a\";",
        ["\""; "a"; "\""; ";"],
        (Ident "\"a\"",[";"])
    );
    (
        // idx 30
        // parser.lex.rawtoken.31
        // a string followed by a ident
        "\"a\"_a",
        ["\""; "a"; "\""; "_"; "a"],
        (Ident "\"a\"",["_"; "a"])
    );
    (
        // idx 31
        // parser.lex.rawtoken.32
        // a bracket followed by a string
        "[\"a\"",
        ["["; "\""; "a"; "\""],
        (Ident "[",["\""; "a"; "\""])
    );
    (
        // idx 32
        // parser.lex.rawtoken.33
        // a bracket followed by a seperator
        "[;",
        ["["; ";"],
        (Ident "[",[";"])
    );
    (
        // idx 33
        // parser.lex.rawtoken.34
        // a bracket followed by an identifier
        "[_a",
        ["["; "_"; "a"],
        (Ident "[",["_"; "a"])
    );
    (
        // idx 34
        // parser.lex.rawtoken.35
        // a seperator followed by a string
        ";\"a\"",
        [";"; "\""; "a"; "\""],
        (Ident ";",["\""; "a"; "\""])
    );
    (
        // idx 35
        // parser.lex.rawtoken.36
        // a seperator followed by a bracket
        ";[",
        [";"; "["],
        (Ident ";",["["])
    );
    (
        // idx 36
        // parser.lex.rawtoken.37
        // a seperator followed by an identifier
        ";_a",
        [";"; "_"; "a"],
        (Ident ";",["_"; "a"])
    );
    (
        // idx 37
        // parser.lex.rawtoken.38
        // a identifier followed by a string
        "_a\"b\"",
        ["_"; "a"; "\""; "b"; "\""],
        (Ident "_a",["\""; "b"; "\""])
    );
    (
        // idx 38
        // parser.lex.rawtoken.39
        // a identifier followed by a bracket
        "_a[",
        ["_"; "a"; "["],
        (Ident "_a",["["])
    );
    (
        // idx 39
        // parser.lex.rawtoken.40
        // a identifier followed by an seperator
        "_a;",
        ["_"; "a"; ";"],
        (Ident "_a",[";"])
    );
    |]
[<Test>]
[<TestCase(0, TestName = "parser.lex.rawtoken.01", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.lex.rawtoken.02", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(2, TestName = "parser.lex.rawtoken.03")>]
[<TestCase(3, TestName = "parser.lex.rawtoken.04")>]
[<TestCase(4, TestName = "parser.lex.rawtoken.05")>]
[<TestCase(5, TestName = "parser.lex.rawtoken.06")>]
[<TestCase(6, TestName = "parser.lex.rawtoken.07")>]
[<TestCase(7, TestName = "parser.lex.rawtoken.08")>]
[<TestCase(8, TestName = "parser.lex.rawtoken.09")>]
[<TestCase(9, TestName = "parser.lex.rawtoken.10")>]
[<TestCase(10, TestName = "parser.lex.rawtoken.11")>]
[<TestCase(11, TestName = "parser.lex.rawtoken.12")>]
[<TestCase(12, TestName = "parser.lex.rawtoken.13")>]
[<TestCase(13, TestName = "parser.lex.rawtoken.14")>]
[<TestCase(14, TestName = "parser.lex.rawtoken.15")>]
[<TestCase(15, TestName = "parser.lex.rawtoken.16")>]
[<TestCase(16, TestName = "parser.lex.rawtoken.17")>]
[<TestCase(17, TestName = "parser.lex.rawtoken.18")>]
[<TestCase(18, TestName = "parser.lex.rawtoken.19")>]
[<TestCase(19, TestName = "parser.lex.rawtoken.20")>]
[<TestCase(20, TestName = "parser.lex.rawtoken.21")>]
[<TestCase(21, TestName = "parser.lex.rawtoken.22")>]
[<TestCase(22, TestName = "parser.lex.rawtoken.23")>]
[<TestCase(23, TestName = "parser.lex.rawtoken.24")>]
[<TestCase(24, TestName = "parser.lex.rawtoken.25")>]
[<TestCase(25, TestName = "parser.lex.rawtoken.26")>]
[<TestCase(26, TestName = "parser.lex.rawtoken.27")>]
[<TestCase(27, TestName = "parser.lex.rawtoken.28")>]
[<TestCase(28, TestName = "parser.lex.rawtoken.29")>]
[<TestCase(29, TestName = "parser.lex.rawtoken.30")>]
[<TestCase(30, TestName = "parser.lex.rawtoken.31")>]
[<TestCase(31, TestName = "parser.lex.rawtoken.32")>]
[<TestCase(32, TestName = "parser.lex.rawtoken.33")>]
[<TestCase(33, TestName = "parser.lex.rawtoken.34")>]
[<TestCase(34, TestName = "parser.lex.rawtoken.35")>]
[<TestCase(35, TestName = "parser.lex.rawtoken.36")>]
[<TestCase(36, TestName = "parser.lex.rawtoken.37")>]
[<TestCase(37, TestName = "parser.lex.rawtoken.38")>]
[<TestCase(38, TestName = "parser.lex.rawtoken.39")>]
[<TestCase(39, TestName = "parser.lex.rawtoken.40")>]
let ``function lex.rawtoken`` idx =
    let (externalForm, _, _) = rawtokenValues.[idx]
    let (_, internalForm, _) = rawtokenValues.[idx]
    let (_, _, (currentResult , restResult)) = rawtokenValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    let (current,rest) = rawtoken internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    current |> assertEqual currentResult
    rest |> assertEqual restResult

let simptoken = many(some NHol.printer.isspace) .>>. rawtoken |>> (reserve << snd)

// The first simptoken is what humans expect to read
// and the second simptoken list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private simptokenValues : (string * string list * (lexcode * string list))[] = [|
    (
        // idx 0
        // parser.lex.simptoken.01
        // No input
        // throws noparse
        "",    // humans read this
        [],    // the simptoken function reads this
        (Ident "",[])  // dummy value
    );
    (
        // idx 1
        // parser.lex.simptoken.02
        // single double quote
        // throws noparse
        "\"",
        ["\""],
        (Ident "",[])  // dummy value
    );
    (
        // idx 2
        // parser.lex.simptoken.03
        // empty quoted string
        "\"\"",
        ["\"";"\""],
        (Ident "\"\"",[])
    );
    (
        // idx 3
        // parser.lex.simptoken.04
        // quoted string with one character
        "\"a\"",
        ["\"";"a";"\""],
        (Ident "\"a\"",[])
    );
    (
        // idx 4
        // parser.lex.simptoken.05
        // quoted string with several characters
        "\"a1#[\t;\"",  // "\"a1#[\t;\",
        ["\""; "a"; "1"; "#"; "["; "\t"; ";"; "\""],
        (Ident "\"a1#[\t;\"",[])
    );
    (
        // idx 5
        // parser.lex.simptoken.06
        // left paren
        "(",
        ["("],
        (Resword "(",[]) // dummy value
    );
    (
        // idx 6
        // parser.lex.simptoken.07
        // right paren
        ")",
        [")"],
        (Resword ")",[])
    );
    (
        // idx 7
        // parser.lex.simptoken.08
        // left square bracket
        "[",
        ["["],
        (Resword "[",[])
    );
    (
        // idx 8
        // parser.lex.simptoken.09
        // right square bracket
        "]",
        ["]"],
        (Resword "]",[])
    );
    (
        // idx 9
        // parser.lex.simptoken.10
        // left curly bracket
        "{",
        ["{"],
        (Resword "{",[])
    );
    (
        // idx 10
        // parser.lex.simptoken.11
        // right curly bracket
        "}",
        ["}"],
        (Resword "}",[])
    );
    (
        // idx 11
        // parser.lex.simptoken.12
        // comma
        ",",
        [","],               // Notice comma is a seperator but is not a Resword
        (Ident ",",[])
    );
    (
        // idx 12
        // parser.lex.simptoken.13
        // semicolon
        ";",
        [";"],               // Notice semicolon is a seperator and is a Resword
        (Resword ";",[])
    );
    (
        // idx 13
        // parser.lex.simptoken.14
        // the lowercase character a
        "a",
        ["a"],
        (Ident "a",[])
    );
    (
        // idx 14
        // parser.lex.simptoken.15
        // the uppercase character a
        "A",
        ["A"],
        (Ident "A",[])
    );
    (
        // idx 15
        // parser.lex.simptoken.16
        // the number zero
        "0",
        ["0"],
        (Ident "0",[])
    );
    (
        // idx 16
        // parser.lex.simptoken.17
        // the underscore character
        "_",
        ["_"],
        (Ident "_",[])
    );
    (
        // idx 17
        // parser.lex.simptoken.18
        // the single quote character
        "'",
        ["'"],
        (Ident "'",[])
    );
    (
        // idx 18
        // parser.lex.simptoken.19
        // the reserved word let
        "let",
        ["l";"e";"t"],
        (Resword "let",[])
    );
    (
        // idx 19
        // parser.lex.simptoken.20
        // two letters
        "ab",
        ["a";"b"],
        (Ident "ab",[])
    );
    (
        // idx 20
        // parser.lex.simptoken.21
        // two letters then left open paren
        "ab(",
        ["a";"b";"("],
        (Ident "ab",["("])
    );
    (
        // idx 21
        // parser.lex.simptoken.22
        // two numbers
        "12",
        ["1";"2"],
        (Ident "12",[])
    );
    (
        // idx 22
        // parser.lex.simptoken.23
        // two numbers then left open paren
        "12(",
        ["1";"2";"("],
        (Ident "12",["("])
    );
    (
        // idx 23
        // parser.lex.simptoken.24
        // two brackets
        "()",
        ["(";")"],
        (Resword "(",[")"])
    );
    (
        // idx 24
        // parser.lex.simptoken.25
        // two seperators
        ",;",
        [",";";"],
        (Ident ",;",[])   // Notice two seperators together are treated as a single token
    );
    (
        // idx 25
        // parser.lex.simptoken.26
        // two seperators seperated by a space
        ", ;",
        [",";" ";";"],
        (Ident ",",[" "; ";"])
    );
    (
        // idx 26
        // parser.lex.simptoken.27
        // two strings
        "\"11\"\"22\"",
        ["\""; "1"; "1"; "\""; "\""; "2"; "2"; "\""],
        (Ident "\"11\"",["\""; "2"; "2"; "\""])
    );
    (
        // idx 27
        // parser.lex.simptoken.28
        // two identifiers seperated by a space
        "a b",
        ["a"; " "; "b"],
        (Ident "a",[" "; "b"])
    );
    (
        // idx 28
        // parser.lex.simptoken.29
        // a string followed by a bracket
        "\"a\"[",
        ["\""; "a"; "\""; "["],
        (Ident "\"a\"",["["])
    );
    (
        // idx 29
        // parser.lex.simptoken.30
        // a string followed by a seperator
        "\"a\";",
        ["\""; "a"; "\""; ";"],
        (Ident "\"a\"",[";"])
    );
    (
        // idx 30
        // parser.lex.simptoken.31
        // a string followed by a ident
        "\"a\"_a",
        ["\""; "a"; "\""; "_"; "a"],
        (Ident "\"a\"",["_"; "a"])
    );
    (
        // idx 31
        // parser.lex.simptoken.32
        // a bracket followed by a string
        "[\"a\"",
        ["["; "\""; "a"; "\""],
        (Resword "[",["\""; "a"; "\""])
    );
    (
        // idx 32
        // parser.lex.simptoken.33
        // a bracket followed by a seperator
        "[;",
        ["["; ";"],
        (Resword "[",[";"])
    );
    (
        // idx 33
        // parser.lex.simptoken.34
        // a bracket followed by an identifier
        "[_a",
        ["["; "_"; "a"],
        (Resword "[",["_"; "a"])
    );
    (
        // idx 34
        // parser.lex.simptoken.35
        // a seperator followed by a string
        ";\"a\"",
        [";"; "\""; "a"; "\""],
        (Resword ";",["\""; "a"; "\""])
    );
    (
        // idx 35
        // parser.lex.simptoken.36
        // a seperator followed by a bracket
        ";[",
        [";"; "["],
        (Resword ";",["["])
    );
    (
        // idx 36
        // parser.lex.simptoken.37
        // a seperator followed by an identifier
        ";_a",
        [";"; "_"; "a"],
        (Resword ";",["_"; "a"])
    );
    (
        // idx 37
        // parser.lex.simptoken.38
        // a identifier followed by a string
        "_a\"b\"",
        ["_"; "a"; "\""; "b"; "\""],
        (Ident "_a",["\""; "b"; "\""])
    );
    (
        // idx 38
        // parser.lex.simptoken.39
        // a identifier followed by a bracket
        "_a[",
        ["_"; "a"; "["],
        (Ident "_a",["["])
    );
    (
        // idx 39
        // parser.lex.simptoken.40
        // a identifier followed by an seperator
        "_a;",
        ["_"; "a"; ";"],
        (Ident "_a",[";"])
    );
    (
        // idx 40
        // parser.lex.simptoken.41
        // a space
        // throws noparse
        " ",
        [" "],
        (Ident "",[])  // dummy value
    );
    (
        // idx 41
        // parser.lex.simptoken.42
        // a space followed by single double quote
        // throws noparse
        " \"",
        [" "; "\""],
        (Ident "",[])  // dummy value
    );
    (
        // idx 42
        // parser.lex.simptoken.43
        // a space followed by empty quoted string
        " \"\"",
        [" "; "\"";"\""],
        (Ident "\"\"",[])
    );
    (
        // idx 43
        // parser.lex.simptoken.44
        // a space followed by quoted string with one character
        " \"a\"",
        [" "; "\"";"a";"\""],
        (Ident "\"a\"",[])
    );
    (
        // idx 44
        // parser.lex.simptoken.45
        // a space followed by quoted string with several characters
        " \"a1#[\t;\"",  // "\"a1#[\t;\",
        [" "; "\""; "a"; "1"; "#"; "["; "\t"; ";"; "\""],
        (Ident "\"a1#[\t;\"",[])
    );
    (
        // idx 45
        // parser.lex.simptoken.46
        // a space followed by left paren
        " (",
        [" "; "("],
        (Resword "(",[]) // dummy value
    );
    (
        // idx 46
        // parser.lex.simptoken.47
        // a space followed by right paren
        " )",
        [" "; ")"],
        (Resword ")",[])
    );
    (
        // idx 47
        // parser.lex.simptoken.48
        // a space followed by left square bracket
        " [",
        [" "; "["],
        (Resword "[",[])
    );
    (
        // idx 48
        // parser.lex.simptoken.49
        // a space followed by right square bracket
        " ]",
        [" "; "]"],
        (Resword "]",[])
    );
    (
        // idx 49
        // parser.lex.simptoken.50
        // a space followed by left curly bracket
        " {",
        [" "; "{"],
        (Resword "{",[])
    );
    (
        // idx 50
        // parser.lex.simptoken.51
        // a space followed by right curly bracket
        " }",
        [" "; "}"],
        (Resword "}",[])
    );
    (
        // idx 51
        // parser.lex.simptoken.52
        // a space followed by comma
        " ,",
        [" "; ","],               // Notice comma is a seperator but is not a Resword
        (Ident ",",[])
    );
    (
        // idx 52
        // parser.lex.simptoken.53
        // a space followed by semicolon
        " ;",
        [" "; ";"],               // Notice semicolon is a seperator and is a Resword
        (Resword ";",[])
    );
    (
        // idx 53
        // parser.lex.simptoken.54
        // a space followed by the lowercase character a
        " a",
        [" "; "a"],
        (Ident "a",[])
    );
    (
        // idx 54
        // parser.lex.simptoken.55
        // a space followed by the uppercase character a
        " A",
        [" "; "A"],
        (Ident "A",[])
    );
    (
        // idx 55
        // parser.lex.simptoken.56
        // a space followed by the number zero
        " 0",
        [" "; "0"],
        (Ident "0",[])
    );
    (
        // idx 56
        // parser.lex.simptoken.57
        // a space followed by the underscore character
        " _",
        [" "; "_"],
        (Ident "_",[])
    );
    (
        // idx 57
        // parser.lex.simptoken.58
        // a space followed by the single quote character
        " '",
        [" "; "'"],
        (Ident "'",[])
    );
    (
        // idx 58
        // parser.lex.simptoken.59
        // a space followed by the reserved word let
        " let",
        [" "; "l";"e";"t"],
        (Resword "let",[])
    );
    (
        // idx 59
        // parser.lex.simptoken.60
        // a space followed by two letters
        " ab",
        [" "; "a";"b"],
        (Ident "ab",[])
    );
    (
        // idx 60
        // parser.lex.simptoken.61
        // a space followed by two letters then left open paren
        " ab(",
        [" "; "a";"b";"("],
        (Ident "ab",["("])
    );
    (
        // idx 61
        // parser.lex.simptoken.62
        // a space followed by two numbers
        " 12",
        [" "; "1";"2"],
        (Ident "12",[])
    );
    (
        // idx 62
        // parser.lex.simptoken.63
        // a space followed by two numbers then left open paren
        " 12(",
        [" "; "1";"2";"("],
        (Ident "12",["("])
    );
    (
        // idx 63
        // parser.lex.simptoken.64
        // a space followed by two brackets
        " ()",
        [" "; "(";")"],
        (Resword "(",[")"])
    );
    (
        // idx 64
        // parser.lex.simptoken.65
        // a space followed by two seperators
        " ,;",
        [" "; ",";";"],
        (Ident ",;",[])   // Notice two seperators together are treated as a single token
    );
    (
        // idx 65
        // parser.lex.simptoken.66
        // a space followed by two seperators seperated by a space
        " , ;",
        [" "; ",";" ";";"],
        (Ident ",",[" "; ";"])
    );
    (
        // idx 66
        // parser.lex.simptoken.67
        // a space followed by two strings
        " \"11\"\"22\"",
        [" "; "\""; "1"; "1"; "\""; "\""; "2"; "2"; "\""],
        (Ident "\"11\"",["\""; "2"; "2"; "\""])
    );
    (
        // idx 67
        // parser.lex.simptoken.68
        // a space followed by two identifiers seperated by a space
        " a b",
        [" "; "a"; " "; "b"],
        (Ident "a",[" "; "b"])
    );
    (
        // idx 68
        // parser.lex.simptoken.69
        // a space followed by a string followed by a bracket
        " \"a\"[",
        [" "; "\""; "a"; "\""; "["],
        (Ident "\"a\"",["["])
    );
    (
        // idx 69
        // parser.lex.simptoken.70
        // a space followed by a string followed by a seperator
        " \"a\";",
        [" "; "\""; "a"; "\""; ";"],
        (Ident "\"a\"",[";"])
    );
    (
        // idx 70
        // parser.lex.simptoken.71
        // a space followed by a string followed by a ident
        " \"a\"_a",
        [" "; "\""; "a"; "\""; "_"; "a"],
        (Ident "\"a\"",["_"; "a"])
    );
    (
        // idx 71
        // parser.lex.simptoken.72
        // a space followed by a bracket followed by a string
        " [\"a\"",
        [" "; "["; "\""; "a"; "\""],
        (Resword "[",["\""; "a"; "\""])
    );
    (
        // idx 72
        // parser.lex.simptoken.73
        // a space followed by a bracket followed by a seperator
        " [;",
        [" "; "["; ";"],
        (Resword "[",[";"])
    );
    (
        // idx 73
        // parser.lex.simptoken.74
        // a space followed by a bracket followed by an identifier
        " [_a",
        [" "; "["; "_"; "a"],
        (Resword "[",["_"; "a"])
    );
    (
        // idx 74
        // parser.lex.simptoken.75
        // a space followed by a seperator followed by a string
        " ;\"a\"",
        [" "; ";"; "\""; "a"; "\""],
        (Resword ";",["\""; "a"; "\""])
    );
    (
        // idx 75
        // parser.lex.simptoken.76
        // a space followed by a seperator followed by a bracket
        " ;[",
        [" "; ";"; "["],
        (Resword ";",["["])
    );
    (
        // idx 76
        // parser.lex.simptoken.77
        // a space followed by a seperator followed by an identifier
        " ;_a",
        [" "; ";"; "_"; "a"],
        (Resword ";",["_"; "a"])
    );
    (
        // idx 77
        // parser.lex.simptoken.78
        // a space followed by a identifier followed by a string
        " _a\"b\"",
        [" "; "_"; "a"; "\""; "b"; "\""],
        (Ident "_a",["\""; "b"; "\""])
    );
    (
        // idx 78
        // parser.lex.simptoken.79
        // a space followed by a identifier followed by a bracket
        " _a[",
        [" "; "_"; "a"; "["],
        (Ident "_a",["["])
    );
    (
        // idx 79
        // parser.lex.simptoken.80
        // a space followed by a identifier followed by an seperator
        " _a;",
        [" "; "_"; "a"; ";"],
        (Ident "_a",[";"])
    );
    (
        // idx 80
        // parser.lex.simptoken.81
        // a empty comment
        "//",
        ["/"; "/"],
        (Resword "//",[])
    );
    (
        // idx 81
        // parser.lex.simptoken.82
        // a coment no spaces then some text
        "//abc",
        ["/"; "/"; "a"; "b"; "c"],
        (Resword "//",["a";"b";"c"])
    );
    (
        // idx 82
        // parser.lex.simptoken.83
        // a coment then a space then some text
        "// abc",
        ["/"; "/"; " "; "a"; "b"; "c"],
        (Resword "//",[" "; "a";"b";"c"])
    );
    |]
[<Test>]
[<TestCase(0, TestName = "parser.lex.simptoken.01", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(1, TestName = "parser.lex.simptoken.02", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(2, TestName = "parser.lex.simptoken.03")>]
[<TestCase(3, TestName = "parser.lex.simptoken.04")>]
[<TestCase(4, TestName = "parser.lex.simptoken.05")>]
[<TestCase(5, TestName = "parser.lex.simptoken.06")>]
[<TestCase(6, TestName = "parser.lex.simptoken.07")>]
[<TestCase(7, TestName = "parser.lex.simptoken.08")>]
[<TestCase(8, TestName = "parser.lex.simptoken.09")>]
[<TestCase(9, TestName = "parser.lex.simptoken.10")>]
[<TestCase(10, TestName = "parser.lex.simptoken.11")>]
[<TestCase(11, TestName = "parser.lex.simptoken.12")>]
[<TestCase(12, TestName = "parser.lex.simptoken.13")>]
[<TestCase(13, TestName = "parser.lex.simptoken.14")>]
[<TestCase(14, TestName = "parser.lex.simptoken.15")>]
[<TestCase(15, TestName = "parser.lex.simptoken.16")>]
[<TestCase(16, TestName = "parser.lex.simptoken.17")>]
[<TestCase(17, TestName = "parser.lex.simptoken.18")>]
[<TestCase(18, TestName = "parser.lex.simptoken.19")>]
[<TestCase(19, TestName = "parser.lex.simptoken.20")>]
[<TestCase(20, TestName = "parser.lex.simptoken.21")>]
[<TestCase(21, TestName = "parser.lex.simptoken.22")>]
[<TestCase(22, TestName = "parser.lex.simptoken.23")>]
[<TestCase(23, TestName = "parser.lex.simptoken.24")>]
[<TestCase(24, TestName = "parser.lex.simptoken.25")>]
[<TestCase(25, TestName = "parser.lex.simptoken.26")>]
[<TestCase(26, TestName = "parser.lex.simptoken.27")>]
[<TestCase(27, TestName = "parser.lex.simptoken.28")>]
[<TestCase(28, TestName = "parser.lex.simptoken.29")>]
[<TestCase(29, TestName = "parser.lex.simptoken.30")>]
[<TestCase(30, TestName = "parser.lex.simptoken.31")>]
[<TestCase(31, TestName = "parser.lex.simptoken.32")>]
[<TestCase(32, TestName = "parser.lex.simptoken.33")>]
[<TestCase(33, TestName = "parser.lex.simptoken.34")>]
[<TestCase(34, TestName = "parser.lex.simptoken.35")>]
[<TestCase(35, TestName = "parser.lex.simptoken.36")>]
[<TestCase(36, TestName = "parser.lex.simptoken.37")>]
[<TestCase(37, TestName = "parser.lex.simptoken.38")>]
[<TestCase(38, TestName = "parser.lex.simptoken.39")>]
[<TestCase(39, TestName = "parser.lex.simptoken.40")>]
[<TestCase(40, TestName = "parser.lex.simptoken.41", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(41, TestName = "parser.lex.simptoken.42", ExpectedException=typeof<NHol.parser.Noparse>, ExpectedMessage = "Exception of type 'NHol.parser+Noparse' was thrown.")>]
[<TestCase(42, TestName = "parser.lex.simptoken.43")>]
[<TestCase(43, TestName = "parser.lex.simptoken.44")>]
[<TestCase(44, TestName = "parser.lex.simptoken.45")>]
[<TestCase(45, TestName = "parser.lex.simptoken.46")>]
[<TestCase(46, TestName = "parser.lex.simptoken.47")>]
[<TestCase(47, TestName = "parser.lex.simptoken.48")>]
[<TestCase(48, TestName = "parser.lex.simptoken.49")>]
[<TestCase(49, TestName = "parser.lex.simptoken.50")>]
[<TestCase(50, TestName = "parser.lex.simptoken.51")>]
[<TestCase(51, TestName = "parser.lex.simptoken.52")>]
[<TestCase(52, TestName = "parser.lex.simptoken.53")>]
[<TestCase(53, TestName = "parser.lex.simptoken.54")>]
[<TestCase(54, TestName = "parser.lex.simptoken.55")>]
[<TestCase(55, TestName = "parser.lex.simptoken.56")>]
[<TestCase(56, TestName = "parser.lex.simptoken.57")>]
[<TestCase(57, TestName = "parser.lex.simptoken.58")>]
[<TestCase(58, TestName = "parser.lex.simptoken.59")>]
[<TestCase(59, TestName = "parser.lex.simptoken.60")>]
[<TestCase(60, TestName = "parser.lex.simptoken.61")>]
[<TestCase(61, TestName = "parser.lex.simptoken.62")>]
[<TestCase(62, TestName = "parser.lex.simptoken.63")>]
[<TestCase(63, TestName = "parser.lex.simptoken.64")>]
[<TestCase(64, TestName = "parser.lex.simptoken.65")>]
[<TestCase(65, TestName = "parser.lex.simptoken.66")>]
[<TestCase(66, TestName = "parser.lex.simptoken.67")>]
[<TestCase(67, TestName = "parser.lex.simptoken.68")>]
[<TestCase(68, TestName = "parser.lex.simptoken.69")>]
[<TestCase(69, TestName = "parser.lex.simptoken.70")>]
[<TestCase(70, TestName = "parser.lex.simptoken.71")>]
[<TestCase(71, TestName = "parser.lex.simptoken.72")>]
[<TestCase(72, TestName = "parser.lex.simptoken.73")>]
[<TestCase(73, TestName = "parser.lex.simptoken.74")>]
[<TestCase(74, TestName = "parser.lex.simptoken.75")>]
[<TestCase(75, TestName = "parser.lex.simptoken.76")>]
[<TestCase(76, TestName = "parser.lex.simptoken.77")>]
[<TestCase(77, TestName = "parser.lex.simptoken.78")>]
[<TestCase(78, TestName = "parser.lex.simptoken.79")>]
[<TestCase(79, TestName = "parser.lex.simptoken.80")>]
[<TestCase(80, TestName = "parser.lex.simptoken.81")>]
[<TestCase(81, TestName = "parser.lex.simptoken.82")>]
[<TestCase(82, TestName = "parser.lex.simptoken.83")>]

let ``function lex.simptoken`` idx =
    let (externalForm, _, _) = simptokenValues.[idx]
    let (_, internalForm, _) = simptokenValues.[idx]
    let (_, _, (currentResult , restResult)) = simptokenValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "externalForm: %A" externalForm
//    printfn "internalForm: %A" internalForm
//    printfn "convertedForm: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    let (current,rest) = simptoken internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    current |> assertEqual currentResult
    rest |> assertEqual restResult

let comment_token = ref(Resword "//")

[<Test>]
let ``function comment_token`` () =
    let result = !comment_token
//    printfn "result: %A" result
    Assert.AreEqual(result, Resword "//")

// (string list -> lexcode list * string list)
let rec tokens (i : string list) : (lexcode list * string list) =
    let tokensResult =
        try
            let (t, rst) =
                simptoken i
            if t = !comment_token then
                (many(fun i ->
                            if i <> [] && NHol.lib.hd i <> "\n" then 1, NHol.lib.tl i
                            else raise Noparse) .>>. tokens |>> snd) rst
            else
                let toks, rst1 = tokens rst
                t :: toks, rst1
        with Noparse ->
            [], i
    tokensResult

// The first tokens is what humans expect to read
// and the second tokens list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private tokensValues : (string * string list * (lexcode list * string list))[] = [|
    (
        // idx 0
        // parser.lex.tokens.01
        // No input
        "",    // humans read this
        [],    // the tokens function reads this
        ([],[])                                    // Notice no noparse exception
    );
    (
        // idx 1
        // parser.lex.tokens.02
        // empty string using the empty string literal
        String.empty,
        [],
        ([],[])
    );
    (
        // idx 2
        // parser.lex.tokens.03
        // char value x00 not in a quoted string
        "\x00",
        ["\x00"],
        ([],["\u0000"])
    );
    (
        // idx 3
        // parser.lex.tokens.04
        // char value x00 within a quoted string
        "\"\x00\"",
        ["\"";"\x00";"\""],          // Notice an escaped char can only occur within a quoted string.
        ([Ident "\"\u0000\""],[])    // Notice F# does not use \xNN but uses \uNNNN
    );
    (
        // idx 4
        // parser.lex.tokens.05
        // a single comment with no text
        "//",
        ["/";"/"],
        ([],[])
    );
    (
        // idx 5
        // parser.lex.tokens.06
        // a single comment with some text
        "// a",
        ["/";"/";" ";"a"],
        ([],[])
    );
    (
        // idx 6
        // parser.lex.tokens.07
        // some text, then a comment
        "a // b",
        ["a"; " "; "/";"/"; " "; "b"],
        ([Ident "a"],[])
    );
    (
        // idx 7
        // parser.lex.tokens.08
        // a comment, then a new line with text and a comment, then a new line with a comment
        "// a\nb // c\n// d",
        ["/"; "/"; " "; "a"; "\n"; "b"; " "; "/"; "/"; " "; "c"; "\n"; "/"; "/"; " "; "d"],
        ([Ident "b"],[])
    );
    (
        // idx 8
        // parser.lex.tokens.09
        // a Resword then a Ident
        "->a",
        ["-"; ">"; "a"],
        ([Resword "->"; Ident "a"],[])
    );
    (
        // idx 9
        // parser.lex.tokens.10
        // a Ident then a Resword
        "a->",
        ["a"; "-"; ">"],
        ([Ident "a"; Resword "->"],[])
    );
    (
        // idx 10
        // parser.lex.tokens.11
        // two differnt idents needing a space seperator
        "a b",
        ["a"; " "; "b"],
        ([Ident "a"; Ident "b"],[])
    );
    (
        // idx 11
        // parser.lex.tokens.12
        // one double quote
        "\"",
        ["\""],
        ([],["\""])   // Notice if a noparse exceptions occurs, tokens function ends with data in second value of tuple result.
    );
    |]

[<Test>]
[<TestCase(0, TestName = "parser.lex.tokens.01")>]
[<TestCase(1, TestName = "parser.lex.tokens.02")>]
[<TestCase(2, TestName = "parser.lex.tokens.03")>]
[<TestCase(3, TestName = "parser.lex.tokens.04")>]
[<TestCase(4, TestName = "parser.lex.tokens.05")>]
[<TestCase(5, TestName = "parser.lex.tokens.06")>]
[<TestCase(6, TestName = "parser.lex.tokens.07")>]
[<TestCase(7, TestName = "parser.lex.tokens.08")>]
[<TestCase(8, TestName = "parser.lex.tokens.09")>]
[<TestCase(9, TestName = "parser.lex.tokens.10")>]
[<TestCase(10, TestName = "parser.lex.tokens.11")>]
[<TestCase(11, TestName = "parser.lex.tokens.12")>]
let ``function lex.tokens`` idx =
    let (externalForm, _, _) = tokensValues.[idx]
    let (_, internalForm, _) = tokensValues.[idx]
    let (_, _, (currentResult , restResult)) = tokensValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "external form: %A" externalForm
//    printfn "internal form: %A" internalForm
//    printfn "converted form: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    let (current,rest) = tokens internalForm
//    printfn "expected result: %A %A" currentResult restResult
//    printfn "function result: %A %A" current rest
    current |> assertEqual currentResult
    rest |> assertEqual restResult

// Setup for mutables
NHol.printer.reserve_words ["//"]

let private lexValues : (string * NHol.parser.lexcode list)[] = [|
    (
        // idx 0
        // parser.lex.01
        // empty string using double quotes
        "",
        []
    );
    (
        // idx 1
        // parser.lex.02
        // empty string using the empty string literal
        String.empty,
        []
    );
    (
        // idx 2
        // parser.lex.03
        // A comment with no text
        "//",
        []
    );
    (
        // idx 3
        // parser.lex.04
        // A comment with some text
        "// a",
        []
    );
    (
        // idx 4
        // parser.lex.05
        // A comment with text on the next line
        "// a\nb",
        [Ident "b"]
    );
    (
        // idx 5
        // parser.lex.06
        // A comment followed by a comment on the next line
        "// a\n// b",
        []
    );
    (
        // idx 6
        // parser.lex.07
        // An Ident token with comment on line before and comment on line after
        "// a \nb\n// c",
        [Ident "b"]
    );
    (
        // idx 7
        // parser.lex.08
        // A comment with Ident token on line before and Ident on line after
        "a\n// b\nc",
        [Ident "a"; Ident "c"]
    );
    (
        // idx 8
        // parser.lex.09
        // A Ident starting with 'a'
        "a",
        [Ident "a"]
    );
    (
        // idx 9
        // parser.lex.10
        // A Ident starting with '1'
        "1",
        [Ident "1"]
    );
    (
        // idx 10
        // parser.lex.11
        // A Ident starting with '_'
        "_",
        [Ident "_"]
    );
    (
        // idx 11
        // parser.lex.12
        // A Ident starting with '#'
        "#",
        [Ident "#"]
    );
    (
        // idx 12
        // parser.lex.13
        // a space then an Ident
        " a",
        [Ident "a"]
    );
    (
        // idx 13
        // parser.lex.14
        // a quoted string with a character
        "\"a\"",
        [Ident "\"a\""]
    );
    (
        // idx 14
        // parser.lex.15
        // if
        "if",
        [Resword "if"]
    );
    (
        // idx 15
        // parser.lex.16
        // a single double quote
        // throws System.Exception - "Unparsed input"
        "\"",
        [] // dummy value
    );
    (
        // idx 16
        // parser.lex.17
        // a quoted string with a slash character
        "\"\\\\\"",
        [Ident "\"\\\""]
    );
    (
        // idx 17
        // parser.lex.18
        // a quoted string with a double qoute character
        "\"\\\"\"",
        [Ident "\"\"\""]
    );
    (
        // idx 18
        // parser.lex.19
        // a quoted string with a single quote character
        "\"\\\'\"",
        [Ident "\"\'\""]
    );
    (
        // idx 19
        // parser.lex.20
        // a quoted string with a new line character
        "\"\\n\"",
        [Ident "\"\n\""]
    );
    (
        // idx 20
        // parser.lex.21
        // a quoted string with a carriage return character
        "\"\\r\"",
        [Ident "\"\r\""]
    );
    (
        // idx 21
        // parser.lex.22
        // a quoted string with a tab character
        "\"\\t\"",
        [Ident "\"\t\""]
    );
    (
        // idx 22
        // parser.lex.23
        // a quoted string with a backspace character
        "\"\\b\"",
        [Ident "\"\b\""]
    );
    (
        // idx 23
        // parser.lex.24
        // a quoted string with a blank character
        "\"\\ \"",
        [Ident "\" \""]
    );
    (
        // idx 24
        // parser.lex.25
        // a quoted string with a uppercase A
        "\"\\x41\"",
        [Ident "\"\x41\""]
    );
    (
        // idx 25
        // parser.lex.26
        // a quoted string with a uppercase A
        "\"\\065\"",
        [Ident "\"\065\""]
    );
    (
        // idx 26
        // parser.lex.27
        // a quoted string with a uppercase A
        "\"\\c\"",
        [Ident ""]
    )
    (
        // idx 27
        // parser.lex.28
        // test from HOL Light reference manual.
        "if p+1=2 then x + 1 else y - 1",
        [Resword "if"; Ident "p"; Ident "+"; Ident "1"; Ident "="; Ident "2";
         Resword "then"; Ident "x"; Ident "+"; Ident "1"; Resword "else"; Ident "y";
         Ident "-"; Ident "1"]
    );
    |]

[<Test>]
[<TestCase(0, TestName = "parser.lex.01")>]
[<TestCase(1, TestName = "parser.lex.02")>]
[<TestCase(2, TestName = "parser.lex.03")>]
[<TestCase(3, TestName = "parser.lex.04")>]
[<TestCase(4, TestName = "parser.lex.05")>]
[<TestCase(5, TestName = "parser.lex.06")>]
[<TestCase(6, TestName = "parser.lex.07")>]
[<TestCase(7, TestName = "parser.lex.08")>]
[<TestCase(8, TestName = "parser.lex.09")>]
[<TestCase(9, TestName = "parser.lex.10")>]
[<TestCase(10, TestName = "parser.lex.11")>]
[<TestCase(11, TestName = "parser.lex.12")>]
[<TestCase(12, TestName = "parser.lex.13")>]
[<TestCase(13, TestName = "parser.lex.14")>]
[<TestCase(14, TestName = "parser.lex.15")>]
[<TestCase(15, TestName = "parser.lex.16", ExpectedException=typeof<System.Exception>, ExpectedMessage = "Unparsed input")>]
[<TestCase(16, TestName = "parser.lex.17")>]
[<TestCase(17, TestName = "parser.lex.18")>]
[<TestCase(18, TestName = "parser.lex.19")>]
[<TestCase(19, TestName = "parser.lex.20")>]
[<TestCase(20, TestName = "parser.lex.21")>]
[<TestCase(21, TestName = "parser.lex.22")>]
[<TestCase(22, TestName = "parser.lex.23")>]
[<TestCase(23, TestName = "parser.lex.24")>]
[<TestCase(24, TestName = "parser.lex.25")>]
[<TestCase(25, TestName = "parser.lex.26")>]
[<TestCase(26, TestName = "parser.lex.27", ExpectedException=typeof<System.Exception>, ExpectedMessage = "lex:unrecognized OCaml-style escape in string")>]

let ``function lex`` idx =
    let (externalForm, _) = lexValues.[idx]
    let (_, result) = lexValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "converted form: %A" convertedForm

    let functionResult = NHol.parser.lex convertedForm
//    printfn "expected result: %A" result
//    printfn "function result: %A" functionResult
    functionResult |> assertEqual result

(* parse_pretype  tests *)

(* install_parser  tests *)

(* delete_parser  tests *)

(* installed_parsers  tests *)

(* try_user_parser  tests *)

(* parse_preterm  tests *)

(* parse_type  tests *)

(* parse_term  tests *)
