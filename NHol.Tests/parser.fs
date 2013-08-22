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
//    printfn "convertedForm: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let seperatorParser = a seperator
    let stringParser = NHol.parser.listof valueParser seperatorParser "listof error"
    let (current, rest) = stringParser internalForm
//    printfn "current: %A" current
//    printfn "rest: %A" rest
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
//    printfn "convertedForm: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let seperatorParser = a seperator
    let lexcodeParser = NHol.parser.listof valueParser seperatorParser "listof error"
    let (current, rest) = lexcodeParser internalForm
//    printfn "current: %A" current
//    printfn "rest: %A" rest
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
let private possiblyStringTypeValues : (string * string list * string * (string list * string list))[] = [|
    (
        // idx 0
        // parser.possibly.01
        // No input
        "",    // humans read this
        [],    // the NHol.parser.possibly function reads this
        "",
        ([],[])  // Notice result is a (string list * string list) and not (string * string list)
    );
    (
        // idx 1
        // parser.possibly.02
        // one char input, one value that matches
        "1",
        ["1"],
        "",
        (["1"],[])
    );
    (
        // idx 2
        // parser.possibly.03
        // one char input, one value that doesn't match
        "a",
        ["a"],
        "",
        ([],["a"])
    );
    (
        // idx 3
        // parser.possibly.04
        // two char input, one value that matches
        "12",
        ["1";"2"],
        "",
        (["1"],["2"])
    );
    (
        // idx 4
        // parser.possibly.05
        // two char input, first value doesn't match, second value matches
        "a1",
        ["a";"1"],
        "",
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
    let (externalForm, _, _, _) = possiblyStringTypeValues.[idx]
    let (_, internalForm, _, _) = possiblyStringTypeValues.[idx]
    let (_, _, value, _) = possiblyStringTypeValues.[idx]
    let (_, _, _, (currentResult , restResult)) = possiblyStringTypeValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = NHol.lib.explode externalForm
//    printfn "convertedForm: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let stringParser : string list -> string list * string list = NHol.parser.possibly intParser
    let (current, rest) = stringParser internalForm
//    printfn "current: %A" current
//    printfn "rest: %A" rest
    Assert.AreEqual(current, currentResult)
    Assert.AreEqual(rest, restResult)

// The first sting is what humans expect to read
// and the second lexcode list is what the function reads.
// Both are shown to make the test easier to comprehend.
let private possiblyLexcodeTypeValues : (string * lexcode list * lexcode * (lexcode list * lexcode list))[] = [|
    (
        // idx 0
        // parser.possibly.101
        // No input
        "",    // humans read this
        [],    // the NHol.parser.possibly function reads this
        Ident "",
        ([],[])  // Notice result is a (lexcode list * lexcode list) and not (lexcode * lexcode list)
    );
    (
        // idx 1
        // parser.possibly.102
        // one char input, one value that matches
        "1",
        [Ident "1"],
        Ident "",
        ([Ident "1"],[])
    );
    (
        // idx 2
        // parser.possibly.103
        // one char input, one value that doesn't match
        "a",
        [Ident "a"],
        Ident "",
        ([],[Ident "a"])
    );
    (
        // idx 3
        // parser.possibly.104
        // two char input, one value that matches
        "12",
        [Ident "12"],
        Ident "",
        ([Ident "12"],[])
    );
    (
        // idx 4
        // parser.possibly.105
        // two char input, first value doesn't match, second value matches
        "a1",
        [Ident "a1"],
        Ident "",
        ([],[Ident "a1"])
    );
    (
        // idx 5
        // parser.possibly.106
        // three char input, first value matches second value doesn't match
        "12a",
        [Ident "12a"],
        Ident "",
        ([],[Ident "12a"])
    );
    (
        // idx 6
        // parser.possibly.107
        // three char input, first value matches second value doesn't match
        "12#",
        [Ident "12";Ident "#"],
        Ident "",
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
    let (externalForm, _, _, _) = possiblyLexcodeTypeValues.[idx]
    let (_, internalForm, _, _) = possiblyLexcodeTypeValues.[idx]
    let (_, _, value, _) = possiblyLexcodeTypeValues.[idx]
    let (_, _, _, (currentResult , restResult)) = possiblyLexcodeTypeValues.[idx]

    // Verify function input form and human form match.
    let convertedForm = (NHol.parser.lex << NHol.lib.explode) externalForm  // Notice use of lex to convert string to lexcode.
//    printfn "convertedForm: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let lexcodeParser : lexcode list -> lexcode list * lexcode list = NHol.parser.possibly intLexcodeParser
    let (current, rest) = lexcodeParser internalForm
//    printfn "current: %A" current
//    printfn "rest: %A" rest
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
//    printfn "convertedForm: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let stringParser : string list -> string * string list = NHol.parser.some isNum
    let (current, rest) = stringParser internalForm
//    printfn "current: %A" current
//    printfn "rest: %A" rest
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
        // one char input, one value that matches
        "1",
        [Ident "1"],
        (Ident "1",[])
    );
    (
        // idx 2
        // parser.some.103
        // one char input, one value that doesn't match
        // throws NHol.parser.Noparse
        "a",
        [Ident "a"],
        (Ident "",[])  // dummy value
    );
    (
        // idx 3
        // parser.some.104
        // two char input, one value that matches
        "12",
        [Ident "12"],
        (Ident "12",[])
    );
    (
        // idx 4
        // parser.some.105
        // two char input, first value doesn't match, second value matches
        // throws NHol.parser.Noparse
        "a1",
        [Ident "a1"],
        (Ident "",[])  // dummy value
    );
    (
        // idx 5
        // parser.some.106
        // three char input, first value matches second value doesn't match
        // throws NHol.parser.Noparse
        // Note: This throws Noparse exception because "12a" is lexed as "12a" and not "12" and "a",
        // so "12a" is not a num.
        "12a",
        [Ident "12a"],
        (Ident "",[])
    );
    (
        // idx 6
        // parser.some.107
        // three char input, first value matches second value doesn't match
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
//    printfn "convertedForm: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let lexcodeParser : lexcode list -> lexcode * lexcode list = NHol.parser.some isLexcodeNum
    let (current, rest) = lexcodeParser internalForm
//    printfn "current: %A" current
//    printfn "rest: %A" rest
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
//    printfn "convertedForm: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let stringParser : string list -> string * string list = NHol.parser.a value
    let (current, rest) = stringParser internalForm
//    printfn "current: %A" current
//    printfn "rest: %A" rest
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
        // one char input, empty value
        // throws NHol.parser.Noparse
        "(",
        [Resword "("],
        Resword "",
        (Resword "",[])  // dummy value
    );
    (
        // idx 2
        // parser.a.103
        // one char input, value that matches
        "(",
        [Resword "("],
        Resword "(",
        (Resword "(",[])
    );
    (
        // idx 3
        // parser.a.104
        // one char input, value that doesn't match
        // throws NHol.parser.Noparse
        "(",
        [Resword "("],
        Resword ")",
        (Resword "",[])  // dummy value
    );
    (
        // idx 4
        // parser.a.105
        // multi char input, value that matches
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
//    printfn "convertedForm: %A" convertedForm
    Assert.AreEqual(convertedForm, internalForm)

    // Verify result of function
    let lexcodeParser : lexcode list -> lexcode * lexcode list = NHol.parser.a value
    let (current, rest) = lexcodeParser internalForm
//    printfn "current: %A" current
//    printfn "rest: %A" rest
    Assert.AreEqual(current, currentResult)
    Assert.AreEqual(rest, restResult)

(* atleast  tests *)

(* finished  tests *)

(* comment_token  tests *)

(* lex  tests *)

let private lexValues : (string * NHol.parser.lexcode list)[] = [|
    (
        // idx 0
        // parser.lex.01
        // empty string using double quotes
        "if p+1=2 then x + 1 else y - 1",
        [Resword "if"; Ident "p"; Ident "+"; Ident "1"; Ident "="; Ident "2";
         Resword "then"; Ident "x"; Ident "+"; Ident "1"; Resword "else"; Ident "y";
         Ident "-"; Ident "1"]
    );
    |]

[<Test>]
[<TestCase(0, TestName = "parser.lex.01")>]
let ``function lex`` idx =
    let (input, _) = lexValues.[idx]
    let (_, result) = lexValues.[idx]

    let strings = NHol.lib.explode input
    let lexResult = NHol.parser.lex strings
    printfn "%A" lexResult
    lexResult |> assertEqual result

(* parse_pretype  tests *)

(* install_parser  tests *)

(* xyzdelete_parser  tests *)

(* installed_parsers  tests *)

(* try_user_parser  tests *)

(* parse_preterm  tests *)

(* parse_type  tests *)

(* parse_term  tests *)
