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

/// Tests for functions in the NHol.printer module.
module Tests.NHol.printer

open NUnit.Framework

(* OCaml.Compatability. *)

(* open_box  tests *)
(* close_box  tests *)
(* print_string  tests *)
(* print_as  tests *)
(* print_int  tests *)
(* print_float  tests *)
(* print_char  tests *)
(* print_bool  tests *)
(* print_space  tests *)
(* print_cut  tests *)
(* print_break  tests *)
(* print_flush  tests *)
(* print_newline  tests *)
(* force_newline  tests *)
(* print_if_newline  tests *)
(* set_margin  tests *)
(* get_margin  tests *)
(* set_max_indent  tests *)
(* get_max_indent  tests *)
(* set_max_boxes  tests *)
(* get_max_boxes  tests *)
(* over_max_boxes  tests *)
(* open_hbox  tests *)
(* open_vbox  tests *)
(* xyzopen_hvbox  tests *)
(* open_hovbox  tests *)
(* open_tbox  tests *)
(* close_tbox  tests *)
(* print_tbreak   tests *)
(* set_tab  tests *)
(* print_tab  tests *)
(* set_ellipsis_text  tests *)
(* get_ellipsis_text  tests *)
(* open_tag  tests *)
(* close_tag  tests *)
(* set_tags  tests *)
(* set_print_tags  tests *)
(* set_mark_tags  tests *)
(* get_print_tags  tests *)
(* get_mark_tags  tests *)
(* set_formatter_out_channel  tests *)
(* set_formatter_output_functions  tests *)
(* get_formatter_output_functions  tests *)
(* set_all_formatter_output_functions  tests *)
(* get_all_formatter_output_functions  tests *)
(* set_formatter_tag_functions  tests *)
(* get_formatter_tag_functions  tests *)
(* formatter_of_out_channel  tests *)
(* std_formatter  tests *)
(* err_formatter  tests *)
(* formatter_of_buffer  tests *)
(* stdbuf  tests *)
(* str_formatter  tests *)
(* flush_str_formatter  tests *)
(* make_formatter  tests *)
(* pp_open_hbox  tests *)
(* pp_open_vbox  tests *)
(* pp_open_hvbox  tests *)
(* pp_open_hovbox  tests *)
(* pp_open_box  tests *)
(* pp_close_box  tests *)
(* pp_open_tag  tests *)
(* pp_close_tag  tests *)
(* pp_print_string  tests *)
(* pp_print_as  tests *)
(* pp_print_int  tests *)
(* pp_print_float  tests *)
(* pp_print_char  tests *)
(* pp_print_bool  tests *)
(* pp_print_break  tests *)
(* pp_print_cut  tests *)
(* pp_print_space  tests *)
(* pp_force_newline  tests *)
(* pp_print_flush  tests *)
(* pp_print_newline  tests *)
(* pp_print_if_newline  tests *)
(* pp_open_tbox  tests *)
(* pp_close_tbox  tests *)
(* pp_print_tbreak  tests *)
(* pp_set_tab  tests *)
(* pp_print_tab  tests *)
(* pp_set_tags  tests *)
(* pp_set_print_tags  tests *)
(* pp_set_mark_tags  tests *)
(* pp_get_print_tags  tests *)
(* pp_get_mark_tags  tests *)
(* pp_set_margin  tests *)
(* pp_get_margin  tests *)
(* pp_set_max_indent  tests *)
(* pp_get_max_indent  tests *)
(* pp_set_max_boxes  tests *)
(* pp_get_max_boxes  tests *)
(* pp_over_max_boxes  tests *)
(* pp_set_ellipsis_text  tests *)
(* pp_get_ellipsis_text  tests *)
(* pp_set_formatter_out_channel  tests *)
(* pp_set_formatter_output_functions  tests *)
(* pp_get_formatter_output_functions  tests *)
(* pp_set_all_formatter_output_functions  tests *)
(* pp_get_all_formatter_output_functions  tests *)
(* pp_set_formatter_tag_functions  tests *)
(* pp_get_formatter_tag_functions  tests *)
(* fprintf  tests *)
(* printf  tests *)
(* eprintf  tests *)
(* sprintf  tests *)
(* bprintf  tests *)
(* kfprintf  tests *)
(* ifprintf  tests *)
(* ksprintf  tests *)
(* kprintf  tests *)

(* charcode  tests *)

[<Test>]
let ``function charcode`` () =
    // This is copied from charcode because it is private.
    // TODO: When we have a standard plan for testing private functions this copy of charcode needs to be removed.
    // Note: 65536 retuns 0
    let inline charcode (s : string) = int s.[0]
    for i in 0 .. 65535 do
        let ch = char(i)
        let result = charcode (ch.ToString ())
        Assert.AreEqual(result,i)

(* ctable  tests *)

(* checkStringIsSingleChar  tests *)

(* name_of  tests *)

(* pp_print_type  tests *)

(* pp_print_qtype  tests *)

(* install_user_printer  tests *)

(* delete_user_printer  tests *)

(* try_user_printer  tests *)

(* pp_print_term  tests *)

(* pp_print_qterm  tests *)

(* pp_print_thm  tests *)

(* print_type  tests *)

(* print_qtype  tests *)

(* print_term  tests *)

(* print_qterm  tests *)

(* print_thm  tests *)

(* print_to_string  tests *)

(* string_of_type  tests *)

(* string_of_term  tests *)

(* string_of_thm  tests *)

(* isspace tests *)

[<Test>]
let ``function isspace`` () =
    // Note: The OCaml char range is 0-255, but in NHol with F# it is 0..65535
    // We expect System.IndexOutOfRangeException for characters with values of 256 or greater.
    let inline charcode (s : string) = int s.[0]
    for i in 0 .. 65535 do
//        if (i = 65535) then printfn "Done."
        try
            match char(i) with
            | ' ' | '\t' | '\n' | '\r' ->
                let result = NHol.printer.isspace (char(i).ToString())
//                printfn "i: %d ch: '%s' expected: %b result: %b " i (char(i).ToString()) true result
                result |> Assert.True
            | _ ->
                let result = NHol.printer.isspace (char(i).ToString())
//                printfn "i: %d ch: '%s' expected: %b result: %b " i (char(i).ToString()) false result
                result |> Assert.False
        with
        | ex ->
            Assert.IsInstanceOf<System.IndexOutOfRangeException>(ex)

(* issep tests *)

[<Test>]
let ``function issep`` () =
    // Note: The OCaml char range is 0-255, but in NHol with F# it is 0..65535
    // We expect System.IndexOutOfRangeException for characters with values of 256 or greater.
    let inline charcode (s : string) = int s.[0]
    for i in 0 .. 65535 do
//        if (i = 65535) then printfn "Done."
        try
            match char(i) with
            | ',' | ';' ->
                let result = NHol.printer.issep (char(i).ToString())
//                printfn "i: %d ch: '%s' expected: %b result: %b " i (char(i).ToString()) true result
                result |> Assert.True
            | _ ->
                let result = NHol.printer.issep (char(i).ToString())
//                printfn "i: %d ch: '%s' expected: %b result: %b " i (char(i).ToString()) false result
                result |> Assert.False
        with
        | ex ->
            Assert.IsInstanceOf<System.IndexOutOfRangeException>(ex)

(* isbra tests *)

[<Test>]
let ``function isbra`` () =
    // Note: The OCaml char range is 0-255, but in NHol with F# it is 0..65535
    // We expect System.IndexOutOfRangeException for characters with values of 256 or greater.
    let inline charcode (s : string) = int s.[0]
    for i in 0 .. 65535 do
//        if (i = 65535) then printfn "Done."
        try
            match char(i) with
            | '(' | ')' | '[' | ']' | '{' | '}' ->
                let result = NHol.printer.isbra (char(i).ToString())
//                printfn "i: %d ch: '%s' expected: %b result: %b " i (char(i).ToString()) true result
                result |> Assert.True
            | _ ->
                let result = NHol.printer.isbra (char(i).ToString())
//                printfn "i: %d ch: '%s' expected: %b result: %b " i (char(i).ToString()) false result
                result |> Assert.False
        with
        | ex ->
            Assert.IsInstanceOf<System.IndexOutOfRangeException>(ex)

(* issymb tests *)

[<Test>]
let ``function issymb`` () =
    // Note: The OCaml char range is 0-255, but in NHol with F# it is 0..65535
    // We expect System.IndexOutOfRangeException for characters with values of 256 or greater.
    let inline charcode (s : string) = int s.[0]
    for i in 0 .. 65535 do
//        if (i = 65535) then printfn "Done."
        try
            match char(i) with
            | '\\' | '!' | '@' | '#' | '$' | '%' | '^' | '&' | '*' | '-' | '+' | '|' | '<' | '=' | '>' | '/' | '?' | '~' | '.' | ':' ->
                let result = NHol.printer.issymb (char(i).ToString())
//                printfn "i: %d ch: '%s' expected: %b result: %b " i (char(i).ToString()) true result
                result |> Assert.True
            | _ ->
                let result = NHol.printer.issymb (char(i).ToString())
//                printfn "i: %d ch: '%s' expected: %b result: %b " i (char(i).ToString()) false result
                result |> Assert.False
        with
        | ex ->
            Assert.IsInstanceOf<System.IndexOutOfRangeException>(ex)

(* isalpha tests *)

[<Test>]
let ``function isalpha`` () =
    // Note: The OCaml char range is 0-255, but in NHol with F# it is 0..65535
    // We expect System.IndexOutOfRangeException for characters with values of 256 or greater.
    let (|NHolalphaChar|_|) c =
        if c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c = '_' || c = '\'' then Some(c) else None
    let inline charcode (s : string) = int s.[0]
    for i in 0 .. 65535 do
//        if (i = 65535) then printfn "Done."
        try
            match char(i) with
            | NHolalphaChar c ->
                let result = NHol.printer.isalpha (char(i).ToString())
//                printfn "i: %d ch: '%s' expected: %b result: %b " i (char(i).ToString()) true result
                result |> Assert.True
            | _ ->
                let result = NHol.printer.isalpha (char(i).ToString())
//                printfn "i: %d ch: '%s' expected: %b result: %b " i (char(i).ToString()) false result
                result |> Assert.False
        with
        | ex ->
            Assert.IsInstanceOf<System.IndexOutOfRangeException>(ex)

(* isnum tests *)

[<Test>]
let ``function isnum`` () =
    // Note: The OCaml char range is 0-255, but in NHol with F# it is 0..65535
    // We expect System.IndexOutOfRangeException for characters with values of 256 or greater.
    let inline charcode (s : string) = int s.[0]
    for i in 0 .. 65535 do
//        if (i = 65535) then printfn "Done."
        try
            match char(i) with
            | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' ->
                let result = NHol.printer.isnum (char(i).ToString())
//                printfn "i: %d ch: '%s' expected: %b result: %b " i (char(i).ToString()) true result
                result |> Assert.True
            | _ ->
                let result = NHol.printer.isnum (char(i).ToString())
//                printfn "i: %d ch: '%s' expected: %b result: %b " i (char(i).ToString()) false result
                result |> Assert.False
        with
        | ex ->
            Assert.IsInstanceOf<System.IndexOutOfRangeException>(ex)

(* isalnum tests *)

[<Test>]
let ``function isalnum`` () =
    // Note: The OCaml char range is 0-255, but in NHol with F# it is 0..65535
    // We expect System.IndexOutOfRangeException for characters with values of 256 or greater.
    let (|NHolalnumChar|_|) c =
        if c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c = '_' || c = '\'' || c >= '0' && c <= '9' then Some(c) else None
    let inline charcode (s : string) = int s.[0]
    for i in 0 .. 65535 do
//        if (i = 65535) then printfn "Done."
        try
            match char(i) with
            | NHolalnumChar c ->
                let result = NHol.printer.isalnum (char(i).ToString())
//                printfn "i: %d ch: '%s' expected: %b result: %b " i (char(i).ToString()) true result
                result |> Assert.True
            | _ ->
                let result = NHol.printer.isalnum (char(i).ToString())
//                printfn "i: %d ch: '%s' expected: %b result: %b " i (char(i).ToString()) false result
                result |> Assert.False
        with
        | ex ->
            Assert.IsInstanceOf<System.IndexOutOfRangeException>(ex)

(* reserve_words  tests *)

(* unreserve_words  tests *)

(* is_reserved_word  tests *)

let private is_reserved_wordValues : (string * bool)[] = [|
    (
        // idx 0
        // printer.is_reserved_word.01
        "(",
        true
    );
    (
        // idx 1
        // printer.is_reserved_word.02
        ")",
        true
    );
    (
        // idx 2
        // printer.is_reserved_word.03
        "[",
        true
    );
    (
        // idx 3
        // printer.is_reserved_word.04
        "]",
        true
    );
    (
        // idx 4
        // printer.is_reserved_word.05
        "{",
        true
    );
    (
        // idx 5
        // printer.is_reserved_word.06
        "}",
        true
    );
    (
        // idx 6
        // printer.is_reserved_word.07
        ":",
        true
    );
    (
        // idx 7
        // printer.is_reserved_word.08
        ";",
        true
    );
    (
        // idx 8
        // printer.is_reserved_word.09
        ".",
        true
    );
    (
        // idx 9
        // printer.is_reserved_word.10
        "|",
        true
    );
    (
        // idx 10
        // printer.is_reserved_word.11
        "let",
        true
    );
    (
        // idx 11
        // printer.is_reserved_word.12
        "in",
        true
    );
    (
        // idx 12
        // printer.is_reserved_word.13
        "and",
        true
    );
    (
        // idx 13
        // printer.is_reserved_word.14
        "if",
        true
    );
    (
        // idx 14
        // printer.is_reserved_word.15
        "then",
        true
    );
    (
        // idx 15
        // printer.is_reserved_word.16
        "else",
        true
    );
    (
        // idx 16
        // printer.is_reserved_word.17
        "match",
        true
    );
    (
        // idx 17
        // printer.is_reserved_word.18
        "with",
        true
    );
    (
        // idx 18
        // printer.is_reserved_word.19
        "function",
        true
    );
    (
        // idx 19
        // printer.is_reserved_word.20
        "->",
        true
    );
    (
        // idx 20
        // printer.is_reserved_word.21
        "when",
        true
    );
    (
        // idx 21
        // printer.is_reserved_word.22
        "",
        false
    );
    (
        // idx 22
        // printer.is_reserved_word.23
        "a",
        false
    );
    (
        // idx 23
        // printer.is_reserved_word.24
        "#",
        false
    );
    |]

[<Test>]
[<TestCase(0, TestName = "printer.is_reserved_word.01")>]
[<TestCase(1, TestName = "printer.is_reserved_word.02")>]
[<TestCase(2, TestName = "printer.is_reserved_word.03")>]
[<TestCase(3, TestName = "printer.is_reserved_word.04")>]
[<TestCase(4, TestName = "printer.is_reserved_word.05")>]
[<TestCase(5, TestName = "printer.is_reserved_word.06")>]
[<TestCase(6, TestName = "printer.is_reserved_word.07")>]
[<TestCase(7, TestName = "printer.is_reserved_word.08")>]
[<TestCase(8, TestName = "printer.is_reserved_word.09")>]
[<TestCase(9, TestName = "printer.is_reserved_word.10")>]
[<TestCase(10, TestName = "printer.is_reserved_word.11")>]
[<TestCase(11, TestName = "printer.is_reserved_word.12")>]
[<TestCase(12, TestName = "printer.is_reserved_word.13")>]
[<TestCase(13, TestName = "printer.is_reserved_word.14")>]
[<TestCase(14, TestName = "printer.is_reserved_word.15")>]
[<TestCase(15, TestName = "printer.is_reserved_word.16")>]
[<TestCase(16, TestName = "printer.is_reserved_word.17")>]
[<TestCase(17, TestName = "printer.is_reserved_word.18")>]
[<TestCase(18, TestName = "printer.is_reserved_word.19")>]
[<TestCase(19, TestName = "printer.is_reserved_word.20")>]
[<TestCase(20, TestName = "printer.is_reserved_word.21")>]
[<TestCase(21, TestName = "printer.is_reserved_word.22")>]
[<TestCase(22, TestName = "printer.is_reserved_word.23")>]
[<TestCase(23, TestName = "printer.is_reserved_word.24")>]
let ``function is_reserved_word`` idx =
    let (word, _) = is_reserved_wordValues.[idx]
    let (_, result) = is_reserved_wordValues.[idx]
    let end_itlistResult = NHol.printer.is_reserved_word word
//    printfn "%A" end_itlistResult
    end_itlistResult |> assertEqual result

(* reserved_words  tests *)

(* unparse_as_binder  tests *)
(* parse_as_binder  tests *)
(* parses_as_binder  tests *)
(* binders  tests *)
(* unparse_as_prefix  tests *)
(* parse_as_prefix  tests *)
(* is_prefix  tests *)
(* prefixes  tests *)
(* unparse_as_infix  tests *)
(* parse_as_infix  tests *)
(* get_infix_status  tests *)
(* infixes  tests *)