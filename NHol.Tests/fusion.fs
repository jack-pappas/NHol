(*

Copyright 2013 Jack Pappas, Anh-Dung Phan

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

/// Tests for functions in the NHol.fusion module.
module Tests.NHol.fusion

open NHol.fusion

open NUnit.Framework
open FsUnit

// Note: Many of the next test cases came from the HOL Light reference manual

(* types tests *)

[<Test>]
let ``{types} returns a list of all the type constructors declared``() =

    types ()
    |> assertEqual [("bool",0); ("fun",2)]

(* get_type_arity tests *)

[<Test>]
let ``{get_type_arity} when applied to the name of a type constructor returns its arity``() =

    get_type_arity "bool"
    |> evaluate
    |> assertEqual 0

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "find")>]
let ``{get_type_arity} fails if there is no type constructor of that name``() =

    get_type_arity "nocon"
    |> evaluate
    |> assertEqual 0

(* new_type tests *)

[<Test>]
let ``{new_type {"t",n}} declares a new {n}-ary type constructor called {t}``() =

    let expected = [("set",0); ("bool",0); ("fun",2)]

    new_type ("set",0) |> ignore

    let actual = !the_type_constants

    the_type_constants := [("bool",0); ("fun",2)]

    actual
    |> assertEqual expected

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "new_type: type bool has already been declared")>]
let ``{new_type {"t",n}} fails if HOL is there is already a type operator of that name in the current theory``() =

    new_type ("bool",0) 
    |> evaluate
    |> ignore

(* mk_type tests *)

[<Test>]
let ``{mk_type} constructs a type, other than a variable type``() =

    mk_type ("bool",[])
    |> evaluate
    |> assertEqual (Tyapp ("bool", []))

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "mk_type: type set has not been defined")>]
let ``{mk_type} fails if the string is not the name of a known type``() =

    mk_type ("set",[])
    |> evaluate
    |> ignore

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "mk_type: wrong number of arguments to fun")>]
let ``{mk_type} fails if if the type is known but the length of the list of argument types is not equal to the arity of the type constructor``() =

    mk_type ("fun",[])
    |> evaluate
    |> ignore

(* mk_vartype tests *)

[<Test>]
let ``{mk_vartype "A"} returns a type variable {:A}``() =

    mk_vartype "Test"
    |> assertEqual (Tyvar "Test")

(* dest_type tests *)

[<Test>]
let ``{dest_type} breaks apart a type``() =

    dest_type (Tyapp ("fun", [Tyvar "A"; Tyvar "B"]))
    |> evaluate
    |> assertEqual ("fun", [Tyvar "A"; Tyvar "B"])

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "dest_type: type variable not a constructor")>]
let ``{dest_type} fails if the type is a type variable``() =

    dest_type (Tyvar "Test")
    |> evaluate
    |> ignore

(* dest_vartype tests *)

[<Test>]
let ``{dest_vartype} breaks a type variable down to its name``() =

    dest_vartype (Tyvar "A")
    |> evaluate
    |> assertEqual "A"

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "dest_vartype: type constructor not a variable")>]
let ``{dest_vartype} fails if the type is not a type variable``() =

    dest_vartype (Tyapp ("bool", []))
    |> evaluate
    |> ignore

(* is_type tests *)

[<Test>]
let ``{is_type ty} returns {true} if {ty} is a base type or constructed by an outer type constructor``() =

    is_type (Tyapp ("fun", [Tyvar "A"; Tyvar "B"]))
    |> assertEqual true

[<Test>]
let ``{is_type ty} returns {false} if {ty} is a type variable``() =

    is_type (Tyvar "A")
    |> assertEqual false

(* is_vartype tests *)

[<Test>]
let ``{is_vartype ty} returns {true} if {ty} is a type variable``() =

    is_vartype (Tyvar "A")
    |> assertEqual true

[<Test>]
let ``{is_vartype ty} returns {false} if {ty} is not a type variable``() =

    is_vartype (Tyapp ("fun", [Tyvar "A"; Tyvar "B"]))
    |> assertEqual false

(* tyvars tests *)

[<Test>]
let ``{tyvars}, when applied to a type, returns a list, possibly empty, of the type  variables``() =

    tyvars (Tyapp ("fun", [Tyvar "A"; Tyapp ("fun", [Tyvar "A"; Tyvar "B"])]))
    |> assertEqual [Tyvar "A";Tyvar "B"]

(* constants tests *)

[<Test>]
let ``{constants} returns a list of all the constants that have been defined so far``() =

    constants ()
    |> assertEqual [("=", Tyapp ("fun", [aty; Tyapp ("fun",[aty; bool_ty])]))]

(* get_const_type tests *)

[<Test>]
let ``{get_const_type "c"} returns the generic type of {c}, if {c} is a constant``() =

    get_const_type "="
    |> evaluate
    |> assertEqual (Tyapp ("fun", [aty; Tyapp ("fun",[aty; bool_ty])]))

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "find")>]
let ``{get_const_type st} fails if {st} is not the name of a constant``() =

    get_const_type "xx"
    |> evaluate
    |> ignore

(* new_constant tests *)

[<Test>]
let ``{new_constant {"c",:ty}} makes {c} a constant with most general type {ty}``() =

    new_constant ("graham's_number", Tyvar "num") |> ignore

    let expected = [("graham's_number", Tyvar "num");("=",Tyapp("fun",[aty;Tyapp("fun",[aty;bool_ty])]))]
    let actual = !the_term_constants

    the_term_constants := ["=",Tyapp("fun",[aty;Tyapp("fun",[aty;bool_ty])])]

    actual
    |> assertEqual expected

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "new_constant: constant = has already been declared")>]
let ``{new_constant {"c",:ty}} fails if there is already a constant of that name in the current theory``() =

    new_constant ("=", Tyvar "num")
    |> evaluate 
    |> ignore

(* type_of tests *)

[<Test>]
let ``{type_of} returns the type of a term``() =

    type_of (Const ("=",Tyapp("fun",[aty;Tyapp("fun",[aty;bool_ty])])))
    |> evaluate
    |> assertEqual (Tyapp ("fun", [aty; Tyapp ("fun",[aty; bool_ty])]))

(* inst tests *)

[<Test>]
let ``{inst [ty1,tv1; _ ; tyn,tvn] t} will systematically replace each type variable {tvi} by the corresponding type {tyi} inside the term {t}``() =

    // `x:A = x`
    let input = 
        Comb
            (Comb
               (Const
                  ("=",
                   Tyapp
                     ("fun",[Tyvar "A"; Tyapp ("fun",[Tyvar "A"; Tyapp ("bool",[])])])), Var ("x",Tyvar "A")),Var ("x",Tyvar "A"))

    let expected = 
        Comb
            (Comb
               (Const
                  ("=",
                   Tyapp
                     ("fun",[Tyvar "num"; Tyapp ("fun",[Tyvar "num"; Tyapp ("bool",[])])])), Var ("x",Tyvar "num")),Var ("x",Tyvar "num"))

    let actual = inst [Tyvar "num",Tyvar "A"] input


    actual
    |> evaluate
    |> assertEqual expected

(* REFL tests *)

[<Test>]
let ``{REFL} maps any term {t} to the corresponding theorem {|- t = t}``() =

    let input = Const ("2", Tyvar "num")
    let expected = 
        Sequent 
            (
                [], 
                Comb 
                    (
                        Comb 
                            (
                                Const 
                                    (
                                        "=", 
                                        Tyapp ("fun", [Tyvar "num"; Tyapp ("fun", [Tyvar "num"; Tyapp ("bool", [])])])
                                    ), 
                                Const 
                                    (
                                        "2", 
                                        Tyvar "num"
                                    )
                            ), 
                        Const ("2", Tyvar "num")
                    )
            )

    REFL input
    |> evaluate
    |> assertEqual expected




