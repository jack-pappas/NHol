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

/// Tests for functions in the NHol.nets module.
module Tests.NHol.nets

open NHol.fusion
open NHol.nets

open NUnit.Framework
open FsUnit

[<Test>]
let dummy () : unit =
    Assert.Ignore "Test not yet implemented."

[<Test>]
let ``{enter} insert a new element into a net``() =

    let aTerm = Const ("a",Tyvar "bool")
    let bTerm = Const ("b",Tyvar "bool")

    //a = b
    let equalityTerm = 
        Comb
            (Comb
               (Const
                  ("=",
                   Tyapp
                     ("fun",[Tyvar "A"; Tyapp ("fun",[Tyvar "A"; Tyapp ("bool",[])])])), aTerm),bTerm)

    let MY_CONV (x:term) = Sequent([], equalityTerm)

    let expected = Netnode([(Cnet("a", 0), Netnode([], [MY_CONV]))], [])

    let actual = enter [] (aTerm,MY_CONV) empty_net

    actual
    |> should equal expected

//[<Test>]
//let ``{lookup} looks up a term in a net and return possible matches``() =
//
//    let aTerm = Const ("a",Tyvar "bool")
//    let bTerm = Const ("b",Tyvar "bool")
//
//    //a = b
//    let equalityTerm = 
//        Comb
//            (Comb
//               (Const
//                  ("=",
//                   Tyapp
//                     ("fun",[Tyvar "A"; Tyapp ("fun",[Tyvar "A"; Tyapp ("bool",[])])])), aTerm),bTerm)
//
//    let MY_CONV (x:term) = Sequent([], equalityTerm)
//
//    let termNet = Netnode([(Cnet("a", 0), Netnode([], [MY_CONV]))], [])
//
//    let actual = lookup bTerm termNet
//
//    actual
//    |> should equal bTerm




