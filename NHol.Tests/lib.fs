(*

Copyright 2013 Jack Pappas, Anh-Dung Phan, Domenico D. D. Masini

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

/// Tests for functions in the NHol.lib module.
module Tests.NHol.lib

open NHol.lib

open NUnit.Framework
open FsUnit
open FsCheck
open FSharp.Compatibility.OCaml

#nowarn "62"

open FSharp.Compatibility.OCaml.Big_int
open FSharp.Compatibility.OCaml.Num

// Almost all functions here have equivalences in FSharp.Core.
// We use the core functions as models for testing.

[<Test>]
let ``map is equivalent to List.map``() =
    assertProp "map" <| fun (xs : int list) f ->
        map f xs = List.map f xs

[<Test>]
let ``map2 is equivalent to List.map2``() =
    assertProp "map2" <| fun (zs : (int * int) list) f ->
        let (xs, ys) = List.unzip zs
        map2 f xs ys = List.map2 f xs ys

[<Test>]
let ``el is equivalent to List.nth``() =
    assertProp "chop_list" <| fun n xs ->
        (n >= 0 && List.length xs > n) ==> 
            lazy (el n xs = List.nth xs n)

[<Test>]
let ``itlist is equivalent to List.fold``() =
    assertProp "itlist" <| fun xs ->
        itlist (fun x acc -> acc - x) xs 0 = List.fold (fun acc x -> acc - x) 0 xs

[<Test>]
let ``rev_itlist is equivalent to List.fold``() =
    assertProp "rev_itlist" <| fun xs ->
        rev_itlist (fun x acc -> x - acc) xs 0 = List.fold (fun acc x -> x - acc) 0 xs

[<Test>]
let ``end_itlist is equivalent to List.reduceBack on non-empty lists``() =
    assertProp "end_itlist" <| fun (xs : int list) f ->
        xs <> [] ==> lazy (end_itlist f xs = List.reduceBack f xs)

[<Test>]
let ``itlist2 is equivalent to List.foldBack2 on two same-length lists``() =
    assertProp "itlist2" <| fun zs f ->
        let (xs : int64 list), (ys : int16 list) = List.unzip zs
        itlist2 f xs ys "" = List.foldBack2 f xs ys ""

[<Test>]
let ``rev_itlist2 is equivalent to List.fold2 on two same-length lists``() =
    assertProp "rev_itlist2" <| fun zs ->
        let (xs : int64 list), (ys : int16 list) = List.unzip zs
        rev_itlist2 (fun x y acc -> acc + ((int x) + (int y)).ToString()) xs ys "" = List.fold2 (fun acc x y -> acc + ((int x) + (int y)).ToString()) "" xs ys

[<Test>]
let ``replicate is equivalent to List.replicate``() =
    assertProp "replicate" <| fun x n ->
        n >= 0 ==> lazy (replicate x n = List.replicate n x)

[<Test>]
let ``-- is equivalent to ..``() =
    assertProp "(--)" <| fun m n ->
        m -- n = [m..n]

[<Test>]
let ``forall is equivalent to List.forall``() =
    assertProp "forall" <| fun (xs : int list) f ->
        forall f xs = List.forall f xs

[<Test>]
let ``forall2 is equivalent to List.forall2``() =
    assertProp "forall2" <| fun (zs : (int * int) list) f ->
        let (xs, ys) = List.unzip zs
        forall2 f xs ys = List.forall2 f xs ys

[<Test>]
let ``exists is equivalent to List.exists``() =
    assertProp "exists" <| fun (xs : int list) f ->
        exists f xs = List.exists f xs

[<Test>]
let ``length is equivalent to List.length``() =
    assertProp "length" <| fun xs ->
        length xs = List.length xs

[<Test>]
let ``filter is equivalent to List.filter``() =
    assertProp "filter" <| fun (xs : int list) f ->
        filter f xs = List.filter f xs

[<Test>]
let ``partition is equivalent to List.partition``() =
    assertProp "partition" <| fun (xs : int list) f ->
        partition f xs = List.partition f xs

// The `lazy` keyword is important in order to avoid early evaluation
[<Test>]
let ``find is equivalent to List.find``() =
    assertProp "find" <| fun xs ->
        List.exists (fun x -> x > 0) xs ==> 
            lazy (find (fun x -> x > 0) xs = (Some <| List.find (fun x -> x > 0) xs))

[<Test>]
let ``index is equivalent to List.findIndex``() =
    assertProp "index" <| fun xs ->
        List.exists (fun x -> x = 3) xs ==> 
            lazy (index 3 xs = List.findIndex (fun x -> x = 3) xs)

[<Test>]
let ``chop_list is equivalent to List.take``() =
    assertProp "chop_list" <| fun n xs ->
        (n >= 0 && List.length xs >= n) ==> 
            lazy (chop_list n xs = List.take n xs)

[<Test>]
let ``flat is equivalent to List.concat``() =
    assertProp "flat" <| fun xss ->
        flat xss = List.concat xss

[<Test>]
let ``sort is equivalent to List.sortWith``() =
    assertProp "sort" <| fun (xs : int list) ->
        sort (<) xs = List.sortWith compare xs

[<Test>]
let ``mergesort is equivalent to List.sortWith``() =
    assertProp "mergesort" <| fun (xs : int list) ->
        mergesort (<) xs = List.sortWith compare xs

// Now other functions are tested based on their properties

[<Test>]
let ``zip and unzip inverse each other``() =
    assertProp "zip-unzip" <| fun zs ->
        let (xs, ys) = unzip zs
        zs = zip xs ys

[<Test>]
let ``hd and tl can build up the old list``() =
    assertProp "hd-tl" <| fun xs ->
        xs <> [] ==> lazy (hd xs :: tl xs = xs)

[<Test>]
let ``last and butlast can build up the old list``() =
    assertProp "last-butlast" <| fun xs ->
        xs <> [] ==> lazy ([yield! butlast xs; yield last xs] = xs)

[<Test>]
let ``reversing a list two times gives the list``() =
    assertProp "rev" <| fun xs ->
        rev (rev xs) = xs

[<Test>]
let ``intersect and subtract can build up the set``() =
    assertProp "intersect-subtract" <| fun (xs : int list) ys ->
        setify (intersect xs ys @ subtract xs ys) = setify xs

[<Test>]
let ``union and subtract can build up the set``() =
    assertProp "union-subtract" <| fun (xs : int list) ys ->
        setify (union xs ys) = setify (subtract xs ys @ ys)

[<Test>]
let ``subset implies intersect``() =
    assertProp "subset-intersect" <| fun (xs : int list) ys ->
        if intersect xs ys = xs then subset xs ys else not <| subset xs ys

[<Test>]
let ``subset implies union``() =
    assertProp "subset-union" <| fun (xs : int list) ys ->
        if union xs ys = ys then subset xs ys else not <| subset xs ys

[<Test>]
let ``explode and implode inverse each other``() =
    assertProp "explode-implode" <| fun s ->
        implode (explode s) = s

[<Test>]
let ``uniq doesn't contain adjacent equal elements``() =
    let rec hasAdjacentEqual = function
        | [] | [_] -> false
        | x::y::_ when x = y -> true
        | x::xs -> hasAdjacentEqual xs

    assertProp "uniq" <| fun (xs : int list) ->
        not <| hasAdjacentEqual (uniq xs)

//  OCaml          F#
//  ('a, 'b) func  Map<'a, 'b>
//  undefined      Map.empty
//  is_undefined   Map.isEmpty
//  mapf           Map.map
//  foldl          Map.fold
//  foldr          Map.foldBack
//  graph          Map.toList
//  dom            new function based on Map.fold
//  ran            new function based on Map.fold
//  applyd         new function based on Map.tryFind
//  apply          new function based on Map.tryFind
//  tryapplyd      new function based on Map.tryFind
//  tryapplyl      based on tryapplyd
//  defined        Map.containsKey
//  undefine       Map.remove
//  |->            Map.add
//  |=>            Map.add initialized wtih Map.Empty
//  fpf            new function based on List.zip and Map.ofList

open FsCheck.Commands

// We use Map<'a, 'b> as the model to test func<'a, 'b>
type FuncActual = func<int, int>
type FuncModel = Map<int, int>

// Create a specification for testing
let spec =
    let check (c, m) =
        is_undefined c = Map.isEmpty m
        && graph c = Map.toList m
        && dom c = Set.toList (Map.keys m)
        && ran c = Set.toList (Map.values m)

    let add = 
        gen { let! k = Arb.generate<int>
              let! v = Arb.generate<int>
              return
                { new ICommand<FuncActual, FuncModel>() with
                    member x.RunActual c = (|->) k v c
                    member x.RunModel m = Map.add k v m
                    member x.Post (c, m) = check (c, m)
                    override x.ToString() = sprintf "add %i %i" k v }
            }

    let remove = 
        gen { let! k = Arb.generate<int>
              return
                { new ICommand<FuncActual, FuncModel>() with
                    member x.RunActual c = undefine k c
                    member x.RunModel m = Map.remove k m
                    member x.Post (c, m) = check (c, m)
                    override x.ToString() = sprintf "remove %i" k }
            }

    let map = 
        Gen.constant <| 
            { new ICommand<FuncActual, FuncModel>() with
                member x.RunActual c = mapf (fun v -> 2 * v) c
                member x.RunModel m = Map.map (fun k v -> 2 * v) m 
                member x.Post (c, m) = check (c, m)
                override x.ToString() = "map" }

    let foldl = 
        Gen.constant <| 
            { new ICommand<FuncActual, FuncModel>() with
                member x.RunActual c = foldl (fun acc k v -> (|->) k (v-1) acc) undefined c
                member x.RunModel m = Map.fold (fun acc k v -> Map.add k (v-1) acc) Map.empty m 
                member x.Post (c, m) = check (c, m)
                override x.ToString() = "foldl" }

    let foldr = 
        Gen.constant <| 
            { new ICommand<FuncActual, FuncModel>() with
                member x.RunActual c = foldr (fun k v acc -> (|->) k (v+1) acc) undefined c
                member x.RunModel m = Map.foldBack (fun k v acc -> Map.add k (v+1) acc) Map.empty m 
                member x.Post (c, m) = check (c, m)
                override x.ToString() = "foldr" }

    { new ISpecification<FuncActual, FuncModel> with
        member x.Initial() = (undefined, Map.empty)
        member x.GenCommand _ = Gen.oneof [add; remove; map; foldl; foldr] }

[<Test>]
let ``check func<'a, 'b> against Map<'a, 'b> model in F# Core``() =
    Check.QuickThrowOnFailure (asProperty spec)

// Now we test case by case using FsUnit

// Note: Many of the next test cases came from the HOL Light reference manual

(* failtests *)

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "")>]
let ``{fail} fails with empty string``() =

    fail ()
    |> ignore

(* curry tests *)

[<Test>]
let ``{curry f} converts a function {f} on a pair to a corresponding curried function``() =

    curry snd 1 2
    |> assertEqual 2

(* uncurry tests *)

[<Test>]
let ``{uncurry f} converts a function {f} taking two arguments into a function taking a single paired argument``() =

    uncurry max (1,2)
    |> assertEqual 2

(* I tests *)

[<Test>]
let ``{I x} performs identity operation, {I x} = {x}``() =

    I 4
    |> assertEqual 4

(* K tests *)

[<Test>]
let ``{(K x) y} forms a constant function, {(K x) y} = {x}``() =

    K 4 5
    |> assertEqual 4

(* C tests *)

[<Test>]
let ``{C f x y} permutes first two arguments to curried function, {C f x y} = {f y x}``() =

    C ( ** ) 2. 3.          // 2^3
    |> assertEqual 9.      // 3^2

(* W tests *)

[<Test>]
let ``{W f x} duplicates function argument, {W f x} = {f x x}``() =

    W (+) 4
    |> assertEqual 8

(* F_F (||>>) tests *)

[<Test>]
let ``{{f ||>>} g {x,y}} applies two functions to a pair, {{f ||>> g} {x,y}} = {{f x, g y}}``() =
    
    let add1 x = x + 1
    let add2 x = x + 2

    (add1 ||>> add2) (1,2)
    |> assertEqual (2,4)

(* hd tests *)

[<Test>]
let ``{hd} computes the first element, the head, of a list``() =

    hd [1;2;3;4]
    |> assertEqual 1

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "hd")>]
let ``{hd} Fails with "Empty list" if the list is empty``() =
    
    hd [] 
    |> ignore

(* tl tests *)

[<Test>]
let ``{tl} Computes the tail of a list, the original list less the first element``() =

    tl [1;2;3;4]
    |> assertEqual [2;3;4]

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "tl")>]
let ``{tl} Fails with "Empty list" if the list is empty``() =
    
    tl []
    |> ignore

(* map tests *)

[<Test>]
let ``{map} applies a function to every element of a list``() =

    map (fun x -> x * 2) [1;2;3]
    |> assertEqual [2;4;6]

[<Test>]
let ``{map} applied to an empty list returns again an empty list``() =

    map (fun x -> x * 2) []
    |> assertEqual []

(* last tests *)

[<Test>]
let ``{last} computes the last element of a list``() =

    last [1;2;3;4]
    |> assertEqual 4

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "last")>]
let ``{last} fails if applied to en empty list``() =
    
    last [] 
    |> ignore

(* butlast tests *)

[<Test>]
let ``{butlast} computes the sub-list of a list consisting of all but the last element``() =

    butlast [1;2;3;4]
    |> assertEqual [1;2;3]

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "butlast")>]
let ``{butlast} fails if applied to en empty list``() =
    
    butlast [] 
    |> ignore

(* el tests *)

[<Test>]
let ``{el} extracts a specified element from a list``() =

    el 2 [1;2;7;8]
    |> assertEqual 7

[<Test>]
let ``{el 0} extracts the first element from a list, elements are numbered starting from 0 not 1``() =

    el 0 [1;2;7;8]
    |> assertEqual 1

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "tl")>]
let ``el fails if the integer argument is greater then the length of the list``() =

    el 4 [1;2;3] 
    |> ignore

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "tl")>]
let ``el fails if the integer argument is negative``() =

    el -1 [1;2;3] 
    |> ignore

(* rev tests *)

[<Test>]
let ``{rev} reverses a list``() =

    rev [1;2;3]
    |> assertEqual [3;2;1]

[<Test>]
let ``{rev} applied to an empty list returns an empty list again``() =
    
    rev []
    |> assertEqual []

(* map2 tests *)

[<Test>]
let ``{map2} maps a binary function over two lists to create one new list``() =

    map2 (+) [1;2;3] [30;20;10]
    |> assertEqual [31;22;13]

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "map2: length mismatch")>]
let ``{map2} fails if the two lists are of different lengths``() =

    map2 (+) [1;2;3;5] [1;2;3] 
    |> ignore

(* can tests *)

//[<Test>]
//let ``{can f x} evaluates to {true} if the application of {f} to {x} succeeds``() =
//
//    can hd [1;2]
//    |> assertEqual true
//
//[<Test>]
//let ``{can f x} evaluates to {false} if the application of {f} to {x} causes an System.Exception exception``() =
//
//    can hd []
//    |> assertEqual false
//
//[<Test>]
//[<ExpectedException(typeof<System.DivideByZeroException>, ExpectedMessage = "Attempted to divide by zero.")>]
//let ``{can f x} fails if the application of {f} to {x} causes an exception different from System.Exception``() =
//
//    can (fun x -> x / 0) 3
//    |> ignore

(* check tests *)

[<Test>]
let ``{check p x} returns {x} if the application {p x} yields {true}``() =

    check ((=) 1) 1
    |> evaluate
    |> assertEqual 1

[<Test>]
let ``{check p x} returns choice exception if the predicate {p} yields {false} when applied to the value {x}``() =

    let x = check ((=) 1) 2
    // TODO: Make this a NUnit custom constraint
    match x with
    | Choice1Of2 v -> Assert.Fail ()
    | Choice2Of2 e -> Assert.AreEqual (e.Message, "check")

(* funpow tests *)

[<Test>]
let ``{funpow n f x} applies {f} to {x}, {n} times, giving the result {f {f  {f x}  }} where the number of {f}'s is {n}``() =

    funpow 3 tl [1;2;3;4;5]
    |> assertEqual [4;5]

[<Test>]
let ``{funpow 0 f x} returns {x}``() =

    funpow 0 tl [1;2;3;4;5]
    |> assertEqual [1;2;3;4;5]

[<Test>]
let ``{funpow n f x} returns {x} if {n} is negative``() =

    funpow -1 tl [1;2;3;4;5]
    |> assertEqual [1;2;3;4;5]

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "tl")>]
let ``{funpow n f x} fails if any of the {n} applications of {f} fail``() =

    funpow 6 tl [1;2;3;4;5] 
    |> ignore

(* repeat tests *)

//[<Test>]
//let ``{repeat f x} repeatedly apply a function until it fails``() =
//
//    let funcUtil x = 
//        match x with
//        | 1 -> failwith ("func 1")
//        | 2 -> failwith ("func 2")
//        | 9 -> failwith ("func 4")
//        | _ -> x + 2
//
//    repeat funcUtil 3
//    |> assertEqual 9
//
//[<Test>]
//[<ExpectedException(typeof<System.DivideByZeroException>, ExpectedMessage = "Attempted to divide by zero.")>]
//let ``{repeat f x} fails if {f} raises an exception different from System.Exception at once``() =
//
//    let funcUtil x = 
//        match x with
//        | 1 -> failwith ("func 1")
//        | 2 -> failwith ("func 2")
//        | 9 -> x / 0
//        | _ -> x + 2
//
//    repeat funcUtil 3
//    |> assertEqual 9

(* itlist tests *)

[<Test>]
let ``{itlist} applies a binary function between adjacent elements of a list``() =

    itlist (+) [1;2;3;4;5] 0
    |> assertEqual 15

[<Test>]
let ``{itlist} applies a binary function between adjacent elements of a list and then to the last argument``() =

    itlist (+) [1;2;3;4;5] 6
    |> assertEqual 21

[<Test>]
let ``{itlist} returns just the last argument if the list is empty``() =

    itlist (+) [] 6
    |> assertEqual 6

(* rev_itlist tests *)

[<Test>]
let ``{rev_itlist} applies a binary function between adjacent elements of the reverse of a list``() =

    rev_itlist (fun x y -> x * y) [1;2;3;4] 1
    |> assertEqual 24

(* end_itlist tests *)

[<Test>]
let ``{end_itlist} applies a binary function between adjacent elements of a list``() =

    end_itlist (+) [1;2;3;4]
    |> assertEqual 10

[<Test>]
let ``{end_itlist} returns {x} for a one-element list {[x]}``() =

    end_itlist (+) [4]
    |> assertEqual 4

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "end_itlist")>]
let ``{end_itlist} fails if the list is empty``() =

    end_itlist (+) [] 
    |> ignore

(* itlist2 tests *)

[<Test>]
let ``{itlist2} applies a paired function between adjacent elements of 2 lists``() =

    // This takes a `dot product' of two vectors of integers
    let dot v w = itlist2 (fun x y z -> x * y + z) v w 0

    // 1 * 4 + (2 * 5 + (3 * 6))
    dot [1;2;3] [4;5;6]
    |> assertEqual 32

[<Test>]
let ``{itlist2} returns the last argument if the 2 lists are empty``() =

     itlist2 (fun x y z -> x * y + z) [] [] 6
    |> assertEqual 6

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "itlist2")>]
let ``{itlist2} fails if the two lists are of different length``() =

     itlist2 (fun x y z -> x * y + z) [1;2;3] [4;5;6;7] 0
    |> ignore

(* rev_itlist2 tests *)

[<Test>]
let ``{rev_itlist2} applies a paired function between adjacent elements of 2 lists``() =

    // This takes a `dot product' of two vectors of integers
    let dot v w = rev_itlist2 (fun x y z -> x * y + z) v w 0

    // 3 * 6 + (2 * 5 + (1 * 4))
    dot [1;2;3] [4;5;6]
    |> assertEqual 32

[<Test>]
let ``{rev_itlist2} returns the last argument if the 2 lists are empty``() =

     rev_itlist2 (fun x y z -> x * y + z) [] [] 6
    |> assertEqual 6

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "rev_itlist2")>]
let ``{rev_itlist2} fails if the two lists are of different length``() =

    rev_itlist2 (fun x y z -> x * y + z) [1;2;3] [4;5;6;7] 0
    |> ignore

(* splitlist tests *)

type exp =
    | Atom of int
    | And of exp * exp
    with
    override this.ToString() =
        match this with
        | Atom x    -> sprintf "Atom (%A)" x
        | And (x,y) -> sprintf "And (%A,%A)" x y

let dest_conj x =
        match x with
        | And (x1,x2) -> (x1,x2)
        | _           -> failwith("dest_conj: not an And expression")

let dest_conjOption x =
        match x with
        | And (x1,x2) -> Some(x1,x2)
        | _           -> None

[<Test>]
let ``{splitlist} applies a binary destructor repeatedly in left-associative mode``() = 

    splitlist dest_conjOption (And (And (Atom 5, Atom 6), Atom 2))
    |> assertEqual ([And (Atom 5, Atom 6)], Atom 2)

(* rev_splitlist tests *)

[<Test>]
let ``{rev_splitlist} applies a binary destructor repeatedly in right-associative mode``() =

    rev_splitlist dest_conjOption (And (And (Atom 5, Atom 6), Atom 2))
    |> assertEqual (Atom 5, [Atom 6;Atom 2])

(* striplist tests *)

[<Test>]
let ``{striplist} applies a binary destructor repeatedly, flattening the construction tree into a list``() =

    striplist dest_conjOption (And (And (Atom 5,Atom 6), Atom 2))
    |> assertEqual [Atom 5;Atom 6;Atom 2]

(* nsplit tests *)

[<Test>]
let ``{nsplit} applies a destructor in right-associative mode a specified number of times``() =

    nsplit dest_conj [1;2;3] (And (Atom 1, And (Atom 2, And (Atom 3, Atom 4))))
    |> assertEqual ([Atom 1;Atom 2;Atom 3], Atom 4)

(* replicate tests *)

[<Test>]
let ``{replicate} makes a list consisting of a value replicated a specified number of times``() = 

    replicate "p" 2
    |> assertEqual ["p";"p"]

[<Test>]
let ``{replicate} returns an empty list if the number of replications is less than 1``() = 

    replicate "p" -1
    |> assertEqual []

(* (--) tests *)

[<Test>]
let ``{m--n} returns the list of consecutive numbers from {m} to {n}``() = 

    1--10
    |> assertEqual [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]

[<Test>]
let ``{m--n} returns [{m}] if {m} = {n}``() = 

    5--5
    |> assertEqual [5]

[<Test>]
let ``{m--n} returns the list of consecutive numbers from {m} to {n} also if {m} and {n} are negative with {m} < {n}``() = 

    (-1)--1
    |> assertEqual [-1; 0; 1]

[<Test>]
let ``{m--n} returns an empty list if {m} > {n}``() = 

    2--1
    |> assertEqual []

(* forall tests *)

[<Test>]
let ``{forall p [x1;_;xn]} returns {true} if {p xi} is true for all {xi} in the list``() = 

    forall (fun x -> x <= 2) [0;1;2]
    |> assertEqual true

[<Test>]
let ``{forall p [x1;_;xn]} returns {false} if {p xi} is false for one or more {xi} in the list``() = 

    forall (fun x -> x <= 2) [1;2;3]
    |> assertEqual false

[<Test>]
let ``{forall p []} returns {true}``() = 

    forall (fun x -> x <= 2) []
    |> assertEqual true

(* forall2 tests *)

[<Test>]
let ``{forall2 p [x1;_;xn] [y1;_;yn]} returns {true} if {p xi yi} is true for all corresponding {xi} and {yi} in the list``() = 

    forall2 (<) [1;2;3] [2;3;4]
    |> assertEqual true

[<Test>]
let ``{forall2 p [x1;_;xn] [y1;_;yn]} returns {false} if {p xi yi} is false for one or more corresponding {xi} and {yi} in the list``() = 

    forall2 (<) [1;2;3;4] [5;4;3;5]
    |> assertEqual false

[<Test>]
let ``{forall2 p [x1;_;xn] [y1;_;yn]} returns {false} if the lengths of the lists are different``() = 

    forall2 (<) [1] [2;3]
    |> assertEqual false

[<Test>]
let ``{forall2 p [] []} returns {true}``() = 

    forall2 (<) [] []
    |> assertEqual true

(* exists tests *)

[<Test>]
let ``{exists p [x1;_;xn]} returns {true} if {p xi} is true for some {xi} in the list``() = 

    exists (fun n -> n % 2 = 0) [2;3;5;7;11;13;17]
    |> assertEqual true

[<Test>]
let ``{exists p [x1;_;xn]} returns {false} if {p xi} is false for all {xi} in the list``() = 

    exists (fun n -> n % 2 = 0) [3;5;7;9;11;13;15]
    |> assertEqual false

[<Test>]
let ``{exists p []} returns {false}``() = 

    exists (fun n -> n % 2 = 0) []
    |> assertEqual false

(* length tests *)

[<Test>]
let ``{length [x1;_;xn]} returns {n}``() =
    
    length [11..20]
    |> assertEqual 10

(* filter tests *)

[<Test>]
let ``{filter p l} applies {p} to every element of {l}, returning a list of those that satisfy {p}, in the order they appeared in the original list``() =
    
    filter (fun x -> 10 % x = 0) [1;2;3;4;5;6;7;8;9]
    |> assertEqual [1;2;5]

[<Test>]
[<ExpectedException(typeof<System.DivideByZeroException>, ExpectedMessage = "Attempted to divide by zero.")>]
let ``{filter p l} fails if the predicate fails on any element``() =
    
    filter (fun x -> 10 % x = 0) [1;2;3;4;5;6;7;8;9;0]
    |> ignore

(* partition tests *)

[<Test>]
let ``{partition p l} returns a pair of lists, the first with the elements which satisfy {p}, the second with all the others``() =
    
    partition (fun x -> x % 2 = 0) (1--10)
    |> assertEqual ([2; 4; 6; 8; 10], [1; 3; 5; 7; 9])

(* mapfilter tests *)

[<Test>]
let ``{mapfilter} applies a function to every element of a list, returning a list of results for those elements for which application succeeds``() =

    let fHd l =
        match l with
        | h::t -> Some(h)
        | _ -> None

    mapfilter fHd [[1;2;3];[4;5];[];[6;7;8];[]]
    |> assertEqual [1; 4; 6]

(* find tests *)

[<Test>]
let ``{find p [x1;_;xn]} returns the first {xi} in the list such that {p xi} is {true}``() =
    
    find (fun x -> x > 3) [1;2;3;4;5]
    |> Option.get
    |> assertEqual 4

[<Test>]
let ``{find p [x1;_;xn]} fails with None if no element satisfies the predicate``() =
    
    find (fun x -> x > 5) [1;2;3;4;5]
    |> assertEqual None

(* tryfind tests *)

[<Test>]
let ``{tryfind f [x1;_;xn]} returns Some {f xi} for the first {xi} in the list for  which application of {f} succeeds``() =

    let isUpper x =
        if System.Char.IsUpper x
        then Some x
        else None

    tryfind isUpper ['a';'b';'C';'d']
    |> assertEqual (Some 'C')

[<Test>]
let ``{tryfind f [x1;_;xn]} returns None if the application of the function fails for all elements in the list``() =

    let isUpper x =
        if System.Char.IsUpper x
        then Some x
        else None

    tryfind isUpper ['a';'b';'c';'d']
    |> assertEqual None

(* flat tests *)

[<Test>]
let ``{flat} flattens a list of lists into one long list``() =
    
    flat [[1;2];[3;4;5];[6]]
    |> assertEqual [1; 2; 3; 4; 5; 6]

(* remove tests *)

[<Test>]
let ``{remove} separates the first element of a list to satisfy a predicate from the rest of the list``() =

    remove (fun x -> x >= 3) [1;2;3;4;5;6]
    |> assertEqual (Some (3, [1; 2; 4; 5; 6]))

[<Test>]
let ``{remove} returns None if no element satisfies the predicate``() =

    remove (fun x -> x >= 7) [1;2;3;4;5;6]
    |> assertEqual None

[<Test>]
let ``{remove} returns None if applied to an empty list``() =

    remove (fun x -> true) []
    |> assertEqual None

(* chop_list tests *)

[<Test>]
let ``{chop_list i [x1;_;xn]} chops a list into two parts at a specified point, returns {[x1;_;xi],[x_{i+1};_;xn]}``() =
    
    chop_list 3 [1;2;3;4;5]
    |> assertEqual ([1; 2; 3], [4; 5])

[<Test>]
[<ExpectedException(typeof<System.ArgumentException>, ExpectedMessage = "The number of items to take from the list is greater than the length of the list.\r\nParameter name: count")>]
let ``{chop_list i [x1;_;xn]} fails with if {i} is greater than the length of the list``() =

    chop_list 4 [1;2;3] 
    |> ignore

[<Test>]
[<ExpectedException(typeof<System.ArgumentException>, ExpectedMessage = "The number of items to take from the list is negative.\r\nParameter name: count")>]
let ``{chop_list i [x1;_;xn]} fails with if {i} is negative``() =

    chop_list -1 [1;2;3] 
    |> ignore

(* index tests *)

[<Test>]
let ``{index x l} where l is a list returns the position number of the first instance of x in the list``() =
    
    index "d" ["a";"b";"c";"d";"e";"f";"g"]
    |> assertEqual 3

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "index")>]
let ``{index x l} fails if there isn't any instance of {x} in {l}``() =
    
    index "p" ["a";"b";"c";"d";"e";"f";"g"]
    |> ignore

(* mem tests *)

[<Test>]
let ``{mem x [x1;_;xn]} returns {true} if some {xi} in the list is equal to {x}``() =
    
    mem 3 [1;2;3;4;5]
    |> assertEqual true

[<Test>]
let ``{mem x [x1;_;xn]} returns {false} if no {xi} in the list is equal to {x}``() =
    
    mem 3 [1;2;4;5]
    |> assertEqual false

(* insert tests *)

[<Test>]
let ``{insert x l} returns {x::l} if {x} is not already present in the list``() =
    
    insert 15 (1--10)
    |> assertEqual [15; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]

[<Test>]
let ``{insert x l} returns just {l} if {x} is already in the list``() =
    
    insert 5 (1--10)
    |> assertEqual [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]

(* union tests *)

[<Test>]
let ``{union l1 l2} returns a list consisting of the elements of {l1} not already in {l2} concatenated with {l2}``() =
    
    union [1;2;3] [1;5;4;3]
    |> assertEqual [2; 1; 5; 4; 3]

[<Test>]
let ``{union l1 l2} removes duplicates in the result``() =
    
    union [1;1;1] [1;2;3;2]
    |> assertEqual [1; 2; 3; 2]

(* unions tests *)

[<Test>]
let ``{unions} applied to a list of lists, {union} returns a list of all the elements of them, in some unspecified order, with no repetitions``() =
    
    unions [[1;2]; [2;2;2;]; [2;3;4;5]]
    |> assertEqual [1; 2; 3; 4; 5]

(* intersect tests *)

[<Test>]
let ``{intersect l1 l2} returns a list consisting of those elements of {l1} that also appear in {l2}``() =
    
    intersect [1;2;3] [3;5;4;1]
    |> assertEqual [1; 3]

[<Test>]
let ``{intersect l1 l2} mantains duplicates of the first list in the result``() =
    
    intersect [1;2;4;1] [1;2;3;2]
    |> assertEqual [1; 2; 1]

(* subtract tests *)

[<Test>]
let ``{subtract l1 l2} returns a list consisting of those elements of {l1} that do not appear in {l2}``() =
    
    subtract [1;2;3] [3;5;4;1]
    |> assertEqual [2]

[<Test>]
let ``{subtract l1 l2} mantains duplicates of the first list in the result``() =
    
    subtract [1;2;4;1] [4;5]
    |> assertEqual [1; 2; 1]

(* subset tests *)

[<Test>]
let ``{subset l1 l2} returns {true} if every element of {l1} also occurs in {l2}``() =
    
    subset [1;1;2;2] [1;2;3]
    |> assertEqual true

[<Test>]
let ``{subset l1 l2} returns {false} if no element of {l1} also occurs in {l2}``() =
    
    subset [5;6;7] [1;2;3]
    |> assertEqual false

(* set_eq tests *)

[<Test>]
let ``{set_eq l1 l2} returns {true} if every element of {l1} appears in {l2} and every element of {l2} appears in {l1}``() =
    
    set_eq [1;2] [2;1;2]
    |> assertEqual true

[<Test>]
let ``{set_eq l1 l2} returns {false} if some element of {l1} do not appear in {l2} or some element of {l2} do not appear in {l1}, or both``() =
    
    set_eq [1;2] [1;3]
    |> assertEqual false

(* assoc tests *)

[<Test>]
let ``{assoc x [{x1,y1};_;{xn,yn}]} searches a list of pairs for a pair whose first component equals a specified value``() =
    
    assoc 2 [(1,4); (3,2); (2,5); (2,6)]
    |> Option.getOrFailWith "find"
    |> assertEqual 5

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "find")>]
let ``{assoc x [{x1,y1};_;{xn,yn}]} fails if no matching pair is found``() =
    
    assoc 10 [(1,4); (3,2); (2,5); (2,6)]
    |> Option.getOrFailWith "find"
    |> ignore

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "find")>]
let ``{assoc x []} fails for any {x}``() =
    
    assoc 10 []
    |> Option.getOrFailWith "find"
    |> ignore

(* rev_assoc tests *)

[<Test>]
let ``rev_assoc x [{x1,y1};_;{xn,yn}]} searches a list of pairs for a pair whose second component equals a specified value``() =
    
    rev_assoc 2 [(1,4);(3,2);(2,5);(2,6)]
    |> Option.getOrFailWith "find"
    |> assertEqual 3

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "find")>]
let ``{rev_assoc x [{x1,y1};_;{xn,yn}]} fails if no matching pair is found``() =
    
    rev_assoc 10 [(1,4); (3,2); (2,5); (2,6)]
    |> Option.getOrFailWith "find"
    |> ignore

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "find")>]
let ``{rev_assoc x []} fails for any {x}``() =
    
    rev_assoc 10 []
    |> Option.getOrFailWith "find"
    |> ignore

(* zip tests *)

[<Test>]
let ``{zip} combines corresponding items of the two supplied lists into pairs, {zip [x1;_;xn] [y1;_;yn]} returns {[{x1,y1};_;{xn,yn}]}``() =

    zip [1;2;3;4] ["a";"b";"c";"d"]
    |> assertEqual [(1,"a");(2,"b");(3,"c");(4,"d")]

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "zip")>]
let ``{zip} fails if the lists do not have the same length``() =
    
    zip [1;2;3] ["a";"b"]
    |> ignore

(* unzip tests *)

[<Test>]
let ``{unzip} converts a list of pairs into a pair of lists, {unzip [{x1,y1};_;{xn,yn}]} returns {[x1;_;xn],[y1;_;yn]}``() =

    unzip [(1,"a");(2,"b");(3,"c");(4,"d")]
    |> assertEqual ([1;2;3;4],["a";"b";"c";"d"])

[<Test>]
let ``{unzip []} = {[],[]}``() =

    unzip []
    |> assertEqual ([],[])

(* shareout tests *)

[<Test>]
let ``{shareout} shares out the elements of the second list according to pattern in first``() =

    shareout [[1;2;3]; [4;5]; [6]; [7;8;9]] ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"]
    |> assertEqual [["a"; "b"; "c"]; ["d"; "e"]; ["f"]; ["g"; "h"; "i"]]

[<Test>]
[<ExpectedException(typeof<System.ArgumentException>, ExpectedMessage = "The number of items to take from the list is greater than the length of the list.\r\nParameter name: count")>]
let ``{shareout} fails if there are too few elements in the second list``() =

    shareout [[1;2;3]; [4;5]; [6]; [7;8;9]] ["a"; "b"; "c"; "d"; "e"; "f"; "g"] |> ignore

(* do_list tests *)

////A wraper to return the print on the standard output side-effect
//let testPrintf f arg =
//    let oldOut = System.Console.Out
//    use out = new System.IO.StringWriter()
//    System.Console.SetOut(out)
//    f arg |>ignore
//    System.Console.SetOut(oldOut)
//    out.GetStringBuilder().ToString()

//let printOnStdOut x = printfn "%s" x
//
//[<Test>]
//let ``printOnStdOut_test``() =
//
//    testPrintf printOnStdOut "pippo"
//    |> assertEqual "pippo\r\n"
//
//[<Test>]
//let ``{do_list} applies imperative function, such as printing on terminal, to each element of a list``() =
//    
//    let do_map_printOnStdOut = do_list printOnStdOut
//
//    testPrintf do_map_printOnStdOut ["p";"c"]
//    |> assertEqual "p\r\nc\r\n"

(* sort tests *)

[<Test>]
let ``{sort} sorts a list using a given transitive 'ordering' relation``() =

    sort (<) [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5; 8; 9; 7; 9]
    |> assertEqual [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 7; 8; 9; 9; 9]

(* uniq tests *)

[<Test>]
let ``{uniq} eliminate adjacent identical elements from a list``() =

    uniq [1;1;1;2;3;3;3;3;4]
    |> assertEqual [1; 2; 3; 4]

[<Test>]
let ``{uniq} has no effect if there aren't adjacent indentical elements``() =

    uniq [1;2;3;1;2;3]
    |> assertEqual [1; 2; 3; 1; 2; 3]

(* setify tests *)

[<Test>]
let ``{setify} removes repeated elements from a list``() =

    setify [1;2;3;1;4;3]
    |> assertEqual [1; 2; 3; 4]

(* implode tests *)

[<Test>]
let ``{implode [s1;_;sn]} returns the string formed by concatenating the strings {s1_sn}``() =

    implode ["e";"x";"a";"m";"p";"l";"e"]
    |> assertEqual "example"

[<Test>]
let ``{implode [s1;_;sn]} returns the string formed by concatenating the strings {s1 _ sn}, {si} need not be single characters``() =

    implode ["ex";"a";"mpl";"";"e"]
    |> assertEqual "example"

[<Test>]
let ``{implode []} returns the empty string``() =

    implode []
    |> assertEqual ""

(* explode tests *)

[<Test>]
let ``{explode} converts a string into a list of single-character strings``() =

    explode "example"
    |> assertEqual ["e"; "x"; "a"; "m"; "p"; "l"; "e"]

[<Test>]
let ``{explode ""} returns the empty list``() =

    explode ""
    |> assertEqual []

(* gcd tests *)

[<Test>]
let ``{gcd m n} for two integers {m} and {n} returns the, nonnegative, greatest common divisor of {m} and {n}``() =

    gcd 10 12
    |> assertEqual 2

[<Test>]
let ``gcd_2_test``() =

    gcd 11 27
    |> assertEqual 1

[<Test>]
let ``gcd_3_test``() =

    gcd (-33) 76
    |> assertEqual 1

[<Test>]
let ``{gcd m n} returns {n} if {m} is zero``() =

    gcd 0 99
    |> assertEqual 99

[<Test>]
let ``{gcd m n} returns {m} if {n} is zero``() =

    gcd 99 0
    |> assertEqual 99

[<Test>]
let ``{gcd m n} returns zero if both {m} and {n} are zero``() =

    gcd 0 0
    |> assertEqual 0

(* pow2 tests *)

[<Test>]
let ``{pow2} returns power of 2 as unlimited-size integer``() =

    pow2 (64)
    |> assertEqual (Big_int (big_int_of_string "18446744073709551616"))

[<Test>]
let ``{pow2} accepts a negative argument``() =

    pow2 (-2)
    |> assertEqual ((Int 1) / (Int 4))

(* pow10 tests *)

[<Test>]
let ``{pow10} returns power of 10 as unlimited-size integer``() =

    pow10 (16)
    |> assertEqual (Big_int (big_int_of_string "10000000000000000"))

[<Test>]
let ``{pow10} accepts a negative argument``() =

    pow10 (-1)
    |> assertEqual ((Int 1) / (Int 10))

(* numdom tests *)

[<Test>]
let ``{numdom} returns numerator and denominator of normalized fraction``() =

    numdom (Int 22 / Int 7)
    |> assertEqual (Int 22, Int 7)

[<Test>]
let ``{numdom Int 0} returns {Int 0, Int 1}``() =

    numdom (Int 0)
    |> assertEqual (Int 0, Int 1)

[<Test>]
let ``{numdom x} denomaintor one if {x} is an integer``() =

    numdom (Int 100)
    |> assertEqual (Int 100, Int 1)

[<Test>]
let ``{numdom x} return a negative numerator if {x} has a negative denominator, note that the rational is normalized down``() =

    numdom (Int 4 / Int -2)
    |> assertEqual (Int -2, Int 1)

[<Test>]
let ``{numdom x} return a negative numerator if {x} has a negative numerator, note that the rational is normalized down``() =

    numdom (Int -4 / Int 2)
    |> assertEqual (Int -2, Int 1)

[<Test>]
let ``{numdom x} return a positive numerator if {x} has both a negative numerator and negative denominator, note that the rational is normalized down``() =

    numdom (Int -4 / Int -2)
    |> assertEqual (Int 2, Int 1)

(* numerator tests *)

[<Test>]
let ``{numerator} returns numerator of rational number in canonical form``() =

    numerator (Int 22 / Int 7)
    |> assertEqual (Int 22)

[<Test>]
let ``{numerator} returns numerator of rational number in canonical form, the numerator will be negative if the rational is negative``() =

    numerator (Int 4 / Int -2)
    |> assertEqual (Int -2)

// TODO: add the other unit tests from the original documentation samples

(* denominator tests *)

[<Test>]
let ``{denominator} returns denominator of rational number in canonical form``() =

    denominator (Int 22 / Int 7)
    |> assertEqual (Int 7)

[<Test>]
let ``{denominator} returns denominator of rational number in canonical form, the denominator will be always positive``() =

    denominator (Int 4 / Int -2)
    |> assertEqual (Int 1)

(* gcd_num tests *)

[<Test>]
let ``{gcd_num m n} for two unlimited-precision, type {num}, integers {m} and {n} returns the positive greatest common divisor of {m} and {n}``() =

    gcd_num (Int 35) (Int(-77))
    |> assertEqual (Int 7)

[<Test>]
let ``{gcd_num m 0} returns {m}``() =

    gcd_num (Int 11) (Int 0)
    |> assertEqual (Int 11)

[<Test>]
let ``{gcd_num 0 n} returns {n}``() =

    gcd_num (Int 0) (Int 11)
    |> assertEqual (Int 11)

[<Test>]
let ``{gcd_num m n} returns zero if both {m} and {n} are zero``() =

    gcd_num (Int 0) (Int 0)
    |> assertEqual (Int 0)

[<Test>]
let ``{gcd_num m n} returns the positive greatest common divisor if {m} is a rational that can be normalized to an integer``() =

    gcd_num (Int 20 / Int 2) (Int 5)
    |> assertEqual (Int 5)

[<Test>]
let ``{gcd_num m n} returns the positive greatest common divisor if {n} is a rational that can be normalized to an integer``() =

    gcd_num (Int 5) (Int 20 / Int 2) 
    |> assertEqual (Int 5)

[<Test>]
[<ExpectedException(typeof<exn>, ExpectedMessage = "big_int_of_ratio")>]
let ``{gcd_num m n} fails if either number is not an integer the type {num} supports arbitrary rationals``() =

    gcd_num (Int 22 / Int 7) (Int 2)
    |> ignore

(* lcm_num tests *)

[<Test>]
let ``{lcm_num m n} computes the positive lowest common multiple of two unlimited-precision integers``() =

    lcm_num (Int 35) (Int -77)
    |> assertEqual (Int 385)

// With one or both arguments with value zero

[<Test>]
let ``{lcm_num m n} returns zero if {m} is zero``() =

    lcm_num (Int 0) (Int -77)
    |> assertEqual (Int 0)

[<Test>]
let ``{lcm_num m n} returns zero if {n} is zero``() =

    lcm_num (Int 35) (Int 0)
    |> assertEqual (Int 0)

[<Test>]
let ``{lcm_num m n} returns zero if both {m} and {n} are zero``() =

    lcm_num (Int 0) (Int 0)
    |> assertEqual (Int 0)

// With rational arguments that can be normalized to an integer

[<Test>]
let ``{lcm_num m n} computes the positive lcm if {m} is a rational that can be normalized to an integer``() =

    lcm_num (Int 20 / Int 2)  (Int 5)
    |> assertEqual (Int 10)

[<Test>]
let ``{lcm_num m n} computes the positive lcm if {n} is a rational that can be normalized to an integer``() =

    lcm_num (Int 5) (Int 20 / Int 2)  
    |> assertEqual (Int 10)

// With rational arguments that can not be normalized to an integer

[<Test>]
[<ExpectedException(typeof<exn>, ExpectedMessage = "big_int_of_ratio")>]
let ``{lcm_num m n} fails if either number is not an integer``() =

    lcm_num (Int 22 / Int 7) (Int 2)
    |> ignore

(* allpairs tests *)

[<Test>]
let ``{allpairs} compute list of all results from applying function to pairs from two lists``() =

    allpairs (fun x y -> (x,y)) [1;2;3] [4;5]
    |> assertEqual [(1, 4); (1, 5); (2, 4); (2, 5); (3, 4); (3, 5)]

//(* report tests *)
//
//[<Test>]
//let ``{report s} prints the string {s} to the terminal and then a following newline``() =
//
//    testPrintf report "Proof completed OK"
//    |> assertEqual "Proof completed OK\r\n"
//
//(* warn tests *)
//
//[<Test>]
//let ``{warn b s} prints out {Warning: s} and a following newline to the terminal if {b} is true``() =
//
//    let n = 7
//
//    testPrintf (warn (n <> 0)) "Nonzero value" // here testPrintf is a litle bit tricky 
//    |> assertEqual "Warning: Nonzero value\r\n"
//
//[<Test>]
//let ``{warn b s} does nothing if {b} is false``() =
//
//    let n = 0
//
//    testPrintf (warn (n <> 0)) "Nonzero value" // here testPrintf is a litle bit tricky 
//    |> assertEqual ""
//
//(* remark tests *)
//
//[<Test>]
//let ``{remark s} prints the string {s} and a following newline if and only if {verbose} flag is set to {true}``() =
//
//    testPrintf remark "Proof is going OK so far"
//    |> assertEqual "Proof is going OK so far\n"
//
//[<Test>]
//let ``{remark s} does nothing if {verbose} flag is set to {false}``() =
//
//    verbose := false
//
//    let actual = testPrintf remark "Proof is going OK so far"
//
//    verbose := true
//
//    actual
//    |> assertEqual ""
//
//(* time tests *)
//
//[<Test>]
//let ``{time f x} report CPU time taken by a function, if {report_timing} is set to {true}``() =
//
//    (testPrintf (time (List.fold (fun acc elem -> acc + elem) 0)) [1..1000000]).Substring(0,17)
//    |> assertEqual "CPU time (user): "

(* assocd tests *)

[<Test>]
let ``{assocd x [x1,y1; _; xn,yn] y} returns the first {yi} in the list where the corresponding {xi} is the same as {x}``() =
    
    assocd 2 [(1,2); (2,4); (3,6)] (-1)
    |> assertEqual 4

[<Test>]
let ``{assocd x [x1,y1; _; xn,yn] y} returns y if there isn't an {yi} in the list where the corresponding {xi} is the same as {x}``() =
    
    assocd 4 [1,2; 2,4; 3,6] (-1)
    |> assertEqual -1

(* rev_assocd tests *)

[<Test>]
let ``{rev_assocd y [x1,y1; _; xn,yn] x} returns the first {yi} in the list where the corresponding {xi} is the same as {x}``() =
    
    rev_assocd 6 [(1,2); (2,4); (3,6)] (-1)
    |> assertEqual 3

[<Test>]
let ``{rev_assocd y [x1,y1; _; xn,yn] x} returns y if there isn't an {yi} in the list where the corresponding {xi} is the same as {x}``() =
    
    rev_assocd 8 [1,2; 2,4; 3,6] (-1)
    |> assertEqual -1

(* qmap tests *)

//[<Test>]
//let ``{qmap} applies a function to every element of a list``() =
//
//    qmap (fun x -> x * 2) [1;2;3]
//    |> assertEqual [2;4;6]

//[<Test>]
//let ``{qmap} applied to an empty list returns again an empty list``() =
//
//    qmap (fun x -> x * 2) []
//    |> assertEqual []

//[<Test>]
//let ``{qmap} is faster then map where the function returns the argument unchanged ``() =
//
//    let million = 1--1000000
//
//    (qmap I) million = million
//    |> assertEqual true

(* merge tests *)

[<Test>]
let ``{merge l1 l2} {l1} and {l2} are sorted with respect to the given ordering {ord}``() =

    merge (<) [1;2;3;4;5;6] [2;4;6;8]
    |> assertEqual [1; 2; 2; 3; 4; 4; 5; 6; 6; 8]

(* mergesort tests *)

[<Test>]
let ``{mergesort ord l} will sort the list {l} according to the order {ord}``() =

    mergesort (<) [6;2;5;9;2;5;3]
    |> assertEqual [2; 2; 3; 5; 5; 6; 9]

(* increasing tests *)

[<Test>]
let ``{increasing f} returns a binary function ordering elements in a call {increasing f x y} by {f x <? f y}``() =

    let nums = -5 -- 5

    sort (increasing abs) nums
    |> assertEqual [0; 1; -1; 2; -2; 3; -3; 4; -4; 5; -5]

(* decreasing tests *)

[<Test>]
let ``{decreasing f} returns a binary function ordering elements in a call {decreasing f x y} by {f x >? f y}``() =

    let nums = -5 -- 5

    sort (decreasing abs) nums
    |> assertEqual [5; -5; 4; -4; 3; -3; 2; -2; 1; -1; 0]

(* TODO: add a short description of what Finite Partial Functions are to clear the following unit tests. *)

(* undefined tests *)

[<Test>]
let ``{undefined} is the "empty" finite partial function that is nowhere defined``() =

    // i.e. let undefined = Empty

    apply undefined "anything" // note that apply is defined later in Lib module
    |> assertEqual None

(* applyd tests *)

[<Test>]
let ``{applyd f g x} returns {Some (f x)} if {f} is defined on {x}``() =

    applyd (1 |=> 2) (fun x -> Some x) 1 // note that |=> is defined later in Lib module
    |> assertEqual (Some 2)

[<Test>]
let ``{applyd f g x} returns {Some (g x)} is {f} if undefined on {x}``() =

    applyd undefined (fun x -> Some x) 1
    |> assertEqual (Some 1)

(* apply tests *)

[<Test>]
let ``{apply f x} returns {Some (f x)} if {f} is defined on {x}``() =

    apply (1 |=> 2) 1 // note that |=> is defined later in Lib module
    |> assertEqual (Some 2)

[<Test>]
let ``{apply f x} returns None if {f} is undefined on {x}``() =

    apply undefined 1
    |> assertEqual None

(* tryapplyd tests *)

[<Test>]
let ``{tryapplyd f x y} tries to apply {f} to the value {x} if it is defined for {x} returns {f x}``() = 

    tryapplyd (1 |=> 2) 1 (-1)
    |> assertEqual 2

[<Test>]
let ``{tryapplyd f x y} tries to apply {f} to the value {x} if it is undefined, simply returns {y} ``() = 

    tryapplyd undefined 1 (-1)
    |> assertEqual -1

(* defined tests *)

[<Test>]
let ``{defined f x} returns {true} if the finite partial function {f} is defined on domain value {x}``() = 

    defined (1 |=> 2) 1
    |> assertEqual true

[<Test>]
let ``{defined f x} returns {false} if the finite partial function {f} is not defined on domain value {x}``() = 

    defined (1 |=> 2) 2
    |> assertEqual false

(* undefine tests *)

[<Test>]
let ``{undefine x f} removes a definition for the domain value {x} in the finite partial function {f}``() = 

    let f = itlist I [1 |-> "1"; 2 |-> "2"; 3 |-> "3"] undefined

    dom (undefine 2 f)
    |> assertEqual [1; 3]

[<Test>]
let ``{undefine x f} if there was no value to begin with the function is unchanged``() = 

    let f = itlist I [1 |-> "1"; 2 |-> "2"; 3 |-> "3"] undefined

    dom (undefine 4 f)
    |> assertEqual [1; 2; 3]

(* (|->) tests *)

[<Test>]
let ``{{x |-> y} f}, if {f} is a finite partial function, gives a modified version that maps {x} to {y}``() = 

    let f = (1 |-> 2) undefined // definition of a finite partial function
    let g = (1 |-> 3) f         // a modified version of the finite partial function f

    let valueBeforeModification = apply f 1 // 2
    let valueAfterModification = apply g 1  // 3

    (valueBeforeModification,valueAfterModification)
    |> assertEqual (Some(2),Some(3))

(* (|=>) tests *)

[<Test>]
let ``{x |=> y} gives a finite partial function that maps {x} to {y}``() = 

    let f = (1 |=> 2)

    apply f 1
    |> assertEqual (Some 2)

[<Test>]
let ``{x |=> y} is undefined for all arguments other than {x}``() =

    let f = (1 |=> 2)

    apply f 2
    |> assertEqual None

(* is_undefined tests *)

[<Test>]
let ``{is_undefined} return {true} if the argument is the completely undefined function``() = 

    let x = undefined

    is_undefined x
    |> assertEqual true

[<Test>]
let ``{is_undefined} return {false} if the argument is defined somewhere``() = 

    let y = (1 |=> 2)

    is_undefined y
    |> assertEqual false

(* mapf tests *)

[<Test>]
let ``{mapf f p} applies the, ordinary, function {f} to all  the range elements of a finite partial function``() = 

    let f = (1 |=> 2)

    let string_of_int x = x.ToString()

    let mappedF = mapf string_of_int f

    apply mappedF 1
    |> assertEqual (Some "2")

(* foldl tests *)

[<Test>]
let ``{foldl f a p} returns { f {f _ {f {f a x1 y1} x2 y2} _ } xn yn }``() = 

    let f = (1 |-> 2) (2 |=> 3) 

    foldl (fun a x y -> (x,y)::a) [] f  // The {graph} function is implemented based on the following invocation of {foldl}
    |> assertEqual [(1, 2); (2, 3)]    //Note that in this case the order happened to be the same, but this is an accident.

(* foldr tests *)

[<Test>]
let ``{foldr f a p} returns { f x1 y1 {f x2 y2 {f x3 y3 {f _ {f xn yn a} _ }}} }``() = 

    let f = (1 |-> 2) (2 |=> 3) 

    foldr (fun x y a -> (x,y)::a) f []  
    |> assertEqual [(2, 3); (1, 2)]  
    
    // Note how the pairs are actually processed in the opposite order to the order in 
    // which they are presented by {graph}. The order will in general not be obvious, 
    // and generally this is applied to operations with appropriate commutativity 
    // properties.

(* graph tests *)

[<Test>]
let ``{graph} function takes a finite partial function and returns its graph as a list``() = 

    graph (1 |=> 2)
    |> assertEqual [(1, 2)]

[<Test>]
let ``{graph} returns an empty list if the argument is the undefined function``() = 

    graph undefined
    |> assertEqual []

// TODO: a fails unit test for types that don't permit comparisons

(* dom tests *)

[<Test>]
let ``{dom} returns the domain of a function``() = 

    dom(itlist I [2|->4; 3|->6] undefined)
    |> assertEqual [2; 3]

// TODO: a fails unit test for types that don't permit comparisons

(* ran tests *)

[<Test>]
let ``{ran} returns the domain of a function``() = 

    ran(itlist I [2|->4; 3|->6] undefined)
    |> assertEqual [4; 6]

// TODO: a fails unit test for types that don't permit comparisons

(* choose tests *)

[<Test>]
let ``{choose f} picks an arbitrary pair of values from the graph of a fpf {f}: a pair {x,y} where {f} maps {x} to {y}``() = 

    let f = itlist I [1 |-> 2; 2 |-> 3; 3 |-> 4] undefined

    choose f
    |> assertEqual (2, 3)

[<Test>]
[<ExpectedException(typeof<System.Exception>, ExpectedMessage = "choose: completely undefined function")>]
let ``{choose f} fails if {f} is the completely undefined function``() = 

    choose undefined
    |> ignore

(* mem' tests *)

[<Test>]
let ``{mem' r x l} returns {true} if there is an element in the list {l} that is equivalent to {x} according to {r}``() = 

    mem' (fun x y -> abs(x) = abs(y)) (-1) [1;2;3]
    |> assertEqual true

[<Test>]
let ``{mem' r x l} returns {false} if there isn't an element in the list {l} that is equivalent to {x} according to {r}``() = 

    mem' (fun x y -> abs(x) = abs(y)) (-4) [1;2;3]
    |> assertEqual false

[<Test>]
[<ExpectedException(typeof<System.DivideByZeroException>, ExpectedMessage = "Attempted to divide by zero.")>]
let ``{mem' r x l} fails if relation {r} fails``() = 

    mem' (fun x y -> x / y = 2) (4) [0;2;3]
    |> ignore

(* insert' tests *)

[<Test>]
let ``{insert' r x l} will add {x} if there isn't an element in the list {l} that is equivalent to {x} according to {r}``() = 

    insert' (fun x y -> abs(x) = abs(y)) (-1) [2;3;4]
    |> assertEqual [-1;2;3;4]

[<Test>]
let ``{insert' r x l} returns the list unchanged if there is an element in the list {l} that is equivalent to {x} according to {r}``() = 

    insert' (fun x y -> abs(x) = abs(y)) (-1) [1;2;3]
    |> assertEqual [1;2;3]

[<Test>]
[<ExpectedException(typeof<System.DivideByZeroException>, ExpectedMessage = "Attempted to divide by zero.")>]
let ``{insert' r x l} fails if relation {r} fails``() = 

    insert' (fun x y -> x / y = 2) (4) [0;2;3]
    |> ignore

(* union' tests *)

[<Test>]
let ``{union' r l1 l2} appends to the list {l2} all those elements {x} of {l1} for which there is not already an equivalent {x'} with {r x x'} in {l2} or earlier in {l1}``() = 

    union' (fun x y -> abs(x) = abs(y)) [-1; 2; 1] [-2; -3; 4; -4]
    |> assertEqual [1; -2; -3; 4; -4]

(* unions' tests *)

[<Test>]
let ``{unions' r l} returns a list with one representative of each {r}-equivalence class occurring in any of the members``() = 

    unions' (fun x y -> abs(x) = abs(y))[[-1; 2; 3]; [-2; -3; -4]; [4; 5; -6]]
    |> assertEqual [-1; -2; -3; 4; 5; -6]

(* subtract' tests *)

[<Test>]
let ``{subtract' r l1 l2} removes from the list {l1} all elements {x} such that there is an {x'} in {l2} with {r x x'}``() = 

    subtract' (fun x y -> abs(x) = abs(y)) [-1; 2; 1] [-2; -3; 4; -4]
    |> assertEqual [-1; 1]

(* num_of_string tests *)

[<Test>]
let ``{num_of_string "n"} converts the string {"n"} into an OCaml unlimited-precision number: type {num}``() = 

    NHol.lib.num_of_string "0b11000000"
    |> ExtCore.Choice.get
    |> assertEqual (Int 192)
