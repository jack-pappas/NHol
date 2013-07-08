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

// Almost all functions here have equivalences in FSharp.Core.
// We use the core functions as models for testing.

[<Test>]
let ``map is equivalent to List.map``() =
    assertProp "map" <| fun xs ->
        map (fun x -> 2 * x) xs = List.map (fun x -> 2 * x) xs

[<Test>]
let ``map2 is equivalent to List.map2``() =
    assertProp "map2" <| fun zs ->
        let (xs, ys) = List.unzip zs
        map2 (fun x y -> x * y) xs ys = List.map2 (fun x y -> x * y) xs ys

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
    assertProp "end_itlist" <| fun xs ->
        xs <> [] ==> lazy (end_itlist (fun x y -> x - y) xs = List.reduceBack (fun x y -> x - y) xs)

[<Test>]
let ``itlist2 is equivalent to List.foldBack2 on two same-length lists``() =
    assertProp "itlist2" <| fun zs ->
        let (xs : int64 list), (ys : int16 list) = List.unzip zs
        itlist2 (fun x y acc -> acc + ((int x) + (int y)).ToString()) xs ys "" = List.foldBack2 (fun x y acc -> acc + ((int x) + (int y)).ToString()) xs ys ""

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
    assertProp "forall" <| fun xs ->
        forall (fun x -> x > 0) xs = List.forall (fun x -> x > 0) xs

[<Test>]
let ``forall2 is equivalent to List.forall2``() =
    assertProp "forall2" <| fun (zs : (int * int) list) ->
        let (xs, ys) = List.unzip zs
        forall2 (fun x y -> x >= y) xs ys = List.forall2 (fun x y -> x >= y) xs ys

[<Test>]
let ``exists is equivalent to List.exists``() =
    assertProp "exists" <| fun xs ->
        exists (fun x -> x > 0) xs = List.exists (fun x -> x > 0) xs

[<Test>]
let ``length is equivalent to List.length``() =
    assertProp "length" <| fun xs ->
        length xs = List.length xs

[<Test>]
let ``filter is equivalent to List.filter``() =
    assertProp "filter" <| fun xs ->
        filter (fun x -> x > 0) xs = List.filter (fun x -> x > 0) xs

[<Test>]
let ``partition is equivalent to List.partition``() =
    assertProp "partition" <| fun xs ->
        partition (fun x -> x > 0) xs = List.partition (fun x -> x > 0) xs

// The `lazy` keyword is important in order to avoid early evaluation
[<Test>]
let ``find is equivalent to List.find``() =
    assertProp "find" <| fun xs ->
        List.exists (fun x -> x > 0) xs ==> 
            lazy (find (fun x -> x > 0) xs = List.find (fun x -> x > 0) xs)

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
let ``intersect and subtract can build up the setify``() =
    assertProp "intersect-subtract" <| fun (xs : int list) ys ->
        setify (intersect xs ys @ subtract xs ys) = setify xs

[<Test>]
let ``union and subtract can build up the setify``() =
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
let ``check func<'a, 'b> against Map<'a, 'b> model in F# core``() =
    Check.QuickThrowOnFailure (asProperty spec)

// Now we test case by case using FsUnit

[<Test>]
let ``{can f x} evaluates to {false} if the application of {f} to {x} causes exception of type Failure _``() = 
    can hd [] |> should equal false