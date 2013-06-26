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
let ``rev_itlist is equivalent to List.foldBack``() =
    assertProp "rev_itlist" <| fun xs ->
        rev_itlist (fun x acc -> x - acc) xs 0 = List.foldBack (fun x acc -> x - acc) xs 0

[<Test>]
let ``end_itlist is equivalent to List.reduceBack on non-empty lists``() =
    assertProp "end_itlist" <| fun xs ->
        xs <> [] ==> lazy (end_itlist (fun x y -> x - y) xs = List.reduceBack (fun x y -> x - y) xs)

[<Test>]
let ``itlist2 is equivalent to List.fold2 on two same-length lists``() =
    assertProp "itlist2" <| fun zs ->
        let (xs, ys) = List.unzip zs
        itlist2 (fun x y acc -> acc - x + y) xs ys 0 = List.fold2 (fun acc x y -> acc - x + y) 0 xs ys

[<Test>]
let ``rev_itlist2 is equivalent to List.foldBack2 on two same-length lists``() =
    assertProp "rev_itlist2" <| fun zs ->
        let (xs, ys) = List.unzip zs
        rev_itlist2 (fun x y acc -> x + y - acc) xs ys 0 = List.foldBack2 (fun x y acc -> x + y - acc) xs ys 0

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
let ``intersect and subtract can build up the set``() =
    assertProp "intersect-subtract" <| fun (xs : int list) ys ->
        set (intersect xs ys @ subtract xs ys) = set xs

[<Test>]
let ``union and subtract can build up the set``() =
    assertProp "union-subtract" <| fun (xs : int list) ys ->
        set (union xs ys) = set (subtract xs ys @ ys)

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