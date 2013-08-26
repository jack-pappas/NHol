(*

Copyright 2013 Domenico Masini

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

#I "./../packages"
#r "ExtCore.0.8.33/lib/net40/ExtCore.dll"

#I "./../NHol"
#r @"bin/Debug/NHol.dll"

#nowarn "25"
#nowarn "40"
#nowarn "49"
#nowarn "62"

open NHol
open NHol.lib

open ExtCore.Control
open ExtCore.Control.Collections

// My experiments on using choice workflow

// Return early with the first success (multidictionary lookup example)
// This is an OrElse pattern: we try a call and if this succeeds we return the result else we try the next options till the first that succeeds

let map1 = [ ("1","One"); ("2","Two") ] |> Map.ofList
let map2 = [ ("A","Alice"); ("B","Bob") ] |> Map.ofList
let map3 = [ ("CA","California"); ("NY","New York") ] |> Map.ofList

let tryFindIn (map:Map<string,string>) (key:string) : Protected<string> = 
    match map.TryFind key with
    | Some result -> Choice.result <| result
    | None -> NHol.lib.Choice.failwith "coludn't find key"

let multiLookup key  = 
    choice {
        return! tryFindIn map1 <| key
    } 
    |> 
    Choice.bindError (function
                    | Failure _ ->
                        choice {
                            return! tryFindIn map2 <| key
                        }
                    | e -> Choice.error e)
    |>
    Choice.bindError (function
                    | Failure _ ->
                        choice {
                            return! tryFindIn map3 <| key
                        }
                    | e -> Choice.error e)

multiLookup "A" |> printfn "Result for A is %A" 
multiLookup "CA" |> printfn "Result for CA is %A"
multiLookup "X" |> printfn "Result for X is %A"