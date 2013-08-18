(*

Copyright 1998 University of Cambridge
Copyright 1998-2007 John Harrison
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

#if USE
#else
/// Term nets: reasonably fast lookup based on term matchability.
module NHol.nets

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

open ExtCore.Control

open NHol
open system
open lib
open fusion
open fusion.Hol_kernel
open basics
#endif

logger.Trace("Entering nets.fs")

(* ------------------------------------------------------------------------- *)
(* Term nets are a finitely branching tree structure; at each level we       *)
(* have a set of branches and a set of "values". Linearization is            *)
(* performed from the left of a combination; even in iterated                *)
(* combinations we look at the head first. This is probably fastest, and     *)
(* anyway it's useful to allow our restricted second order matches: if       *)
(* the head is a variable then then whole term is treated as a variable.     *)
(* ------------------------------------------------------------------------- *)

type term_label = 
    | Vnet                      (* variable (instantiable)   *)
    | Lcnet of (string * int)   (* local constant            *)
    | Cnet of (string * int)    (* constant                  *)
    | Lnet of int               (* lambda term (abstraction) *)
    override this.ToString() = 
        match this with
        | Vnet -> "Vnet"
        | Lcnet(s, i) -> "Lcnet (\"" + s + "\", " + i.ToString() + ")"
        | Cnet(s, i) -> "Cnet (\"" + s + "\", " + i.ToString() + ")"
        | Lnet i -> "Lnet (" + i.ToString() + ")"

type net<'a> = 
    | Netnode of (term_label * 'a net) list * 'a list
    override this.ToString() = 
        match this with
        | Netnode(tlList, aList) -> 
            "Netnode (" + tlList.ToString() + ", " + aList.ToString() + ")"

(* ------------------------------------------------------------------------- *)
(* The empty net.                                                            *)
(* ------------------------------------------------------------------------- *)

/// The empty net.
let empty_net = Netnode([], [])

(* ------------------------------------------------------------------------- *)
(* Insert a new element into a net.                                          *)
(* ------------------------------------------------------------------------- *)

/// Insert a new element into a net.
let enter : _ -> _ -> _ -> Protected<net<'T>> = 
    let label_to_store lconsts tm = 
        choice {
            let op, args = strip_comb tm
            if is_const op then
                let! (s, _) = dest_const op
                return Cnet(s, length args), args
            elif is_abs op then 
                let! (bv, bod) = dest_abs op
                if mem bv lconsts then
                    let! tb = type_of bv
                    let! bod' = vsubst [genvar tb, bv] bod
                    return Lnet(length args), bod' :: args
                else
                    return Lnet(length args), bod :: args                
            elif mem op lconsts then
                let! (s, _) = dest_var op 
                return Lcnet(s, length args), args
            else 
                return Vnet, []
        }

    let canon_eq x y = 
        Unchecked.compare x y = 0

    let canon_lt x y = 
        Unchecked.compare x y < 0

    let rec sinsert x l =
        choice {
        match l with
        | [] ->
            return [x]
        | hd :: tl -> 
            if canon_eq hd x then
                return! Choice.failwith "sinsert"
            elif canon_lt x hd then
                return! Choice.result (x :: l)
            else
                let! tl = sinsert x tl
                return hd :: tl
        }

    let set_insert x l =
        sinsert x l
        |> Choice.fill l

    let rec net_update lconsts (elem, tms, Netnode(edges, tips)) = 
        choice {
            match tms with
            | [] ->
                return Netnode(edges, set_insert elem tips)
            | tm :: rtms -> 
                let! label, ntms = label_to_store lconsts tm
                let child, others =
                    match remove (fun (x, y) -> x = label) edges with
                    | None ->
                        empty_net, edges
                    | Some x ->
                        (snd ||>> I) x
                    
                let! new_child = net_update lconsts (elem, ntms @ rtms, child)
                return Netnode((label, new_child) :: others, tips)
        }

    fun lconsts (tm, elem) net ->
        net_update lconsts (elem, [tm], net)

(* ------------------------------------------------------------------------- *)
(* Look up a term in a net and return possible matches.                      *)
(* ------------------------------------------------------------------------- *)

/// Look up a term in a net and return possible matches.
let lookup : _ -> _ -> Protected<'T list> =
    let label_for_lookup tm =
        choice {
            let op, args = strip_comb tm
            if is_const op then
                let! (s, _) = dest_const op
                return Cnet(s, length args), args
            elif is_abs op then
                let! tm = body op
                return Lnet(length args), tm :: args
            else
                let! (s, _) = dest_var op
                return Lcnet(s, length args), args
        }

    let rec follow(tms, Netnode(edges, tips)) =
        choice {
            match tms with
            | [] ->
                return tips
            | tm :: rtms ->
                let! label, ntms = label_for_lookup tm
                let! collection =
                    // OPTIMIZE : Use Option.map and Option.fill to replace the 'match' statement.
                    match assoc label edges with
                    | None -> Choice.result []
                    | Some child ->
                        follow(ntms @ rtms, child)

                if label = Vnet then
                    return collection
                else
                    // OPTIMIZE : Use Option.map and Option.fill to replace the 'match' statement.
                    match assoc Vnet edges with
                    | None -> return collection
                    | Some x ->
                        let! coll = follow(rtms, x)
                        return collection @ coll
        }

    fun tm net ->
        follow([tm], net)

(* ------------------------------------------------------------------------- *)
(* Function to merge two nets (code from Don Syme's hol-lite).               *)
(* ------------------------------------------------------------------------- *)

/// Function to merge two nets.
let merge_nets = 
    let canon_eq x y = 
        compare x y = 0
        
    let canon_lt x y = 
        compare x y < 0
        
    let rec set_merge l1 l2 =
        match l1, l2 with
        | [], _ -> l2
        | _, [] -> l1
        | h1 :: t1, h2 :: t2 ->
            if canon_eq h1 h2 then
                h1 :: (set_merge t1 t2)
            elif canon_lt h1 h2 then
                h1 :: (set_merge t1 l2)
            else
                h2 :: (set_merge l1 t2)

    let rec merge_nets (Netnode (l1, data1), Netnode (l2, data2)) = 
        let add_node ((lab, net) as p) l =
            match remove (fun (x, y) -> x = lab) l with
            | None ->
                p :: l
            | Some ((lab', net'), rest) ->
                (lab', merge_nets(net, net')) :: rest

        Netnode (itlist add_node l2 (itlist add_node l1 []), set_merge data1 data2)

    merge_nets
