(*

Copyright 1998 University of Cambridge
Copyright 1998-2007 John Harrison
Copyright 2013 Jack Pappas

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

/// Basic equality reasoning including conversionals.
module NHol.equal

open FSharp.Compatibility.OCaml
open lib
open fusion
open basics
open nets
open printer
open preterm
open parser


(* ------------------------------------------------------------------------- *)
(* Type abbreviation for conversions.                                        *)
(* ------------------------------------------------------------------------- *)

type conv = term -> thm

(* ------------------------------------------------------------------------- *)
(* A bit more syntax.                                                        *)
(* ------------------------------------------------------------------------- *)

let lhand = rand << rator

let lhs = fst << dest_eq

let rhs = snd << dest_eq

(* ------------------------------------------------------------------------- *)
(* Similar to variant, but even avoids constants, and ignores types.         *)
(* ------------------------------------------------------------------------- *)

let mk_primed_var =
  let rec svariant avoid s =
    if mem s avoid || (can get_const_type s && not (is_hidden s)) then
      svariant avoid (s + "'")
    else s
  fun avoid v ->
    let s,ty = dest_var v
    let s' = svariant (mapfilter (fst << dest_var) avoid) s
    mk_var(s',ty)

(* ------------------------------------------------------------------------- *)
(* General case of beta-conversion.                                          *)
(* ------------------------------------------------------------------------- *)

/// General case of beta-conversion.
let BETA_CONV tm =
    try BETA tm
    with Failure _ ->
        try
            let f,arg = dest_comb tm
            let v = bndvar f
            INST [arg,v] (BETA (mk_comb(f,v)))
        with Failure _ ->
            failwith "BETA_CONV: Not a beta-redex"

(* ------------------------------------------------------------------------- *)
(* A few very basic derived equality rules.                                  *)
(* ------------------------------------------------------------------------- *)

let AP_TERM tm th =
  try MK_COMB(REFL tm,th)
  with Failure _ -> failwith "AP_TERM"

let AP_THM th tm =
  try MK_COMB(th,REFL tm)
  with Failure _ -> failwith "AP_THM"

let SYM th =
  let tm = concl th
  let l,r = dest_eq tm
  let lth = REFL l
  EQ_MP (MK_COMB(AP_TERM (rator (rator tm)) th,lth)) lth

let ALPHA tm1 tm2 =
  try TRANS (REFL tm1) (REFL tm2)
  with Failure _ -> failwith "ALPHA"

let ALPHA_CONV v tm =
  let res = alpha v tm
  ALPHA tm res

let GEN_ALPHA_CONV v tm =
    if is_abs tm then
        ALPHA_CONV v tm
    else
        let b,abs = dest_comb tm
        AP_TERM b (ALPHA_CONV v abs)

let MK_BINOP op (lth,rth) =
  MK_COMB(AP_TERM op lth,rth)

(* ------------------------------------------------------------------------- *)
(* Terminal conversion combinators.                                          *)
(* ------------------------------------------------------------------------- *)

let (NO_CONV:conv) = fun tm -> failwith "NO_CONV"

let (ALL_CONV:conv) = REFL

(* ------------------------------------------------------------------------- *)
(* Combinators for sequencing, trying, repeating etc. conversions.           *)
(* ------------------------------------------------------------------------- *)

let THENC : conv -> conv -> conv =
  fun conv1 conv2 t ->
    let th1 = conv1 t
    let th2 = conv2 (rand(concl th1))
    TRANS th1 th2

let ORELSEC : conv -> conv -> conv =
    fun conv1 conv2 t ->
        try conv1 t
        with Failure _ ->
            conv2 t

let (FIRST_CONV:conv list -> conv) = end_itlist (fun c1 c2 -> ORELSEC c1 c2)

let (EVERY_CONV:conv list -> conv) =
    fun l -> itlist THENC l ALL_CONV

let REPEATC : conv -> conv =
    let rec REPEATC conv t =
        (ORELSEC (THENC conv (REPEATC conv)) ALL_CONV) t
    REPEATC

let (CHANGED_CONV:conv->conv) =
  fun conv tm ->
    let th = conv tm
    let l,r = dest_eq (concl th)
    if aconv l r then failwith "CHANGED_CONV" else th

let TRY_CONV conv = ORELSEC conv ALL_CONV

(* ------------------------------------------------------------------------- *)
(* Subterm conversions.                                                      *)
(* ------------------------------------------------------------------------- *)

let (RATOR_CONV:conv->conv) =
    fun conv tm ->
        let l,r = dest_comb tm
        AP_THM (conv l) r

let (RAND_CONV:conv->conv) =
    fun conv tm ->
        let l,r = dest_comb tm
        AP_TERM l (conv r)

let LAND_CONV = RATOR_CONV << RAND_CONV

let (COMB2_CONV: conv->conv->conv) =
    fun lconv rconv tm ->
        let l,r = dest_comb tm
        MK_COMB(lconv l,rconv r)

let COMB_CONV = W COMB2_CONV

let (ABS_CONV:conv->conv) =
    fun conv tm ->
        let v,bod = dest_abs tm
        let th = conv bod
        try ABS v th
        with Failure _ ->
            let gv = genvar(type_of v)
            let gbod = vsubst[gv,v] bod
            let gth = ABS gv (conv gbod)
            let gtm = concl gth
            let l,r = dest_eq gtm
            let v' = variant (frees gtm) v
            let l' = alpha v' l
            let r' = alpha v' r
            EQ_MP (ALPHA gtm (mk_eq(l',r'))) gth

let BINDER_CONV conv tm =
    if is_abs tm then ABS_CONV conv tm
    else RAND_CONV(ABS_CONV conv) tm

let SUB_CONV conv tm =
    match tm with
    | Comb(_,_) -> COMB_CONV conv tm
    | Abs(_,_) -> ABS_CONV conv tm
    | _ -> REFL tm

let BINOP_CONV conv tm =
    let lop,r = dest_comb tm
    let op,l = dest_comb lop
    MK_COMB(AP_TERM op (conv l),conv r)

(* ------------------------------------------------------------------------- *)
(* Depth conversions; internal use of a failure-propagating `Boultonized'    *)
(* version to avoid a great deal of reuilding of terms.                      *)
(* ------------------------------------------------------------------------- *)

let rec private THENQC conv1 conv2 tm =
    try
        let th1 = conv1 tm
        try
            let th2 = conv2(rand(concl th1))
            TRANS th1 th2
        with Failure _ -> th1
    with Failure _ -> conv2 tm

and private THENCQC conv1 conv2 tm =
    let th1 = conv1 tm
    try
        let th2 = conv2(rand(concl th1))
        TRANS th1 th2
    with Failure _ -> th1

and private COMB_QCONV conv tm =
    let l,r = dest_comb tm
    try
        let th1 = conv l
        try
            let th2 = conv r
            MK_COMB(th1,th2)
        with Failure _ ->
            AP_THM th1 r
    with Failure _ ->
        AP_TERM l (conv r)

let rec private REPEATQC conv tm =
    THENCQC conv (REPEATQC conv) tm

let private SUB_QCONV conv tm =
    if is_abs tm then ABS_CONV conv tm
    else COMB_QCONV conv tm

let rec private ONCE_DEPTH_QCONV conv tm =
      (ORELSEC conv (SUB_QCONV (ONCE_DEPTH_QCONV conv))) tm

and private DEPTH_QCONV conv tm =
    THENQC (SUB_QCONV (DEPTH_QCONV conv))
           (REPEATQC conv) tm

and private REDEPTH_QCONV conv tm =
    THENQC (SUB_QCONV (REDEPTH_QCONV conv))
           (THENCQC conv (REDEPTH_QCONV conv)) tm

and private TOP_DEPTH_QCONV conv tm =
    THENQC (REPEATQC conv)
           (THENCQC (SUB_QCONV (TOP_DEPTH_QCONV conv))
                    (THENCQC conv (TOP_DEPTH_QCONV conv))) tm

and private TOP_SWEEP_QCONV conv tm =
    THENQC (REPEATQC conv)
           (SUB_QCONV (TOP_SWEEP_QCONV conv)) tm

let ONCE_DEPTH_CONV (c : conv) : conv =
    TRY_CONV (ONCE_DEPTH_QCONV c)

let DEPTH_CONV (c : conv) : conv =
    TRY_CONV (DEPTH_QCONV c)

let REDEPTH_CONV (c : conv) : conv =
    TRY_CONV (REDEPTH_QCONV c)

let TOP_DEPTH_CONV (c : conv) : conv =
    TRY_CONV (TOP_DEPTH_QCONV c)

let TOP_SWEEP_CONV (c : conv) : conv =
    TRY_CONV (TOP_SWEEP_QCONV c)


(* ------------------------------------------------------------------------- *)
(* Apply at leaves of op-tree; NB any failures at leaves cause failure.      *)
(* ------------------------------------------------------------------------- *)

let rec DEPTH_BINOP_CONV op conv tm =
  match tm with
  | Comb(Comb(op',l),r) when op' = op ->
      let l,r = dest_binop op tm
      let lth = DEPTH_BINOP_CONV op conv l
      let rth = DEPTH_BINOP_CONV op conv r
      MK_COMB(AP_TERM op' lth,rth)
  | _ -> conv tm

(* ------------------------------------------------------------------------- *)
(* Follow a path.                                                            *)
(* ------------------------------------------------------------------------- *)

/// Follow a path.
let PATH_CONV =
  let rec path_conv s cnv =
    match s with
      [] -> cnv
    | "l"::t -> RATOR_CONV (path_conv t cnv)
    | "r"::t -> RAND_CONV (path_conv t cnv)
    | _::t -> ABS_CONV (path_conv t cnv)
  fun s cnv -> path_conv (explode s) cnv

(* ------------------------------------------------------------------------- *)
(* Follow a pattern                                                          *)
(* ------------------------------------------------------------------------- *)

/// Follow a pattern.
let PAT_CONV =
  let rec PCONV xs pat conv =
    if mem pat xs then conv
    elif not(exists (fun x -> free_in x pat) xs) then ALL_CONV
    elif is_comb pat then
      COMB2_CONV (PCONV xs (rator pat) conv) (PCONV xs (rand pat) conv)
    else
      ABS_CONV (PCONV xs (body pat) conv)
  fun pat ->
    let xs,pbod = strip_abs pat
    PCONV xs pbod

(* ------------------------------------------------------------------------- *)
(* Symmetry conversion.                                                      *)
(* ------------------------------------------------------------------------- *)

/// Symmetry conversion.
let SYM_CONV tm =
  try let th1 = SYM(ASSUME tm)
      let tm' = concl th1
      let th2 = SYM(ASSUME tm')
      DEDUCT_ANTISYM_RULE th2 th1
  with Failure _ -> failwith "SYM_CONV"

(* ------------------------------------------------------------------------- *)
(* Conversion to a rule.                                                     *)
(* ------------------------------------------------------------------------- *)

/// Conversion to a rule.
let CONV_RULE (conv:conv) th =
  EQ_MP (conv(concl th)) th

(* ------------------------------------------------------------------------- *)
(* Substitution conversion.                                                  *)
(* ------------------------------------------------------------------------- *)

/// Substitution conversion.
let SUBS_CONV ths tm =
    try
        if ths = [] then REFL tm
        else
            let lefts = map (lhand << concl) ths
            let gvs = map (genvar << type_of) lefts
            let pat = subst (zip gvs lefts) tm
            let abs = list_mk_abs(gvs,pat)
            let th = rev_itlist
                      (fun y x -> CONV_RULE (THENC (RAND_CONV BETA_CONV) (LAND_CONV BETA_CONV))
                                    (MK_COMB(x,y))) ths (REFL abs)
            if rand(concl th) = tm then REFL tm else th
    with Failure _ ->
        failwith "SUBS_CONV"

(* ------------------------------------------------------------------------- *)
(* Get a few rules.                                                          *)
(* ------------------------------------------------------------------------- *)

let BETA_RULE = CONV_RULE(REDEPTH_CONV BETA_CONV)

let GSYM = CONV_RULE(ONCE_DEPTH_CONV SYM_CONV)

let SUBS ths = CONV_RULE (SUBS_CONV ths)

(* ------------------------------------------------------------------------- *)
(* A cacher for conversions.                                                 *)
(* ------------------------------------------------------------------------- *)

let private ALPHA_HACK th =
    let tm' = lhand(concl th)
    fun tm ->
        if tm' = tm then th
        else TRANS (ALPHA tm tm') th

/// A cacher for conversions.
let CACHE_CONV (conv : conv) : conv =
    // NOTE : This is not thread-safe!
    let net = ref empty_net
    fun tm ->
        try tryfind (fun f -> f tm) (lookup tm (!net))
        with Failure _ ->
            let th : thm = conv tm
            net := enter [] (tm,ALPHA_HACK th) (!net)
            th



