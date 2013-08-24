(*

Copyright 1998 University of Cambridge
Copyright 1998-2007 John Harrison
Copyright 2013 Jack Pappas, Eric Taucher, Anh-Dung Phan

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
/// More syntax constructors, and prelogical utilities like matching.
module NHol.basics

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

open ExtCore.Control
open ExtCore.Control.Collections

open NHol
open system
open lib
open fusion
open fusion.Hol_kernel
#endif

infof "Entering basics.fs"

(* ------------------------------------------------------------------------- *)
(* Create probably-fresh variable                                            *)
(* ------------------------------------------------------------------------- *)

let internal gcounter = ref 0

/// Returns a 'fresh' variable with specified type.
let genvar ty =
    let count = !gcounter
    gcounter := count + 1
    mk_var("_" + (string count), ty)

(* ------------------------------------------------------------------------- *)
(* Convenient functions for manipulating types.                              *)
(* ------------------------------------------------------------------------- *)

/// Break apart a function type into domain and range.
let dest_fun_ty ty : Protected<hol_type * hol_type> =
    choice {
    match ty with
    | Tyapp("fun", [ty1; ty2]) ->
        return ty1, ty2
    | _ ->
        return! Choice.failwith "dest_fun_ty"
    }

/// Tests if one type occurs in another.
let rec occurs_in ty bigty : Protected<bool> =
    choice {
        // In order to preserve original behaviour, this function now returns Protected<bool>
        let! (_, tys0) = dest_type bigty
        // Interpret the condition as a || (b && c)
        if bigty = ty then
            return true
        elif not (is_type bigty) then
            return false
        else
            return! Choice.List.exists (occurs_in ty) tys0
    }

/// The call tysubst [ty1',ty1; ... ; tyn',tyn] ty will systematically traverse the type ty
/// and replace the topmost instances of any tyi encountered with the corresponding tyi'.
/// In the (usual) case where all the tyi are type variables, this is the same as type_subst,
/// but also works when they are not.
let rec tysubst alist ty : Protected<hol_type> =
    choice {
        // OPTIMIZE : Use Option.fillWith from ExtCore.
        match rev_assoc ty alist with
        | Some ty -> 
            return ty
        | None ->
            if is_vartype ty then 
                return ty
            else 
                let! tycon, tyvars = dest_type ty
                let! tms = Choice.List.map (tysubst alist) tyvars
                return! mk_type(tycon, tms)
    }

(* ------------------------------------------------------------------------- *)
(* A bit more syntax.                                                        *)
(* ------------------------------------------------------------------------- *)

/// Returns the bound variable of an abstraction.
let bndvar tm : Protected<term> =
    choice {
        let! (tm0, _) = dest_abs tm
        return tm0
    }
    |> Choice.mapError (fun e -> nestedFailure e "bndvar: Not an abstraction")

/// Returns the body of an abstraction.
let body tm : Protected<term> =
    choice {
        let! (_, tm1) = dest_abs tm
        return tm1
    }
    |> Choice.mapError (fun e -> nestedFailure e "body: Not an abstraction")

/// Iteratively constructs combinations (function applications).
let list_mk_comb(h, t) = 
    Choice.List.fold (curry mk_comb) h t

/// Iteratively constructs abstractions.
let list_mk_abs(vs, bod) : Protected<term> = 
    Choice.List.foldBack (fun x acc -> mk_abs(x, acc)) vs bod

/// Iteratively breaks apart combinations (function applications).
let strip_comb = rev_splitlist (Choice.toOption << dest_comb)

/// Iteratively breaks apart abstractions.
let strip_abs = splitlist (Choice.toOption << dest_abs)

(* ------------------------------------------------------------------------- *)
(* Generic syntax to deal with some binary operators.                        *)
(*                                                                           *)
(* Note that "mk_binary" only works for monomorphic functions.               *)
(* ------------------------------------------------------------------------- *)

/// Tests if a term is an application of a named binary operator.
let is_binary s tm = 
    match tm with
    | Comb(Comb(Const(s', _), _), _) -> s' = s
    | _ -> false

/// Breaks apart an instance of a binary operator with given name.
let dest_binary s tm : Protected<term * term> = 
    match tm with
    | Comb(Comb(Const(s', _), l), r) when s' = s -> 
        Choice.result (l, r)
    | _ -> 
        Choice.failwith "dest_binary"

/// Constructs an instance of a named monomorphic binary operator.
let mk_binary s = 
    let c = mk_const(s, [])
    fun (l, r) -> 
        choice {
            let! c' = c 
            let! l' = mk_comb(c', l)
            return! mk_comb(l', r)
        }
        |> Choice.mapError (fun e -> nestedFailure e "mk_binary")
        : Protected<term>

(* ------------------------------------------------------------------------- *)
(* Produces a sequence of variants, considering previous inventions.         *)
(* ------------------------------------------------------------------------- *)

/// Pick a list of variants of variables, avoiding a list of variables and each other.
let rec variants av vs : Protected<term list> =
    choice {
        if List.isEmpty vs then
            return []
        else
            let! vh = variant av (hd vs)
            let! vhs = variants (vh :: av) (tl vs)
            return vh :: vhs
    }

(* ------------------------------------------------------------------------- *)
(* Gets all variables (free and/or bound) in a term.                         *)
(* ------------------------------------------------------------------------- *)

/// Determines the variables used, free or bound, in a given term.
let variables : term -> Protected<term list> =
    let rec vars(acc, tm) =
        choice {
        if is_var tm then
            return insert tm acc
        elif is_const tm then
            return acc
        elif is_abs tm then 
            let! v, bod = dest_abs tm
            return! vars(insert v acc, bod)
        else
            let! l, r = dest_comb tm
            let! l' = vars(acc, l)
            return! vars(l', r)
        }
    fun tm ->
        vars([], tm)

(* ------------------------------------------------------------------------- *)
(* General substitution (for any free expression).                           *)
(* ------------------------------------------------------------------------- *)

/// Substitute terms for other terms inside a term.
let subst : (term * term) list -> term -> Protected<term> = 
    let rec ssubst ilist tm =
        choice {
        if List.isEmpty ilist then
            return tm
        else 
            match find ((aconv tm) << snd) ilist with
            | Some(tm', _) ->
                return tm'
            | None ->
                match tm with
                | Comb(f, x) -> 
                    let! f' = ssubst ilist f
                    let! x' = ssubst ilist x
                    if f' == f && x' == x then
                        return tm
                    else
                        return! mk_comb(f', x')
                | Abs(v, bod) ->
                    // CLEAN : Rename this value to something sensible.
                    let! foo1 =
                        let ilist' = filter (not << (vfree_in v) << snd) ilist
                        ssubst ilist' bod
                    return! mk_abs(v, foo1)
                | _ ->
                    return tm
        }

    let subst ilist =
        let theta = filter (fun (s, t) -> compare s t <> 0) ilist
        if List.isEmpty theta then
            Choice.result
        else 
            let ts, xs = unzip theta
            fun tm ->
                choice {
                let! variables_tm = variables tm
                // CLEAN : Rename this value to something sensible.
                let! foo1 = Choice.List.map (Choice.map genvar << type_of) xs
                let! gs = variants variables_tm foo1
                let! tm' = ssubst (zip gs xs) tm
                if tm' == tm then return tm
                else return! vsubst (zip ts gs) tm'
                }

    subst

(* ------------------------------------------------------------------------- *)
(* Alpha conversion term operation.                                          *)
(* ------------------------------------------------------------------------- *)

/// Changes the name of a bound variable.
let alpha v tm : Protected<term> = 
    choice {
        let! (v0, bod) = 
            dest_abs tm 
            |> Choice.mapError (fun e -> nestedFailure e "alpha: Not an abstraction")
        if v = v0 then 
            return tm
        else
            let! ty = type_of v
            let! ty0 = type_of v0
            if ty = ty0 && not(vfree_in v bod) then 
                let! sub = vsubst [v, v0] bod
                return! mk_abs(v, sub)
            else return! Choice.failwith "alpha: Invalid new variable"
    }

(* ------------------------------------------------------------------------- *)
(* Type matching.                                                            *)
(* ------------------------------------------------------------------------- *)

/// Computes a type instantiation to match one type to another.
let rec type_match vty cty sofar : Protected<(hol_type * hol_type) list> =
    choice {
    if is_vartype vty then
        match rev_assoc vty sofar with
        | Some x ->
            if x = cty then
                return sofar
            else
                return! Choice.failwith "type_match"
        | None ->
            return (cty, vty) :: sofar
    else 
        let! vop, vargs = dest_type vty
        let! cop, cargs = dest_type cty
        if vop = cop then
            return! Choice.List.foldBack2 type_match vargs cargs sofar
        else
            return! Choice.failwith "type_match"
    }

(* ------------------------------------------------------------------------- *)
(* Conventional matching version of mk_const (but with a sanity test).       *)
(* ------------------------------------------------------------------------- *)

/// Constructs a constant with type matching.
let mk_mconst(c, ty) : Protected<term> =
    choice {
        let! uty = get_const_type c
        let! mat = type_match uty ty []
        let! con = mk_const(c, mat)
        let! tc = type_of con
        if tc = ty then
            return con
        else
            return! Choice.failwith "mk_mconst"
    }
    |> Choice.mapError (fun e ->
        nestedFailure e "mk_const: generic type cannot be instantiated")

(* ------------------------------------------------------------------------- *)
(* Like mk_comb, but instantiates type variables in rator if necessary.      *)
(* ------------------------------------------------------------------------- *)

/// Makes a combination, instantiating types in rator if necessary.
let mk_icomb(tm1, tm2) : Protected<term> =
    choice {
        let! ty1 = type_of tm1
        let! (s, ty1') = dest_type ty1
        match (s, ty1') with
        | "fun", [ty; _] ->
            let! ty2 = type_of tm2
            let! tyins = type_match ty ty2 []
            let! tm1' = inst tyins tm1
            return! mk_comb(tm1', tm2)
        | _ ->
            return! Choice.failwith "mk_icomb: Unhandled case."
    }

(* ------------------------------------------------------------------------- *)
(* Instantiates types for constant c and iteratively makes combination.      *)
(* ------------------------------------------------------------------------- *)

/// Applies constant to list of arguments, instantiating constant type as needed.
let list_mk_icomb cname args : Protected<term> =
    choice {
        let! ty1 = get_const_type cname
        let! atys, _ = Choice.List.nsplit dest_fun_ty args ty1
        let! tyin =
            (atys, args, [])
            |||> Choice.List.foldBack2 (fun g a acc -> 
                choice {
                let! tya = type_of a
                return! type_match g tya acc
                })
        let! tm1 = mk_const(cname, tyin)
        return! list_mk_comb(tm1, args)
    }
(* ------------------------------------------------------------------------- *)
(* Free variables in assumption list and conclusion of a theorem.            *)
(* ------------------------------------------------------------------------- *)

/// Returns a list of the variables free in a theorem's assumptions and conclusion.
let thm_frees th = 
    let asl, c = dest_thm th
    itlist (union << frees) asl (frees c)

(* ------------------------------------------------------------------------- *)
(* Is one term free in another?                                              *)
(* ------------------------------------------------------------------------- *)

/// Tests if one term is free in another.
let rec free_in tm1 tm2 : Protected<bool> =
    choice {
    if aconv tm1 tm2 then
        return true
    elif is_comb tm2 then
        let! l, r = dest_comb tm2
        let! l_result = free_in tm1 l
        if l_result then return true
        else
            return! free_in tm1 r
    elif is_abs tm2 then
        let! bv, bod = dest_abs tm2
        if not <| vfree_in bv tm1 then
            return! free_in tm1 bod
        else return false
    else return false
    }

(* ------------------------------------------------------------------------- *)
(* Searching for terms.                                                      *)
(* ------------------------------------------------------------------------- *)

/// Searches a term for a subterm that satisfies a given predicate.
// TODO : Modify this function to accept a protected predicate, i.e., (p : term -> Protected<bool>)
let rec find_term p tm : Protected<term> =
    choice {
        let! b = p tm
        if b then 
            return tm
        elif is_abs tm then
            let! bod = body tm
            return! find_term p bod
        elif is_comb tm then
            let! l, r = dest_comb tm
            return!
                find_term p l
                |> Choice.bindError (function
                        | Failure _ -> find_term p r
                        | e -> Choice.error e)
        else
            return! Choice.failwith "find_term"
    }

/// Searches a term for all subterms that satisfy a predicate.
let find_terms =
    let rec accum tl p tm = 
        choice {
            let! tl' = 
                choice {
                    let! b = p tm
                    if b then 
                        return insert tm tl
                    else 
                        return tl
                }
            if is_abs tm then 
                let! tm' = body tm
                return! accum tl' p tm'
            elif is_comb tm then
                let! rat = rator tm
                let! tl'' = accum tl' p rat
                let! ran = rand tm
                return! accum tl'' p ran
            else return tl'
        } : Protected<term list>
    accum []

(* ------------------------------------------------------------------------- *)
(* General syntax for binders.                                               *)
(*                                                                           *)
(* NB! The "mk_binder" function expects polytype "A", which is the domain.   *)
(* ------------------------------------------------------------------------- *)

/// Tests if a term is a binder construct with named constant.
let is_binder s tm = 
    match tm with
    | Comb(Const(s', _), Abs(_, _)) -> s' = s
    | _ -> false

/// Breaks apart a "binder".
let dest_binder s tm : Protected<term * term> =
    choice {
    match tm with
    | Comb(Const(s', _), Abs(x, t)) when s' = s -> 
        return x, t
    | _ ->
        return! Choice.failwith "dest_binder"
    }

/// Constructs a term with a named constant applied to an abstraction.
let mk_binder op = 
    let c = mk_const(op, [])
    fun (v, tm) -> 
        choice {
            let! tv = type_of v
            let! c' = c 
            let! tm' = inst [tv, aty] c'
            let! tm'' = mk_abs(v, tm)
            return! mk_comb(tm', tm'')
        } : Protected<term>

(* ------------------------------------------------------------------------- *)
(* Syntax for binary operators.                                              *)
(* ------------------------------------------------------------------------- *)

/// Tests if a term is an application of the given binary operator.
let is_binop op tm = 
    match tm with
    | Comb(Comb(op', _), _) -> op' = op
    | _ -> false

/// Breaks apart an application of a given binary operator to two arguments.
let dest_binop op tm : Protected<term * term> =
    choice {
    match tm with
    | Comb(Comb(op', l), r) when op' = op -> 
        return l, r
    | _ -> 
        return! Choice.failwith "dest_binop"
    }

/// The call 'mk_binop op l r' returns the term '(op l) r'.
let mk_binop op tm1 : (term -> Protected<term>) =
    let tm1' = mk_comb(op, tm1)
    fun tm2 ->
        choice {
        let! tm1' = tm1'
        return! mk_comb(tm1', tm2)
        }

/// Makes an iterative application of a binary operator.
// TODO : Modify this to use Choice.List.reduce/reduceBack.
let list_mk_binop op : term list -> Protected<term> = 
    Choice.List.reduceBack (mk_binop op)

/// Repeatedly breaks apart an iterated binary operator into components.
let binops op = striplist(Choice.toOption << dest_binop op)

(* ------------------------------------------------------------------------- *)
(* Some common special cases                                                 *)
(* ------------------------------------------------------------------------- *)

/// Tests a term to see if it is a conjunction.
let is_conj = is_binary "/\\"

/// Term destructor for conjunctions.
let dest_conj = dest_binary "/\\"

/// Iteratively breaks apart a conjunction.
let conjuncts = striplist (Choice.toOption << dest_conj)

/// Tests if a term is an application of implication.
let is_imp = is_binary "==>"

/// Breaks apart an implication into antecedent and consequent.
let dest_imp = dest_binary "==>"

/// Tests a term to see if it is a universal quantification.
let is_forall = is_binder "!"

/// Breaks apart a universally quantified term into quantified variable and body.
let dest_forall = dest_binder "!"

/// Iteratively breaks apart universal quantifications.
let strip_forall = splitlist (Choice.toOption << dest_forall)

/// Tests a term to see if it as an existential quantification.
let is_exists = is_binder "?"

/// Breaks apart an existentially quantified term into quantified variable and body.
let dest_exists = dest_binder "?"

/// Iteratively breaks apart existential quantifications.
let strip_exists = splitlist (Choice.toOption << dest_exists)

/// Tests a term to see if it is a disjunction.
let is_disj = is_binary "\\/"

/// Breaks apart a disjunction into the two disjuncts.
let dest_disj = dest_binary "\\/"

/// Iteratively breaks apart a disjunction.
let disjuncts = striplist (Choice.toOption << dest_disj)

/// Tests a term to see if it is a logical negation.
let is_neg tm =
    choice {
        let! tm1 = rator tm
        let! (s, _) = dest_const tm1
        return s = "~"
    }
    |> Choice.fill false

/// Breaks apart a negation, returning its body.
let dest_neg tm : Protected<term> =
    choice {
    let! n, p = dest_comb tm
    let! s, _ = dest_const n
    if s = "~" then
        return p
    else
        return! Choice.fail ()
    }
    |> Choice.mapError (fun e -> nestedFailure e "dest_neg")

/// Tests if a term is of the form `there exists a unique ...'
let is_uexists = is_binder "?!"

/// Breaks apart a unique existence term.
let dest_uexists = dest_binder "?!"

/// Breaks apart a `CONS pair' into head and tail.
let dest_cons = dest_binary "CONS"

/// Tests a term to see if it is an application of CONS.
let is_cons = is_binary "CONS"

/// Iteratively breaks apart a list term.
let dest_list tm : Protected<term list> =
    choice { 
        let tms, nil = splitlist (Choice.toOption << dest_cons) tm
        let! (s, _) = dest_const nil
        if s = "NIL" then 
            return tms
        else 
            return! Choice.fail()
    }
    |> Choice.mapError (fun e -> nestedFailure e "dest_list")

/// Tests a term to see if it is a list.
let is_list x =
    Choice.isResult <| dest_list x

(* ------------------------------------------------------------------------- *)
(* Syntax for numerals.                                                      *)
(* ------------------------------------------------------------------------- *)

/// Converts a HOL numeral term to unlimited-precision integer.
let dest_numeral : term -> Protected<Num> =
    let rec dest_num tm = 
        choice {
            let b = 
                choice {
                    let! (s, _) = dest_const tm
                    return s = "_0"
                }
                |> Choice.fill false

            if b then 
                return num_0
            else 
                let! l, r = dest_comb tm
                let! r' = dest_num r
                let n = num_2 * r'
                let! (cn, _) = dest_const l
                if cn = "BIT0" then 
                    return n
                elif cn = "BIT1" then 
                    return n + num_1
                else 
                    return! Choice.fail()
        }

    fun tm -> 
        choice { 
            let! l, r = dest_comb tm
            let! (s, _) = dest_const l
            if s = "NUMERAL" then 
                return! dest_num r
            else 
                return! Choice.fail()
        }
        |> Choice.mapError (fun e -> nestedFailure e "dest_numeral")

(* ------------------------------------------------------------------------- *)
(* Syntax for generalized abstractions.                                      *)
(*                                                                           *)
(* These are here because they are used by the preterm->term translator;     *)
(* preterms regard generalized abstractions as an atomic notion. This is     *)
(* slightly unclean --- for example we need locally some operations on       *)
(* universal quantifiers --- but probably simplest. It has to go somewhere!  *)
(* ------------------------------------------------------------------------- *)

/// Breaks apart a generalized abstraction into abstracted varstruct and body.
let dest_gabs : term -> Protected<term * term> =
    let dest_geq = dest_binary "GEQ"
    fun tm ->
        choice {
            if is_abs tm then
                return! dest_abs tm
            else
                let! (l, r) = dest_comb tm
                let! (l', _) = dest_const l
                if not (l' = "GABS") then
                    return! Choice.fail()
                else
                    let! r' = body r
                    let! (ltm, rtm) = dest_geq(snd(strip_forall r'))
                    let! ltm' = rand ltm
                    return (ltm', rtm)
        }
        |> Choice.mapError (fun e -> nestedFailure e "dest_gabs: Not a generalized abstraction")

/// Tests if a term is a basic or generalized abstraction.
let is_gabs x =
    Choice.isResult (dest_gabs x)
    
/// Constructs a generalized abstraction.
let mk_gabs : term * term -> Protected<term> = 
    let mk_forall(v, t) = 
        choice {
            let! ty1 = type_of v
            let! cop = mk_const("!", [ty1, aty])
            let! tm1 = mk_abs(v, t)
            return! mk_comb(cop, tm1)
        }

    let list_mk_forall(vars, bod) = 
        Choice.List.foldBack (fun x acc -> mk_forall(x, acc)) vars bod

    let mk_geq(t1, t2) = 
        choice {
            let! ty1 = type_of t1
            let! p = mk_const("GEQ", [ty1, aty])
            let! tm1 = mk_comb(p, t1)
            return! mk_comb(tm1, t2)
        }

    fun (tm1, tm2) ->
        choice {
            if is_var tm1 then 
                return! mk_abs(tm1, tm2)
            else 
                let fvs = frees tm1
                let! ty1 = type_of tm1
                let! ty2 = type_of tm2
                let! fty = mk_fun_ty ty1 ty2
                let! f = variant (frees tm1 @ frees tm2) (mk_var("f", fty))
                let! tm3 = mk_comb(f, tm1)
                let! tm4 = mk_geq(tm3, tm2)
                let! tm5 = list_mk_forall(fvs, tm4)
                let! tm6 = mk_const("GABS", [fty, aty])
                let! bod = mk_abs(f, tm5)
                return! mk_comb(tm6, bod)
        }

/// Iteratively makes a generalized abstraction.
let list_mk_gabs(vs, bod) : Protected<term> =
    Choice.List.foldBack (fun x acc -> mk_gabs(x, acc)) vs bod

/// Breaks apart an iterated generalized or basic abstraction.
let strip_gabs = splitlist (Choice.toOption << dest_gabs)

(* ------------------------------------------------------------------------- *)
(* Syntax for let terms.                                                     *)
(* ------------------------------------------------------------------------- *)

/// Breaks apart a let-expression.
let dest_let tm : Protected<(term * term) list * term> = 
    choice { 
        let l, aargs = strip_comb tm
        let! (l', _ ) = dest_const l
        if l' <> "LET" then
            return! Choice.fail()
        else 
            let vars, lebod = strip_gabs(hd aargs)
            let eqs = zip vars (tl aargs)
            let! (le, bod) = dest_comb lebod
            let! (le', _ ) = dest_const le
            if le' = "LET_END" then return (eqs, bod)
            else return! Choice.fail()
    }
    |> Choice.mapError (fun e -> nestedFailure e "dest_let: not a let-term")

/// Tests a term to see if it is a let-expression.
let is_let x =
    Choice.isResult (dest_let x)

/// Constructs a let-expression.
let mk_let(assigs, bod) : Protected<term> = 
    choice {
        let lefts, rights = unzip assigs
        let! tb = type_of bod
        let! tm = mk_const("LET_END", [tb, aty])
        let! lend = mk_comb(tm, bod)
        let! lbod = list_mk_gabs(lefts, lend)
        let! tlb = type_of lbod
        let! (ty1, ty2) = dest_fun_ty tlb
        let! ltm = mk_const("LET", [ty1, aty; ty2, bty])
        return! list_mk_comb(ltm, lbod :: rights)
    }

(* ------------------------------------------------------------------------- *)
(* Useful function to create stylized arguments using numbers.               *)
(* ------------------------------------------------------------------------- *)

/// Make a list of terms with stylized variable names.
let make_args : _ -> _ -> _ -> Protected<term list> = 
    let rec margs n s avoid tys =
        choice {
        if List.isEmpty tys then
            return []
        else
            let! v = variant avoid (mk_var(s + (string n), hd tys))
            let! vs = margs (n + 1) s (v :: avoid) (tl tys)
            return v :: vs
        }
    fun s avoid tys ->
        if length tys = 1 then
            mk_var(s, hd tys)
            |> variant avoid
            |> Choice.map List.singleton
        else margs 0 s avoid tys

(* ------------------------------------------------------------------------- *)
(* Director strings down a term.                                             *)
(* ------------------------------------------------------------------------- *)

/// Returns a path to some subterm satisfying a predicate.
let find_path : _ -> _ -> Protected<string> = 
    let rec find_path p tm = 
        choice {
            if p tm then 
                return []
            elif is_abs tm then 
                let! tm1 = body tm
                let! bs = find_path p tm1
                return "b" :: bs
            else 
                return!
                    choice { 
                        let! tm1 = rand tm
                        let! rs = find_path p tm1
                        return "r" :: rs
                    }
                    |> Choice.bindError (function
                        | Failure _ -> 
                            choice {
                                let! tm1 = rator tm
                                let! ls = find_path p tm1
                                return "l" :: ls
                            }
                        | e -> Choice.error e)
        }

    fun p tm ->
        Choice.map implode (find_path p tm)

/// Find the subterm of a given term indicated by a path.
let follow_path : string -> term -> Protected<term> =
    let rec follow_path s tm =
        choice {
            match s with
            | [] -> return tm
            | "l" :: t ->
                let! tm1 = rator tm
                return! follow_path t tm1
            | "r" :: t ->
                let! tm1 = rand tm
                return! follow_path t tm1
            | _ :: t ->
                let! tm1 = body tm
                return! follow_path t tm1
        }

    fun s tm ->
        follow_path (explode s) tm
