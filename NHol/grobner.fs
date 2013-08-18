(*

Copyright 1998 University of Cambridge
Copyright 1998-2007 John Harrison
Copyright 2013 Jack Pappas, Eric Taucher, Domenico Masini

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
/// Groebner basis procedure for most semirings.
module NHol.grobner

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Num

open ExtCore.Control
open ExtCore.Control.Collections

open NHol
open system
open lib
open fusion
open fusion.Hol_kernel
open basics
open nets
open printer
open preterm
open parser
open equal
open bool
open drule
open tactics
open itab
open simp
open theorems
open ind_defs
open ``class``
open trivia
open canon
open meson
open quot
//open pair
open nums
open recursion
open arith
//open wf
open calc_num
open normalizer
#endif

logger.Trace("Entering grobner.fs")


(* ------------------------------------------------------------------------- *)
(* Type for recording history, i.e. how a polynomial was obtained.           *)
(* ------------------------------------------------------------------------- *)

type history =
 | Start of int
 | Mmul of (num * (int list)) * history
 | Add of history * history;;

(* ------------------------------------------------------------------------- *)
(* Overall function; everything else is local.                               *)
(* ------------------------------------------------------------------------- *)

/// Returns a pair giving a ring proof procedure and an ideal membership routine.
let RING_AND_IDEAL_CONV = 

  (* ----------------------------------------------------------------------- *)
  (* Monomial ordering.                                                      *)
  (* ----------------------------------------------------------------------- *)
  
  let morder_lt = 
      let rec lexorder l1 l2 = 
          match (l1, l2) with
          | [], [] -> false
          | (x1 :: o1, x2 :: o2) -> x1 > x2 || x1 = x2 && lexorder o1 o2
          | _ -> failwith "morder: inconsistent monomial lengths"
      fun m1 m2 -> 
          let n1 = itlist (+) m1 0
          let n2 = itlist (+) m2 0
          n1 < n2 || n1 = n2 && lexorder m1 m2
  
  (* ----------------------------------------------------------------------- *)
  (* Arithmetic on canonical polynomials.                                    *)
  (* ----------------------------------------------------------------------- *)
  
  let grob_neg = map (fun (c, m) -> (minus_num c, m))
  
  let rec grob_add l1 l2 = 
      match (l1, l2) with
      | ([], l2) -> l2
      | (l1, []) -> l1
      | ((c1, m1) :: o1, (c2, m2) :: o2) -> 
          if m1 = m2 then 
              let c = c1 + c2
              let rest = grob_add o1 o2
              if c = num_0 then rest
              else (c, m1) :: rest
          else if morder_lt m2 m1 then (c1, m1) :: (grob_add o1 l2)
          else (c2, m2) :: (grob_add l1 o2)
  
  let grob_sub l1 l2 = grob_add l1 (grob_neg l2)
  
  let grob_mmul (c1, m1) (c2, m2) = (c1 * c2, map2 (+) m1 m2)
  
  let rec grob_cmul cm pol = map (grob_mmul cm) pol
  
  let rec grob_mul l1 l2 = 
      match l1 with
      | [] -> []
      | (h1 :: t1) -> grob_add (grob_cmul h1 l2) (grob_mul t1 l2)
  
  let grob_inv l = 
    choice {
      match l with
      | [c, vs] when forall (fun x -> x = 0) vs -> 
          if c = num_0 then 
              return! Choice.failwith "grob_inv: division by zero"
          else 
              return [num_1 / c, vs]
      | _ -> 
           return! Choice.failwith "grob_inv: non-constant divisor polynomial"
    }
  
  let grob_div l1 l2 = 
    choice {
      match l2 with
      | [c, l] when forall (fun x -> x = 0) l -> 
          if c = num_0 then 
              return! Choice.failwith "grob_div: division by zero"
          else 
            return grob_cmul (num_1 / c, l) l1
      | _ -> 
          return! Choice.failwith "grob_div: non-constant divisor polynomial"
    }
  
  let rec grob_pow vars l n = 
    choice {
      if n < 0 then 
          return! Choice.failwith "grob_pow: negative power"
      else if n = 0 then 
          return [num_1, map (fun v -> 0) vars]
      else
          let! r = grob_pow vars l (n - 1)
          return grob_mul l r
    }
  
  (* ----------------------------------------------------------------------- *)
  (* Monomial division operation.                                            *)
  (* ----------------------------------------------------------------------- *)
  
  let mdiv (c1, m1) (c2, m2) = 
    choice {
        let! ns = Choice.List.map2 (fun n1 n2 -> 
           if n1 < n2 then Choice.failwith "mdiv"
           else Choice.result (n1 - n2)) m1 m2
        return (c1 / c2, ns)
    }
  
  (* ----------------------------------------------------------------------- *)
  (* Lowest common multiple of two monomials.                                *)
  (* ----------------------------------------------------------------------- *)
  
  let mlcm (c1, m1) (c2, m2) = (num_1, map2 max m1 m2)
  
  (* ----------------------------------------------------------------------- *)
  (* Reduce monomial cm by polynomial pol, returning replacement for cm.     *)
  (* ----------------------------------------------------------------------- *)
  
  let reduce1 cm (pol, hpol) = 
    choice {
      match pol with
      | [] -> 
          return! Choice.failwith "reduce1"
      | cm1 :: cms -> 
          return!
              choice { 
                  let! (c, m) = mdiv cm cm1
                  return (grob_cmul (minus_num c, m) cms, Mmul((minus_num c, m), hpol))
              }
              |> Choice.mapError (fun e -> nestedFailure e "reduce1")
    }
  
  (* ----------------------------------------------------------------------- *)
  (* Try this for all polynomials in a basis.                                *)
  (* ----------------------------------------------------------------------- *)
  
  let reduceb cm basis =
      tryfind (fun p -> Choice.toOption <| reduce1 cm p) basis 
      |> Option.toChoiceWithError "tryfind"
  
  (* ----------------------------------------------------------------------- *)
  (* Reduction of a polynomial (always picking largest monomial possible).   *)
  (* ----------------------------------------------------------------------- *)
  
  let rec reduce basis (pol, hist) = 
    choice {
      match pol with
      | [] -> 
        return (pol, hist)
      | cm :: ptl -> 
        return!
          choice { 
              let! q, hnew = reduceb cm basis
              return! reduce basis (grob_add q ptl, Add(hnew, hist))
          }
          |> Choice.bindError (fun _ -> 
              choice {
                  let! q, hist' = reduce basis (ptl, hist)
                  return cm :: q, hist'
              })
    }
  
  (* ----------------------------------------------------------------------- *)
  (* Check for orthogonality w.r.t. LCM.                                     *)
  (* ----------------------------------------------------------------------- *)
  
  let orthogonal l p1 p2 = 
    snd l = snd(grob_mmul (hd p1) (hd p2))
  
  (* ----------------------------------------------------------------------- *)
  (* Compute S-polynomial of two polynomials.                                *)
  (* ----------------------------------------------------------------------- *)
  
  let spoly cm ph1 ph2 = 
    choice {
      match (ph1, ph2) with
      | ([], h), p -> 
        return ([], h)
      | p, ([], h) -> 
        return ([], h)
      | (cm1 :: ptl1, his1), (cm2 :: ptl2, his2) -> 
        let! n1 = mdiv cm cm1
        let! n2 = mdiv cm cm2
        let! n3 = mdiv (minus_num(fst cm), snd cm) cm2
        return
          (grob_sub (grob_cmul n1 ptl1) (grob_cmul n2 ptl2), 
           Add(Mmul(n1, his1), Mmul(n3, his2)))
    }

  (* ----------------------------------------------------------------------- *)
  (* Make a polynomial monic.                                                *)
  (* ----------------------------------------------------------------------- *)
  
  let monic(pol, hist) = 
      if pol = [] then (pol, hist)
      else 
          let c', m' = hd pol
          (map (fun (c, m) -> (c / c', m)) pol, Mmul((num_1 / c', map (K 0) m'), hist))
  
  (* ----------------------------------------------------------------------- *)
  (* The most popular heuristic is to order critical pairs by LCM monomial.  *)
  (* ----------------------------------------------------------------------- *)
  
  let forder ((c1,m1),_) ((c2,m2),_) = morder_lt m1 m2
  
  (* ----------------------------------------------------------------------- *)
  (* Stupid stuff forced on us by lack of equality test on num type.         *)
  (* ----------------------------------------------------------------------- *)
  
  let rec poly_lt p q = 
      match (p, q) with
      | p, [] -> false
      | [], q -> true
      | (c1, m1) :: o1, (c2, m2) :: o2 -> 
         c1 < c2 || c1 = c2 && (m1 < m2 || m1 = m2 && poly_lt o1 o2)
  
  let align((p, hp), (q, hq)) = 
      if poly_lt p q then ((p, hp), (q, hq))
      else ((q, hq), (p, hp))
  
  let poly_eq p1 p2 =
    forall2 (fun (c1,m1) (c2,m2) -> c1 = c2 && m1 = m2) p1 p2
  
  let memx ((p1, h1), (p2, h2)) ppairs = 
      not(exists (fun ((q1, _), (q2, _)) -> poly_eq p1 q1 && poly_eq p2 q2) ppairs)
  
  (* ----------------------------------------------------------------------- *)
  (* Buchberger's second criterion.                                          *)
  (* ----------------------------------------------------------------------- *)
  
  let criterion2 basis (lcm, ((p1, h1), (p2, h2))) opairs = 
      exists 
          (fun g -> 
          not(poly_eq (fst g) p1) && not(poly_eq (fst g) p2) && Choice.isResult <| (mdiv lcm) (hd(fst g)) 
          && not(memx (align(g, (p1, h1))) (map snd opairs)) && not(memx (align(g, (p2, h2))) (map snd opairs))) basis
  
  (* ----------------------------------------------------------------------- *)
  (* Test for hitting constant polynomial.                                   *)
  (* ----------------------------------------------------------------------- *)
  
  let constant_poly p =
    length p = 1 && forall ((=) 0) (snd(hd p))
  
  (* ----------------------------------------------------------------------- *)
  (* Grobner basis algorithm.                                                *)
  (* ----------------------------------------------------------------------- *)
  
  let rec grobner_basis basis pairs = 
    choice {
      Format.print_string(string(length basis) + " basis elements and " + string(length pairs) + " critical pairs")
      Format.print_newline()
      match pairs with
      | [] -> 
          return basis
      | (l, (p1, p2)) :: opairs -> 
          let! ns1 = spoly l p1 p2
          let! ns2 = reduce basis ns1
          let (sp, hist as sph) = monic ns2
          if sp = [] || criterion2 basis (l, (p1, p2)) opairs then 
              return! grobner_basis basis opairs
          else if constant_poly sp then 
              return! grobner_basis (sph :: basis) []
          else 
              let rawcps = map (fun p -> mlcm (hd(fst p)) (hd sp), align(p, sph)) basis
              let newcps = filter (fun (l, (p, q)) -> not(orthogonal l (fst p) (fst q))) rawcps
              return! grobner_basis (sph :: basis) (merge forder opairs (mergesort forder newcps))
    }
  
  (* ----------------------------------------------------------------------- *)
  (* Interreduce initial polynomials.                                        *)
  (* ----------------------------------------------------------------------- *)
  
  let rec grobner_interreduce rpols ipols = 
    choice {
      match ipols with
      | [] -> 
          return map monic (rev rpols)
      | p :: ps -> 
          let! p' = reduce (rpols @ ps) p
          if fst p' = [] then 
              return! grobner_interreduce rpols ps
          else 
              return! grobner_interreduce (p' :: rpols) ps
    }
  
  (* ----------------------------------------------------------------------- *)
  (* Overall function.                                                       *)
  (* ----------------------------------------------------------------------- *)
  
  let grobner pols = 
    choice {
      let npols = map2 (fun p n -> p, Start n) pols (0 -- (length pols - 1))
      let phists = filter (fun (p, _) -> p <> []) npols
      let! bas = grobner_interreduce [] (map monic phists)
      let prs0 = allpairs (fun x y -> x, y) bas bas
      let prs1 = filter (fun ((x, _), (y, _)) -> poly_lt x y) prs0
      let prs2 = map (fun (p, q) -> mlcm (hd(fst p)) (hd(fst q)), (p, q)) prs1
      let prs3 = filter (fun (l, (p, q)) -> not(orthogonal l (fst p) (fst q))) prs2
      return! grobner_basis bas (mergesort forder prs3)
    }
  
  (* ----------------------------------------------------------------------- *)
  (* Get proof of contradiction from Grobner basis.                          *)
  (* ----------------------------------------------------------------------- *)
  
  let grobner_refute pols = 
    choice {
      let! gb = grobner pols
      let! (_, history) = 
        find (fun (p, h) -> length p = 1 && forall ((=) 0) (snd(hd p))) gb
        |> Option.toChoiceWithError "find"

      return history
    }
  
  (* ----------------------------------------------------------------------- *)
  (* Turn proof into a certificate as sum of multipliers.                    *)
  (*                                                                         *)
  (* In principle this is very inefficient: in a heavily shared proof it may *)
  (* make the same calculation many times. Could add a cache or something.   *)
  (* ----------------------------------------------------------------------- *)
  
  let rec resolve_proof vars prf = 
      match prf with
      | Start(-1) -> []
      | Start m -> [m, [num_1, map (K 0) vars]]
      | Mmul(pol, lin) -> 
          let lis = resolve_proof vars lin
          map (fun (n, p) -> n, grob_cmul pol p) lis
      | Add(lin1, lin2) -> 
          let lis1 = resolve_proof vars lin1
          let lis2 = resolve_proof vars lin2
          let dom = setify(union (map fst lis1) (map fst lis2))
          map (fun n -> 
              let a = defaultArg (assoc n lis1) []
              let b = defaultArg (assoc n lis2) []
              n, grob_add a b) dom
  
  (* ----------------------------------------------------------------------- *)
  (* Run the procedure and produce Weak Nullstellensatz certificate.         *)
  (* ----------------------------------------------------------------------- *)
  
  let grobner_weak vars pols = 
    choice {
      let! history = grobner_refute pols
      let cert = resolve_proof vars history
      let l = itlist (itlist(lcm_num << denominator << fst) << snd) cert (num_1)
      return l, map (fun (i, p) -> i, map (fun (d, m) -> (l * d, m)) p) cert
    }
  
  (* ----------------------------------------------------------------------- *)
  (* Prove polynomial is in ideal generated by others, using Grobner basis.  *)
  (* ----------------------------------------------------------------------- *)
  
  let grobner_ideal vars pols pol = 
    choice {
      let! ns = grobner pols
      let! pol', h = reduce ns (grob_neg pol, Start(-1))
      if pol' <> [] then 
          return! Choice.failwith "grobner_ideal: not in the ideal"
      else 
          return resolve_proof vars h
    }
  
  (* ----------------------------------------------------------------------- *)
  (* Produce Strong Nullstellensatz certificate for a power of pol.          *)
  (* ----------------------------------------------------------------------- *)
  
  let grobner_strong vars pols pol = 
    choice {
      if pol = [] then 
          return 1, num_1, []
      else
          let! var = Choice.map concl TRUTH
          let vars' = var :: vars
          let grob_z = [num_1, 1 :: (map (fun x -> 0) vars)]
          let grob_1 = [num_1, (map (fun x -> 0) vars')]
          let augment = map(fun (c, m) -> (c, 0 :: m))
          let pols' = map augment pols
          let pol' = augment pol
          let allpols = (grob_sub (grob_mul grob_z pol') grob_1) :: pols'
          let! l, cert = grobner_weak vars' allpols
          let d = itlist (itlist(max << hd << snd) << snd) cert 0
          let transform_monomial(c, m) = 
                choice {
                    let! ns = grob_pow vars pol (d - hd m)
                    return grob_cmul (c, tl m) ns
                }

          let transform_polynomial q = itlist (grob_add << Choice.get << transform_monomial) q []

          let cert' = map (fun (c, q) -> c - 1, transform_polynomial q) (filter (fun (k, _) -> k <> 0) cert)

          return d, l, cert'
    }
    
  (* ----------------------------------------------------------------------- *)
  (* Overall parametrized universal procedure for (semi)rings.               *)
  (* We return an IDEAL_CONV and the actual ring prover.                     *)
  (* ----------------------------------------------------------------------- *)
  
  let pth_step = 
      prove((parse_term @"!(add:A->A->A) (mul:A->A->A) (n0:A).
            (!x. mul n0 x = n0) /\
            (!x y z. (add x y = add x z) <=> (y = z)) /\
            (!w x y z. (add (mul w y) (mul x z) = add (mul w z) (mul x y)) <=>
                       (w = x) \/ (y = z))
            ==> (!a b c d. ~(a = b) /\ ~(c = d) <=>
                           ~(add (mul a c) (mul b d) =
                             add (mul a d) (mul b c))) /\
                (!n a b c d. ~(n = n0)
                             ==> (a = b) /\ ~(c = d)
                                 ==> ~(add a (mul n c) = add b (mul n d)))"),
            REPEAT GEN_TAC
            |> THEN <| STRIP_TAC
            |> THEN <| ASM_REWRITE_TAC [GSYM DE_MORGAN_THM]
            |> THEN <| REPEAT GEN_TAC
            |> THEN <| DISCH_TAC
            |> THEN <| STRIP_TAC
            |> THEN <| FIRST_X_ASSUM(MP_TAC << SPECL [(parse_term @"n0:A");
                                                      (parse_term @"n:A");
                                                      (parse_term @"d:A");
                                                      (parse_term @"c:A")])
            |> THEN <| ONCE_REWRITE_TAC [GSYM CONTRAPOS_THM]
            |> THEN <| ASM_SIMP_TAC [])
  
  let FINAL_RULE = MATCH_MP(TAUT (parse_term @"(p ==> F) ==> (~q = p) ==> q"))

  let false_tm = (parse_term @"F")
  
  let rec refute_disj rfn tm = 
      match tm with
      | Comb(Comb(Const("\\/", _), l), r) -> 
          DISJ_CASES (ASSUME tm) (refute_disj rfn l) (refute_disj rfn r)
      | _ -> rfn tm
  
  fun (ring_dest_const,ring_mk_const,RING_EQ_CONV, ring_neg_tm,ring_add_tm,ring_sub_tm, ring_inv_tm,ring_mul_tm,ring_div_tm,ring_pow_tm, RING_INTEGRAL,RABINOWITSCH_THM,RING_NORMALIZE_CONV) ->
    let rabinowitsch_conv tm =
        choice {
            let! th = RABINOWITSCH_THM
            if is_iff(snd(strip_forall(concl th))) then 
                return! GEN_REWRITE_CONV ONCE_DEPTH_CONV [RABINOWITSCH_THM] tm
            else 
                return! ALL_CONV tm
        }

    let INITIAL_CONV = 
        TOP_DEPTH_CONV BETA_CONV
        |> THENC <| PRESIMP_CONV
        |> THENC <| CONDS_ELIM_CONV
        |> THENC <| NNF_CONV
        |> THENC <| rabinowitsch_conv
        |> THENC <| GEN_REWRITE_CONV REDEPTH_CONV 
                       [AND_FORALL_THM; LEFT_AND_FORALL_THM; RIGHT_AND_FORALL_THM; LEFT_OR_FORALL_THM; RIGHT_OR_FORALL_THM; 
                        OR_EXISTS_THM; LEFT_OR_EXISTS_THM; RIGHT_OR_EXISTS_THM; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM]
    
    let ring_dest_neg t = 
      choice {
        let! l, r = dest_comb t
        if l = ring_neg_tm then 
            return r
        else 
            return! Choice.failwith "ring_dest_neg"
      }
    
    let ring_dest_inv t = 
      choice {
        let! l, r = dest_comb t
        if l = ring_inv_tm then 
            return r
        else 
            return! Choice.failwith "ring_dest_inv"
      }
    
    let ring_dest_add = dest_binop ring_add_tm
    let ring_mk_add = mk_binop ring_add_tm
    let ring_dest_sub = dest_binop ring_sub_tm
    let ring_dest_mul = dest_binop ring_mul_tm
    let ring_mk_mul = mk_binop ring_mul_tm
    let ring_dest_div = dest_binop ring_div_tm
    let ring_dest_pow = dest_binop ring_pow_tm
    let ring_mk_pow = mk_binop ring_pow_tm

    let rec grobvars tm acc = 
      choice {
        if Choice.isResult <| ring_dest_const tm then 
            return acc
        else if Choice.isResult <| ring_dest_neg tm then
            let! tm1 = rand tm
            return! grobvars tm1 acc
        else
            let! tm1 = rand tm
            if Choice.isResult <| ring_dest_pow tm && is_numeral tm1 then 
                let! tm2 = lhand tm
                return! grobvars tm2 acc
            else if Choice.isResult <| ring_dest_add tm || Choice.isResult <| ring_dest_sub tm || Choice.isResult <| ring_dest_mul tm then 
                let! tm2 = lhand tm
                let! ns = grobvars tm1 acc
                return! grobvars tm2 ns
            else if Choice.isResult <| ring_dest_inv tm then 
                let! gvs = grobvars tm1 []
                if gvs = [] then 
                    return acc
                else 
                    return tm :: acc
            else if Choice.isResult <| ring_dest_div tm then 
                let! tm2 = lhand tm
                let! lvs = grobvars tm2 acc
                let! gvs = grobvars tm1 []
                if gvs = [] then 
                    return lvs
                else 
                    return tm :: acc
            else 
                return tm :: acc
      }
  
    let rec grobify_term vars tm = 
        choice { 
            if not(mem tm vars) then 
                return! Choice.failwith ""
            else 
                return [num_1, map (fun i -> 
                                 if i = tm then 1
                                 else 0) vars]
        }
        |> Choice.bindError (fun _ ->
            choice { 
                let! x = ring_dest_const tm
                if x = num_0 then 
                    return []
                else 
                    return [x, map (fun v -> 0) vars]
            }
            |> Choice.bindError (fun _ ->
                choice { 
                    let! ns1 = ring_dest_neg tm
                    let! ns2 = grobify_term vars ns1
                    return grob_neg ns2
                }
                |> Choice.bindError (fun _ ->
                    choice { 
                        let! ns1 = ring_dest_neg tm
                        let! ns2 = grobify_term vars ns1
                        return! grob_inv ns2
                    }
                    |> Choice.bindError (fun _ ->
                        choice { 
                            let! l, r = ring_dest_add tm
                            let! ns1 = grobify_term vars l
                            let! ns2 = grobify_term vars r
                            return grob_add ns1 ns2
                        }
                        |> Choice.bindError (fun _ ->
                            choice { 
                                let! l, r = ring_dest_sub tm
                                let! ns1 = grobify_term vars l
                                let! ns2 = grobify_term vars r
                                return grob_sub ns1 ns2
                            }
                            |> Choice.bindError (fun _ ->
                                choice { 
                                    let! l, r = ring_dest_mul tm
                                    let! ns1 = grobify_term vars l
                                    let! ns2 = grobify_term vars r
                                    return grob_mul ns1 ns2
                                }
                                |> Choice.bindError (fun _ ->
                                    choice { 
                                        let! l, r = ring_dest_div tm
                                        let! ns1 = grobify_term vars l
                                        let! ns2 = grobify_term vars r
                                        return! grob_div ns1 ns2
                                    }
                                    |> Choice.bindError (fun _ ->
                                        choice { 
                                            let! l, r = ring_dest_pow tm
                                            let! ns1 = grobify_term vars l
                                            let! n2 = dest_small_numeral r
                                            return! grob_pow vars ns1 n2
                                        }
                                        |> Choice.mapError (fun e ->
                                            nestedFailure e "grobify_term: unknown or invalid term")))))))))
  
    let grobify_equation vars tm = 
      choice {
        let! l, r = dest_eq tm
        let! l' = grobify_term vars l
        let! r' = grobify_term vars r
        return grob_sub l' r'
      }

    let grobify_equations tm = 
      choice {
        let cjs = conjuncts tm
        let! rawvars = Choice.List.foldBack (fun eq acc -> 
                        choice {
                            let! tm0 = lhand eq
                            let! tm1 = rand eq
                            let! tm2 = grobvars tm1 acc
                            return! grobvars tm0 tm2
                        }) cjs []
        let vars = sort (fun x y -> x < y) (setify rawvars)
        let! cjs' = Choice.List.map (grobify_equation vars) cjs
        return vars, cjs'
      }
    
    let holify_polynomial = 
        let holify_varpow(v, n) = 
          choice {
            if n = 1 then 
                return v
            else 
                let! n' = mk_small_numeral n
                return! ring_mk_pow v n'
          }

        let holify_monomial vars (c, m) = 
          choice {
            let! xps = Choice.List.map holify_varpow (filter (fun (_, n) -> n <> 0) (zip vars m))
            let! xp = ring_mk_const c
            return! Choice.List.reduceBack ring_mk_mul (xp :: xps)
          }

        let holify_polynomial vars p = 
          choice {
            if p = [] then 
                return! ring_mk_const num_0
            else
                let! ns = Choice.List.map (holify_monomial vars) p 
                return! Choice.List.reduceBack ring_mk_add ns
          }

        holify_polynomial
    
    let (pth_idom, pth_ine) = CONJ_PAIR(MATCH_MP pth_step RING_INTEGRAL)

    let IDOM_RULE = CONV_RULE(REWR_CONV pth_idom)

    let PROVE_NZ n = 
        choice {
            let! l = ring_mk_const n
            let! r = ring_mk_const num_0
            let! tm = mk_eq(l, r)
            return! EQF_ELIM(RING_EQ_CONV tm)
        }
    
    let NOT_EQ_01 = PROVE_NZ(num_1)
    let INE_RULE n = MATCH_MP(MATCH_MP pth_ine (PROVE_NZ n))
    let MK_ADD th1 th2 = MK_COMB(AP_TERM ring_add_tm th1, th2)
    
    let execute_proof vars eths prf = 
        let x, th1 = SPEC_VAR(CONJUNCT1(CONJUNCT2 RING_INTEGRAL)) |> ExtCore.Choice.bindOrRaise
        let y, th2 = SPEC_VAR (Choice.result th1) |> ExtCore.Choice.bindOrRaise
        let z, th3 = SPEC_VAR (Choice.result th2) |> ExtCore.Choice.bindOrRaise

        let SUB_EQ_RULE = 
            fun th ->
                choice {
                    let! tm = mk_comb(ring_neg_tm, z)
                    return! GEN_REWRITE_RULE I [SYM(INST [tm, x] (Choice.result th3))] th
                }

        let initpols = map (CONV_RULE(BINOP_CONV RING_NORMALIZE_CONV) << SUB_EQ_RULE) eths
        let ADD_RULE th1 th2 = CONV_RULE (BINOP_CONV RING_NORMALIZE_CONV) (MK_COMB(AP_TERM ring_add_tm th1, th2))

        let MUL_RULE vars m th = 
            choice {
                let! n = holify_polynomial vars [m]
                let! tm = mk_comb(ring_mul_tm, n)
                return! CONV_RULE (BINOP_CONV RING_NORMALIZE_CONV) (AP_TERM tm th)
            }

        let execache = ref []

        let memoize prf x = 
            (execache := (prf, x) :: (!execache))
            x
        
        let rec assoceq a l = 
          choice {
            match l with
            | [] -> 
                return! Choice.failwith "assoceq"
            | (x, y) :: t -> 
                if x == a then 
                    return y
                else 
                    return! assoceq a t
          }

        let rec run_proof vars prf = 
            assoceq prf (!execache)
            |> Choice.fill ( 
                 match prf with
                 | Start m -> el m initpols
                 | Add(p1, p2) -> memoize prf (ADD_RULE (run_proof vars p1) (run_proof vars p2))
                 | Mmul(m, p2) -> memoize prf (MUL_RULE vars m (run_proof vars p2)))

        let th = run_proof vars prf
        execache := []
        CONV_RULE RING_EQ_CONV th
  
    let REFUTE tm = 
      choice {
        if tm = false_tm then 
            return! ASSUME tm
        else 
            let! nths0, eths0 = Choice.List.partition (Choice.map (is_neg << concl)) (CONJUNCTS(ASSUME tm))
            let! nths = Choice.List.filter (Choice.map is_eq << Choice.bind rand << Choice.map concl) nths0
            let! eths = Choice.List.filter (Choice.map (is_eq << concl)) eths0
            if eths = [] then 
                let th1 = end_itlist (fun th1 th2 -> IDOM_RULE(CONJ th1 th2)) nths
                let th2 = CONV_RULE (RAND_CONV(BINOP_CONV RING_NORMALIZE_CONV)) th1
                let! tm1 = Choice.bind (rand << concl) th2
                let! l, r = dest_eq tm1
                return! EQ_MP (EQF_INTRO th2) (REFL l)
            else if nths = [] && not(is_var ring_neg_tm) then 
                let! tms0 = Choice.List.map (Choice.map concl) eths
                let! tm1 = list_mk_conj tms0
                let! vars, pols = grobify_equations tm1
                let! ns = grobner_refute pols
                return! execute_proof vars eths ns
            else 
                let! vars, l, cert, noteqth = 
                  choice {
                    if nths = [] then 
                        let! tms0 = Choice.List.map (Choice.map concl) eths
                        let! tm1 = list_mk_conj tms0
                        let! vars, pols = grobify_equations tm1
                        let! l, cert = grobner_weak vars pols
                        return vars, l, cert, NOT_EQ_01
                    else 
                        let! nth = end_itlist (fun th1 th2 -> IDOM_RULE(CONJ th1 th2)) nths
                        let! tm1 = rand(concl nth)
                        let! tms2 = Choice.List.map (Choice.map concl) eths
                        let! tm3 = list_mk_conj (tm1 :: tms2)
                        let! tms = grobify_equations tm1
                        match tms with
                        | (vars, pol :: pols) -> 
                            let! deg, l, cert = grobner_strong vars pols pol
                            let th1 = CONV_RULE (RAND_CONV(BINOP_CONV RING_NORMALIZE_CONV)) (Choice.result nth)
                            let th2 = funpow deg (IDOM_RULE << CONJ th1) NOT_EQ_01
                            return vars, l, cert, th2
                        | _ -> 
                            return! Choice.failwith "REFUTE: Unhandled case."
                  }

                Format.print_string("Translating certificate to HOL inferences")
                Format.print_newline()
                let cert_pos = map (fun (i, p) -> i, filter (fun (c, m) -> c > num_0) p) cert
                let cert_neg = 
                    map (fun (i, p) -> i, map (fun (c, m) -> minus_num c, m) (filter (fun (c, m) -> c < num_0) p)) cert
                let! herts_pos = Choice.List.map (fun (i, p) -> holify_polynomial vars p |> Choice.map (fun h -> i, h)) cert_pos
                let! herts_neg = Choice.List.map (fun (i, p) -> holify_polynomial vars p |> Choice.map (fun h -> i, h)) cert_neg
               
                let thm_fn pols = 
                    choice {
                        if pols = [] then 
                            let! tm1 = ring_mk_const num_0
                            return! REFL tm1
                        else 
                            let! tms = Choice.List.map (fun (i, p) -> 
                                        choice {
                                            let! tm = mk_comb(ring_mul_tm, p)
                                            return AP_TERM tm (el i eths)
                                        }) pols
                            return! end_itlist MK_ADD tms
                    }

                let th1 = thm_fn herts_pos
                let th2 = thm_fn herts_neg
                let th3 = CONJ (MK_ADD (SYM th1) th2) noteqth
                let th4 = CONV_RULE (RAND_CONV(BINOP_CONV RING_NORMALIZE_CONV)) (INE_RULE l th3)
                let! tm = Choice.bind (rand << concl) th4
                let! l, r = dest_eq tm
                return! EQ_MP (EQF_INTRO th4) (REFL l)
      }

    let RING tm = 
      choice {
        let avs = frees tm
        let! tm' = list_mk_forall(avs, tm)
        let! tm0 = mk_neg tm'
        let th1 = INITIAL_CONV tm0
        let! tm1 = Choice.bind (rand << concl) th1
        let evs, bod = strip_exists tm1
        if is_forall bod then 
            return! Choice.failwith "RING: non-universal formula"
        else 
            let th1a = WEAK_DNF_CONV bod
            let! boda = Choice.bind (rand << concl) th1a
            let th2a = refute_disj REFUTE boda
            let th2b = TRANS th1a (EQF_INTRO(NOT_INTRO(DISCH boda th2a)))
            let th2 = UNDISCH(NOT_ELIM(EQF_ELIM th2b))
            let th3 = itlist SIMPLE_CHOOSE evs th2
            return! SPECL avs (MATCH_MP (FINAL_RULE(DISCH_ALL th3)) th1)
      }

    let ideal tms tm = 
      choice {
        let! rawvars = Choice.List.foldBack (fun x acc -> grobvars x acc) (tm :: tms) []
        let vars = sort (fun x y -> x < y) (setify rawvars)
        let! pols = Choice.List.map (grobify_term vars) tms
        let! pol = grobify_term vars tm
        let! cert = grobner_ideal vars pols pol
        return! 
          Choice.List.map (fun n -> 
            choice {
                let p = assocd n cert []
                return! holify_polynomial vars p
            }) (0 -- (length pols - 1))
      }

    RING,ideal;;

(* ----------------------------------------------------------------------- *)
(* Separate out the cases.                                                 *)
(* ----------------------------------------------------------------------- *)

/// Generic ring procedure.
let RING parms = fst(RING_AND_IDEAL_CONV parms);;

/// Generic procedure to compute cofactors for ideal membership.
let ideal_cofactors parms = snd(RING_AND_IDEAL_CONV parms);;

(* ------------------------------------------------------------------------- *)
(* Simplify a natural number assertion to eliminate conditionals, DIV, MOD,  *)
(* PRE, cutoff subtraction, EVEN and ODD. Try to do it in a way that makes   *)
(* new quantifiers universal. At the moment we don't split "<=>" which would *)
(* make this quantifier selection work there too; better to do NNF first if  *)
(* you care. This also applies to EVEN and ODD.                              *)
(* ------------------------------------------------------------------------- *)

/// Eliminates predecessor, cutoff subtraction, even and odd, division and modulus.
let NUM_SIMPLIFY_CONV = 
    let pre_tm = (parse_term @"PRE")
    let div_tm = (parse_term @"(DIV):num->num->num")
    let mod_tm = (parse_term @"(MOD):num->num->num")
    let p_tm = (parse_term @"P:num->bool")
    let n_tm = (parse_term @"n:num")
    let m_tm = (parse_term @"m:num")
    let q_tm = (parse_term @"P:num->num->bool")
    let a_tm = (parse_term @"a:num")
    let b_tm = (parse_term @"b:num")
    // It's safe to use Choice.get here
    let is_pre tm = is_comb tm && Choice.get <| rator tm = pre_tm
    let is_sub = is_binop(parse_term @"(-):num->num->num")
    let is_divmod = 
        let is_div = is_binop div_tm
        let is_mod = is_binop mod_tm
        fun tm -> is_div tm || is_mod tm
    let contains_quantifier = 
        Choice.isResult << find_term(fun t -> is_forall t || is_exists t || is_uexists t)
    let BETA2_CONV = RATOR_CONV BETA_CONV
                     |> THENC <| BETA_CONV
    let PRE_ELIM_THM'' = CONV_RULE (RAND_CONV NNF_CONV) PRE_ELIM_THM
    let SUB_ELIM_THM'' = CONV_RULE (RAND_CONV NNF_CONV) SUB_ELIM_THM
    let DIVMOD_ELIM_THM'' = CONV_RULE (RAND_CONV NNF_CONV) DIVMOD_ELIM_THM

    let pth_evenodd = 
        prove((parse_term @"(EVEN(x) <=> (!y. ~(x = SUC(2 * y)))) /\
       (ODD(x) <=> (!y. ~(x = 2 * y))) /\
       (~EVEN(x) <=> (!y. ~(x = 2 * y))) /\
       (~ODD(x) <=> (!y. ~(x = SUC(2 * y))))"),
              REWRITE_TAC [GSYM NOT_EXISTS_THM;
                           GSYM EVEN_EXISTS;
                           GSYM ODD_EXISTS]
              |> THEN <| REWRITE_TAC [NOT_EVEN; NOT_ODD])

    let rec NUM_MULTIPLY_CONV pos tm = 
      choice {
        if is_forall tm || is_exists tm || is_uexists tm then 
            return! BINDER_CONV (NUM_MULTIPLY_CONV pos) tm
        elif is_imp tm && contains_quantifier tm then 
            return! COMB2_CONV (RAND_CONV(NUM_MULTIPLY_CONV(not pos))) (NUM_MULTIPLY_CONV pos) tm
        elif (is_conj tm || is_disj tm || is_iff tm) && contains_quantifier tm then 
            return! BINOP_CONV (NUM_MULTIPLY_CONV pos) tm
        elif is_neg tm && not pos && contains_quantifier tm then 
            return! RAND_CONV (NUM_MULTIPLY_CONV(not pos)) tm
        else 
          return!
            choice { 
                let! t = find_term (fun t -> is_pre t && Choice.get <| free_in t tm) tm
                let! ty = type_of t
                let v = genvar ty
                let! tm1 = subst [v, t] tm
                let! p = mk_abs(v, tm1)
                let th0 = 
                    if pos then PRE_ELIM_THM''
                    else PRE_ELIM_THM'
                let! tm2 = rand t
                let th1 = INST [p, p_tm; tm2, n_tm] th0
                let th2 = CONV_RULE (COMB2_CONV (RAND_CONV BETA_CONV) (BINDER_CONV(RAND_CONV BETA_CONV))) th1
                return! CONV_RULE (RAND_CONV(NUM_MULTIPLY_CONV pos)) th2
            }
            |> Choice.bindError (fun _ ->
                choice { 
                    let! t = find_term (fun t -> is_sub t && Choice.get <| free_in t tm) tm
                    let! ty = type_of t
                    let v = genvar ty
                    let! tm1 = subst [v, t] tm
                    let! p = mk_abs(v, tm1)
                    let th0 = 
                        if pos then SUB_ELIM_THM''
                        else SUB_ELIM_THM'
                    let! tm2 = lhand t
                    let! tm3 = rand t
                    let th1 = INST [p, p_tm; tm2, a_tm; tm3, b_tm] th0
                    let th2 = CONV_RULE (COMB2_CONV (RAND_CONV BETA_CONV) (BINDER_CONV(RAND_CONV BETA_CONV))) th1
                    return! CONV_RULE (RAND_CONV(NUM_MULTIPLY_CONV pos)) th2
                }
                |> Choice.bindError (fun _ ->
                    choice { 
                        let! t = find_term (fun t -> is_divmod t && Choice.get <| free_in t tm) tm
                        let! x = lhand t
                        let! y = rand t
                        let! tm1 = mk_comb(div_tm, x)
                        let! dtm = mk_comb(tm1, y)
                        let! tm2 = mk_comb(mod_tm, x)
                        let! mtm = mk_comb(tm2, y)
                        let! vd = Choice.map genvar (type_of dtm)
                        let! vm = Choice.map genvar (type_of mtm)
                        let! tm3 = subst [vd, dtm; vm, mtm] tm
                        let! p = list_mk_abs([vd; vm], tm3)
                        let th0 = 
                            if pos then DIVMOD_ELIM_THM''
                            else DIVMOD_ELIM_THM'
                        let th1 = 
                            INST [p, q_tm;
                                  x, m_tm;
                                  y, n_tm] th0
                        let th2 = 
                            CONV_RULE (COMB2_CONV (RAND_CONV BETA2_CONV) (funpow 2 BINDER_CONV (RAND_CONV BETA2_CONV))) 
                                th1
                        return! CONV_RULE (RAND_CONV(NUM_MULTIPLY_CONV pos)) th2
                    }
                    |> Choice.bindError (fun _ -> REFL tm)))
      }

    NUM_REDUCE_CONV
    |> THENC <| CONDS_CELIM_CONV
    |> THENC <| NNF_CONV
    |> THENC <| NUM_MULTIPLY_CONV true
    |> THENC <| NUM_REDUCE_CONV
    |> THENC <| GEN_REWRITE_CONV ONCE_DEPTH_CONV [pth_evenodd]

(* ----------------------------------------------------------------------- *)
(* Natural number version of ring procedure with this normalization.       *)
(* ----------------------------------------------------------------------- *)

/// Ring decision procedure instantiated to natural numbers.
let NUM_RING = 
    let NUM_INTEGRAL_LEMMA = 
        prove((parse_term @"(w = x + d) /\ (y = z + e) ==> ((w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))"), 
              DISCH_THEN(fun th -> REWRITE_TAC [th])
              |> THEN <| REWRITE_TAC [LEFT_ADD_DISTRIB;
                                      RIGHT_ADD_DISTRIB;
                                      GSYM ADD_ASSOC]
              |> THEN <| ONCE_REWRITE_TAC [AC ADD_AC (parse_term @"a + b + c + d + e = a + c + e + b + d")]
              |> THEN <| REWRITE_TAC [EQ_ADD_LCANCEL; EQ_ADD_LCANCEL_0; MULT_EQ_0])

    let NUM_INTEGRAL = 
        prove((parse_term @"(!x. 0 * x = 0) /\
     (!x y z. (x + y = x + z) <=> (y = z)) /\
     (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))"),
              REWRITE_TAC [MULT_CLAUSES; EQ_ADD_LCANCEL]
              |> THEN <| REPEAT GEN_TAC
              |> THEN <| DISJ_CASES_TAC(SPECL [(parse_term @"w:num");
                                               (parse_term @"x:num")] LE_CASES)
              |> THEN <| DISJ_CASES_TAC(SPECL [(parse_term @"y:num");
                                               (parse_term @"z:num")] LE_CASES)
              |> THEN <| REPEAT(FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC << REWRITE_RULE [LE_EXISTS]))
              |> THEN <| ASM_MESON_TAC [NUM_INTEGRAL_LEMMA; ADD_SYM; MULT_SYM])

    let rawring = 
        RING
            (dest_numeral, mk_numeral, NUM_EQ_CONV, genvar bool_ty, 
             (parse_term @"(+):num->num->num"), genvar bool_ty, genvar bool_ty, (parse_term @"(*):num->num->num"), 
             genvar bool_ty, (parse_term @"(EXP):num->num->num"), NUM_INTEGRAL, TRUTH, NUM_NORMALIZE_CONV)

    let initconv = NUM_SIMPLIFY_CONV
                   |> THENC <| GEN_REWRITE_CONV DEPTH_CONV [ADD1]

    let t_tm = (parse_term @"T")

    fun tm -> 
      choice {
        let th = initconv tm
        let! tm1 = Choice.bind (rand << concl) th
        if tm1 = t_tm then 
            return! th
        else 
            return! EQ_MP (SYM th) (rawring tm1)
      }
