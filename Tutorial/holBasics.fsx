(*

Copyright 2013 Domenico D. D. Masini

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

#load "hol.fsx"

open NHol.lib
open NHol.fusion
open NHol.basics
open NHol.nets
open NHol.printer
open NHol.preterm
open NHol.parser
open NHol.equal
open NHol.bool
open NHol.drule
open NHol.tactics
open NHol.itab
open NHol.simp
open NHol.theorems
open NHol.ind_defs
open NHol.``class``
open NHol.trivia
open NHol.canon
open NHol.meson
open NHol.quot
//open NHol.pair
open NHol.nums
open NHol.recursion
open NHol.arith   
//open NHol.wf
open NHol.calc_num
open NHol.normalizer
open NHol.grobner

//* Initial databases status *//

types();;                                                                           // internal database the_type_constants
//val it : (string * int) list = [("bool", 0); ("fun", 2)]

constants();;                                                                       // internal database the_term_constants
//val it : (string * hol_type) list =
//  [("=",
//    Tyapp ("fun",[Tyvar "A"; Tyapp ("fun",[Tyvar "A"; Tyapp ("bool",[])])]))]

axioms();;                                                                          // internal database the_axioms
//val it : thm list = []

definitions();;                                                                     // internal database the_definitions
//val it : thm list = []

!the_implicit_types;;                                                               // internal database the_implicit_types
//val it : (string * hol_type) list = []

type_abbrevs();;                                                                    // internal database the_type_abbreviations
//val it : (string * hol_type) list = []

//monotonicity_theorems;;       only in ind_defs
//the_inductive_definitions;;   only in ind_defs
//inductive_type_store;;        only after class

//* Bool Module *//

mk_iff;; // forces bool module evaluation

types();;                                                                           // the_type_constants database doesn't change
constants();;                                                                       // new boolean constants
//  [("?!", (A->bool)->bool); ("~", bool->bool); ("F", bool);
//   ("\/", bool->bool->bool); ("?", (A->bool)->bool); ("!", (A->bool)->bool);
//   ("==>", bool->bool->bool); ("/\", bool->bool->bool); ("T", bool);
//   ("=", A->A->bool)]
axioms();;                                                                          // the_axioms database doesn't change
definitions();;                                                                     // the_definitions doesn't change
!the_implicit_types;;                                                               // no change
type_abbrevs();;                                                                    // no change

// after population of constants this parses
parse_term @"~(p /\ q) <=> ~p \/ ~q";;


//* Drule Module *//

MK_CONJ;; // forces drule module evaluation

types();;                                                                           // the_type_constants database doesn't change
constants();;                                                                       // the_term_constants database doesn't change
axioms();;                                                                          // the_axioms database doesn't change
definitions();;                                                                     // new boolean definitions
//  [|- (?!) = (\P. (?) P /\ (!x y. P x /\ P y ==> x = y));
//   |- (~) = (\p. p ==> F); |- F <=> (!p. p);
//   |- (\/) = (\p q. !r. (p ==> r) ==> (q ==> r) ==> r);
//   |- (?) = (\P. !q. (!x. P x ==> q) ==> q); |- (!) = (\P. P = (\x. T));
//   |- (==>) = (\p q. p /\ q <=> p);
//   |- (/\) = (\p q. (\f. f p q) = (\f. f T T)); |- T <=> (\p. p) = (\p. p)]
!the_implicit_types;;                                                               // no change
type_abbrevs();;                                                                    // no change


//* Tactitcs Module *//

_FALSITY_;; // forces tactics module evaluation

types();;                                                                           // the_type_constants database doesn't change
constants();;                                                                       // new constant _FALSITY_
//  [("_FALSITY_", bool); ("?!", (A->bool)->bool); ("~", bool->bool);
//   ("F", bool); ("\/", bool->bool->bool); ("?", (A->bool)->bool);
//   ("!", (A->bool)->bool); ("==>", bool->bool->bool); ("/\", bool->bool->bool);
//   ("T", bool); ("=", A->A->bool)]
axioms();;                                                                          // the_axioms database doesn't change
definitions();;                                                                     // new _FALSITY_ definition
//  [|- _FALSITY_ <=> F; |- (?!) = (\P. (?) P /\ (!x y. P x /\ P y ==> x = y));
//   |- (~) = (\p. p ==> F); |- F <=> (!p. p);
//   |- (\/) = (\p q. !r. (p ==> r) ==> (q ==> r) ==> r);
//   |- (?) = (\P. !q. (!x. P x ==> q) ==> q); |- (!) = (\P. P = (\x. T));
//   |- (==>) = (\p q. p /\ q <=> p);
//   |- (/\) = (\p q. (\f. f p q) = (\f. f T T)); |- T <=> (\p. p) = (\p. p)]
!the_implicit_types;;                                                               // no change
type_abbrevs();;                                                                    // no change

//* Itab Module *//
ITAUT_TAC;; // forces itab module evaluation
// No Changes in internal databases status

//* Simp Module *//
mk_rewrites;; // forces simp module evaluation
// No Changes in internal databases status: to be checked better

//* Theorems Module *//
EQ_REFL;; // forces theorems module evaluation
// No Changes in internal databases status: to be checked better

//* ind_defs Module *//
EXISTS_EQUATION;; // forces ind_defs module evaluation
!the_implicit_types;;                                                               // no change
type_abbrevs();;                                                                    // no change
// No Changes in internal databases status: to be checked better

// Class Module *//

ETA_AX;;    // forces class module evaluation

types();;                                                                           // the_type_constants database doesn't change
constants();;                                                                       // new constants COND, @
//  [("COND", bool->A->A->A); ("@", (A->bool)->A);
//   ("_FALSITY_", bool); ("?!", (A->bool)->bool); ("~", bool->bool);
//   ("F", bool); ("\/", bool->bool->bool); ("?", (A->bool)->bool);
//   ("!", (A->bool)->bool); ("==>", bool->bool->bool); ("/\", bool->bool->bool);
//   ("T", bool); ("=", A->A->bool)]
axioms();;                                                                          // new axioms: ETA, SELECT
//  [|- !P x. P x ==> P ((@) P); |- !t. (\x. t x) = t]
definitions();;                                                                     // new COND definition
//  [|- COND = (\t t1 t2. @x. ((t <=> T) ==> x = t1) /\ ((t <=> F) ==> x = t2));
//   |- _FALSITY_ <=> F; |- (?!) = (\P. (?) P /\ (!x y. P x /\ P y ==> x = y));
//   |- (~) = (\p. p ==> F); |- F <=> (!p. p);
//   |- (\/) = (\p q. !r. (p ==> r) ==> (q ==> r) ==> r);
//   |- (?) = (\P. !q. (!x. P x ==> q) ==> q); |- (!) = (\P. P = (\x. T));
//   |- (==>) = (\p q. p /\ q <=> p);
//   |- (/\) = (\p q. (\f. f p q) = (\f. f T T)); |- T <=> (\p. p) = (\p. p)]

// Trivia Module *//

o_DEF;; // forces trivia module evaluation

types();;                                                                           // new type 1
//  [("1", 0); ("bool", 0); ("fun", 2)]
constants();;                                                                       // new constants one, one_REP, one_ABS, I, o
//  [("one", 1); ("one_REP", 1->bool); ("one_ABS", bool->1); ("I", A->A);
//   ("o", (B->C)->(A->B)->A->C); ("COND", bool->A->A->A); ("@", (A->bool)->A);
//   ("_FALSITY_", bool); ("?!", (A->bool)->bool); ("~", bool->bool);
//   ("F", bool); ("\/", bool->bool->bool); ("?", (A->bool)->bool);
//   ("!", (A->bool)->bool); ("==>", bool->bool->bool); ("/\", bool->bool->bool);
//   ("T", bool); ("=", A->A->bool)]

//ocaml

//[("one", `:1`); ("one_REP", `:1->bool`); ("one_ABS", `:bool->1`);
//   ("I", `:A->A`); ("o", `:(B->C)->(A->B)->A->C`);
//   ("COND", `:bool->A->A->A`); ("@", `:(A->bool)->A`);
//   ("_FALSITY_", `:bool`); ("?!", `:(A->bool)->bool`); ("~", `:bool->bool`);
//   ("F", `:bool`); ("\\/", `:bool->bool->bool`); ("?", `:(A->bool)->bool`);
//   ("!", `:(A->bool)->bool`); ("==>", `:bool->bool->bool`);
//   ("/\\", `:bool->bool->bool`); ("T", `:bool`); ("=", `:A->A->bool`)]


axioms();;                                                                          // the_axioms database doesn't change
//  [|- !P x. P x ==> P ((@) P); |- !t. (\x. t x) = t]

//ocaml

//[|- !P x. P x ==> P ((@) P); |- !t. (\x. t x) = t]

definitions();;                                                                     // new definitions one, I, (o)
//  [|- one = (@x. T); |- I = (\x. x); |- (o) = (\f g x. f (g x));
//   |- COND = (\t t1 t2. @x. ((t <=> T) ==> x = t1) /\ ((t <=> F) ==> x = t2));
//   |- _FALSITY_ <=> F; |- (?!) = (\P. (?) P /\ (!x y. P x /\ P y ==> x = y));
//   |- (~) = (\p. p ==> F); |- F <=> (!p. p);
//   |- (\/) = (\p q. !r. (p ==> r) ==> (q ==> r) ==> r);
//   |- (?) = (\P. !q. (!x. P x ==> q) ==> q); |- (!) = (\P. P = (\x. T));
//   |- (==>) = (\p q. p /\ q <=> p);
//   |- (/\) = (\p q. (\f. f p q) = (\f. f T T)); |- T <=> (\p. p) = (\p. p)]

//ocaml

//[|- one = (@x. T); |- I = (\x. x); |- (o) = (\f g x. f (g x));
//   |- COND = (\t t1 t2. @x. ((t <=> T) ==> x = t1) /\ ((t <=> F) ==> x = t2));
//   |- _FALSITY_ <=> F; |- (?!) = (\P. (?) P /\ (!x y. P x /\ P y ==> x = y));
//   |- (~) = (\p. p ==> F); |- F <=> (!p. p);
//   |- (\/) = (\p q. !r. (p ==> r) ==> (q ==> r) ==> r);
//   |- (?) = (\P. !q. (!x. P x ==> q) ==> q); |- (!) = (\P. P = (\x. T));
//   |- (==>) = (\p q. p /\ q <=> p);
//   |- (/\) = (\p q. (\f. f p q) = (\f. f T T)); |- T <=> (\p. p) = (\p. p)]

!the_implicit_types;;                                                               // internal database the_implicit_types
//val it : (string * hol_type) list = []

type_abbrevs();;                                                                    // internal database the_type_abbreviations
//val it : (string * hol_type) list = []

//monotonicity_theorems;;       only in ind_defs
//{contents =
//    [|- (A ==> B) /\ (C ==> D) ==> (if b then A else C) ==> (if b then B else D);
//     |- (A ==> B) /\ (C ==> D) ==> A /\ C ==> B /\ D;
//     |- (A ==> B) /\ (C ==> D) ==> A \/ C ==> B \/ D;
//     |- (B ==> A) /\ (C ==> D) ==> (A ==> C) ==> B ==> D;
//     |- (B ==> A) ==> ~A ==> ~B;
//     |- (!x. P x ==> Q x) ==> (?x. P x) ==> (?x. Q x);
//     |- (!x. P x ==> Q x) ==> (!x. P x) ==> (!x. Q x)];}

// ocaml

//{contents =
//    [|- (A ==> B) /\ (C ==> D)
//        ==> (if b then A else C)
//        ==> (if b then B else D);
//     |- (A ==> B) /\ (C ==> D) ==> A /\ C ==> B /\ D;
//     |- (A ==> B) /\ (C ==> D) ==> A \/ C ==> B \/ D;
//     |- (B ==> A) /\ (C ==> D) ==> (A ==> C) ==> B ==> D;
//     |- (B ==> A) ==> ~A ==> ~B;
//     |- (!x. P x ==> Q x) ==> (?x. P x) ==> (?x. Q x);
//     |- (!x. P x ==> Q x) ==> (!x. P x) ==> (!x. Q x)]}


//the_inductive_definitions;;   only in ind_defs

//inductive_type_store;;        only after class
//{contents =
//    [("1", (1, |- !P. P one ==> (!x. P x), |- !e. ?fn. fn one = e));
//     ("bool",
//      (2, |- !P. P F /\ P T ==> (!x. P x), |- !a b. ?f. f F = a /\ f T = b))];}

// ocaml 

//val it : (string * (int * thm * thm)) list ref =
//  {contents =
//    [("1", (1, |- !P. P one ==> (!x. P x), |- !e. ?fn. fn one = e));
//     ("bool",
//      (2, |- !P. P F /\ P T ==> (!x. P x), |- !a b. ?f. f F = a /\ f T = b))]}

//* Canon Module *//
CONJ_ACI_RULE;; // forces canon module evaluation
// No Changes in internal databases status: but maybe other changes

//* Meson Module *//
ASM_MESON_TAC;; // forces meson module evaluation
// No Changes in internal databases status: but maybe other changes

//* Quot Module *//
lift_function;; // forces quot module evaluation
// No Changes in internal databases status: but maybe other changes

//* Pair Module *//

//LET_DEF;; // forces pair module evaluation: TO BE CHECKED because there is an unsolved goal TAC_PROOF

types();;                                                                           // new type prod
//  [("prod", 2); ("1", 0); ("bool", 0); ("fun", 2)]
constants();;                                                                       // lots of new constants
//  [("PASSOC", ((A#B)#C->D)->A#B#C->D); ("UNCURRY", (A->B->C)->A#B->C);
//   ("CURRY", (A#B->C)->A->B->C); ("SND", A#B->B); ("FST", A#B->A);
//   (",", A->B->A#B); ("REP_prod", A#B->A->B->bool);
//   ("ABS_prod", (A->B->bool)->A#B); ("mk_pair", A->B->A->B->bool);
//   ("_FUNCTION", (?28823->?28826->bool)->?28823->?28826);
//   ("_MATCH", ?28801->(?28801->?28804->bool)->?28804);
//   ("_GUARDED_PATTERN", bool->bool->bool->bool);
//   ("_UNGUARDED_PATTERN", bool->bool->bool);
//   ("_SEQPATTERN",
//    (?28759->?28756->bool)->(?28759->?28756->bool)->?28759->?28756->bool);
//   ("GEQ", A->A->bool); ("GABS", (A->bool)->A); ("LET_END", A->A);
//   ("LET", (A->B)->A->B); ("one", 1); ("one_REP", 1->bool);
//   ("one_ABS", bool->1); ("I", A->A); ("o", (B->C)->(A->B)->A->C);
//   ("COND", bool->A->A->A); ("@", (A->bool)->A); ("_FALSITY_", bool);
//   ("?!", (A->bool)->bool); ("~", bool->bool); ("F", bool);
//   ("\/", bool->bool->bool); ("?", (A->bool)->bool); ("!", (A->bool)->bool);
//   ("==>", bool->bool->bool); ("/\", bool->bool->bool); ("T", bool);
//   ("=", A->A->bool)]

// ocaml

//[("PASSOC", `:((A#B)#C->D)->A#B#C->D`); ("UNCURRY", `:(A->B->C)->A#B->C`);
//   ("CURRY", `:(A#B->C)->A->B->C`); ("SND", `:A#B->B`); ("FST", `:A#B->A`);
//   (",", `:A->B->A#B`); ("REP_prod", `:A#B->A->B->bool`);
//   ("ABS_prod", `:(A->B->bool)->A#B`); ("mk_pair", `:A->B->A->B->bool`);
//   ("_FUNCTION", `:(?4069->?4073->bool)->?4069->?4073`);
//   ("_MATCH", `:?4047->(?4047->?4051->bool)->?4051`);
//   ("_GUARDED_PATTERN", `:bool->bool->bool->bool`);
//   ("_UNGUARDED_PATTERN", `:bool->bool->bool`);
//   ("_SEQPATTERN",
//    `:(?4005->?4002->bool)->(?4005->?4002->bool)->?4005->?4002->bool`);
//   ("GEQ", `:A->A->bool`); ("GABS", `:(A->bool)->A`); ("LET_END", `:A->A`);
//   ("LET", `:(A->B)->A->B`); ("one", `:1`); ("one_REP", `:1->bool`);
//   ("one_ABS", `:bool->1`); ("I", `:A->A`); ("o", `:(B->C)->(A->B)->A->C`);
//   ("COND", `:bool->A->A->A`); ("@", `:(A->bool)->A`);
//   ("_FALSITY_", `:bool`); ("?!", `:(A->bool)->bool`); ("~", `:bool->bool`);
//   ("F", `:bool`); ("\\/", `:bool->bool->bool`); ("?", `:(A->bool)->bool`);
//   ("!", `:(A->bool)->bool`); ("==>", `:bool->bool->bool`);
//   ("/\\", `:bool->bool->bool`); ("T", `:bool`); ("=", `:A->A->bool`)]

axioms();;                                                                          // no new axioms
//  [|- !P x. P x ==> P ((@) P); |- !t. (\x. t x) = t]

// ocaml

//[|- !P x. P x ==> P ((@) P); |- !t. (\x. t x) = t]

definitions();;                                                                     // lots of new definitions
//  [|- PASSOC =
//   (\_1099 _1100. _1099 ((FST _1100,FST (SND _1100)),SND (SND _1100)));
//   |- UNCURRY = (\_1082 _1083. _1082 (FST _1083) (SND _1083));
//   |- CURRY = (\_1061 _1062 _1063. _1061 (_1062,_1063));
//   |- SND = (\p. @y. ?x. p = x,y); |- FST = (\p. @x. ?y. p = x,y);
//   |- (,) = (\x y. ABS_prod (mk_pair x y));
//   |- mk_pair = (\x y a b. a = x /\ b = y);
//   |- _FUNCTION = (\r x. if (?!) (r x) then (@) (r x) else @z. F);
//   |- _MATCH = (\e r. if (?!) (r e) then (@) (r e) else @z. F);
//   |- _GUARDED_PATTERN = (\p g r. p /\ g /\ r);
//   |- _UNGUARDED_PATTERN = (\p r. p /\ r);
//   |- _SEQPATTERN = (\r s x. if ?y. r x y then r x else s x);
//   |- GEQ = (\a b. a = b); |- GABS = (\P. (@) P); |- LET_END = (\t. t);
//   |- LET = (\f x. f x); |- one = (@x. T); |- I = (\x. x);
//   |- (o) = (\f g x. f (g x));
//   |- COND = (\t t1 t2. @x. ((t <=> T) ==> x = t1) /\ ((t <=> F) ==> x = t2));
//   |- _FALSITY_ <=> F; |- (?!) = (\P. (?) P /\ (!x y. P x /\ P y ==> x = y));
//   |- (~) = (\p. p ==> F); |- F <=> (!p. p);
//   |- (\/) = (\p q. !r. (p ==> r) ==> (q ==> r) ==> r);
//   |- (?) = (\P. !q. (!x. P x ==> q) ==> q); |- (!) = (\P. P = (\x. T));
//   |- (==>) = (\p q. p /\ q <=> p);
//   |- (/\) = (\p q. (\f. f p q) = (\f. f T T)); |- T <=> (\p. p) = (\p. p)]

// ocaml

//[|- PASSOC =
//      (\_1099 _1100. _1099 ((FST _1100,FST (SND _1100)),SND (SND _1100)));
//   |- UNCURRY = (\_1082 _1083. _1082 (FST _1083) (SND _1083));
//   |- CURRY = (\_1061 _1062 _1063. _1061 (_1062,_1063));
//   |- SND = (\p. @y. ?x. p = x,y); |- FST = (\p. @x. ?y. p = x,y);
//   |- (,) = (\x y. ABS_prod (mk_pair x y));
//   |- mk_pair = (\x y a b. a = x /\ b = y);
//   |- _FUNCTION = (\r x. if (?!) (r x) then (@) (r x) else @z. F);
//   |- _MATCH = (\e r. if (?!) (r e) then (@) (r e) else @z. F);
//   |- _GUARDED_PATTERN = (\p g r. p /\ g /\ r);
//   |- _UNGUARDED_PATTERN = (\p r. p /\ r);
//   |- _SEQPATTERN = (\r s x. if ?y. r x y then r x else s x);
//   |- GEQ = (\a b. a = b); |- GABS = (\P. (@) P); |- LET_END = (\t. t);
//   |- LET = (\f x. f x); |- one = (@x. T); |- I = (\x. x);
//   |- (o) = (\f g x. f (g x));
//   |- COND = (\t t1 t2. @x. ((t <=> T) ==> x = t1) /\ ((t <=> F) ==> x = t2));
//   |- _FALSITY_ <=> F; |- (?!) = (\P. (?) P /\ (!x y. P x /\ P y ==> x = y));
//   |- (~) = (\p. p ==> F); |- F <=> (!p. p);
//   |- (\/) = (\p q. !r. (p ==> r) ==> (q ==> r) ==> r);
//   |- (?) = (\P. !q. (!x. P x ==> q) ==> q); |- (!) = (\P. P = (\x. T));
//   |- (==>) = (\p q. p /\ q <=> p);
//   |- (/\) = (\p q. (\f. f p q) = (\f. f T T)); |- T <=> (\p. p) = (\p. p)]

//* Num Module *//

ONE_ONE;; // forces num module evaluation

parse_term(@"x + 1");;

PRE;; //arith: error on EXP_ZERO

ARITH_ZERO;; //calc_num

SEMIRING_NORMALIZERS_CONV;; //normalizer

RING_AND_IDEAL_CONV;; //grobner


