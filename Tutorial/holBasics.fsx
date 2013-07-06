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
axioms();;                                                                          // the_axioms database doesn't change
definitions();;                                                                     // new definitions one, I, (o)
//  [|- one = (@x. T); |- I = (\x. x); |- (o) = (\f g x. f (g x));
//   |- COND = (\t t1 t2. @x. ((t <=> T) ==> x = t1) /\ ((t <=> F) ==> x = t2));
//   |- _FALSITY_ <=> F; |- (?!) = (\P. (?) P /\ (!x y. P x /\ P y ==> x = y));
//   |- (~) = (\p. p ==> F); |- F <=> (!p. p);
//   |- (\/) = (\p q. !r. (p ==> r) ==> (q ==> r) ==> r);
//   |- (?) = (\P. !q. (!x. P x ==> q) ==> q); |- (!) = (\P. P = (\x. T));
//   |- (==>) = (\p q. p /\ q <=> p);
//   |- (/\) = (\p q. (\f. f p q) = (\f. f T T)); |- T <=> (\p. p) = (\p. p)]


//* Canon Module *//
CONJ_ACI_RULE;; // forces canon module evaluation
// No Changes in internal databases status

//* Meson Module *//
ASM_MESON_TAC;; // forces meson module evaluation
// No Changes in internal databases status

//* Quot Module *//
lift_function;; // forces quot module evaluation
// No Changes in internal databases status




// -- Tying Examples -- //

mk_iff;;            // forces bool module evaluation
MK_CONJ;;           // forces drule module evaluation
_FALSITY_;;         // forces tactics module evaluation
ITAUT_TAC;;         // forces itab module evaluation: maybe not needd
mk_rewrites;;       // forces simp module evaluation
EQ_REFL;;           // forces theorems module evaluation
EXISTS_EQUATION;;   // forces ind_defs module evaluation
ETA_AX;;            // forces class module evaluation
o_DEF;;             // forces trivia module evaluation

parse_term @"~(p /\ q) <=> ~p \/ ~q";;
parse_term @"~(p \/ q) <=> ~p /\ ~q";;
parse_term @"~gate ==> (source <=> drain)";;

TAUT <| parse_term
     @"(~input_a ==> (internal <=> T)) /\
      (~input_b ==> (output <=> internal)) /\
      (input_a ==> (output <=> F)) /\
      (input_b ==> (output <=> F))
      ==> (output <=> ~(input_a \/ input_b))";;

TAUT <| parse_term
    @"(i1 /\ i2 <=> a) /\
    (i1 /\ i3 <=> b) /\
    (i2 /\ i3 <=> c) /\
    (i1 /\ c <=> d) /\
    (m /\ r <=> e) /\
    (m /\ w <=> f) /\
    (n /\ w <=> g) /\
    (p /\ w <=> h) /\
    (q /\ w <=> i) /\
    (s /\ x <=> j) /\
    (t /\ x <=> k) /\
    (v /\ x <=> l) /\
    (i1 \/ i2 <=> m) /\
    (i1 \/ i3 <=> n) /\
    (i1 \/ q <=> p) /\
    (i2 \/ i3 <=> q) /\
    (i3 \/ a <=> r) /\
    (a \/ w <=> s) /\
    (b \/ w <=> t) /\
    (d \/ h <=> u) /\
    (c \/ w <=> v) /\
    (~e <=> w) /\
    (~u <=> x) /\
    (i \/ l <=> o1) /\
    (g \/ k <=> o2) /\
    (f \/ j <=> o3)
    ==> (o1 <=> ~i1) /\ (o2 <=> ~i2) /\ (o3 <=> ~i3)";;

(* 4. Propositional logic *)

parse_term @"p \/ ~p";;
ASSUME <| parse_term @"p /\ q";;
