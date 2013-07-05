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

// Exception
parse_term @"˜(p /\ q) <=> ˜p \/ ˜q";;
parse_term @"˜(p \/ q) <=> ˜p /\ ˜q";;
parse_term @"˜gate ==> (source <=> drain)";;

TAUT <| parse_term
 "(˜input_a ==> (internal <=> T)) /\
  (˜input_b ==> (output <=> internal)) /\
  (input_a ==> (output <=> F)) /\
  (input_b ==> (output <=> F))
  ==> (output <=> ˜(input_a \/ input_b))";;

TAUT <| parse_term
 "(i1 /\ i2 <=> a) /\
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
(˜e <=> w) /\
(˜u <=> x) /\
(i \/ l <=> o1) /\
(g \/ k <=> o2) /\
(f \/ j <=> o3)
==> (o1 <=> ˜i1) /\ (o2 <=> ˜i2) /\ (o3 <=> ˜i3)";;

(* 4. Propositional logic *)

parse_term @"p \/ ~p";;
ASSUME <| parse_term @"p /\ q";;

parse_term @"x < 1 ==> p";;
//ARITH_RULE <| parse_term "x < y \/ y <= x";;

get_infix_status "==>";;
get_infix_status "-";;

parse_as_infix("<>",(12,"right"));;
parse_as_infix("+",(1,"left"));;

parse_term "x < x + 1";;

parse_as_infix("+",(16,"right"));;