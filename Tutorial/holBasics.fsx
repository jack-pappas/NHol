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

constants();;
//val it : (string * hol_type) list =
//  [("=",
//    Tyapp ("fun",[Tyvar "A"; Tyapp ("fun",[Tyvar "A"; Tyapp ("bool",[])])]))]

mk_iff;; //bool

constants();;
//val it : (string * hol_type) list =
//  [("?!", (A->bool)->bool); ("~", bool->bool); ("F", bool);
//   ("\/", bool->bool->bool); ("?", (A->bool)->bool); ("!", (A->bool)->bool);
//   ("==>", bool->bool->bool); ("/\", bool->bool->bool); ("T", bool);
//   ("=", A->A->bool)]

parse_term @"~(p /\ q) <=> ~p \/ ~q";;