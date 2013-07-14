(*

Copyright 2013 Anh-Dung Phan, Domenico Masini

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

#r "FSharp.Compatibility.OCaml.0.1.10/lib/net40/FSharp.Compatibility.OCaml.dll"
#r "FSharp.Compatibility.OCaml.Format.0.1.10/lib/net40/FSharp.Compatibility.OCaml.Format.dll"
#r "FSharp.Compatibility.OCaml.System.0.1.10/lib/net40/FSharp.Compatibility.OCaml.System.dll"
#r "ExtCore.0.8.29/lib/net40/ExtCore.dll"

#I "./../NHol"
#r @"bin/Debug/NHol.dll"

#nowarn "25"
#nowarn "40"
#nowarn "49"
#nowarn "62"

open FSharp.Compatibility.OCaml;;
open FSharp.Compatibility.OCaml.Num;;

open NHol
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
open NHol.pair //pair module has to be checked
open NHol.nums
open NHol.recursion
open NHol.arith   
open NHol.wf //
open NHol.calc_num
open NHol.normalizer
open NHol.grobner
open NHol.ind_types //
open NHol.lists
open NHol.realax   
open NHol.calc_int 
open NHol.realarith
open NHol.real  //  
//open NHol.calc_rat 
//open NHol.int     
//open NHol.sets     
//open NHol.iterate
//open NHol.cart     
//open NHol.define   

fsi.AddPrinter string_of_type;;
fsi.AddPrinter string_of_term;;
fsi.AddPrinter string_of_thm;;

BETA_RULE;;                 // forces equal module evaluation: maybe not needed
mk_iff;;                    // forces bool module evaluation
MK_CONJ;;                   // forces drule module evaluation
_FALSITY_;;                 // forces tactics module evaluation
ITAUT_TAC;;                 // forces itab module evaluation: maybe not needd
mk_rewrites;;               // forces simp module evaluation
EQ_REFL;;                   // forces theorems module evaluation
EXISTS_EQUATION;;           // forces ind_defs module evaluation
ETA_AX;;                    // forces class module evaluation
o_DEF;;                     // forces trivia module evaluation
CONJ_ACI_RULE;;             // forces canon module evaluation
ASM_MESON_TAC;;             // forces meson module evaluation
lift_function;;             // forces quot module evaluation
LET_DEF;;                   // forces pair module evaluation: pair module has to be checked
ONE_ONE;;                   // forces num module evaluation
PRE;;                       // forces arith module evaluation
WF_EQ;;                     // forces wf module evaluation
ARITH_ZERO;;                // forces calc_num module evaluation
SEMIRING_NORMALIZERS_CONV;; // forces normalizer module evaluation
RING_AND_IDEAL_CONV;;       // forces grobner module evaluation

INJ_INVERSE2;;      //ind_types
LIST_INDUCT_TAC;;   // lists
dist;;              //relax
mk_realintconst;;   //calc_int
REAL_LTE_TOTAL;;    //realarith
REAL_OF_NUM_LT;;    //real various

#load "calc_rat.fs" 
open NHol.calc_rat 

//DECIMAL;;           //calc_rat first issue at line 120
//integer;;           //int
//IN;;                //sets
//FINITE_NUMSEG;;     //iterate
//dimindex;;          //cart
//CASEWISE_DEF;;      //define
