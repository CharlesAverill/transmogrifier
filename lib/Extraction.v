From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNativeString.
From Stdlib Require Import NArith ZArith.
From compcert Require Import Csyntax.

From Transmogrifier.compiler Require Import dfa moore.

Extraction Language OCaml.

(* Linear let + beta reduction *)
Set Extraction Flag 1536.

Extraction Blacklist Int String List Nat Moore.

#[local] Set Warnings "-extraction-default-directory,-extraction-ambiguous-name".

From compcert Require Import Compiler.
 
Extract Constant Compiler.print_Clight => "PrintClight.print_if".

Separate Extraction DFACompiler MooreCompiler
    Pos Stdlib.ZArith.BinInt.Z Integers Floats Values Csyntax Clight.type_of_function BinNat.N.
