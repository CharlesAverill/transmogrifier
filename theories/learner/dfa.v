From lstar Require Import automata.DFA Teacher.
From Transmogrifier Require Import compiler.dfa transparency.dfaproofs.
From compcert Require Import AST Clight Ctypes Integers Values Coqlib.
From compcert Require Import ClightBigstep Events Globalenvs Memory.
From Stdlib Require Import ZArith Lia.

Module Type DFALearner (s : Symbol) (L : RegularLanguage s) (Tch : DFATeacher s L).
    Parameter learn : unit -> {state : Type & {d : L.D.t state | L.minimal d}}.
End DFALearner.

Module CompileLearnedDFA (s : Symbol) (L : RegularLanguage s)
                         (Tch : DFATeacher s L)
                         (Learner : DFALearner s L Tch).

Module D <: DFAType s := L.D.

Module Correctness := Correctness s D.
Import Correctness DC L M.

Definition learned : { St : Type & { d : D.t St | minimal d } } :=
    Learner.learn tt.

Definition LSt : Type := projT1 learned.
Definition learned_dfa : L.D.t LSt := proj1_sig (projT2 learned).

Definition base : positive := 1.

Parameter p : Clight.program.
Parameter m0 : mem.
Definition ge := M.ge p.
Definition m := moore_of_dfa LSt learned_dfa.

(* The learned DFA has compiled successfully and is well-formed *)
Parameter state_eq_dec : forall (x y : LSt), {x = y} + {x <> y}.
Parameter compile_ok :
    compile_program LSt (moore_of_dfa LSt learned_dfa) state_eq_dec base = Ok p.
Parameter m0_ok :
    Genv.init_mem p = Some m0.
Parameter states_ok :
    Z.of_nat (Datatypes.length (Moore.states LSt m)) < Int64.modulus.
Parameter alphabet_ok :
    0 < Z.of_nat (Datatypes.length s.enum) < Int64.modulus.
Parameter states_alphabet_ok :
    8 * (Z.of_nat (Datatypes.length (Moore.states LSt m)) *
         Z.of_nat (Datatypes.length s.enum)) < Ptrofs.modulus.

(* Running a learned DFA on any string is equivalent
   to running its compiled form on the same string *)
Theorem run_equiv : forall w l b ofs,
  sym_indices w l ->
  word_in_mem m0 b ofs l ->
  0 <= ofs ->
  Z.of_nat (length w) < Int64.modulus ->
  ofs + 8 * Z.of_nat (length w) < Ptrofs.modulus ->
  exists r_idx,
    sidx LSt m state_eq_dec (D.run learned_dfa w) = Some r_idx /\
    eval_funcall function_entry2 ge m0
      (compile_run LSt m state_eq_dec (alloc_idents base))
      [Vptr b (Ptrofs.repr ofs); Vlong (Int64.repr (Z.of_nat (length w)))] E0 m0
      (Vlong (Int64.repr r_idx)).
Proof.
    intros. eapply compile_run_correct; eauto.
    apply states_ok.
    apply alphabet_ok.
    unfold Out.enum. simpl. now compute.
    apply compile_ok.
    apply m0_ok.
    apply states_alphabet_ok.
Qed.

End CompileLearnedDFA.
