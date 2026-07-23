From lstar Require Import automata.Moore Teacher.
From Transmogrifier Require Import compiler.moore transparency.mooreproofs.
From compcert Require Import AST Clight Ctypes Integers Values Coqlib.
From compcert Require Import ClightBigstep Events Globalenvs Memory.
From Stdlib Require Import ZArith Lia.

Module Type MooreLearner (s : Symbol) (O : Output) (L : MooreLanguage s O) (Tch : MooreTeacher s O L).
    Parameter learn : unit -> {state : Type & {m : L.M.t state | L.minimal m}}.
End MooreLearner.

Module CompileLearnedMoore (s : Symbol) (O : Output) (L : MooreLanguage s O)
                           (Tch : MooreTeacher s O L)
                           (Learner : MooreLearner s O L Tch).

Module M <: MooreType s O := L.M.

Module Correctness := Correctness s O M.
Import Correctness L M MC.

Definition learned : { St : Type & { m : M.t St | minimal m } } :=
    Learner.learn tt.

Definition LSt : Type := projT1 learned.
Definition learned_moore : L.M.t LSt := proj1_sig (projT2 learned).

Definition base : positive := 1.

(* The learned Moore machine has compiled successfully and is well-formed *)
Section correctness.
Variable p : Clight.program.
Variable m0 : mem.
Definition ge := ge p.
Variable state_eq_dec : forall (x y : LSt), {x = y} + {x <> y}.
Variable compile_ok :
    compile_program LSt learned_moore state_eq_dec base = Ok p.
Variable m0_ok :
    Genv.init_mem p = Some m0.
Variable states_ok :
    Z.of_nat (Datatypes.length (M.states LSt learned_moore)) < Int64.modulus.
Variable alphabet_ok :
    0 < Z.of_nat (Datatypes.length s.enum) < Int64.modulus.
Variable output_alphabet_ok :
    0 < Z.of_nat (length O.enum) < Int64.modulus.
Variable states_alphabet_ok :
    8 * (Z.of_nat (Datatypes.length (M.states LSt learned_moore)) *
         Z.of_nat (Datatypes.length s.enum)) < Ptrofs.modulus.

(* Running a compiled Moore machine on any string is equivalent
   to running its compiled form on the same string *)
Theorem run_equiv : forall w l b ofs,
  sym_indices w l ->
  word_in_mem m0 b ofs l ->
  0 <= ofs ->
  Z.of_nat (length w) < Int64.modulus ->
  ofs + 8 * Z.of_nat (length w) < Ptrofs.modulus ->
  exists r_idx,
    sidx LSt learned_moore state_eq_dec (M.run learned_moore w) = Some r_idx /\
    eval_funcall function_entry2 ge m0
      (compile_run LSt learned_moore state_eq_dec (alloc_idents base))
      [Vptr b (Ptrofs.repr ofs); Vlong (Int64.repr (Z.of_nat (length w)))] E0 m0
      (Vlong (Int64.repr r_idx)).
Proof.
    eauto using compile_run_correct.
Qed.

(* The output of learned_moore for a string w is the same as its compiled form *)
Theorem run_output_encodes : forall w l b ofs,
  sym_indices w l -> word_in_mem m0 b ofs l -> 0 <= ofs ->
  Z.of_nat (length w) < Int64.modulus ->
  ofs + 8 * Z.of_nat (length w) < Ptrofs.modulus ->
  exists r_idx o_idx,
    sidx LSt learned_moore state_eq_dec (M.run learned_moore w) = Some r_idx /\
    (* run(q0, w) returns r_idx *)
    eval_funcall function_entry2 ge m0
      (compile_run LSt learned_moore state_eq_dec (alloc_idents base))
      [Vptr b (Ptrofs.repr ofs); Vlong (Int64.repr (Z.of_nat (length w)))] E0 m0
      (Vlong (Int64.repr r_idx)) /\
    (* accept(r_idx) returns o_idx *)
    eval_funcall function_entry2 ge m0
      (compile_accept LSt learned_moore (alloc_idents base))
      [Vlong (Int64.repr r_idx)] E0 m0 (Vlong (Int64.repr o_idx)) /\
    (* o_idx is the O.enum index of the LANGUAGE's output on w *)
    nth_error O.enum (Z.to_nat o_idx) = Some (L.output_lang w).
Proof.
  intros w l b ofs Hsym Hword Hofs Hlen Hbound.
  destruct (run_equiv w l b ofs Hsym Hword Hofs Hlen Hbound)
    as (r_idx & Hrun & Hexec).
  (* the value accept returns is accept_entry on the reached state *)
  set (q := M.run learned_moore w) in *.
  exists r_idx, (accept_entry LSt learned_moore q).
  assert (Henc : encodes learned_moore)
    by (destruct (proj2_sig (projT2 learned)) as [He _]; exact He).
  split; [exact Hrun | split; [exact Hexec | split]].
  - eapply compile_accept_correct; eauto using
      states_ok, alphabet_ok, output_alphabet_ok,
      compile_ok, m0_ok, states_alphabet_ok.
  - unfold accept_entry.
    destruct (index_of_complete O.enum (M.output LSt learned_moore q) 0 O.eq_dec
                (O.t_enumerable _)) as (idx & Hidx).
    rewrite Hidx.
    pose proof (index_of_nth_error _ O.eq_dec O.enum
                  (M.output LSt learned_moore q) idx 0 Hidx) as Hnth.
    rewrite Z.sub_0_r in Hnth.
    replace (M.output LSt learned_moore q)
       with (L.output_lang w) in Hnth.
    + exact Hnth.
    + unfold q. rewrite <- (Henc w). reflexivity.
Qed.

End correctness.
End CompileLearnedMoore.
