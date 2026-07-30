From lstar Require Import automata.DFA automata.NFA.
From compcert Require Import AST Clight Ctypes Integers Values Coqlib.
From compcert Require Import ClightBigstep Events Globalenvs Memory.
From Transmogrifier.compiler Require Import dfa nfa moore.
From Transmogrifier.transparency Require Import dfaproofs.
From Stdlib Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

(** Correctness of the NFA -> Clight compiler *)

Module Correctness (s : Symbol) (NFA : NFAType s) (DFA : DFAType s) (Moore : MooreType s Out).

Module D := dfaproofs.Correctness s DFA Moore.

Module NC := NFACompiler s NFA DFA Moore.

Import D.DC NC NC.N2D.
Import D.M.MC.

Section correctness.
Variable state : Type.
Variable nfa : NFA.t state.
Variable state_eq_dec : forall (x y : state), {x = y} + {x <> y}.
Definition list_state_eq_dec := N2D.list_state_eq_dec state_eq_dec.

Notation d := (to_dfa state_eq_dec nfa).
Notation m := (D.moore_of_dfa (list state) d).

(** Well-formedness: the state and symbol enumerations fit in [tlong] *)
Variable states_bounded : Z.of_nat (length nfa.(NFA.states _)) < Int64.modulus.
Variable syms_bounded   : 0 < Z.of_nat (length s.enum) < Int64.modulus.

Variable base : ident.
Variable p : Clight.program.
Variable Hp : NC.compile_program nfa state_eq_dec base = Ok p.

Definition ge : genv := D.ge p.
Definition ids := D.ids base.

Variable m0 : mem.
Variable Hinit : Genv.init_mem p = Some m0.

Variable table_bounded :
  0 < 8 * (Z.of_nat (length (powerset nfa.(NFA.states _))) * Z.of_nat (length s.enum)) < Ptrofs.modulus.

Definition sidx (q : list state) : option Z := D.sidx (list state) d list_state_eq_dec q.
Definition symidx (a : s.t) : option Z := D.symidx a.

Definition sym_indices (w : list s.t) (l : list Z) : Prop := D.sym_indices w l.
Definition word_in_mem (mm : mem) (b : block) (ofs : Z) (l : list Z) : Prop :=
  D.word_in_mem mm b ofs l.

Lemma sidx_run : forall w, exists li, sidx (DFA.run d w) = Some li.
Proof. intros. apply D.sidx_run. Qed.

Lemma symidx_total : forall a, exists i, symidx a = Some i.
Proof. apply D.symidx_total. Qed.

Lemma q0_index_correct :
  sidx d.(DFA.initial _) = Some (q0_index (list state) m list_state_eq_dec).
Proof. apply D.q0_index_correct. Qed.

Lemma compile_delta_correct : forall q sym q_idx s_idx next_idx,
  sidx q = Some q_idx ->
  symidx sym = Some s_idx ->
  sidx (d.(DFA.transition _) q sym) = Some next_idx ->
  eval_funcall function_entry2 ge m0
    (compile_delta (list state) m ids)
    [Vlong (Int64.repr q_idx); Vlong (Int64.repr s_idx)] E0 m0
    (Vlong (Int64.repr next_idx)).
Proof.
  intros. eapply D.compile_delta_correct; eauto;
  unfold d; change Int64.modulus with Ptrofs.modulus; cbn [DFA.states]; nia.
Qed.

Lemma compile_delta_sink : forall q_idx s_idx mm,
  0 <= q_idx < Int64.modulus ->
  0 <= s_idx < Int64.modulus ->
  q_idx >= nstates (list state) m ->
  eval_funcall function_entry2 ge mm
    (compile_delta (list state) m ids)
    [Vlong (Int64.repr q_idx); Vlong (Int64.repr s_idx)] E0 mm
    (Vlong (Int64.repr (sink_index (list state) m))).
Proof.
  intros. eapply D.compile_delta_sink; eauto.
  unfold d; change Int64.modulus with Ptrofs.modulus; cbn [DFA.states]; nia.
Qed.

(** [accept_entry] indexes into [DC.Out.enum = [true; false]], so it is [0] on
    an accepting state and [1] otherwise. *)
Lemma accept_entry_val : forall q,
  accept_entry (list state) m q = (if d.(DFA.accept _) q then 0 else 1).
Proof. intros. apply D.accept_entry_val. Qed.

Lemma compile_accept_correct : forall q q_idx,
  sidx q = Some q_idx ->
  eval_funcall function_entry2 ge m0
    (compile_accept (list state) m ids)
    [Vlong (Int64.repr q_idx)] E0 m0
    (Vlong (Int64.repr (if d.(DFA.accept _) q then 0 else 1))).
Proof.
  intros. eapply D.compile_accept_correct; eauto;
  unfold d; change Int64.modulus with Ptrofs.modulus; cbn [DFA.states]; nia.
Qed.

Lemma compile_run_correct : forall w l b ofs,
  sym_indices w l ->
  word_in_mem m0 b ofs l ->
  0 <= ofs ->
  Z.of_nat (length w) < Int64.modulus ->
  ofs + 8 * Z.of_nat (length w) < Ptrofs.modulus ->
  exists r_idx,
    sidx (DFA.run d w) = Some r_idx /\
    eval_funcall function_entry2 ge m0
      (compile_run (list state) m list_state_eq_dec ids)
      [Vptr b (Ptrofs.repr ofs); Vlong (Int64.repr (Z.of_nat (length w)))] E0 m0
      (Vlong (Int64.repr r_idx)).
Proof.
  intros. eapply D.compile_run_correct; eauto;
  unfold d; change Int64.modulus with Ptrofs.modulus; cbn [DFA.states]; nia.
Qed.

(* The DFA reached by running [d] on [w] accepts iff the NFA accepts [w]. *)
Lemma accept_run_nfa : forall w,
  d.(DFA.accept _) (DFA.run d w) = NFA.accept_string nfa w.
Proof. intro. apply (to_dfa_correct state_eq_dec nfa w). Qed.

(* [d]'s transition is the NFA subset-construction step, restricted to the listed states. *)
Lemma transition_nfa : forall q a,
  d.(DFA.transition _) q a
  = restrict state_eq_dec nfa (NFA.step (NFA.transition _ nfa) q a).
Proof. reflexivity. Qed.

(** Running the compiled program on a word [w] held in memory reaches some state
    index [r_idx], and the compiled accept function maps that index to the NFA's
    acceptance verdict on [w] ([0] = accept, [1] = reject). *)
Theorem compile_accepts_nfa : forall w l b ofs,
  sym_indices w l ->
  word_in_mem m0 b ofs l ->
  0 <= ofs ->
  Z.of_nat (length w) < Int64.modulus ->
  ofs + 8 * Z.of_nat (length w) < Ptrofs.modulus ->
  exists r_idx,
    eval_funcall function_entry2 ge m0
      (compile_run (list state) m list_state_eq_dec ids)
      [Vptr b (Ptrofs.repr ofs); Vlong (Int64.repr (Z.of_nat (length w)))] E0 m0
      (Vlong (Int64.repr r_idx)) /\
    eval_funcall function_entry2 ge m0
      (compile_accept (list state) m ids)
      [Vlong (Int64.repr r_idx)] E0 m0
      (Vlong (Int64.repr (if NFA.accept_string nfa w then 0 else 1))).
Proof.
  intros w l b ofs Hsym Hmem Hofs Hlen Hptr.
  destruct (compile_run_correct w l b ofs Hsym Hmem Hofs Hlen Hptr)
    as (r_idx & Hr & Hrun).
  exists r_idx. split.
    exact Hrun.
  rewrite <- accept_run_nfa.
  now apply compile_accept_correct.
Qed.

End correctness.
End Correctness.