From lstar Require Import automata.DFA.
From compcert Require Import AST Clight Ctypes Integers Values Coqlib.
From compcert Require Import ClightBigstep Events Globalenvs Memory.
From Transmogrifier Require Import Monads.
From Transmogrifier.compiler Require Import dfa.
From Transmogrifier.transparency Require Import mooreproofs.
From Stdlib Require Import List ZArith Lia.
Import ListNotations.
Open Scope result_scope.
Open Scope Z_scope.

(** Correctness of the DFA -> Clight compiler *)

Module Correctness (s : Symbol) (DFA : DFAType s).

Module DC := DFACompiler s DFA.

Module M := mooreproofs.Correctness s DC.Out DC.Moore.
Import M.DC.

Section coercion.
Variable state : Type.

Definition moore_of_dfa (d : DFA.t state) : DC.Moore.t state :=
  DC.Moore.Build_t state
    d.(DFA.transition state)
    d.(DFA.initial state)
    d.(DFA.accept state)
    d.(DFA.states state)
    (d.(DFA.states_complete state)).

Lemma run_moore_of_dfa : forall (d : DFA.t state) (w : list s.t),
  DC.Moore.run (moore_of_dfa d) w = DFA.run d w.
Proof. reflexivity. Qed.

Lemma states_moore_of_dfa : forall (d : DFA.t state),
  DC.Moore.states state (moore_of_dfa d) = DFA.states state d.
Proof. reflexivity. Qed.

Lemma accept_moore_of_dfa : forall (d : DFA.t state) (q : state),
  DC.Moore.output state (moore_of_dfa d) q = DFA.accept state d q.
Proof. reflexivity. Qed.

End coercion.

Section correctness.
Variable state : Type.
Variable dfa : DFA.t state.
Variable state_eq_dec : forall (x y : state), {x = y} + {x <> y}.

Notation m := (moore_of_dfa state dfa).

(** Well-formedness: the state and symbol enumerations fit in [tlong] *)
Variable states_bounded : Z.of_nat (length dfa.(DFA.states _)) < Int64.modulus.
Variable syms_bounded   : 0 < Z.of_nat (length s.enum) < Int64.modulus.

(** [DC.Out.enum] is [[true; false]], so the output bound is discharged, not
    assumed: it is the one hypothesis of [mooreproofs] a DFA pays for free. *)
Lemma O_bounded : 0 < Z.of_nat (length DC.Out.enum) < Int64.modulus.
Proof. cbn. unfold Int64.modulus, Int64.wordsize, Wordsize_64.wordsize, two_power_nat. cbn. lia. Qed.

Variable base : ident.
Variable p : Clight.program.
Variable Hp : compile_program state m state_eq_dec base = Ok p.

Definition ge : genv := M.ge p.
Definition ids : idents := M.ids base.

Variable m0 : mem.
Variable Hinit : Genv.init_mem p = Some m0.

Variable table_bounded :
  8 * (Z.of_nat (length dfa.(DFA.states _)) * Z.of_nat (length s.enum)) < Ptrofs.modulus.

(** Indices. Definitionally the Moore ones, since [m] shares [dfa]'s carrier. *)
Definition sidx (q : state) : option Z := M.sidx state m state_eq_dec q.
Definition symidx (a : s.t) : option Z := M.symidx a.

Definition sym_indices (w : list s.t) (l : list Z) : Prop := M.sym_indices w l.
Definition word_in_mem (mm : mem) (b : block) (ofs : Z) (l : list Z) : Prop :=
  M.word_in_mem mm b ofs l.

Lemma sidx_run : forall w, exists i, sidx (DFA.run dfa w) = Some i.
Proof. intros. rewrite <- run_moore_of_dfa. apply M.sidx_run. Qed.

Lemma symidx_total : forall a, exists i, symidx a = Some i.
Proof. apply M.symidx_total. Qed.

Lemma q0_index_correct :
  sidx dfa.(DFA.initial _) = Some (q0_index state m state_eq_dec).
Proof. apply M.q0_index_correct. Qed.

Lemma compile_delta_correct : forall q sym q_idx s_idx next_idx,
  sidx q = Some q_idx ->
  symidx sym = Some s_idx ->
  sidx (dfa.(DFA.transition _) q sym) = Some next_idx ->
  eval_funcall function_entry2 ge m0
    (compile_delta state m ids)
    [Vlong (Int64.repr q_idx); Vlong (Int64.repr s_idx)] E0 m0
    (Vlong (Int64.repr next_idx)).
Proof.
  intros. eapply M.compile_delta_correct; eauto.
  now compute.
Qed.

Lemma compile_delta_sink : forall q_idx s_idx mm,
  0 <= q_idx < Int64.modulus ->
  0 <= s_idx < Int64.modulus ->
  q_idx >= nstates state m ->
  eval_funcall function_entry2 ge mm
    (compile_delta state m ids)
    [Vlong (Int64.repr q_idx); Vlong (Int64.repr s_idx)] E0 mm
    (Vlong (Int64.repr (sink_index state m))).
Proof.
  intros. eapply M.compile_delta_sink; eauto.
Qed.

(** [accept_entry] indexes into [DC.Out.enum = [true; false]], so it is [0] on
    an accepting state and [1] otherwise. This is the DFA-facing restatement
    that [mooreproofs] cannot make, and the only lemma here with real content. *)
Lemma accept_entry_val : forall q,
  accept_entry state m q = (if dfa.(DFA.accept _) q then 0 else 1).
Proof.
  intros. unfold accept_entry. cbn.
  destruct (DFA.accept state dfa q); reflexivity.
Qed.

Lemma compile_accept_correct : forall q q_idx,
  sidx q = Some q_idx ->
  eval_funcall function_entry2 ge m0
    (compile_accept state m ids)
    [Vlong (Int64.repr q_idx)] E0 m0
    (Vlong (Int64.repr (if dfa.(DFA.accept _) q then 0 else 1))).
Proof.
  intros. rewrite <- accept_entry_val.
  eapply M.compile_accept_correct; eauto.
  now compute.
Qed.

Lemma compile_run_correct : forall w l b ofs,
  sym_indices w l ->
  word_in_mem m0 b ofs l ->
  0 <= ofs ->
  Z.of_nat (length w) < Int64.modulus ->
  ofs + 8 * Z.of_nat (length w) < Ptrofs.modulus ->
  exists r_idx,
    sidx (DFA.run dfa w) = Some r_idx /\
    eval_funcall function_entry2 ge m0
      (compile_run state m state_eq_dec ids)
      [Vptr b (Ptrofs.repr ofs); Vlong (Int64.repr (Z.of_nat (length w)))] E0 m0
      (Vlong (Int64.repr r_idx)).
Proof.
  intros. rewrite <- run_moore_of_dfa.
  eapply M.compile_run_correct; eauto.
  now compute.
Qed.

End correctness.
End Correctness.
