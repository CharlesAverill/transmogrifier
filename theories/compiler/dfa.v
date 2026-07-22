From lstar Require Import automata.DFA.
From compcert Require Import AST Clight Ctypes Integers Cop Maps.
From Transmogrifier Require Import moore.
From Stdlib Require Import String List ZArith Bool.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** Compile a DFA into a Clight program.

    \Sigma : alphabet, represented as integer indices 0..|\Sigma|-1
    Q      : state set, represented as integer indices 0..|Q|-1
    q_0    : exported as a read-only global; see [q0_index]
    \delta : compiled to
                unsigned int delta(unsigned int q, unsigned int s);
    F      : compiled to
                unsigned int accept(unsigned int q); *)

Module Type DFAType (s : Symbol).
  Record t (state : Type) : Type := {
        transition : state -> s.t -> state;
        initial : state;
        accept : state -> bool;
        states : list state;
        states_complete : forall w, In (fold_left transition w initial) (states)
    }.

  Definition run {state : Type} (dfa : t state) (s : list s.t) : state :=
        fold_left dfa.(transition state) s dfa.(initial state).

  Theorem run_in_states : forall {state : Type} (d : t state) (w : list s.t),
        In (run d w) (states state d).
  Proof. apply states_complete. Qed.
End DFAType.

Module DFACompiler (s : Symbol) (DFA : DFAType s).

Import DFA.

Module Out <: Output.
  Definition t := bool.
  Definition eq_dec := bool_dec.
  Definition enum := [true; false].
  Theorem t_enumerable : forall x : bool, In x enum.
  Proof. unfold enum. intros [|]. now left. right. now left. Qed.
End Out.

Module Moore <: MooreType s Out.
  Record t (state : Type) : Type := {
        transition : state -> s.t -> state;
        initial : state;
        output : state -> bool;
        states : list state;
        states_complete : forall w, In (fold_left transition w initial) (states)
    }.

  Definition run {state : Type} (dfa : t state) (s : list s.t) : state :=
        fold_left dfa.(transition state) s dfa.(initial state).

  Theorem run_in_states : forall {state : Type} (d : t state) (w : list s.t),
        In (run d w) (states state d).
  Proof. intros. apply states_complete. Qed.
End Moore.

Module MooreCompiler := MooreCompiler s Out Moore.
Include MooreCompiler.

End DFACompiler.
