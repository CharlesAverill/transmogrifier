From lstar Require Import automata.DFA automata.Moore.
From compcert Require Import AST Clight Ctypes Integers Cop Maps.
From Transmogrifier Require Import compiler.moore.
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
  Include (DFA s).
End DFAType.

Module Out <: Output.
  Definition t := bool.
  Definition eq_dec := bool_dec.
  Definition enum := [true; false].
  Theorem t_enumerable : forall x : bool, In x enum.
  Proof. unfold enum. intros [|]. now left. right. now left. Qed.
End Out.

Module DFACompiler (s : Symbol) (DFA : DFAType s) (Moore : MooreType s Out).

Import DFA Moore.

Module MooreCompiler := MooreCompiler s Out Moore.

Definition moore_of_dfa {state : Type} (d : DFA.t state) : Moore.t state :=
  Moore.Build_t state
    d.(DFA.transition state)
    d.(DFA.initial state)
    d.(DFA.accept state)
    d.(DFA.states state)
    (d.(DFA.states_complete state)).

Definition compile_dfa {state : Type}
    (d : DFA.t state)
    (state_eq_dec : forall x y : state, {x = y} + {x <> y})
    (base : ident) : result Clight.program string :=
  MooreCompiler.compile_program state (moore_of_dfa d) state_eq_dec base.

End DFACompiler.