From lstar Require Import automata.NFA automata.DFA.
From compcert Require Import AST Clight Ctypes Integers Cop Maps.
From Transmogrifier Require Import compiler.dfa compiler.moore.
From Stdlib Require Import List ZArith Permutation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

#[local] Set Warnings "-intuition-auto-with-star".

Module Type NFAType (s : Symbol).
  Include (NFA s).
End NFAType.

(** NFA to DFA conversion *)
Module NFA_to_DFA (s : Symbol) (D : DFAType s) (NFA : NFAType s).
  Import NFA D s.
  Section Conversion.
  Context {nfa_state : Type}.
  Variable eq_dec : forall x y : nfa_state, {x = y} + {x <> y}.

  Definition list_state_eq_dec : forall x y : list nfa_state, {x = y} + {x <> y} :=
      list_eq_dec eq_dec.

  Fixpoint powerset (l : list nfa_state) : list (list nfa_state) :=
    match l with
    | [] => [[]]
    | x :: xs =>
        let ps := powerset xs in
        ps ++ map (cons x) ps
    end.

  Lemma nil_in_powerset : forall l, In [] (powerset l).
  Proof.
    induction l.
      now left.
    simpl. apply in_or_app. now left.
  Qed.

  Lemma sublist_in_powerset : forall l1 l2 l3,
    In l2 (powerset (l1 ++ l2 ++ l3)).
  Proof.
    induction l1; intros; simpl in *.
    - induction l2. apply nil_in_powerset.
      simpl. apply in_or_app. right. now apply in_map.
    - apply in_or_app. left. apply IHl1.
  Qed.

  Definition canonical (qs : list nfa_state) : list nfa_state :=
    nodup eq_dec qs.

  Lemma filter_in_powerset : forall (f : nfa_state -> bool) l,
    In (filter f l) (powerset l).
  Proof.
    induction l; simpl in *.
      now left.
    destruct (f a); apply in_or_app.
      right. now apply in_map.
      now left.
  Qed.

  Theorem powerset_complete : forall (l qs : list nfa_state),
    (forall x, In x qs -> In x l) -> NoDup qs ->
    exists qs', (forall x, In x qs' <-> In x qs) /\ In qs' (powerset l).
  Proof.
    intros. exists (filter (fun x => if in_dec eq_dec x qs then true else false) l).
    split; [| apply filter_in_powerset ].
    intro. rewrite filter_In.
    destruct (in_dec eq_dec x qs) as [Hin | Hnin]; simpl.
    - split; auto.
    - now split.
  Qed.

  (* The members of [qs] that are NFA states, listed in the fixed order of [NFA.states]. *)
  Definition restrict (nfa : NFA.t nfa_state) (qs : list nfa_state) : list nfa_state :=
    filter (fun x => if in_dec eq_dec x qs then true else false)
           (NFA.states nfa_state nfa).

  Lemma restrict_In : forall nfa qs x,
    In x (restrict nfa qs) <-> In x (NFA.states nfa_state nfa) /\ In x qs.
  Proof.
    intros. unfold restrict. rewrite filter_In.
    destruct (in_dec eq_dec x qs); simpl; intuition.
  Qed.

  Definition dtransition (nfa : NFA.t nfa_state)
      (qs : list nfa_state) (a : s.t) : list nfa_state :=
    restrict nfa (NFA.step (NFA.transition nfa_state nfa) qs a).

  Definition daccept (nfa : NFA.t nfa_state) (qs : list nfa_state) : bool :=
    existsb (NFA.accept nfa_state nfa) qs.

  (* Every reachable DFA state is a [restrict], hence in the powerset. *)
  Lemma dtransition_in_powerset : forall nfa qs a,
    In (dtransition nfa qs a) (powerset (NFA.states nfa_state nfa)).
  Proof. intros. apply filter_in_powerset. Qed.

  Lemma fold_dtransition_in_powerset : forall nfa w qs0,
    In qs0 (powerset (NFA.states nfa_state nfa)) ->
    In (fold_left (dtransition nfa) w qs0) (powerset (NFA.states nfa_state nfa)).
  Proof.
    induction w; intros; simpl in *.
      assumption.
    apply IHw, dtransition_in_powerset.
  Qed.

  Lemma to_dfa_states_complete : forall nfa w,
    In (fold_left (dtransition nfa) w
          (restrict nfa (NFA.initial nfa_state nfa)))
       (powerset (NFA.states nfa_state nfa)).
  Proof. intros. apply fold_dtransition_in_powerset, filter_in_powerset. Qed.

  Definition to_dfa (nfa : NFA.t nfa_state) : D.t (list nfa_state) :=
    {| D.transition := dtransition nfa;
       D.initial := restrict nfa (NFA.initial nfa_state nfa);
       D.accept := daccept nfa;
       D.states := powerset (NFA.states nfa_state nfa);
       D.states_complete := to_dfa_states_complete nfa |}.

  (* Reachable NFA states are closed under one transition step *)
  Lemma step_reachable_closed : forall nfa qs a q,
    (forall x, In x qs -> exists u, In x (NFA.run nfa u)) ->
    In q (NFA.step (NFA.transition nfa_state nfa) qs a) ->
    exists u, In q (NFA.run nfa u).
  Proof.
    intros. unfold NFA.step in H0. apply in_flat_map in H0.
    destruct H0 as (q' & Hq' & Htrans).
    destruct (H q' Hq') as (u & Hu).
    exists (u ++ [a])%list.
    unfold NFA.run, NFA.run_from in *.
    rewrite fold_left_app. simpl.
    unfold NFA.step. apply in_flat_map. exists q'. now split.
  Qed.

  Lemma run_from_correspond : forall nfa w dqs qs,
    (forall q, In q dqs <-> In q qs) ->
    (forall q, In q qs -> exists u, In q (NFA.run nfa u)) ->
    forall q, In q (fold_left (dtransition nfa) w dqs)
            <-> In q (fold_left (NFA.step (NFA.transition nfa_state nfa)) w qs).
  Proof.
    induction w; intros; simpl in *. auto.
    apply IHw; [|eauto using step_reachable_closed].
    intro x. unfold dtransition. rewrite restrict_In. split.
      intros. destruct H1. unfold NFA.step in *.
        apply in_flat_map in H2. destruct H2 as (y & Hy & Hxy).
        apply in_flat_map. exists y. split. now apply H. assumption.
      intros. split.
        destruct (step_reachable_closed nfa qs a x H0 H1) as (u & Hu).
          unfold NFA.run, NFA.run_from in Hu.
          apply (NFA.states_complete nfa_state nfa u x). assumption.
        unfold NFA.step in *.
          apply in_flat_map in H1. destruct H1 as (y & Hy & Hxy).
          apply in_flat_map. exists y. split. now apply H. assumption.
  Qed.

  Lemma run_correspond : forall nfa w q,
    In q (D.run (to_dfa nfa) w) <-> In q (NFA.run nfa w).
  Proof.
    intros. unfold D.run, to_dfa, NFA.run, NFA.run_from. simpl.
    apply run_from_correspond.
    - intros. rewrite restrict_In. split; intro. intuition. intuition. unfold NFA.states.
      destruct nfa. simpl in *. now apply states_complete0 with (w := []).
    - intros. exists []. apply H.
  Qed.

  Lemma existsb_iff_In : forall (f : nfa_state -> bool) l1 l2,
    (forall q, In q l1 <-> In q l2) -> existsb f l1 = existsb f l2.
  Proof.
    intros. apply Bool.eq_true_iff_eq. split; intro;
      apply existsb_exists in H0; destruct H0 as (q & Hq & Hf);
      apply existsb_exists; exists q; split; eauto; now apply H.
  Qed.

  (* The subset-construction DFA accepts exactly the NFA's language. *)
  Theorem to_dfa_correct : forall nfa w,
    D.accept_string (to_dfa nfa) w = NFA.accept_string nfa w.
  Proof.
    intros. unfold D.accept_string, NFA.accept_string.
    replace (D.accept (list nfa_state) (to_dfa nfa))
      with (daccept nfa) by reflexivity.
    unfold daccept.
    apply existsb_iff_In. intro. apply run_correspond.
  Qed.

  End Conversion.
End NFA_to_DFA.

Module NFACompiler (s : Symbol) (N : NFAType s) (D : DFAType s) (M : MooreType s Out).

  Module N2D := NFA_to_DFA s D N.
  Import N.

  Module DC := DFACompiler s D M.

  Definition compile_program {state} (n : N.t state) eq_dec base :=
    DC.compile_dfa (N2D.to_dfa eq_dec n) (list_eq_dec eq_dec) base.

End NFACompiler.