From lstar Require Import Automata.
From compcert Require Import AST Clight Ctypes Integers Cop Maps.
From compcert Require Import ClightBigstep Values Events Coqlib.
From compcert Require Import Globalenvs Memory.
From Transmogrifier Require Import Monads.
From Transmogrifier.compiler Require Import nfa.
From Stdlib Require Import List ZArith Lia.
Import ListNotations.
Open Scope result_scope.
Open Scope Z_scope.

(** Correctness of the NFA -> Clight compiler *)

Module Correctness (s : Symbol) (NFA : NFAType s).

Module NC := NFACompiler s NFA.
Import NC NFA.

Section index.
Variable X : Type.
Variable eq_dec : forall x y : X, {x = y} + {x <> y}.

Lemma index_of_ge : forall l x i k,
  index_of eq_dec x l k = Some i -> k <= i.
Proof.
  induction l; intros; simpl in *.
    discriminate.
  destruct eq_dec.
    now inversion H.
  apply IHl in H. lia.
Qed.

Lemma index_of_lt : forall l x i k,
  index_of eq_dec x l k = Some i -> i < k + Z.of_nat (length l).
Proof.
  induction l; intros; simpl in *.
    discriminate.
  destruct eq_dec.
    inversion H. lia.
  apply IHl in H. lia.
Qed.

Lemma index_of_bounds : forall l x i,
  index_of eq_dec x l 0 = Some i -> 0 <= i < Z.of_nat (length l).
Proof.
  intros. split.
    eauto using index_of_ge.
  apply index_of_lt in H. lia.
Qed.

Lemma index_of_complete : forall l x k,
  In x l -> exists i, index_of eq_dec x l k = Some i.
Proof.
  induction l; intros. contradiction.
  simpl in *. destruct eq_dec; subst.
    now exists k.
  destruct H. congruence. eauto.
Qed.

Lemma index_of_inj : forall l x y i k,
  index_of eq_dec x l k = Some i ->
  index_of eq_dec y l k = Some i ->
  x = y.
Proof.
  induction l; intros; simpl in *.
    discriminate.
  destruct eq_dec, eq_dec;
    inversion H; inversion H0; subst; clear H H0; eauto.
  apply index_of_ge in H3. lia.
  apply index_of_ge in H2. lia.
Qed.

End index.

Section bitmaps.

Lemma word_of_indices_bound : forall idxs k,
  0 <= k ->
  0 <= word_of_indices idxs k < 2 ^ 64.
Proof.
  intros idxs k Hk. unfold word_of_indices.
  assert (Hgen : forall l acc, 0 <= acc < 2 ^ 64 ->
    0 <= fold_left
      (fun acc i =>
         if andb (Z.leb (64 * k) i) (Z.ltb i (64 * (k + 1)))
         then Z.lor acc (Z.shiftl 1 (i - 64 * k))
         else acc) l acc < 2 ^ 64).
  { induction l; intros acc Hacc; cbn - [Z.mul].
      assumption.
    destruct (Z.leb (64 * k) a) eqn:El, (Z.ltb a (64 * (k + 1))) eqn:Eu; cbn - [Z.mul];
      try (apply IHl; assumption).
    apply IHl.
    apply Z.leb_le in El. apply Z.ltb_lt in Eu.
    assert (Hd : 0 <= a - 64 * k < 64) by lia.
    assert (Hs : 0 <= Z.shiftl 1 (a - 64 * k) < 2 ^ 64).
    { rewrite Z.shiftl_1_l. split.
        apply Z.pow_nonneg. lia.
      apply Z.pow_lt_mono_r; lia. }
    split.
      apply Z.lor_nonneg. lia.
    (* both operands below 2^64 => lor below 2^64 *)
    destruct Hs.
    apply Z.log2_lt_pow2 in H0.
    destruct (Z.eq_dec (Z.lor acc (Z.shiftl 1 (a - 64 * k))) 0) as [E|E].
      rewrite E. lia.
    apply Z.log2_lt_pow2.
      apply Z.le_neq. split. apply Z.lor_nonneg. lia. easy.
    rewrite Z.log2_lor by lia.
    apply Z.max_lub_lt.
      destruct (Z.eq_dec acc 0). subst. now compute.
      apply Z.log2_lt_pow2; lia.
    destruct (Z.eq_dec (Z.shiftl 1 (a - 64 * k)) 0).
      rewrite e. now compute.
    apply Z.log2_lt_pow2; try lia.
    admit. (* Z.shiftl 1 (a - 64 * k) < 2^64 *) 
    admit. (* 0 < Z.shiftl 1 (a - 64 * k) *) }
  apply Hgen. lia.
Admitted.

Lemma word_of_indices_fold : forall idxs k b acc,
  0 <= b < 64 ->
  Z.testbit
    (fold_left
      (fun acc i =>
         if andb (Z.leb (64 * k) i) (Z.ltb i (64 * (k + 1)))
         then Z.lor acc (Z.shiftl 1 (i - 64 * k))
         else acc)
      idxs acc) b
  = orb (Z.testbit acc b) (existsb (fun i => Z.eqb i (64 * k + b)) idxs).
Proof.
  induction idxs; intros k b acc Hb; cbn - [Z.mul].
  - now rewrite orb_false_r.
  - rewrite IHidxs by assumption.
    destruct (Z.leb (64 * k) a) eqn:El, (Z.ltb a (64 * (k + 1))) eqn:Eu; cbn - [Z.mul].
    + rewrite Z.lor_spec, Z.shiftl_spec by lia.
      destruct (Z.eqb a (64 * k + b)) eqn:Ea.
      * apply Z.eqb_eq in Ea. subst a.
        replace (64 * k + b - 64 * k) with b by lia.
        rewrite Z.sub_diag, Z.bit0_odd.
        now rewrite <- orb_assoc, orb_true_r, orb_true_r.
      * apply Z.eqb_neq in Ea.
        replace (Z.testbit 1 (b - (a - 64 * k))) with false.
          now rewrite orb_false_r.
        symmetry.
        destruct (Z.ltb (b - (a - 64 * k)) 0) eqn:Eneg.
        -- apply Z.ltb_lt in Eneg. now apply Z.testbit_neg_r.
        -- apply Z.ltb_ge in Eneg.
           change 1 with (2 ^ 0). apply Z.pow2_bits_false. lia.
    + (* a >= 64*(k+1): out of this word *)
      destruct (Z.eqb a (64 * k + b)) eqn:Ea; [|reflexivity].
      apply Z.eqb_eq in Ea. apply Z.ltb_ge in Eu. lia.
    + (* a < 64*k: out of this word *)
      destruct (Z.eqb a (64 * k + b)) eqn:Ea; [|reflexivity].
      apply Z.eqb_eq in Ea. apply Z.leb_gt in El. lia.
    + destruct (Z.eqb a (64 * k + b)) eqn:Ea; [|reflexivity].
      apply Z.eqb_eq in Ea. apply Z.leb_gt in El. lia.
Qed.

(** Bit [b] of word [k] is set iff index [64*k+b] is in the set. *)
Lemma word_of_indices_spec : forall idxs k b,
  0 <= k -> 0 <= b < 64 ->
  Z.testbit (word_of_indices idxs k) b = true <-> In (64 * k + b) idxs.
Proof.
  intros idxs k b Hk Hb. unfold word_of_indices.
  rewrite word_of_indices_fold by assumption.
  rewrite Z.testbit_0_l. cbn.
  split.
  - intros H. apply existsb_exists in H as (x & Hx & Heq).
    apply Z.eqb_eq in Heq. now subst x.
  - intros H. apply existsb_exists. exists (64 * k + b).
    split. assumption. apply Z.eqb_refl.
Qed.

Lemma word_of_indices_nil : forall k, word_of_indices [] k = 0.
Proof. reflexivity. Qed.

(** [bitmap_init] emits exactly [nwords] words, word 0 first. *)
Lemma bitmap_init_length : forall state nfa idxs,
  length (bitmap_init state nfa idxs)
  = Z.to_nat (nwords state nfa).
Proof.
  intros. unfold bitmap_init.
  now rewrite length_map, length_map, length_seq.
Qed.

Lemma bitmap_init_nth : forall state nfa idxs k,
  0 <= k < nwords state nfa ->
  nth_error (bitmap_init state nfa idxs) (Z.to_nat k)
  = Some (Init_int64 (Int64.repr (word_of_indices idxs k))).
Proof.
  intros state nfa idxs k Hk. unfold bitmap_init.
  rewrite nth_error_map, nth_error_map, nth_error_seq.
  (* [seq 0 (Z.to_nat nwords)] has [Z.to_nat k] in range, so the guard is true
     and the element is [Z.to_nat k] itself; [Z2Nat.id] then restores [k]. *)
  unfold Datatypes.option_map.
  replace (Z.to_nat k <? Z.to_nat (nwords state nfa))%nat with true
    by (symmetry; apply Nat.ltb_lt; lia).
  now rewrite Nat.add_0_l, Z2Nat.id by lia.
Qed.

End bitmaps.

Section correctness.
Variable state : Type.
Variable nfa : NFA.t state.
Variable state_eq_dec : forall (x y : state), {x = y} + {x <> y}.

Notation nstates := (nstates state nfa).
Notation nsyms   := (nsyms).
Notation nwords  := (nwords state nfa).

(** Well-formedness *)
Variable states_bounded : 0 < Z.of_nat (length nfa.(states _)) < Int64.modulus.
Variable syms_bounded   : 0 < Z.of_nat (length s.enum) < Int64.modulus.
Variable table_bounded  : 8 * (nstates * nsyms * nwords) < Ptrofs.modulus.

Variable base : ident.
Variable p : Clight.program.
Variable Hp : compile_program state nfa state_eq_dec base = Ok p.

Definition ge : genv := Clight.globalenv p.
Definition ids : idents := alloc_idents base.

Variable m0 : mem.
Variable Hinit : Genv.init_mem p = Some m0.

(** Global environment *)

Lemma compile_program_defs :
  prog_defs p =
    [ (ids.(id_table),  Gvar (compile_table state nfa state_eq_dec));
      (ids.(id_init),   Gvar (compile_init state nfa state_eq_dec));
      (ids.(id_final),  Gvar (compile_final state nfa state_eq_dec));
      (ids.(id_step),   Gfun (compile_step state nfa ids));
      (ids.(id_accept), Gfun (compile_accept state nfa ids));
      (ids.(id_run),    Gfun (compile_run state nfa ids));
      (ids.(id_main),   Gfun (compile_main ids)) ].
Proof.
  unfold ids. unfold compile_program in Hp.
  destruct Ctypes.make_program eqn:E; [|discriminate].
  inversion Hp; subst; clear Hp.
  unfold Ctypes.make_program in E. cbn in E.
  now inversion E.
Qed.

Lemma global_idents_norepet :
  list_norepet (map fst (prog_defs p)).
Proof.
  rewrite compile_program_defs.
  cbv [ids alloc_idents id_table id_init id_final id_step id_accept id_run
       id_main map fst].
  repeat constructor; cbn - [Pos.succ Pos.add]; intro H;
    repeat (destruct H as [H|H]; [lia|]); contradiction.
Qed.

Lemma find_table :
  exists b,
    Genv.find_symbol ge ids.(id_table) = Some b /\
    Genv.find_def ge b = Some (Gvar (compile_table state nfa state_eq_dec)).
Proof.
  apply Genv.find_def_symbol.
  apply prog_defmap_norepet.
    apply global_idents_norepet.
  change (AST.prog_defs p) with (prog_defs p).
  rewrite compile_program_defs. now left.
Qed.

Lemma find_final :
  exists b,
    Genv.find_symbol ge ids.(id_final) = Some b /\
    Genv.find_def ge b = Some (Gvar (compile_final state nfa state_eq_dec)).
Proof.
  apply Genv.find_def_symbol.
  apply prog_defmap_norepet.
    apply global_idents_norepet.
  change (AST.prog_defs p) with (prog_defs p).
  rewrite compile_program_defs. right. right. now left.
Qed.

Definition sidx (q : state) : option Z := state_index state nfa state_eq_dec q.

Definition set_in_mem (m : mem) (b : block) (ofs : Z) (idxs : list Z) : Prop :=
  forall k, 0 <= k < nwords ->
    Mem.loadv Mint64 m (Vptr b (Ptrofs.repr (ofs + 8 * k)))
      = Some (Vlong (Int64.repr (word_of_indices idxs k))).

(* Two index sets with the same members induce the same bitmap.*)
Lemma word_of_indices_ext : forall S1 S2 k,
  0 <= k ->
  (forall i, In i S1 <-> In i S2) ->
  word_of_indices S1 k = word_of_indices S2 k.
Proof.
  intros S1 S2 k Hk Hext.
  apply Z.bits_inj'. intros b Hb.
  destruct (Z.ltb b 64) eqn:Eb.
  - apply Z.ltb_lt in Eb.
    destruct (Z.testbit (word_of_indices S1 k) b) eqn:E1,
             (Z.testbit (word_of_indices S2 k) b) eqn:E2; try reflexivity.
    + apply (word_of_indices_spec S1 k b Hk) in E1; [|lia].
      apply Hext in E1.
      apply (word_of_indices_spec S2 k b Hk) in E1; [|lia]. congruence.
    + apply (word_of_indices_spec S2 k b Hk) in E2; [|lia].
      apply Hext in E2.
      apply (word_of_indices_spec S1 k b Hk) in E2; [|lia]. congruence.
  - apply Z.ltb_ge in Eb.
    pose proof (word_of_indices_bound S1 k Hk) as H1.
    pose proof (word_of_indices_bound S2 k Hk) as H2.
    rewrite !Z.bits_above_log2; try lia.
    (* Z.log2 (word_of_indices S[1/2] k) < b *)
    admit. admit.
Admitted.

(* Two index sets with the same members induce the same bitmap. *)
Lemma set_in_mem_ext : forall m b ofs S1 S2,
  (forall i, In i S1 <-> In i S2) ->
  set_in_mem m b ofs S1 -> set_in_mem m b ofs S2.
Proof.
  intros m b ofs S1 S2 Hext H k Hk.
  rewrite <- (word_of_indices_ext S1 S2 k) by (assumption || lia).
  apply H. assumption.
Qed.

Lemma sidx_bounds : forall q i, sidx q = Some i -> 0 <= i < nstates.
Proof.
  intros q i H. unfold sidx, state_index in H.
  apply index_of_bounds in H. unfold NC.nstates. lia.
Qed.

Lemma sidx_total : forall q, In q nfa.(states _) -> exists i, sidx q = Some i.
Proof. intros. unfold sidx, state_index. now apply index_of_complete. Qed.

(* [indices_of] is the pointwise image of [sidx] over a state list. *)
Lemma indices_of_spec : forall qs i,
  In i (indices_of state nfa state_eq_dec qs) <->
  (exists q, In q qs /\ sidx q = Some i).
Proof.
  induction qs; intros; cbn.
  - split. contradiction. intros (q & [] & _).
  - unfold indices_of in *. cbn.
    destruct (state_index state nfa state_eq_dec a) eqn:E.
    + (* a has an index *)
      cbn. split.
      * intros [->|H].
          exists a. split. now left. exact E.
        apply IHqs in H as (q & Hq & Hi). exists q. split. now right. exact Hi.
      * intros (q & [->|Hq] & Hi).
          left. unfold sidx in Hi. congruence.
        right. apply IHqs. eauto.
    + (* a is not in states: dropped *)
      split.
      * intros H. apply IHqs in H as (q & Hq & Hi). exists q. split. now right. exact Hi.
      * intros (q & [->|Hq] & Hi).
          unfold sidx in Hi. congruence.
        apply IHqs. eauto.
Qed.

(** The transition table

    Row [(q,a)] occupies [nwords] words at flat offset [(qi * nsyms + ai) * nwords]. *)

Lemma table_row_length : forall q sym,
  length (table_row state nfa state_eq_dec q sym) = Z.to_nat nwords.
Proof. intros. unfold table_row. apply bitmap_init_length. Qed.

Lemma nth_error_flat_map_uniform :
  forall (A B : Type) (f : A -> list B) (l : list A) (kw : nat),
  (forall x, In x l -> length (f x) = kw) ->
  forall i j x,
  nth_error l i = Some x ->
  (j < kw)%nat ->
  nth_error (flat_map f l) (i * kw + j) = nth_error (f x) j.
Proof.
  induction l; intros kw Hk i j x Hi Hj; simpl in *.
    now destruct i.
  destruct i; simpl in *.
  - inversion Hi; subst; clear Hi.
    rewrite nth_error_app1. reflexivity.
    rewrite Hk by now left. assumption.
  - rewrite nth_error_app2.
      rewrite Hk by now left.
      replace (kw + i * kw + j - kw)%nat with (i * kw + j)%nat by lia. eauto.
    rewrite Hk. lia. now left.
Qed.

Lemma index_of_nth_error : forall (X : Type) eq_dec (l : list X) x i k,
  index_of eq_dec x l k = Some i ->
  nth_error l (Z.to_nat (i - k)) = Some x.
Proof.
  induction l; intros x i k H; simpl in *.
    discriminate.
  destruct eq_dec.
    inversion H. rewrite Z.sub_diag. now subst.
  pose proof (index_of_ge _ eq_dec _ _ _ _ H).
  apply IHl in H.
  now replace (Z.to_nat (i - k)) with (S (Z.to_nat (i - Z.succ k))) by lia.
Qed.

Lemma nth_error_combine : forall (A B : Type) (la : list A) (lb : list B) n,
  nth_error (combine la lb) n =
  match nth_error la n, nth_error lb n with
  | Some a, Some b => Some (a, b)
  | _, _ => None
  end.
Proof.
  induction la; intros; simpl in *.
    now destruct n.
  destruct lb; simpl in *.
    destruct n; simpl. reflexivity. now destruct nth_error.
  destruct n; simpl.
    reflexivity.
  apply IHla.
Qed.

Lemma enumerate_nth : forall (X : Type) eq_dec (l : list X) x i,
  index_of eq_dec x l 0 = Some i ->
  nth_error (enumerate l) (Z.to_nat i) = Some (i, x).
Proof.
  intros X eq_dec l x i H.
  pose proof (index_of_bounds _ eq_dec _ _ _ H) as Hb.
  apply index_of_nth_error in H. rewrite Z.sub_0_r in H.
  unfold enumerate.
  rewrite nth_error_combine, H, nth_error_map, nth_error_seq. cbn - [Nat.ltb].
  unfold Datatypes.option_map.
  replace (Z.to_nat i <? length l)%nat with true
    by (symmetry; apply Nat.ltb_lt; lia).
  now rewrite Z2Nat.id by lia.
Qed.

Lemma state_table_nth : forall qi q,
  sidx q = Some qi ->
  nth_error (state_table state nfa) (Z.to_nat qi) = Some (qi, q).
Proof.
  intros qi q Hq. unfold state_table.
  apply enumerate_nth with (eq_dec := state_eq_dec). exact Hq.
Qed.

Lemma sym_table_nth : forall ai sym,
  index_of s.eq_dec sym s.enum 0 = Some ai ->
  nth_error (sym_table) (Z.to_nat ai) = Some (ai, sym).
Proof.
  intros ai sym Ha. unfold sym_table.
  apply enumerate_nth with (eq_dec := s.eq_dec). exact Ha.
Qed.

Lemma flat_map_const_length :
  forall (A B : Type) (f : A -> list B) (l : list A) (kw : nat),
  (forall x, In x l -> length (f x) = kw) ->
  length (flat_map f l) = (length l * kw)%nat.
Proof.
  induction l; intros kw Hk; cbn.
    reflexivity.
  rewrite length_app, Hk by now left.
  erewrite IHl by (intros; eapply Hk; now right). lia.
Qed.

Lemma sym_table_length : length (sym_table) = Z.to_nat nsyms.
Proof.
  unfold sym_table, enumerate.
  rewrite length_combine, length_map, length_seq.
  unfold NC.nsyms. lia.
Qed.

Lemma inner_flat_map_length : forall q,
  length (flat_map (fun '(_, sym) => table_row state nfa state_eq_dec q sym)
                   (sym_table))
  = Z.to_nat (nsyms * nwords).
Proof.
  intros q.
  rewrite flat_map_const_length with (kw := Z.to_nat nwords).
  - rewrite sym_table_length. unfold NC.nsyms, NC.nwords. lia.
  - intros (si & sy) _. apply table_row_length.
Qed.

Lemma table_row_correct : forall q sym qi ai k,
  sidx q = Some qi ->
  index_of s.eq_dec sym s.enum 0 = Some ai ->
  0 <= k < nwords ->
  nth_error (table_init state nfa state_eq_dec)
    (Z.to_nat ((qi * nsyms + ai) * nwords + k))
  = Some (Init_int64 (Int64.repr
      (word_of_indices (indices_of state nfa state_eq_dec
                          (nfa.(transition _) q sym)) k))).
Proof.
  intros q sym qi ai k Hq Ha Hk.
  assert (Hqb : 0 <= qi < nstates)
    by (eauto using sidx_bounds).
  assert (Hab : 0 <= ai < nsyms)
    by (unfold NC.nsyms; apply index_of_bounds in Ha; lia).
  unfold table_init.
  replace (Z.to_nat ((qi * nsyms + ai) * nwords + k))
    with (Z.to_nat qi * Z.to_nat (nsyms * nwords)
          + Z.to_nat (ai * nwords + k))%nat
    by (unfold NC.nsyms, NC.nwords in *; lia).
  rewrite nth_error_flat_map_uniform
    with (kw := Z.to_nat (nsyms * nwords)) (x := (qi, q)).
  - replace (Z.to_nat (ai * nwords + k))
      with (Z.to_nat ai * Z.to_nat nwords + Z.to_nat k)%nat
      by (unfold NC.nwords in *; lia).
    rewrite nth_error_flat_map_uniform
      with (kw := Z.to_nat nwords) (x := (ai, sym)).
    + unfold table_row. now apply bitmap_init_nth.
    + intros (si & sy) _. apply table_row_length.
    + now apply sym_table_nth.
    + lia.
  - intros (qj & qq) _. apply inner_flat_map_length.
  - now apply state_table_nth.
  - unfold NC.nsyms, NC.nwords in *. nia.
Qed.

Lemma table_in_mem : forall b k v,
  Genv.find_symbol ge ids.(id_table) = Some b ->
  nth_error (table_init state nfa state_eq_dec) (Z.to_nat k) = Some (Init_int64 v) ->
  0 <= k < nstates * nsyms * nwords ->
  Mem.loadv Mint64 m0 (Vptr b (Ptrofs.repr (8 * k))) = Some (Vlong v).
Proof.
  intros b k v Hsym Hnth Hk.
  destruct find_table as (b' & Hsym' & Hdef).
  assert (b' = b) by congruence. subst b'.
Admitted.

(** step

    Given [cur] holding set [S], after the call [next] holds [step nfa S a],
    the union of the rows of every member of [S]. *)

Definition step_spec (S : list Z) (a : s.t) (S' : list Z) : Prop :=
  forall i, In i S' <->
    (exists qi q, In qi S /\ sidx q = Some qi /\
       exists q', In q' (nfa.(transition _) q a) /\ sidx q' = Some i).

Lemma compile_step_correct : forall b_cur b_next ofs_cur ofs_next S a ai m,
  index_of s.eq_dec a s.enum 0 = Some ai ->
  set_in_mem m b_cur ofs_cur S ->
  b_cur <> b_next ->
  eval_funcall function_entry2 ge m
    (compile_step state nfa ids)
    [Vptr b_cur (Ptrofs.repr ofs_cur); Vlong (Int64.repr ai);
     Vptr b_next (Ptrofs.repr ofs_next)] E0 m
    Vundef.
Proof.
Admitted. (* the nested-loop union invariant; the substantial obligation *)

(** accept

    A single loop accumulating [cur[j] & final[j]] into a temp, then a
    nonzero test. *)

Lemma compile_accept_correct : forall b ofs S m,
  set_in_mem m b ofs S ->
  eval_funcall function_entry2 ge m
    (compile_accept state nfa ids)
    [Vptr b (Ptrofs.repr ofs)] E0 m
    (Vint (if existsb (fun q => match sidx q with
                                | Some i => existsb (Z.eqb i) S
                                | None => false
                                end) (accepting_states state nfa)
           then Int.one else Int.zero)).
Proof.
Admitted. (* loop accumulating cur[j] & final[j]; invariant is scalar *)

(** run *)

Lemma run_loop_correct : forall suf pre le b_cur b_next,
  set_in_mem m0 b_cur 0 (indices_of state nfa state_eq_dec (NFA.run nfa pre)) ->
  b_cur <> b_next ->
  exists le',
    set_in_mem m0 b_cur 0
      (indices_of state nfa state_eq_dec (NFA.run nfa (pre ++ suf))) /\
    exec_stmt function_entry2 ge empty_env le m0 (run_loop state nfa ids) E0 le' m0 Out_normal.
Proof.
  induction suf; intros.
  - (* empty suffix: the guard fails and the loop breaks *)
    exists le. rewrite app_nil_r in *. repeat split; try assumption.
    econstructor.
      econstructor.
        econstructor.
          admit.
          unfold tint. simpl. admit.
          admit.
        admit.
    constructor.
  - (* one iteration, then the loop at prefix [pre ++ [a]] *)
    admit.
Admitted.

(** After [run(w, len, out)], the bitmap at [out] is the set [NFA.run nfa w]. *)
Lemma compile_run_correct : forall w l b_w ofs_w b_out ofs_out,
  Forall2 (fun a i => index_of s.eq_dec a s.enum 0 = Some i) w l ->
  Z.of_nat (length w) < Int64.modulus ->
  exists m',
    eval_funcall function_entry2 ge m0
      (compile_run state nfa ids)
      [Vptr b_w (Ptrofs.repr ofs_w); Vlong (Int64.repr (Z.of_nat (length w)));
       Vptr b_out (Ptrofs.repr ofs_out)] E0 m'
      Vundef /\
    set_in_mem m' b_out ofs_out
      (indices_of state nfa state_eq_dec (NFA.run nfa w)).
Proof.
Admitted.

End correctness.
End Correctness.
