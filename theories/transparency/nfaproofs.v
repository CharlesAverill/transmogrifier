From lstar Require Import automata.NFA.
From compcert Require Import AST Clight Ctypes Integers Cop Maps.
From compcert Require Import ClightBigstep Values Events Coqlib.
From compcert Require Import Globalenvs Memory Zbits.
From Transmogrifier.compiler Require Import nfa.
From Stdlib Require Import List ZArith Lia.
Import ListNotations.
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

Lemma word_of_indices_fold_high : forall idxs k b acc,
  64 <= b ->
  Z.testbit acc b = false ->
  Z.testbit
    (fold_left
      (fun acc i =>
         if andb (Z.leb (64 * k) i) (Z.ltb i (64 * (k + 1)))
         then Z.lor acc (Z.shiftl 1 (i - 64 * k))
         else acc)
      idxs acc) b
  = false.
Proof.
  induction idxs; intros k b acc Hb Hacc; cbn - [Z.mul].
    assumption.
  destruct (Z.leb (64 * k) a) eqn:El, (Z.ltb a (64 * (k + 1))) eqn:Eu;
    cbn - [Z.mul]; try (apply IHidxs; assumption).
  apply IHidxs; [assumption|].
  apply Z.leb_le in El. apply Z.ltb_lt in Eu.
  rewrite Z.lor_spec, Hacc, Z.shiftl_spec by lia. cbn - [Z.mul].
  change 1 with (2 ^ 0). apply Z.pow2_bits_false. lia.
Qed.
 
Lemma word_of_indices_high : forall idxs k b,
  64 <= b -> Z.testbit (word_of_indices idxs k) b = false.
Proof.
  intros idxs k b Hb. unfold word_of_indices.
  apply word_of_indices_fold_high; [assumption|].
  apply Z.testbit_0_l.
Qed.

Lemma word_of_indices_nonneg : forall idxs k,
  0 <= word_of_indices idxs k.
Proof.
  intros idxs k. unfold word_of_indices.
  assert (Hgen : forall l acc, 0 <= acc ->
    0 <= fold_left
      (fun acc i =>
         if andb (Z.leb (64 * k) i) (Z.ltb i (64 * (k + 1)))
         then Z.lor acc (Z.shiftl 1 (i - 64 * k))
         else acc) l acc).
  { induction l; intros acc Hacc; cbn - [Z.mul].
      assumption.
    destruct (Z.leb (64 * k) a), (Z.ltb a (64 * (k + 1)));
      cbn - [Z.mul]; try (apply IHl; assumption).
    apply IHl. apply Z.lor_nonneg. split. assumption.
    rewrite Z.shiftl_1_l.
    destruct (Z.leb 0 (a - 64 * k)) eqn:E.
      apply Z.leb_le in E. apply Z.pow_nonneg. lia.
    apply Z.leb_gt in E. rewrite Z.pow_neg_r by lia. lia. }
  apply Hgen. lia.
Qed.

Lemma word_of_indices_bound : forall idxs k,
  0 <= k ->
  0 <= word_of_indices idxs k < 2 ^ 64.
Proof.
  intros idxs k Hk.
  pose proof (word_of_indices_nonneg idxs k) as Hnn.
  split; [assumption|].
  (* [Ztestbit_le] against [2^64 - 1], whose low 64 bits are all set. *)
  assert (Hle : word_of_indices idxs k <= 2 ^ 64 - 1).
  { apply Ztestbit_le. lia.
    intros b Hb Htb.
    destruct (Z.ltb b 64) eqn:Eb.
    - apply Z.ltb_lt in Eb.
      (* bit b of 2^64-1 is set for b < 64 *)
      replace (2 ^ 64 - 1) with (Z.ones 64) by (rewrite Z.ones_equiv; lia).
      apply Z.ones_spec_low. lia.
    - apply Z.ltb_ge in Eb.
      rewrite word_of_indices_high in Htb by lia. discriminate. }
  lia.
Qed.

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
  - (* low bits: [word_of_indices_spec] on both sides, bridged by [Hext] *)
    apply Z.ltb_lt in Eb.
    destruct (Z.testbit (word_of_indices S1 k) b) eqn:E1,
             (Z.testbit (word_of_indices S2 k) b) eqn:E2; try reflexivity.
    + apply (word_of_indices_spec S1 k b Hk) in E1; [|lia].
      apply Hext in E1.
      apply (word_of_indices_spec S2 k b Hk) in E1; [|lia]. congruence.
    + apply (word_of_indices_spec S2 k b Hk) in E2; [|lia].
      apply Hext in E2.
      apply (word_of_indices_spec S1 k b Hk) in E2; [|lia]. congruence.
  - (* high bits: both are false, by [word_of_indices_high] *)
    apply Z.ltb_ge in Eb.
    rewrite !word_of_indices_high by lia. reflexivity.
Qed.

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

(** Loading the [n]th [Init_int64] of an all-int64 init list. *)
Lemma init_data_list_nth_load :
  forall (F V : Type) (ge' : Genv.t F V) b il n v m base_ofs,
  (forall id, In id il -> exists x, id = Init_int64 x) ->
  Genv.load_store_init_data ge' m b base_ofs il ->
  nth_error il n = Some (Init_int64 v) ->
  Mem.load Mint64 m b (base_ofs + 8 * Z.of_nat n) = Some (Vlong v).
Proof. clear.
  induction il; intros n v m base_ofs Hall Hlsid Hnth.
    now destruct n.
  destruct n; cbn - [Z.of_nat Z.mul] in *.
  - inversion Hnth; subst; clear Hnth.
    destruct Hlsid as (Hload & _).
    now rewrite Z.mul_0_r, Z.add_0_r.
  - destruct (Hall a) as (x & Hx); [now left|]. subst a.
    destruct Hlsid as (_ & Hrest). cbn - [Z.of_nat] in Hrest.
    replace (base_ofs + 8 * Z.of_nat (S n))
      with ((base_ofs + 8) + 8 * Z.of_nat n) by lia.
    eapply IHil; eauto.
Qed.

(** Every [bitmap_init] entry is an [Init_int64]. *)
Lemma bitmap_init_all_int64 : forall idxs id,
  In id (bitmap_init state nfa idxs) -> exists x, id = Init_int64 x.
Proof.
  intros idxs id H. unfold bitmap_init in H.
  apply in_map_iff in H as (k & Heq & _). subst. eauto.
Qed.

Lemma table_init_all_int64 : forall id,
  In id (table_init state nfa state_eq_dec) -> exists x, id = Init_int64 x.
Proof.
  intros id H. unfold table_init in H.
  apply in_flat_map in H as ((qi & q) & _ & Hin).
  apply in_flat_map in Hin as ((si & sy) & _ & Hin').
  unfold table_row in Hin'. eapply bitmap_init_all_int64. exact Hin'.
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
  assert (Hvi : Genv.find_var_info ge b = Some (compile_table state nfa state_eq_dec)).
    { apply Genv.find_var_info_iff. exact Hdef. }
  destruct (Genv.init_mem_characterization _ _ Hvi Hinit)
    as (_ & _ & Hlsid & _).
  specialize (Hlsid eq_refl).
  cbn [Mem.loadv].
  rewrite Ptrofs.unsigned_repr.
  - replace (8 * k) with (0 + 8 * Z.of_nat (Z.to_nat k)) by lia.
    eapply init_data_list_nth_load; eauto.
    apply table_init_all_int64.
  - (* the flattened bitmap table is [nwords] times wider than the Moore one,
       which is exactly what [table_bounded] accounts for *)
    unfold Ptrofs.max_unsigned.
    unfold NC.nstates, NC.nsyms, NC.nwords in *.
    pose proof table_bounded. lia.
Qed.

(** A set occupies [nwords] consecutive int64 slots at [b + ofs]. *)
Definition set_writable (m : mem) (b : block) (ofs : Z) : Prop :=
  Mem.range_perm m b ofs (ofs + 8 * nwords) Cur Writable.

(** The span a set occupies *)
Definition outside_set (b : block) (ofs : Z) : block -> Z -> Prop :=
  fun b' o => b' <> b \/ o < ofs \/ ofs + 8 * nwords <= o.

(** [next] holds the union of the [a]-rows of every state whose index is in [S]. *)
Definition step_set (S : list Z) (a : s.t) : list Z :=
  indices_of state nfa state_eq_dec
    (flat_map (fun q => nfa.(transition _) q a)
              (filter (fun q => match sidx q with
                                | Some i => existsb (Z.eqb i) S
                                | None => false
                                end)
                      nfa.(states _))).

Lemma in_indices_of : forall qs i,
  In i (indices_of state nfa state_eq_dec qs) <->
  (exists q, In q qs /\ sidx q = Some i).
Proof. exact indices_of_spec. Qed.

(** If [q] and [q'] are both in [states] and share an index, they are equal. *)
Lemma sidx_inj : forall q q' i,
  sidx q = Some i -> sidx q' = Some i -> q = q'.
Proof.
  intros q q' i H1 H2. unfold sidx, state_index in *.
  eapply index_of_inj; eauto.
Qed.

(** The filter recovers exactly the states of [qs], up to index-equivalence.
    A state of [states] whose index is in [indices_of qs] must be a state of
    [qs], by [sidx_inj]. *)
Lemma step_set_spec : forall qs a i,
  (forall q, In q qs -> In q nfa.(states _)) ->
  (In i (step_set (indices_of state nfa state_eq_dec qs) a)
   <-> In i (indices_of state nfa state_eq_dec
               (flat_map (fun q => nfa.(transition _) q a) qs))).
Proof.
  intros qs a i Hsub. unfold step_set.
  rewrite !in_indices_of.
  split.
  - (* left to right: the filtered state is in qs *)
    intros (q' & Hq' & Hi).
    apply in_flat_map in Hq' as (q & Hq & Htr).
    apply filter_In in Hq as (Hqst & Hfil).
    destruct (sidx q) as [j|] eqn:Ej; [|discriminate].
    apply existsb_exists in Hfil as (j' & Hj' & Heq).
    apply Z.eqb_eq in Heq. subst j'.
    apply in_indices_of in Hj' as (q0 & Hq0 & Hq0i).
    (* q and q0 share index j, and both are in states, so q = q0 *)
    assert (q = q0) by (eapply sidx_inj; eauto). subst q0.
    exists q'. split; [|exact Hi].
    apply in_flat_map. eauto.
  - (* right to left: every state of qs passes the filter *)
    intros (q' & Hq' & Hi).
    apply in_flat_map in Hq' as (q & Hq & Htr).
    destruct (sidx q) as [j|] eqn:Ej.
    + exists q'. split; [|exact Hi].
      apply in_flat_map. exists q. split; [|exact Htr].
      apply filter_In. split.
        now apply Hsub.
      rewrite Ej. apply existsb_exists. exists j.
      split; [|apply Z.eqb_refl].
      apply in_indices_of. eauto.
    + (* q is in qs, hence in states, hence has an index: contradiction *)
      exfalso.
      destruct (sidx_total q (Hsub q Hq)) as (j & Hj). congruence.
Qed.

(** step

    Given [cur] holding set [S], after the call [next] holds [step nfa S a],
    the union of the rows of every member of [S]. *)

(** Rows of the members of [S] whose index is below [bound]. At
    [bound >= nstates] this saturates to [step_set S a], which is what closes
    the outer loop. *)
Definition partial_step_set (S : list Z) (a : s.t) (bound : Z) : list Z :=
  indices_of state nfa state_eq_dec
    (flat_map (fun q => nfa.(transition _) q a)
              (filter (fun q => match sidx q with
                                | Some i => andb (existsb (Z.eqb i) S) (Z.ltb i bound)
                                | None => false
                                end)
                      nfa.(states _))).

Lemma round_up_to_64_ge : forall x : Z,
  x <= 64 * ((x + 63) / 64).
Proof.
  intros x.
  pose proof (Z_div_mod_eq_full (x + 63) 64) as H.
  rewrite Z.mul_comm.
  assert (H_mod : 0 <= (x + 63) mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  lia.
Qed.

(** The bitmap covers every state: [64 * nwords >= nstates]. This is what lets
    the outer loop's postcondition ([partial] at [64 * nwords]) saturate to the
    full [step_set]. Verified for the [Z] division in [nwords]. *)
Lemma nwords_covers : nstates <= 64 * nwords.
Proof.
  unfold NC.nwords, NC.nstates.
  destruct (Z.max_spec 1 ((Z.of_nat (length nfa.(states _)) + 63) / 64))
    as [(Hlt & Heq)|(Hge & Heq)]; rewrite Heq.
  - (* the max took 1, so (nstates+63)/64 < 1, i.e. nstates = 0 *)
    remember (Z.of_nat _) as x. apply round_up_to_64_ge.
  - (* the max took the quotient: nstates <= 64 * ((nstates+63)/64) *)
    pose proof (Z.mul_div_le (Z.of_nat (length nfa.(states _)) + 63) 64 ltac:(lia)).
    pose proof (Z.div_le_lower_bound
      (Z.of_nat (length nfa.(states _)) + 63) 64
      ((Z.of_nat (length nfa.(states _)) + 63) / 64) ltac:(lia)).
    (* 64 * ((n+63)/64) >= n follows since (n+63)/64 >= n/64 and the +63 pads *)
    assert (Hq : (Z.of_nat (length nfa.(states _)) + 63) / 64
                 >= Z.of_nat (length nfa.(states _)) / 64) by
      (apply Z.le_ge, Z.div_le_mono; lia).
    pose proof (Z.div_mod (Z.of_nat (length nfa.(states _)) + 63) 64 ltac:(lia)).
    pose proof (Z.mod_pos_bound (Z.of_nat (length nfa.(states _)) + 63) 64 ltac:(lia)).
    lia.
Qed.

(** Extending the bound past one more index adds exactly that index's row (when
    it is a member), which is what one iteration of the bit loop does. *)
Lemma partial_step_set_succ : forall S a bound i,
  0 <= bound ->
  (In i (partial_step_set S a (bound + 1)) <->
   In i (partial_step_set S a bound) \/
   (exists q, sidx q = Some bound /\ In bound S /\
              exists q', In q' (nfa.(transition _) q a) /\ sidx q' = Some i)).
Proof.
  intros S a bound i Hb. unfold partial_step_set.
  rewrite !in_indices_of. split.
  - intros (q' & Hq' & Hi).
    apply in_flat_map in Hq' as (q & Hq & Htr).
    apply filter_In in Hq as (Hqst & Hfil).
    destruct (sidx q) as [x|] eqn:Ex; [|discriminate].
    apply andb_true_iff in Hfil as (Hmem & Hlt).
    apply Z.ltb_lt in Hlt.
    destruct (Z.eq_dec x bound) as [->|Hne].
    + (* the new index *)
      right. exists q. split; [exact Ex|].
      split.
        apply existsb_exists in Hmem as (y & Hy & Hyq).
        apply Z.eqb_eq in Hyq. now subst y.
      exists q'. now split.
    + (* an old index *)
      left. exists q'. split; [|exact Hi].
      apply in_flat_map. exists q. split; [|exact Htr].
      apply filter_In. split; [exact Hqst|].
      rewrite Ex. apply andb_true_iff. split; [exact Hmem|].
      apply Z.ltb_lt. lia.
  - intros [(q' & Hq' & Hi) | (q & Hq & Hmem & q' & Htr & Hi)].
    + (* old indices survive the wider bound *)
      apply in_flat_map in Hq' as (q & Hq & Htr).
      apply filter_In in Hq as (Hqst & Hfil).
      destruct (sidx q) as [x|] eqn:Ex; [|discriminate].
      apply andb_true_iff in Hfil as (Hmem & Hlt).
      apply Z.ltb_lt in Hlt.
      exists q'. split; [|exact Hi].
      apply in_flat_map. exists q. split; [|exact Htr].
      apply filter_In. split; [exact Hqst|].
      rewrite Ex. apply andb_true_iff. split; [exact Hmem|].
      apply Z.ltb_lt. lia.
    + (* the new index is now in range *)
      exists q'. split; [|exact Hi].
      apply in_flat_map. exists q. split; [|exact Htr].
      apply filter_In. split.
        (* q has an index, so it is in states *)
        unfold sidx, state_index in Hq.
        destruct (In_dec state_eq_dec q nfa.(states _)) as [Hin|Hnin]; [exact Hin|].
        exfalso. clear -Hq Hnin.
        revert Hq Hnin. generalize 0 at 1.
        induction nfa.(states _); cbn; intros z Hq Hnin.
          discriminate.
        destruct state_eq_dec.
          subst. now apply Hnin; left.
        eapply IHl; eauto.
      rewrite Hq. apply andb_true_iff. split.
        apply existsb_exists. exists bound. split; [exact Hmem|apply Z.eqb_refl].
      apply Z.ltb_lt. lia.
Qed.

Lemma partial_step_set_saturate : forall S a bound i,
  nstates <= bound ->
  (In i (partial_step_set S a bound) <-> In i (step_set S a)).
Proof.
  intros S a bound i Hb. unfold partial_step_set, step_set.
  rewrite !in_indices_of. split.
  - intros (q' & Hq' & Hi).
    apply in_flat_map in Hq' as (q & Hq & Htr).
    apply filter_In in Hq as (Hqst & Hfil).
    destruct (sidx q) as [x|] eqn:Ex; [|discriminate].
    apply andb_true_iff in Hfil as (Hmem & _).
    exists q'. split; [|exact Hi].
    apply in_flat_map. exists q. split; [|exact Htr].
    apply filter_In. split; [exact Hqst|]. now rewrite Ex.
  - intros (q' & Hq' & Hi).
    apply in_flat_map in Hq' as (q & Hq & Htr).
    apply filter_In in Hq as (Hqst & Hfil).
    destruct (sidx q) as [x|] eqn:Ex; [|discriminate].
    exists q'. split; [|exact Hi].
    apply in_flat_map. exists q. split; [|exact Htr].
    apply filter_In. split; [exact Hqst|].
    rewrite Ex. apply andb_true_iff. split; [exact Hfil|].
    (* every state index is below nstates, hence below bound *)
    apply Z.ltb_lt. pose proof (sidx_bounds q x Ex). lia.
Qed.

(** A writable span admits a store at any of its words. *)
Lemma set_store_ok : forall m b ofs k v,
  set_writable m b ofs ->
  0 <= k < nwords ->
  0 <= ofs -> ofs + 8 * nwords < Ptrofs.modulus ->
  (align_chunk Mint64 | ofs + 8 * k) ->
  exists m', Mem.storev Mint64 m (Vptr b (Ptrofs.repr (ofs + 8 * k))) (Vlong v) = Some m'.
Proof.
  intros m b ofs k v Hw Hk Hofs Hlt Halign.
  unfold set_writable in Hw.
  cbn [Mem.storev]. rewrite Ptrofs.unsigned_repr by
    (unfold Ptrofs.max_unsigned; lia).
  pose proof (Mem.valid_access_store m Mint64 b (ofs + 8 * k) (Vlong v)).
  destruct X.
    constructor; [|assumption]. 
    intros o Ho. apply Hw. cbn [size_chunk] in Ho. lia.
  now exists x.
Qed.

(** Storing into word [k] leaves the other words of the span alone. *)
Lemma set_store_other : forall m m' b ofs k k' v,
  Mem.storev Mint64 m (Vptr b (Ptrofs.repr (ofs + 8 * k))) (Vlong v) = Some m' ->
  0 <= k < nwords -> 0 <= k' < nwords -> k <> k' ->
  0 <= ofs -> ofs + 8 * nwords < Ptrofs.modulus ->
  Mem.loadv Mint64 m' (Vptr b (Ptrofs.repr (ofs + 8 * k')))
  = Mem.loadv Mint64 m (Vptr b (Ptrofs.repr (ofs + 8 * k'))).
Proof.
  intros m m' b ofs k k' v Hst Hk Hk' Hne Hofs Hlt.
  cbn [Mem.storev] in Hst. cbn [Mem.loadv].
  rewrite !Ptrofs.unsigned_repr in * by (unfold Ptrofs.max_unsigned; lia).
  eapply Mem.load_store_other; eauto. cbn [size_chunk]. lia.
Qed.

Lemma set_store_same : forall m m' b ofs k v,
  Mem.storev Mint64 m (Vptr b (Ptrofs.repr (ofs + 8 * k))) (Vlong v) = Some m' ->
  Mem.loadv Mint64 m' (Vptr b (Ptrofs.repr (ofs + 8 * k))) = Some (Vlong v).
Proof.
  intros m m' b ofs k v Hst.
  cbn [Mem.storev] in Hst. cbn [Mem.loadv].
  erewrite Mem.load_store_same by eauto. reflexivity.
Qed.

(** A store inside the span is [unchanged_on] everything outside it. *)
Lemma set_store_unchanged : forall m m' b ofs k v,
  Mem.storev Mint64 m (Vptr b (Ptrofs.repr (ofs + 8 * k))) (Vlong v) = Some m' ->
  0 <= k < nwords -> 0 <= ofs -> ofs + 8 * nwords < Ptrofs.modulus ->
  Mem.unchanged_on (outside_set b ofs) m m'.
Proof.
  intros m m' b ofs k v Hst Hk Hofs Hlt.
  cbn [Mem.storev] in Hst.
  rewrite Ptrofs.unsigned_repr in Hst by (unfold Ptrofs.max_unsigned; lia).
  eapply Mem.store_unchanged_on; eauto.
  intros o Ho Hout. unfold outside_set in Hout.
  cbn [size_chunk] in Ho.
  destruct Hout as [Hb|[Hlo|Hhi]]; [congruence|lia|lia].
Qed.

(** Writability survives a store. *)
Lemma set_writable_store : forall m m' b ofs b' ofs' k v,
  Mem.storev Mint64 m (Vptr b' (Ptrofs.repr (ofs' + 8 * k))) (Vlong v) = Some m' ->
  set_writable m b ofs ->
  set_writable m' b ofs.
Proof.
  intros m m' b ofs b' ofs' k v Hst Hw o Ho.
  cbn [Mem.storev] in Hst.
  eapply Mem.perm_store_1; eauto.
Qed.

(** A span is well-formed when it sits at a nonnegative, 8-aligned offset and
    does not wrap. Every set-valued pointer crossing these lemmas carries it. *)
Definition set_span_ok (ofs : Z) : Prop :=
  0 <= ofs /\ (8 | ofs) /\ ofs + 8 * nwords < Ptrofs.modulus.

Lemma span_align : forall ofs k,
  set_span_ok ofs -> 0 <= k -> (align_chunk Mint64 | ofs + 8 * k).
Proof.
  intros ofs k (Hofs & Hdiv & Hlt) Hk. cbn [align_chunk].
  destruct Hdiv as (c & ->). exists (c + k). lia.
Qed.

Lemma nwords_pos : 0 < nwords.
Proof.
  unfold NC.nwords. pose proof (Z.le_max_l 1 ((Z.of_nat (length nfa.(states _)) + 63) / 64)). lia.
Qed.

Lemma eval_lt_test_gen : forall e le m v j k bv,
  le ! v = Some (Vlong (Int64.repr j)) ->
  0 <= j < Int64.modulus -> 0 <= k < Int64.modulus ->
  bv = (if j <? k then Int.one else Int.zero) ->
  eval_expr ge e le m (lt_test v k) (Vint bv).
Proof.
  intros. unfold lt_test. econstructor.
    econstructor. eassumption.
    econstructor.
  cbn. unfold sem_cmp, classify_cmp, tlong, sem_binarith, sem_cast,
              classify_cast, classify_binarith. cbn.
  destruct Archi.ptr64; cbn;
    unfold Val.of_bool, Int64.ltu;
    repeat rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; lia);
    subst; destruct (zlt j k), (j <? k) eqn:E; reflexivity || lia.
Qed.

Lemma bool_val_zero_int : forall m, bool_val (Vint Int.zero) tint m = Some false.
Proof.
  intros m. unfold bool_val, tint. cbn.
  destruct Archi.ptr64; cbn; rewrite Int.eq_true; reflexivity.
Qed.

Lemma bool_val_one_int : forall m, bool_val (Vint Int.one) tint m = Some true.
Proof.
  intros m. unfold bool_val, tint. cbn.
  destruct Archi.ptr64; cbn;
    rewrite Int.eq_false by apply Int.one_not_zero; reflexivity.
Qed.

Lemma nwords_bounded :
  0 <= nwords < Int64.modulus.
Proof.
  unfold nwords. split.
    transitivity 1. now compute.
    apply Z.le_max_l.
  apply Z.max_lub_lt. lia.
  pose proof table_bounded.
  change Ptrofs.modulus with 18446744073709551616 in H.
  destruct (Z.eq_dec nstates 0). rewrite e.
    now compute.
  change Int64.modulus with 18446744073709551616.
  unfold nsyms, nwords, nstates in H |- *.
  set (L := Z.of_nat (Datatypes.length (states state nfa))) in *.
  set (S := Z.of_nat (Datatypes.length s.enum)) in *.
  set (W := (L + 63) / 64) in *.
  assert (HL_pos : 0 <= L) by (subst L; lia).
  assert (HS_pos : 0 <= S) by (subst S; lia).
  assert (HS_ge_1 : S >= 1).
    pose proof syms_bounded. unfold S in *.
    lia.
  lia.
Qed.

(** The word-zeroing loop, generalized over the starting counter [j0].
    The induction is on [Z.to_nat (nwords - j0)] as fuel: [exec_Sloop_loop]
    recurses on the same [Sloop], so there is no structural measure. *)
Lemma zero_next_loop_correct : forall fuel j0 le m b_next ofs_next,
  (Z.to_nat (nwords - j0) <= fuel)%nat ->
  0 <= j0 <= nwords ->
  set_span_ok ofs_next ->
  le ! (ids.(id_next)) = Some (Vptr b_next (Ptrofs.repr ofs_next)) ->
  le ! (ids.(id_j)) = Some (Vlong (Int64.repr j0)) ->
  set_writable m b_next ofs_next ->
  exists le' m',
    exec_stmt function_entry2 ge empty_env le m
      (Sloop
        (Ssequence
          (Sifthenelse (lt_test ids.(id_j) nwords) Sskip Sbreak)
          (Sassign (idx (Etempvar ids.(id_next) tsetptr) (Etempvar ids.(id_j) tlong))
                   (const 0)))
        (Sset ids.(id_j)
          (Ebinop Oadd (Etempvar ids.(id_j) tlong) (const 1) tlong)))
      E0 le' m' Out_normal /\
    (forall k, j0 <= k < nwords ->
       Mem.loadv Mint64 m' (Vptr b_next (Ptrofs.repr (ofs_next + 8 * k)))
         = Some (Vlong Int64.zero)) /\
    (forall k, 0 <= k < j0 ->
       Mem.loadv Mint64 m' (Vptr b_next (Ptrofs.repr (ofs_next + 8 * k)))
       = Mem.loadv Mint64 m (Vptr b_next (Ptrofs.repr (ofs_next + 8 * k)))) /\
    set_writable m' b_next ofs_next /\
    (forall i v, i <> ids.(id_j) -> le ! i = Some v -> le' ! i = Some v) /\
    Mem.unchanged_on (outside_set b_next ofs_next) m m'.
Proof.
  induction fuel; intros j0 le m b_next ofs_next Hfuel Hj0 Hspan Hnext Hj Hw;
  pose proof nwords_bounded as NWB.
  - (* fuel exhausted forces j0 = nwords: the guard fails and the loop stops *)
    assert (j0 = nwords) by lia. subst j0.
    exists le, m. split; [|split; [|split; [|split; [|split]]]].
    + eapply exec_Sloop_stop1.
      * eapply exec_Sseq_2.
        eapply exec_Sifthenelse.
        -- eapply eval_lt_test_gen with (bv := Int.zero); eauto.
           now rewrite Z.ltb_irrefl.
        -- apply bool_val_zero_int.
        -- constructor.
        -- discriminate.
      * constructor.
    + intros k Hk. lia.
    + intros k Hk. reflexivity.
    + exact Hw.
    + intros i v _ Hv. exact Hv.
    + apply Mem.unchanged_on_refl.
  - (* one iteration or the guard fails *)
    destruct (Z.eq_dec j0 nwords) as [->|Hne].
    + (* same as the base case *)
      exists le, m. split; [|split; [|split; [|split; [|split]]]].
      * eapply exec_Sloop_stop1.
        -- eapply exec_Sseq_2.
           eapply exec_Sifthenelse.
           ++ eapply eval_lt_test_gen with (bv := Int.zero); eauto.
              now rewrite Z.ltb_irrefl.
           ++ apply bool_val_zero_int.
           ++ constructor.
           ++ discriminate.
        -- constructor.
      * intros k Hk. lia.
      * intros k Hk. reflexivity.
      * exact Hw.
      * intros i v _ Hv. exact Hv.
      * apply Mem.unchanged_on_refl.
    + (* j0 < nwords: store zero into word j0, then recurse at j0 + 1 *)
      assert (Hlt : j0 < nwords) by lia.
      destruct (set_store_ok m b_next ofs_next j0 Int64.zero Hw
                  ltac:(lia) (proj1 Hspan)
                  ltac:(destruct Hspan as (_&_&H); exact H)
                  (span_align ofs_next j0 Hspan ltac:(lia)))
        as (m1 & Hst).
      set (le1 := PTree.set ids.(id_j)
                    (Vlong (Int64.repr (j0 + 1))) le).
      destruct (IHfuel (j0 + 1) le1 m1 b_next ofs_next)
        as (le' & m' & Hexec & Hzero & Hold & Hw' & Htmp & Hunch); try lia.
      * exact Hspan.
      * unfold le1. rewrite PTree.gso by
          (cbv [ids alloc_idents id_next id_j]; lia). exact Hnext.
      * unfold le1. now rewrite PTree.gss.
      * eapply set_writable_store; eauto.
      * exists le', m'. split; [|split; [|split; [|split; [|split]]]].
        -- change E0 with (E0 ** E0 ** E0). eapply exec_Sloop_loop.
           ++ (* guard true, then the store *)
              change E0 with (E0 ** E0). eapply exec_Sseq_1.
              ** eapply exec_Sifthenelse.
                 --- eapply eval_lt_test_gen with (bv := Int.one); eauto.
                       split. lia.
                       apply Z.lt_le_trans with (m := nwords). assumption.
                       lia.
                     now rewrite (proj2 (Z.ltb_lt _ _)) by lia.
                 --- apply bool_val_one_int.
                 --- constructor.
              ** (* Sassign next[j0] = 0 *)
                 eapply exec_Sassign.
                 --- (* lvalue: Ederef (next + j0) *)
                     econstructor. econstructor.
                     +++ econstructor. exact Hnext.
                     +++ econstructor. eassumption.
                     +++ cbn. unfold sem_add, classify_add, tsetptr, tlong. cbn.
                         destruct Archi.ptr64 eqn:Eptr; cbn; [|discriminate].
                         unfold Ptrofs.of_int64. reflexivity.
                 --- econstructor.
                 --- cbn. unfold sem_cast, classify_cast, tlong. cbn.
                     destruct Archi.ptr64; reflexivity.
                 --- eapply assign_loc_value; [reflexivity|].
                     (* the pointer arithmetic lands on ofs_next + 8*j0 *)
                     replace (Ptrofs.add (Ptrofs.repr ofs_next)
                                (Ptrofs.mul (Ptrofs.repr (sizeof ge tlong))
                                            (Ptrofs.of_int64 (Int64.repr j0))))
                       with (Ptrofs.repr (ofs_next + 8 * j0)).
                     +++ admit.
                     +++ unfold Ptrofs.of_int64, Ptrofs.mul, Ptrofs.add.
                         cbn [sizeof].
                         rewrite !Ptrofs.unsigned_repr_eq, Int64.unsigned_repr.
                         apply Ptrofs.eqm_samerepr.
                         unfold Ptrofs.eqm, eqmod. exists 0.
                          rewrite Z.mul_0_l, Z.add_0_l. admit.
                         split. lia. apply Zsucc_le_reg.
                         change (Z.succ Int64.max_unsigned) with Int64.modulus.
                         apply Zlt_le_succ. lia.
           ++ constructor.
           ++ (* the increment *)
              unfold le1. eapply exec_Sset.
              econstructor.
              ** econstructor. exact Hj.
              ** econstructor.
              ** cbn. unfold sem_add, classify_add, tlong, sem_binarith,
                        sem_cast, classify_cast, classify_binarith. cbn.
                 destruct Archi.ptr64; cbn; do 2 f_equal;
                   now rewrite Int64.add_unsigned, !Int64.unsigned_repr_eq,
                     Zplus_mod_idemp_l, Zplus_mod_idemp_r.
           ++ admit.
        -- (* words [j0, nwords) are zero: j0 by the store, the rest by IH *)
           intros k Hk.
           destruct (Z.eq_dec k j0) as [->|Hkne].
           ++ rewrite Hold by lia. eapply set_store_same; eauto.
           ++ apply Hzero. lia.
        -- (* words below j0 untouched: IH plus the store landing elsewhere *)
           intros k Hk. rewrite Hold by lia.
           eapply set_store_other; eauto; try lia;
             [exact (proj1 Hspan) | destruct Hspan as (_&_&H); exact H].
        -- exact Hw'.
        -- (* the only temp this iteration sets is id_j *)
           intros i v Hij Hv. apply Htmp; [exact Hij|].
           unfold le1. rewrite PTree.gso by (intro; congruence). exact Hv.
        -- eapply Mem.unchanged_on_trans; [|exact Hunch].
           eapply set_store_unchanged; eauto; try lia;
             [exact (proj1 Hspan) | destruct Hspan as (_&_&H); exact H].
Admitted.

Lemma zero_next_correct : forall le m b_next ofs_next,
  set_span_ok ofs_next ->
  le ! (ids.(id_next)) = Some (Vptr b_next (Ptrofs.repr ofs_next)) ->
  set_writable m b_next ofs_next ->
  exists le' m',
    exec_stmt function_entry2 ge empty_env le m (zero_next state nfa ids) E0 le' m' Out_normal /\
    set_in_mem m' b_next ofs_next [] /\
    set_writable m' b_next ofs_next /\
    (forall i v, i <> ids.(id_j) -> le ! i = Some v -> le' ! i = Some v) /\
    Mem.unchanged_on (outside_set b_next ofs_next) m m'.
Proof.
  intros le m b_next ofs_next Hspan Hnext Hw.
  set (le0 := PTree.set ids.(id_j) (Vlong (Int64.repr 0)) le).
  destruct (zero_next_loop_correct (Z.to_nat nwords) 0 le0 m b_next ofs_next)
    as (le' & m' & Hexec & Hzero & _ & Hw' & Htmp & Hunch); try lia.
  - pose proof nwords_pos. lia.
  - admit.
  - unfold le0. rewrite PTree.gso by
      (cbv [ids alloc_idents id_next id_j]; lia). exact Hnext.
  - unfold le0. now rewrite PTree.gss.
  - exact Hw.
  - exists le', m'. split; [|split; [|split; [|split]]].
    + unfold zero_next. change E0 with (E0 ** E0). eapply exec_Sseq_1; [|exact Hexec].
      eapply exec_Sset. econstructor.
    + (* the empty bitmap is all-zero words *)
      intros k Hk. rewrite Hzero by lia.
      rewrite word_of_indices_nil. reflexivity.
    + exact Hw'.
    + (* id_j is the only temp zero_next writes *)
      intros i v Hij Hv. apply Htmp; [exact Hij|].
      unfold le0. rewrite PTree.gso by (intro; congruence). exact Hv.
    + exact Hunch.
Admitted.

(** The table row for the state at global index [gi], as an index list. *)
Definition row_of (gi : Z) (a : s.t) : list Z :=
  match nth_error nfa.(states _) (Z.to_nat gi) with
  | Some q => indices_of state nfa state_eq_dec (nfa.(transition _) q a)
  | None => []
  end.

(** Word [j] of the row lives at flat table index [(gi*nsyms+ai)*nwords+j], and
    [table_row_correct] + [table_in_mem] say what is there. *)
Lemma table_row_load : forall b_tab gi ai a j,
  Genv.find_symbol ge ids.(id_table) = Some b_tab ->
  0 <= gi < nstates ->
  index_of s.eq_dec a s.enum 0 = Some ai ->
  0 <= j < nwords ->
  (exists q, nth_error nfa.(states _) (Z.to_nat gi) = Some q /\ sidx q = Some gi) ->
  Mem.loadv Mint64 m0 (Vptr b_tab (Ptrofs.repr (8 * ((gi * nsyms + ai) * nwords + j))))
  = Some (Vlong (Int64.repr (word_of_indices (row_of gi a) j))).
Proof.
  intros b_tab gi ai a j Hsym Hgi Ha Hj (q & Hnth & Hq).
  unfold row_of. rewrite Hnth.
  eapply table_in_mem; eauto.
  - eapply table_row_correct; eauto.
  - (* the flat index is in range *)
    pose proof nwords_pos.
    assert (0 <= ai < nsyms) by (apply index_of_bounds in Ha; unfold NC.nsyms; lia).
    split.
    + assert (H_nsyms_pos : 0 <= nsyms) by lia.
      assert (H_gi_nsyms_pos : 0 <= gi * nsyms).
      { apply Z.mul_nonneg_nonneg; lia. }
      assert (H_inner_pos : 0 <= gi * nsyms + ai) by lia.
      assert (H_mul_pos : 0 <= (gi * nsyms + ai) * nwords).
      { apply Z.mul_nonneg_nonneg; lia. }
      lia.
    + assert (H_dim12 : gi * nsyms + ai < nstates * nsyms).
      {
        assert (ai <= nsyms - 1) by lia.
        assert (gi <= nstates - 1) by lia.
        nia.
      }
      assert (H_dim3 : (gi * nsyms + ai) * nwords + j < (nstates * nsyms) * nwords).
      {
        assert (j <= nwords - 1) by lia.
        assert (gi * nsyms + ai <= nstates * nsyms - 1) by lia.
        nia.
      }
      replace (nstates * nsyms * nwords) with ((nstates * nsyms) * nwords) by ring.
      exact H_dim3.
Qed.

(** The row-union loop, generalized over [j0] exactly as [zero_next_loop]. *)
Lemma union_row_loop_correct : forall fuel j0 le m b_next ofs_next b_tab gi ai a S,
  (Z.to_nat (nwords - j0) <= fuel)%nat ->
  0 <= j0 <= nwords ->
  set_span_ok ofs_next ->
  Genv.find_symbol ge ids.(id_table) = Some b_tab ->
  0 <= gi < nstates ->
  index_of s.eq_dec a s.enum 0 = Some ai ->
  (exists q, nth_error nfa.(states _) (Z.to_nat gi) = Some q /\ sidx q = Some gi) ->
  b_next <> b_tab ->
  m = m0 ->
  le ! (ids.(id_next)) = Some (Vptr b_next (Ptrofs.repr ofs_next)) ->
  le ! (ids.(id_j)) = Some (Vlong (Int64.repr j0)) ->
  le ! (ids.(id_k)) = Some (Vlong (Int64.repr (gi / 64))) ->
  le ! (ids.(id_q)) = Some (Vlong (Int64.repr (gi mod 64))) ->
  le ! (ids.(id_s)) = Some (Vlong (Int64.repr ai)) ->
  (forall k, 0 <= k < j0 ->
     Mem.loadv Mint64 m (Vptr b_next (Ptrofs.repr (ofs_next + 8 * k)))
     = Some (Vlong (Int64.repr (word_of_indices (S ++ row_of gi a) k)))) ->
  (forall k, j0 <= k < nwords ->
     Mem.loadv Mint64 m (Vptr b_next (Ptrofs.repr (ofs_next + 8 * k)))
     = Some (Vlong (Int64.repr (word_of_indices S k)))) ->
  set_writable m b_next ofs_next ->
  exists le' m',
    exec_stmt function_entry2 ge empty_env le m (union_row state nfa ids) E0 le' m' Out_normal /\
    set_in_mem m' b_next ofs_next (S ++ row_of gi a) /\
    set_writable m' b_next ofs_next /\
    Mem.unchanged_on (outside_set b_next ofs_next) m m'.
Proof.
Admitted. (* Same fuel induction as zero_next_loop_correct: each iteration loads
             next[j] (the S-word) and table[(gi*nsyms+ai)*nwords+j] (the row-word,
             by table_row_load), stores their Z.lor, and word_of_indices_app turns
             that into the union. The only new ingredient over zero_next_loop is
             the second load and the address arithmetic for the table, which is
             the same Ptrofs.eqm_samerepr step. Blocked only on the eval_expr
             chain for the four-deep Ebinop index expression. *)
 
Lemma union_row_correct : forall le m b_next ofs_next b_tab gi ai k q S a,
  Genv.find_symbol ge ids.(id_table) = Some b_tab ->
  gi = 64 * k + q ->
  0 <= gi < nstates ->
  0 <= q < 64 ->
  set_span_ok ofs_next ->
  index_of s.eq_dec a s.enum 0 = Some ai ->
  (exists q_st, nth_error nfa.(states _) (Z.to_nat gi) = Some q_st /\ sidx q_st = Some gi) ->
  m = m0 ->
  le ! (ids.(id_next)) = Some (Vptr b_next (Ptrofs.repr ofs_next)) ->
  le ! (ids.(id_k)) = Some (Vlong (Int64.repr k)) ->
  le ! (ids.(id_q)) = Some (Vlong (Int64.repr q)) ->
  le ! (ids.(id_s)) = Some (Vlong (Int64.repr ai)) ->
  set_in_mem m b_next ofs_next S ->
  set_writable m b_next ofs_next ->
  b_next <> b_tab ->
  exists le' m',
    exec_stmt function_entry2 ge empty_env le m (union_row state nfa ids) E0 le' m' Out_normal /\
    set_in_mem m' b_next ofs_next (S ++ row_of gi a) /\
    set_writable m' b_next ofs_next /\
    Mem.unchanged_on (outside_set b_next ofs_next) m m'.
Proof.
  intros le m b_next ofs_next b_tab gi ai k q S a
         Hsym Hgi Hrange Hq64 Hspan Ha Hst Hm Hnext Hk Hqq Hs Hset Hw Hne.
  set (le0 := PTree.set ids.(id_j) (Vlong (Int64.repr 0)) le).
  eapply union_row_loop_correct with (fuel := Z.to_nat nwords) (j0 := 0)
    (b_tab := b_tab) (gi := gi) (ai := ai); try assumption; try lia.
  pose proof nwords_pos. lia. all: admit.
Admitted.

(** [word_of_indices] of an append is the [lor] of the two words. *)
Lemma word_of_indices_app : forall S1 S2 k,
  0 <= k ->
  word_of_indices (S1 ++ S2) k
  = Z.lor (word_of_indices S1 k) (word_of_indices S2 k).
Proof.
  intros S1 S2 k Hk.
  apply Z.bits_inj'. intros b Hb.
  destruct (Z.ltb b 64) eqn:Eb.
  - apply Z.ltb_lt in Eb.
    rewrite Z.lor_spec.
    (* both sides are membership tests, and In distributes over ++ *)
    destruct (Z.testbit (word_of_indices (S1 ++ S2) k) b) eqn:E.
    + apply (word_of_indices_spec _ k b Hk) in E; [|lia].
      apply in_app_or in E as [E|E];
        [ apply (word_of_indices_spec S1 k b Hk) in E; [|lia]
        | apply (word_of_indices_spec S2 k b Hk) in E; [|lia] ];
        rewrite E; [now rewrite orb_true_l| now rewrite orb_true_r].
    + (* not in the append: in neither *)
      assert (H1 : Z.testbit (word_of_indices S1 k) b = false).
      { destruct (Z.testbit (word_of_indices S1 k) b) eqn:E1; [|reflexivity].
        apply (word_of_indices_spec S1 k b Hk) in E1; [|lia].
        exfalso. admit. }
      assert (H2 : Z.testbit (word_of_indices S2 k) b = false).
      { destruct (Z.testbit (word_of_indices S2 k) b) eqn:E2; [|reflexivity].
        apply (word_of_indices_spec S2 k b Hk) in E2; [|lia].
        exfalso. admit. }
      now rewrite H1, H2.
  - apply Z.ltb_ge in Eb.
    rewrite Z.lor_spec, !word_of_indices_high by lia. reflexivity.
Admitted.

(** The bit test [word & (1 << q)] is nonzero exactly when index [64*k+q] is in
    the set that [word] encodes -- this is [word_of_indices_spec] read through
    the emitted expression. *)
Lemma bit_test_spec : forall S k q,
  0 <= k -> 0 <= q < 64 ->
  (Z.land (word_of_indices S k) (Z.shiftl 1 q) <> 0 <-> In (64 * k + q) S).
Proof.
  intros S k q Hk Hq.
  rewrite <- word_of_indices_spec by assumption.
  split.
  - intros Hne.
    destruct (Z.testbit (word_of_indices S k) q) eqn:E; [reflexivity|].
    exfalso. apply Hne.
    apply Z.bits_inj'. intros b Hb.
    rewrite Z.land_spec, Z.testbit_0_l, Z.shiftl_spec by lia.
    destruct (Z.eq_dec b q) as [->|Hne'].
      rewrite E. reflexivity.
    replace (Z.testbit 1 (b - q)) with false.
      now rewrite andb_false_r.
    symmetry. destruct (Z.ltb (b - q) 0) eqn:Eneg.
      apply Z.ltb_lt in Eneg. now apply Z.testbit_neg_r.
    apply Z.ltb_ge in Eneg. change 1 with (2 ^ 0).
    apply Z.pow2_bits_false. lia.
  - intros Htb Hz.
    assert (Z.testbit (Z.land (word_of_indices S k) (Z.shiftl 1 q)) q = true).
    { rewrite Z.land_spec, Z.shiftl_spec by lia.
      rewrite Htb, Z.sub_diag, Z.bit0_odd. reflexivity. }
    rewrite Hz, Z.testbit_0_l in H. discriminate.
Qed.

(** The inner loop: scan the 64 bits of [word], unioning each set, in-range
    state's row into [next]. Generalized over [q0]; the invariant is that [next]
    holds [partial_step_set S a (64*k + q0)]. *)
Lemma scan_bits_correct : forall fuel q0 le m b_next ofs_next b_tab k S a ai,
  (Z.to_nat (64 - q0) <= fuel)%nat ->
  0 <= q0 <= 64 ->
  0 <= k < nwords ->
  set_span_ok ofs_next ->
  Genv.find_symbol ge ids.(id_table) = Some b_tab ->
  index_of s.eq_dec a s.enum 0 = Some ai ->
  m = m0 ->
  b_next <> b_tab ->
  le ! (ids.(id_next)) = Some (Vptr b_next (Ptrofs.repr ofs_next)) ->
  le ! (ids.(id_k)) = Some (Vlong (Int64.repr k)) ->
  le ! (ids.(id_q)) = Some (Vlong (Int64.repr q0)) ->
  le ! (ids.(id_s)) = Some (Vlong (Int64.repr ai)) ->
  le ! (ids.(id_word)) = Some (Vlong (Int64.repr (word_of_indices S k))) ->
  set_in_mem m b_next ofs_next (partial_step_set S a (64 * k + q0)) ->
  set_writable m b_next ofs_next ->
  exists le' m',
    exec_stmt function_entry2 ge empty_env le m
      (Sloop
        (Ssequence
          (Sifthenelse (lt_test ids.(id_q) 64) Sskip Sbreak)
          (Sifthenelse
            (Ebinop One
              (Ebinop Oand (Etempvar ids.(id_word) tlong)
                (Ebinop Oshl (const 1) (Etempvar ids.(id_q) tlong) tlong) tlong)
              (const 0) tint)
            (Sifthenelse
              (Ebinop Olt
                (Ebinop Oadd
                  (Ebinop Omul (Etempvar ids.(id_k) tlong) (const 64) tlong)
                  (Etempvar ids.(id_q) tlong) tlong)
                (const nstates) tint)
              (union_row state nfa ids) Sskip)
            Sskip))
        (Sset ids.(id_q)
          (Ebinop Oadd (Etempvar ids.(id_q) tlong) (const 1) tlong)))
      E0 le' m' Out_normal /\
    set_in_mem m' b_next ofs_next (partial_step_set S a (64 * (k + 1))) /\
    set_writable m' b_next ofs_next /\
    Mem.unchanged_on (outside_set b_next ofs_next) m m'.
Proof.
Admitted. (* Fuel induction on Z.to_nat (64 - q0), same shape as
             zero_next_loop_correct. Per iteration, three cases:
               - bit clear  -> Sskip; invariant extends by partial_step_set_succ
                               (the new index is not in S, so no row is added)
               - bit set, 64*k+q >= nstates -> Sskip; the index is not a state,
                               so partial_step_set_succ again adds nothing
               - bit set, in range -> union_row_correct, then
                               partial_step_set_succ + set_in_mem_ext to move
                               from (S ++ row_of gi a) to the partial at q0+1
             bit_test_spec is what connects the emitted Ebinop Oand test to
             membership in S. Base case q0 = 64 closes since
             64*k + 64 = 64*(k+1). *)
 
(** The outer loop: for each word [k] of [cur], load it and scan its bits.
    Generalized over [k0]; the invariant is [partial_step_set S a (64*k0)]. *)
Lemma scan_words_correct : forall fuel k0 le m b_cur ofs_cur b_next ofs_next b_tab S a ai,
  (Z.to_nat (nwords - k0) <= fuel)%nat ->
  0 <= k0 <= nwords ->
  set_span_ok ofs_cur -> set_span_ok ofs_next ->
  Genv.find_symbol ge ids.(id_table) = Some b_tab ->
  index_of s.eq_dec a s.enum 0 = Some ai ->
  m = m0 ->
  b_cur <> b_next -> b_next <> b_tab ->
  le ! (ids.(id_cur)) = Some (Vptr b_cur (Ptrofs.repr ofs_cur)) ->
  le ! (ids.(id_next)) = Some (Vptr b_next (Ptrofs.repr ofs_next)) ->
  le ! (ids.(id_k)) = Some (Vlong (Int64.repr k0)) ->
  le ! (ids.(id_s)) = Some (Vlong (Int64.repr ai)) ->
  set_in_mem m b_cur ofs_cur S ->
  set_in_mem m b_next ofs_next (partial_step_set S a (64 * k0)) ->
  set_writable m b_next ofs_next ->
  exists le' m',
    exec_stmt function_entry2 ge empty_env le m
      (Sloop
          (Ssequence
            (Sifthenelse (lt_test ids.(id_k) nwords) Sskip Sbreak)
            (Ssequence
              (Sset ids.(id_word)
                (idx (Etempvar ids.(id_cur) tsetptr) (Etempvar ids.(id_k) tlong)))
              (* OPTIMIZATION 1: Skip entirely empty words immediately *)
              (Sifthenelse (Ebinop Oeq (Etempvar ids.(id_word) tlong) (const 0) tint)
                Scontinue
                (Ssequence
                  (Sset ids.(id_q) (const 0))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (lt_test ids.(id_q) 64) Sskip Sbreak)
                      (Ssequence
                        (* OPTIMIZATION 2: Early exit when remaining bits are all zero *)
                        (Sifthenelse (Ebinop Oeq (Etempvar ids.(id_word) tlong) (const 0) tint)
                          Sbreak
                          Sskip)
                        (Sifthenelse
                          (* OPTIMIZATION 3: Check lowest bit instead of shifting (1 << q) *)
                          (Ebinop One
                            (Ebinop Oand (Etempvar ids.(id_word) tlong) (const 1) tlong)
                            (const 0) tint)
                          (Sifthenelse
                            (Ebinop Olt
                              (Ebinop Oadd
                                (Ebinop Omul (Etempvar ids.(id_k) tlong) (const 64) tlong)
                                (Etempvar ids.(id_q) tlong) tlong)
                              (const nstates) tint)
                            (union_row state nfa ids)
                            Sskip)
                          Sskip)))
                    (Ssequence
                      (Sset ids.(id_q)
                        (Ebinop Oadd (Etempvar ids.(id_q) tlong) (const 1) tlong))
                      (* OPTIMIZATION 4: Shift word right by 1 every iteration *)
                      (Sset ids.(id_word)
                        (Ebinop Oshr (Etempvar ids.(id_word) tlong) (const 1) tlong))))))))
          (Sset ids.(id_k)
            (Ebinop Oadd (Etempvar ids.(id_k) tlong) (const 1) tlong)))
      E0 le' m' Out_normal /\
    set_in_mem m' b_next ofs_next (partial_step_set S a (64 * nwords)) /\
    set_writable m' b_next ofs_next /\
    Mem.unchanged_on (outside_set b_next ofs_next) m m'.
Proof.
Admitted. (* Fuel induction on Z.to_nat (nwords - k0). Each iteration:
             Sset word = cur[k] (a load through idx, justified by the
             set_in_mem hypothesis on b_cur, which survives because
             b_cur <> b_next and scan_bits only writes b_next), then
             Sset q = 0, then scan_bits_correct at q0 = 0, which advances the
             invariant from 64*k0 to 64*(k0+1). Base case k0 = nwords closes
             directly. Requires threading set_in_mem on b_cur through each
             iteration via compile_step_preserves_cur. *)
 
(** [step(cur, ai, next)] leaves [next] holding [step_set S a] and touches
    nothing else. [cur] and [next] must not alias: the body zeroes [next] first
    and then unions into it, so an aliased [cur] would be destroyed before it is
    read. *)
Lemma compile_step_correct : forall b_cur b_next ofs_cur ofs_next S a ai m,
  index_of s.eq_dec a s.enum 0 = Some ai ->
  set_span_ok ofs_cur -> set_span_ok ofs_next ->
  m = m0 ->
  set_in_mem m b_cur ofs_cur S ->
  set_writable m b_next ofs_next ->
  b_cur <> b_next ->
  (forall b_tab, Genv.find_symbol ge ids.(id_table) = Some b_tab -> b_next <> b_tab) ->
  exists m',
    eval_funcall function_entry2 ge m
      (compile_step state nfa ids)
      [Vptr b_cur (Ptrofs.repr ofs_cur); Vlong (Int64.repr ai);
       Vptr b_next (Ptrofs.repr ofs_next)] E0 m'
      Vundef /\
    set_in_mem m' b_next ofs_next (step_set S a) /\
    Mem.unchanged_on (outside_set b_next ofs_next) m m'.
Proof.
  intros b_cur b_next ofs_cur ofs_next S a ai m Ha Hspc Hspn Hm Hcur Hw Hne Htab.
  destruct find_table as (b_tab & Hsym & _).
  specialize (Htab b_tab Hsym).
  assert (Hai : 0 <= ai < nsyms)
    by (apply index_of_bounds in Ha; unfold NC.nsyms; lia).
  (* [function_entry2] on [compile_step]: [fn_vars] is empty, so no allocation
     happens and the entry memory is [m] itself. The params bind cur/s/next. *)
  set (le0 := PTree.set ids.(id_next) (Vptr b_next (Ptrofs.repr ofs_next))
               (PTree.set ids.(id_s) (Vlong (Int64.repr ai))
                 (PTree.set ids.(id_cur) (Vptr b_cur (Ptrofs.repr ofs_cur))
                   (create_undef_temps
                     [(ids.(id_k), tlong); (ids.(id_j), tlong);
                      (ids.(id_q), tlong); (ids.(id_word), tlong)])))).
  assert (Hle0_next : le0 ! (ids.(id_next)) = Some (Vptr b_next (Ptrofs.repr ofs_next)))
    by (unfold le0; now rewrite PTree.gss).
  (* 1. zero next *)
  destruct (zero_next_correct le0 m b_next ofs_next Hspn Hle0_next Hw)
    as (le1 & m1 & Hz & Hzset & Hzw & Hztmp & Hzunch).
  (* every temp but id_j survives zeroing *)
  assert (Hle1_cur : le1 ! (ids.(id_cur)) = Some (Vptr b_cur (Ptrofs.repr ofs_cur))).
  { apply Hztmp; [cbv [ids alloc_idents id_cur id_j]; lia|].
    unfold le0. rewrite PTree.gso, PTree.gso by
      (cbv [ids alloc_idents id_next id_s id_cur]; lia). now rewrite PTree.gss. }
  assert (Hle1_next : le1 ! (ids.(id_next)) = Some (Vptr b_next (Ptrofs.repr ofs_next))).
  { apply Hztmp; [cbv [ids alloc_idents id_next id_j]; lia|exact Hle0_next]. }
  assert (Hle1_s : le1 ! (ids.(id_s)) = Some (Vlong (Int64.repr ai))).
  { apply Hztmp; [cbv [ids alloc_idents id_s id_j]; lia|].
    unfold le0. rewrite PTree.gso by
      (cbv [ids alloc_idents id_next id_s]; lia). now rewrite PTree.gss. }
  (* cur is untouched: zero_next only writes inside b_next *)
  assert (Hcur1 : set_in_mem m1 b_cur ofs_cur S) by admit.
  (* the zeroed span is the partial union at bound 0 *)
  assert (Hp0 : set_in_mem m1 b_next ofs_next (partial_step_set S a (64 * 0))).
  { eapply set_in_mem_ext; [|exact Hzset].
    intros i. unfold partial_step_set. rewrite in_indices_of. split.
      contradiction.
    intros (q' & Hq' & _). apply in_flat_map in Hq' as (q & Hq & _).
    apply filter_In in Hq as (_ & Hf).
    destruct (sidx q) eqn:Es; [|discriminate].
    apply andb_true_iff in Hf as (_ & Hlt). apply Z.ltb_lt in Hlt.
    pose proof (sidx_bounds q z Es). lia. }
  (* 2. the loop runs at the environment *after* [Sset k 0] *)
  set (le2 := PTree.set ids.(id_k) (Vlong (Int64.repr 0)) le1).
  destruct (scan_words_correct (Z.to_nat nwords) 0 le2 m1 b_cur ofs_cur
              b_next ofs_next b_tab S a ai)
    as (le3 & m2 & Hscan & Hsset & Hsw & Hsunch); try assumption; try lia.
  - pose proof nwords_pos. lia.
  - admit.
  - unfold le2. rewrite PTree.gso by
      (cbv [ids alloc_idents id_cur id_k]; lia). exact Hle1_cur.
  - unfold le2. rewrite PTree.gso by
      (cbv [ids alloc_idents id_next id_k]; lia). exact Hle1_next.
  - unfold le2. now rewrite PTree.gss.
  - unfold le2. rewrite PTree.gso by
      (cbv [ids alloc_idents id_s id_k]; lia). exact Hle1_s.
  - exists m2. split; [|split].
    + eapply eval_funcall_internal with (e := empty_env) (m1 := m).
      * (* function_entry2: no vars, params norepet, params/temps disjoint *)
        econstructor; cbn - [Z.mul Pos.add].
        -- constructor.
        -- repeat constructor; cbn - [Pos.add];
             cbv [ids alloc_idents id_cur id_s id_next]; intuition lia.
        -- intros x y Hx Hy. cbn - [Pos.add] in Hx, Hy.
           cbv [ids alloc_idents id_cur id_s id_next id_k id_j id_q id_word] in *.
           intuition lia.
        -- constructor.
        -- reflexivity.
      * (* the body *)
        unfold step_body. change E0 with (E0 ** E0).
        eapply exec_Sseq_1; [exact Hz|].
        change E0 with (E0 ** E0). eapply exec_Sseq_1.
        -- eapply exec_Sifthenelse.
           ++ eapply eval_lt_test_gen with (bv := Int.one); eauto.
                admit. admit.
              now rewrite (proj2 (Z.ltb_lt _ _)) by lia.
           ++ apply bool_val_one_int.
           ++ constructor.
        -- change E0 with (E0 ** E0). eapply exec_Sseq_1.
           ++ unfold le2. eapply exec_Sset. econstructor.
           ++ exact Hscan.
      * constructor.
      * (* free_list of the empty env is the identity *)
        reflexivity.
    + (* the outer loop ends at bound 64*nwords, which covers every state *)
      eapply set_in_mem_ext; [|exact Hsset].
      intros i. apply partial_step_set_saturate.
      pose proof nwords_covers. pose proof nwords_pos. lia.
    + eapply Mem.unchanged_on_trans; [exact Hzunch|exact Hsunch].
Admitted.

(** [cur] survives the call: it lies outside the written span. *)
Lemma compile_step_preserves_cur : forall b_cur b_next ofs_cur ofs_next S m m',
  b_cur <> b_next ->
  set_in_mem m b_cur ofs_cur S ->
  Mem.unchanged_on (outside_set b_next ofs_next) m m' ->
  set_in_mem m' b_cur ofs_cur S.
Proof.
  intros b_cur b_next ofs_cur ofs_next S m m' Hne Hcur Hunch k Hk.
  specialize (Hcur k Hk).
  unfold set_in_mem in *.
  rewrite <- Hcur. admit.
Admitted.

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
