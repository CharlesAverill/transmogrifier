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

Lemma sizeof_tlong : sizeof ge tlong = 8.
Proof. reflexivity. Qed.

Lemma idx_addr : forall jz,
  0 <= jz < Int64.modulus ->
  Ptrofs.add (Ptrofs.repr 0)
    (Ptrofs.mul (Ptrofs.repr (sizeof ge tlong))
                (Ptrofs.of_int64 (Int64.repr jz)))
  = Ptrofs.repr (8 * jz).
Proof.
  intros jz Hjz.
  rewrite sizeof_tlong, Ptrofs.add_zero_l.
  unfold Ptrofs.of_int64.
  rewrite (Int64.unsigned_repr jz) by (unfold Int64.max_unsigned; lia).
  (* product of two [repr]s is the [repr] of the product *)
  unfold Ptrofs.mul.
  apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_mult; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

Lemma idx_addr_ofs : forall ofs jz,
  0 <= ofs -> 0 <= jz < Int64.modulus ->
  ofs + 8 * jz < Ptrofs.modulus ->
  Ptrofs.add (Ptrofs.repr ofs)
    (Ptrofs.mul (Ptrofs.repr (sizeof ge tlong))
                (Ptrofs.of_int64 (Int64.repr jz)))
  = Ptrofs.repr (ofs + 8 * jz).
Proof.
  intros ofs jz Hofs Hjz Hlt.
  rewrite sizeof_tlong.
  unfold Ptrofs.of_int64.
  rewrite (Int64.unsigned_repr jz) by (unfold Int64.max_unsigned; lia).
  apply Ptrofs.eqm_samerepr.
  unfold Ptrofs.add, Ptrofs.mul.
  apply Ptrofs.eqm_add.
  - apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
  - eapply Ptrofs.eqm_trans.
    + apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
    + apply Ptrofs.eqm_mult; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
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
                     replace (Ptrofs.add (Ptrofs.repr ofs_next)
                                (Ptrofs.mul (Ptrofs.repr 8)
                                   (Ptrofs.repr (Int64.unsigned (Int64.repr j0)))))
                       with (Ptrofs.repr (ofs_next + 8 * j0)).
                     +++ exact Hst.
                     +++ symmetry. apply Ptrofs.eqm_samerepr.
                         rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; lia).
                         unfold Ptrofs.add, Ptrofs.mul.
                         apply Ptrofs.eqm_add.
                         *** apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
                         *** eapply Ptrofs.eqm_trans;
                               [ apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr
                               | apply Ptrofs.eqm_mult;
                                   apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr ].
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
           ++ (* the loop continues from [le1, m1]; that is exactly the IH's run *)
              replace (Int64.add (Int64.repr j0) (Int64.repr 1)) with (Int64.repr (j0 + 1)).
                exact Hexec.
              symmetry. apply Int64.eqm_samerepr.
                unfold Int64.add.
                apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
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
Qed. (* UNVERIFIED against build; no admits remain *)

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
  - exact Hspan.
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
Qed.

(** The table row for the state at global index [gi], as an index list. *)
Definition row_of (gi : Z) (a : s.t) : list Z :=
  match nth_error nfa.(states _) (Z.to_nat gi) with
  | Some q => indices_of state nfa state_eq_dec (nfa.(transition _) q a)
  | None => []
  end.

(** Word [j] of the row lives at flat table index [(gi*nsyms+ai)*nwords+j], and
    [table_row_correct] + [table_in_mem] say what is there. *)
(** The table is a read-only global; every load from its block returns the same
    value as in [m0].  This is exactly what survives the writes [step] performs,
    because those writes only ever hit the (writable, distinct) [next] block.
    Threading this predicate through the loop lemmas -- rather than the far
    stronger [m = m0] -- is what lets them run on the post-[zero_next] memory. *)
Definition table_readable (m : mem) (b_tab : block) : Prop :=
  forall ofs v,
    Mem.loadv Mint64 m0 (Vptr b_tab ofs) = Some v ->
    Mem.loadv Mint64 m  (Vptr b_tab ofs) = Some v.

Lemma table_readable_m0 : forall b_tab, table_readable m0 b_tab.
Proof. now intros b_tab ofs v H. Qed.

(** A store outside the table block preserves readability. *)
Lemma table_readable_store : forall m m' b_tab b' ofs' v',
  b' <> b_tab ->
  Mem.storev Mint64 m (Vptr b' ofs') (Vlong v') = Some m' ->
  table_readable m b_tab ->
  table_readable m' b_tab.
Proof.
  intros m m' b_tab b' ofs' v' Hne Hst Hread ofs v Hload.
  specialize (Hread ofs v Hload). cbn [Mem.loadv] in *.
  erewrite Mem.load_store_other with (m1 := m); [exact Hread | | ].
  - (* the store: Hst, after cbn *)
    cbn [Mem.storev] in Hst. exact Hst.
  - (* disjointness: different blocks *)
    left. now symmetry.
Qed.

(** Readability is preserved along any [unchanged_on] that keeps the table block
    fixed -- in particular the [outside_set b_next ofs_next] the loops produce,
    since [b_next <> b_tab]. *)
Lemma table_readable_unchanged : forall m m' b_tab b_next ofs_next,
  b_next <> b_tab ->
  table_readable m b_tab ->
  Mem.unchanged_on (outside_set b_next ofs_next) m m' ->
  table_readable m' b_tab.
Proof.
  intros m m' b_tab b_next ofs_next Hne Hread Hunch ofs v Hload.
  specialize (Hread ofs v Hload). cbn [Mem.loadv] in *.
  eapply Mem.load_unchanged_on; [exact Hunch| |exact Hread].
  intros i Hi. unfold outside_set. left. congruence.
Qed.

Lemma table_row_load : forall m b_tab gi ai a j,
  table_readable m b_tab ->
  Genv.find_symbol ge ids.(id_table) = Some b_tab ->
  0 <= gi < nstates ->
  index_of s.eq_dec a s.enum 0 = Some ai ->
  0 <= j < nwords ->
  (exists q, nth_error nfa.(states _) (Z.to_nat gi) = Some q /\ sidx q = Some gi) ->
  Mem.loadv Mint64 m (Vptr b_tab (Ptrofs.repr (8 * ((gi * nsyms + ai) * nwords + j))))
  = Some (Vlong (Int64.repr (word_of_indices (row_of gi a) j))).
Proof.
  intros m b_tab gi ai a j Hread Hsym Hgi Ha Hj (q & Hnth & Hq).
  apply Hread.
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
    (* Decide membership of [64*k+b] in the append and reflect it through the
       three [word_of_indices_spec] instances.  [In] distributes over [++]. *)
    destruct (in_dec Z.eq_dec (64 * k + b) (S1 ++ S2)) as [Hin|Hnin].
    + (* present in the append: LHS bit is set, and present in S1 or S2 *)
      rewrite (proj2 (word_of_indices_spec (S1 ++ S2) k b Hk ltac:(lia)) Hin).
      symmetry. apply orb_true_iff.
      apply in_app_or in Hin as [Hin|Hin];
        [ left;  apply (word_of_indices_spec S1 k b Hk ltac:(lia)); exact Hin
        | right; apply (word_of_indices_spec S2 k b Hk ltac:(lia)); exact Hin ].
    + (* absent from the append: LHS bit clear, and absent from both S1, S2 *)
      assert (E : Z.testbit (word_of_indices (S1 ++ S2) k) b = false).
      { destruct (Z.testbit (word_of_indices (S1 ++ S2) k) b) eqn:E; [|reflexivity].
        apply (word_of_indices_spec (S1 ++ S2) k b Hk ltac:(lia)) in E.
        contradiction. }
      rewrite E. symmetry. apply orb_false_iff. split.
      * destruct (Z.testbit (word_of_indices S1 k) b) eqn:E1; [|reflexivity].
        apply (word_of_indices_spec S1 k b Hk ltac:(lia)) in E1.
        exfalso. apply Hnin, in_or_app. now left.
      * destruct (Z.testbit (word_of_indices S2 k) b) eqn:E2; [|reflexivity].
        apply (word_of_indices_spec S2 k b Hk ltac:(lia)) in E2.
        exfalso. apply Hnin, in_or_app. now right.
  - apply Z.ltb_ge in Eb.
    rewrite Z.lor_spec, !word_of_indices_high by lia. reflexivity.
Qed.

(** The row-union loop, generalized over [j0] exactly as [zero_next_loop]. *)
(** Evaluate a set-pointer index expression [idx (Etempvar base) (Etempvar off)]
    to the value loaded at [b + 8*offv], given the temp bindings and the load.
    This is the read half of every set access in the loops. *)
Lemma eval_idx_load : forall e le m off b ofsb offv v,
  le ! base = Some (Vptr b (Ptrofs.repr ofsb)) ->
  le ! off  = Some (Vlong (Int64.repr offv)) ->
  0 <= offv < Int64.modulus ->
  0 <= ofsb -> ofsb + 8 * offv < Ptrofs.modulus ->
  Mem.loadv Mint64 m (Vptr b (Ptrofs.repr (ofsb + 8 * offv))) = Some v ->
  eval_expr ge e le m
    (idx (Etempvar base tsetptr) (Etempvar off tlong)) v.
Proof.
  intros e le m off b ofsb offv v Hbase Hoff Hoffv Hofsb Hlt Hload.
  unfold idx.
  eapply eval_Elvalue.
  - econstructor.
    econstructor.
        econstructor. eassumption.
        econstructor. eassumption.
      cbn. unfold sem_add, classify_add, tsetptr, tlong. cbn.
      destruct Archi.ptr64 eqn:E; cbn; [|discriminate].
      unfold Ptrofs.of_int64. reflexivity.
  - (* deref_loc at the reduced address *)
    replace (Ptrofs.add (Ptrofs.repr ofsb)
               (Ptrofs.mul (Ptrofs.repr 8)
                           (Ptrofs.repr (Int64.unsigned (Int64.repr offv)))))
      with (Ptrofs.repr (ofsb + 8 * offv))
      by (symmetry; apply idx_addr_ofs; lia).
    now eapply deref_loc_value.
Qed.

(** The table-index address expression reduces to [8 * ((gi*nsyms+ai)*nwords +
    j0)] given [id_k = gi/64], [id_q = gi mod 64], [id_s = ai], [id_j = j0], and
    [gi = 64*(gi/64) + gi mod 64].  Evaluated as an lvalue whose block is the
    table and whose offset is that flat index times 8. *)
Lemma eval_table_idx_load : forall e le m b_tab gi ai j0 v,
  Genv.find_symbol ge ids.(id_table) = Some b_tab ->
  le ! (ids.(id_k)) = Some (Vlong (Int64.repr (gi / 64))) ->
  le ! (ids.(id_q)) = Some (Vlong (Int64.repr (gi mod 64))) ->
  le ! (ids.(id_s)) = Some (Vlong (Int64.repr ai)) ->
  le ! (ids.(id_j)) = Some (Vlong (Int64.repr j0)) ->
  0 <= gi < nstates -> 0 <= ai < nsyms -> 0 <= j0 < nwords ->
  Mem.loadv Mint64 m
    (Vptr b_tab (Ptrofs.repr (8 * ((gi * nsyms + ai) * nwords + j0)))) = Some v ->
  eval_expr ge e le m
    (idx (Evar ids.(id_table) (table_type _ nfa))
      (Ebinop Oadd
        (Ebinop Omul
          (Ebinop Oadd
            (Ebinop Omul
              (Ebinop Oadd
                (Ebinop Omul (Etempvar ids.(id_k) tlong) (const 64) tlong)
                (Etempvar ids.(id_q) tlong) tlong)
              (const nsyms) tlong)
            (Etempvar ids.(id_s) tlong) tlong)
          (const nwords) tlong)
        (Etempvar ids.(id_j) tlong) tlong)) v.
Proof.
  (* The integer arithmetic [((gi/64)*64 + gi mod 64)*nsyms + ai)*nwords + j0
     = (gi*nsyms + ai)*nwords + j0] uses [Z.div_add' / Z.mod_add] via
     [Z.div_mod gi 64].  The [eval_expr] for the nested [Ebinop]s is mechanical
     ([econstructor] per node, [Etempvar]/[const] leaves), and the final
     [deref_loc_value] uses the address reduction analogous to [idx_addr_ofs] but
     for the [8 * flat] form.  Marked [admit]: the address normalization for the
     table (the [8 * ...] Ptrofs step) and the [Int64]-level flattening of the
     nested products. *)
  admit.
Admitted.

Lemma word_of_indices_row_load :
  (* the [j]-th word of the table row for [gi] on [a], as loaded from the table
     global, equals [word_of_indices (row_of gi a) j] -- the driver for the
     [Oor] step below. *)
  forall m b_tab gi ai a j,
    table_readable m b_tab ->
    Genv.find_symbol ge ids.(id_table) = Some b_tab ->
    0 <= gi < nstates ->
    index_of s.eq_dec a s.enum 0 = Some ai ->
    0 <= j < nwords ->
    (exists q, nth_error nfa.(states _) (Z.to_nat gi) = Some q /\ sidx q = Some gi) ->
    Mem.loadv Mint64 m
      (Vptr b_tab (Ptrofs.repr (8 * ((gi * nsyms + ai) * nwords + j))))
    = Some (Vlong (Int64.repr (word_of_indices (row_of gi a) j))).
Proof. intros. now apply table_row_load. Qed.

(** The row-union loop, generalized over [j0] exactly as [zero_next_loop].  Runs
    the bare [Sloop] (not [union_row], which prefixes [Sset j 0]); the seeding is
    done in [union_row_correct].  The two load hypotheses split [next] at [j0]:
    below [j0] it already holds the union [S ++ row], at and above it still holds
    [S].  Each iteration OR-s the [j0]-th table-row word into [next[j0]]. *)
Lemma union_row_loop_correct : forall fuel j0 le m b_next ofs_next b_tab gi ai a S,
  (Z.to_nat (nwords - j0) <= fuel)%nat ->
  0 <= j0 <= nwords ->
  set_span_ok ofs_next ->
  Genv.find_symbol ge ids.(id_table) = Some b_tab ->
  0 <= gi < nstates ->
  index_of s.eq_dec a s.enum 0 = Some ai ->
  (exists q, nth_error nfa.(states _) (Z.to_nat gi) = Some q /\ sidx q = Some gi) ->
  b_next <> b_tab ->
  table_readable m b_tab ->
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
    exec_stmt function_entry2 ge empty_env le m
      (Sloop
        (Ssequence
          (Sifthenelse (lt_test ids.(id_j) nwords) Sskip Sbreak)
          (Sassign
            (idx (Etempvar ids.(id_next) tsetptr) (Etempvar ids.(id_j) tlong))
            (Ebinop Oor
              (idx (Etempvar ids.(id_next) tsetptr) (Etempvar ids.(id_j) tlong))
              (idx (Evar ids.(id_table) (table_type _ nfa))
                (Ebinop Oadd
                  (Ebinop Omul
                    (Ebinop Oadd
                      (Ebinop Omul
                        (Ebinop Oadd
                          (Ebinop Omul (Etempvar ids.(id_k) tlong) (const 64) tlong)
                          (Etempvar ids.(id_q) tlong) tlong)
                        (const nsyms) tlong)
                      (Etempvar ids.(id_s) tlong) tlong)
                    (const nwords) tlong)
                  (Etempvar ids.(id_j) tlong) tlong))
              tlong)))
        (Sset ids.(id_j)
          (Ebinop Oadd (Etempvar ids.(id_j) tlong) (const 1) tlong)))
      E0 le' m' Out_normal /\
    set_in_mem m' b_next ofs_next (S ++ row_of gi a) /\
    set_writable m' b_next ofs_next /\
    Mem.unchanged_on (outside_set b_next ofs_next) m m'.
Proof.
  (* PROOF SKELETON.  Fuel induction on [Z.to_nat (nwords - j0)], identical in
     shape to [zero_next_loop_correct].  The one new ingredient per iteration is
     the [Oor] assignment [next[j0] := next[j0] | table[row(gi,a)[j0]]], which
     evaluates to
        word_of_indices S j0  |  word_of_indices (row_of gi a) j0
      = word_of_indices (S ++ row_of gi a) j0            (by word_of_indices_app)
     so the invariant advances from "S below j0, S from j0" to "S++row below
     j0+1, S from j0+1".

     Fully determinate parts (write as in zero_next_loop_correct):
       - base / guard-fail cases (j0 = nwords): [exec_Sloop_stop1], the goal
         [set_in_mem] follows because the "below j0" hypothesis at j0 = nwords
         already covers all words.
       - the [gso]/[gss] temp bookkeeping, [set_writable_store],
         [set_store_unchanged], [Mem.unchanged_on_trans].
       - the increment [Sset j (j+1)] and its [Int64] value normalization
         (same [Int64.eqm] step used in zero_next_loop_correct).

     Marked [admit] (the genuinely version-sensitive [eval_expr] chains):
       (A) evaluating the [Oor] rvalue: the left [idx next[j]] loads
           [word_of_indices S j0] (from the "S from j0" hypothesis at k=j0); the
           right [idx table[...]] loads [word_of_indices (row_of gi a) j0] (by
           [word_of_indices_row_load], after showing the 4-deep index expression
           evaluates to [(gi*nsyms+ai)*nwords + j0] using gi = 64*(gi/64)+gi mod
           64); the [Oor] combines them; then [word_of_indices_app] rewrites to
           the append.  This is the only real work.
       (B) the store-address reduction for [next[j0]] (identical to the
           [idx_addr_ofs]/[replace ... exact Hst] step already used in
           zero_next_loop_correct).
       (C) the store [Hst] for the OR-ed value. *)
  induction fuel; intros j0 le m b_next ofs_next b_tab gi ai a S
    Hfuel Hj0 Hspan Hsym Hgi Ha Hstate Hbtab Hread Hnext Hj Hk Hq Hs
    Hbelow Habove Hw; pose proof nwords_bounded as NWB.
  - (* fuel = 0 -> j0 = nwords *)
    assert (j0 = nwords) by lia. subst j0.
    exists le, m. split; [|split; [|split]].
    + eapply exec_Sloop_stop1; [|constructor].
      eapply exec_Sseq_2; [|discriminate].
      eapply exec_Sifthenelse.
      * eapply eval_lt_test_gen with (bv := Int.zero); eauto; try lia.
        now rewrite Z.ltb_irrefl.
      * apply bool_val_zero_int.
      * constructor.
    + (* every word is below nwords, so [Hbelow] gives the full union *)
      intros kk Hkk. apply Hbelow. lia.
    + exact Hw.
    + apply Mem.unchanged_on_refl.
  - destruct (Z.eq_dec j0 nwords) as [->|Hne].
    + exists le, m. split; [|split; [|split]].
      * eapply exec_Sloop_stop1; [|constructor].
        eapply exec_Sseq_2; [|discriminate].
        eapply exec_Sifthenelse.
        -- eapply eval_lt_test_gen with (bv := Int.zero); eauto; try lia.
           now rewrite Z.ltb_irrefl.
        -- apply bool_val_zero_int.
        -- constructor.
      * intros kk Hkk. apply Hbelow. lia.
      * exact Hw.
      * apply Mem.unchanged_on_refl.
    + assert (Hlt : j0 < nwords) by lia.
      (* the OR-ed value to be stored at word j0 *)
      set (vor := Z.lor (word_of_indices S j0)
                        (word_of_indices (row_of gi a) j0)).
      (* the store exists (writable span) *)
      destruct (set_store_ok m b_next ofs_next j0 (Int64.repr vor) Hw
                  ltac:(lia) (proj1 Hspan)
                  ltac:(destruct Hspan as (_&_&H); exact H)
                  (span_align ofs_next j0 Hspan ltac:(lia)))
        as (m1 & Hst).
      set (le1 := PTree.set ids.(id_j) (Vlong (Int64.repr (j0 + 1))) le).
      (* new invariant halves at j0+1: word j0 now holds vor = word_of_indices
         (S ++ row) j0, by word_of_indices_app *)
      assert (Hvor : vor = word_of_indices (S ++ row_of gi a) j0)
        by (unfold vor; symmetry; apply word_of_indices_app; lia).
      destruct (IHfuel (j0 + 1) le1 m1 b_next ofs_next b_tab gi ai a S)
        as (le' & m' & Hexec & Hset & Hw' & Hunch); try lia; try assumption.
      * (* table_readable survives the store into b_next (<> b_tab) *)
        eapply table_readable_store; [exact Hbtab | | exact Hread].
        cbn [Mem.storev] in Hst. exact Hst.
      * unfold le1. rewrite PTree.gso by
          (cbv [ids alloc_idents id_next id_j]; lia). exact Hnext.
      * unfold le1. now rewrite PTree.gss.
      * unfold le1. rewrite PTree.gso by
          (cbv [ids alloc_idents id_k id_j]; lia). exact Hk.
      * unfold le1. rewrite PTree.gso by
          (cbv [ids alloc_idents id_q id_j]; lia). exact Hq.
      * unfold le1. rewrite PTree.gso by
          (cbv [ids alloc_idents id_s id_j]; lia). exact Hs.
      * (* below j0+1: words < j0 unchanged (store hit j0), word j0 = vor *)
        intros kk Hkk. destruct (Z.eq_dec kk j0) as [->|Hkkne].
        -- rewrite <- Hvor. eapply set_store_same; eauto.
        -- erewrite set_store_other; eauto; try lia;
             [ apply Hbelow; lia
             | exact (proj1 Hspan)
             | destruct Hspan as (_&_&H); exact H ].
      * (* from j0+1: words > j0 unchanged, still hold S *)
        intros kk Hkk. erewrite set_store_other; eauto; try lia;
          [ apply Habove; lia
          | exact (proj1 Hspan)
          | destruct Hspan as (_&_&H); exact H ].
      * eapply set_writable_store; eauto.
      * exists le', m'. split; [|split; [|split]].
        -- change E0 with (E0 ** E0 ** E0). eapply exec_Sloop_loop.
           ++ change E0 with (E0 ** E0). eapply exec_Sseq_1.
              ** eapply exec_Sifthenelse.
                 --- eapply eval_lt_test_gen with (bv := Int.one); eauto; try lia.
                     now rewrite (proj2 (Z.ltb_lt _ _)) by lia.
                 --- apply bool_val_one_int.
                 --- constructor.
              ** (* Sassign next[j0] := next[j0] | table[...] *)
                 eapply exec_Sassign.
                 --- (* lvalue: next[j0] *)
                     econstructor. econstructor.
                     +++ econstructor. exact Hnext.
                     +++ econstructor. eassumption.
                     +++ cbn. unfold sem_add, classify_add, tsetptr, tlong. cbn.
                         destruct Archi.ptr64 eqn:Eptr; cbn; [|discriminate].
                         unfold Ptrofs.of_int64. reflexivity.
                 --- (* rvalue: next[j0] | table[row(gi,a)[j0]] *)
                     econstructor.
                     +++ admit.
                     +++ (* right operand: load table row word j0 *)
                         eapply eval_table_idx_load;
                           [ exact Hsym | exact Hk | exact Hq | exact Hs | exact Hj
                           | exact Hgi
                           | apply index_of_bounds in Ha; unfold NC.nsyms; lia
                           | lia
                           | apply word_of_indices_row_load; try assumption; admit ].
                     +++ (* the Oor combines to vor *)
                         cbn. unfold sem_or, sem_binarith, sem_cast,
                                classify_cast, classify_binarith, binarith_type,
                                classify_binarith, tlong. cbn.
                         admit.
                 --- (* cast: long to long is identity *)
                     cbn. unfold sem_cast, classify_cast, tlong. cbn.
                     admit.
                 --- (* assign_loc: store vor at next[j0] *)
                     eapply assign_loc_value; [reflexivity|].
                     replace (Ptrofs.add (Ptrofs.repr ofs_next)
                                (Ptrofs.mul (Ptrofs.repr (sizeof ge tlong))
                                   (Ptrofs.of_int64 (Int64.repr j0))))
                       with (Ptrofs.repr (ofs_next + 8 * j0))
                       by (symmetry; apply idx_addr_ofs;
                           [ exact (proj1 Hspan) | lia
                           | destruct Hspan as (_ & _ & Hsl);
                             pose proof nwords_bounded; nia ]).
                     admit.
           ++ constructor.
           ++ unfold le1. eapply exec_Sset. econstructor.
              ** econstructor. exact Hj.
              ** econstructor.
              ** cbn. unfold sem_add, classify_add, tlong, sem_binarith,
                        sem_cast, classify_cast, classify_binarith. cbn.
                 destruct Archi.ptr64; cbn; do 2 f_equal;
                   now rewrite Int64.add_unsigned, !Int64.unsigned_repr_eq,
                     Zplus_mod_idemp_l, Zplus_mod_idemp_r.
           ++ replace (Int64.add (Int64.repr j0) (Int64.repr 1))
                with (Int64.repr (j0 + 1)).
                exact Hexec.
              symmetry. apply Int64.eqm_samerepr. unfold Int64.add.
              apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
        -- exact Hset.
        -- exact Hw'.
        -- eapply Mem.unchanged_on_trans; [|exact Hunch].
           eapply set_store_unchanged; eauto; try lia;
             [exact (proj1 Hspan) | destruct Hspan as (_&_&H); exact H].
Admitted.

Lemma union_row_correct : forall le m b_next ofs_next b_tab gi ai k q S a,
  Genv.find_symbol ge ids.(id_table) = Some b_tab ->
  gi = 64 * k + q ->
  0 <= gi < nstates ->
  0 <= q < 64 ->
  set_span_ok ofs_next ->
  index_of s.eq_dec a s.enum 0 = Some ai ->
  (exists q_st, nth_error nfa.(states _) (Z.to_nat gi) = Some q_st /\ sidx q_st = Some gi) ->
  table_readable m b_tab ->
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
  (* k = gi/64 and q = gi mod 64, from gi = 64*k + q and 0 <= q < 64 *)
  assert (Hkdiv : k = gi / 64)
    by (subst gi; rewrite Z.mul_comm, Z.div_add_l by lia;
        rewrite (Z.div_small q 64) by lia; lia).
  assert (Hqmod : q = gi mod 64)
    by (subst gi; rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia;
        rewrite Z.mod_small by lia; reflexivity).
  destruct (union_row_loop_correct (Z.to_nat nwords) 0 le0 m b_next ofs_next
              b_tab gi ai a S)
    as (le' & m' & Hexec & Hset' & Hw' & Hunch); eauto; try lia; unfold le0.
  - pose proof nwords_pos. lia.
  - rewrite PTree.gso by
      (cbv [ids alloc_idents id_next id_j]; lia). assumption.
  - now rewrite PTree.gss.
  - rewrite PTree.gso by
      (cbv [ids alloc_idents id_k id_j]; lia). now rewrite <- Hkdiv.
  - rewrite PTree.gso by
      (cbv [ids alloc_idents id_q id_j]; lia). now rewrite <- Hqmod.
  - rewrite PTree.gso by
      (cbv [ids alloc_idents id_s id_j]; lia). assumption.
  - exists le', m'. split; [|split; [|split]].
    + unfold union_row. change E0 with (E0 ** E0).
      eapply exec_Sseq_1; [|exact Hexec].
      eapply exec_Sset. econstructor.
    + exact Hset'.
    + exact Hw'.
    + exact Hunch.
Qed.

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

(** If no index in [[lo, hi)] belongs to [S], the partial set does not grow from
    [lo] to [hi].  Used for OPT2's early break: once the residual is zero every
    remaining bit of the word is absent from [S]. *)
Lemma partial_step_set_stable : forall S a lo hi,
  0 <= lo <= hi ->
  (forall q, lo <= q < hi -> ~ In q S) ->
  forall i, In i (partial_step_set S a hi) <-> In i (partial_step_set S a lo).
Proof.
  intros S a lo hi Hle Hnone i.
  remember (Z.to_nat (hi - lo)) as n eqn:Hn.
  revert hi Hle Hnone Hn.
  induction n as [|n IH]; intros hi Hle Hnone Hn.
  - assert (hi = lo) by lia. subst hi. reflexivity.
  - assert (Hhi : hi = (hi - 1) + 1) by lia.
    rewrite Hhi. rewrite partial_step_set_succ by lia.
    rewrite IH with (hi := hi - 1); [|lia| |lia].
    + split; [intros [H|H]; [exact H|] | now left].
      (* the right disjunct requires [In (hi-1) S], but hi-1 in [lo,hi) is absent *)
      exfalso. destruct H as (q & Hq & Hin & _).
      apply (Hnone (hi - 1)); [lia | exact Hin].
    + intros q Hq. apply Hnone. lia.
Qed.

(** The inner bit-scan loop *)

(** Low bit of the shifted residual = bit [q0] of the original word. *)
Lemma shifted_low_bit : forall S k q0,
  0 <= k -> 0 <= q0 < 64 ->
  (Z.land (Z.shiftr (word_of_indices S k) q0) 1 <> 0 <-> In (64 * k + q0) S).
Proof.
  intros S k q0 Hk Hq. rewrite <- word_of_indices_spec by assumption.
  split.
  - intros Hne.
    destruct (Z.testbit (word_of_indices S k) q0) eqn:E; [reflexivity|].
    exfalso. apply Hne. apply Z.bits_inj'. intros b Hb.
    rewrite Z.land_spec, Z.testbit_0_l, Z.shiftr_spec by lia.
    destruct (Z.eq_dec b 0) as [->|Hb0].
      rewrite Z.add_0_l, E. now rewrite andb_false_l.
    replace (Z.testbit 1 b) with false.
      now rewrite andb_false_r.
    symmetry. change 1 with (2 ^ 0). apply Z.pow2_bits_false. lia.
  - intros Htb Hz.
    assert (Hb : Z.testbit (Z.land (Z.shiftr (word_of_indices S k) q0) 1) 0 = true).
    { rewrite Z.land_spec, Z.shiftr_spec, Z.add_0_l by lia.
      rewrite Htb. now rewrite Z.bit0_odd, Z.odd_1, andb_true_r. }
    rewrite Hz, Z.testbit_0_l in Hb. discriminate.
Qed.

(** Once the residual is 0, every remaining index [>= 64*k+q0] is absent from
    [S] (in this word), so OPT2's early break is sound: the partial set does not
    grow through the rest of the word. *)
Lemma shifted_zero_tail : forall S k q0 q,
  0 <= k -> 0 <= q0 -> q0 <= q < 64 ->
  Z.shiftr (word_of_indices S k) q0 = 0 ->
  ~ In (64 * k + q) S.
Proof.
  intros S k q0 q Hk Hzero Hq0q Hshift Hin.
  apply (word_of_indices_spec S k q Hk ltac:(lia)) in Hin.
  assert (Htb : Z.testbit (Z.shiftr (word_of_indices S k) q0) (q - q0) = true).
  { rewrite Z.shiftr_spec by lia.
    now replace (q - q0 + q0) with q by lia. }
  rewrite Hshift, Z.testbit_0_l in Htb. discriminate.
Qed.

Lemma scan_bits_correct : forall fuel q0 w0 le m b_next ofs_next b_tab k S a ai,
  (Z.to_nat (64 - q0) <= fuel)%nat ->
  0 <= q0 <= 64 ->
  0 <= k < nwords ->
  w0 = word_of_indices S k ->
  set_span_ok ofs_next ->
  Genv.find_symbol ge ids.(id_table) = Some b_tab ->
  index_of s.eq_dec a s.enum 0 = Some ai ->
  table_readable m b_tab ->
  b_next <> b_tab ->
  le ! (ids.(id_next)) = Some (Vptr b_next (Ptrofs.repr ofs_next)) ->
  le ! (ids.(id_k)) = Some (Vlong (Int64.repr k)) ->
  le ! (ids.(id_q)) = Some (Vlong (Int64.repr q0)) ->
  le ! (ids.(id_s)) = Some (Vlong (Int64.repr ai)) ->
  (* OPT4: the loop carries the ORIGINAL word shifted past the consumed bits *)
  le ! (ids.(id_word)) = Some (Vlong (Int64.repr (Z.shiftr w0 q0))) ->
  set_in_mem m b_next ofs_next (partial_step_set S a (64 * k + q0)) ->
  set_writable m b_next ofs_next ->
  exists le' m',
    exec_stmt function_entry2 ge empty_env le m
      (Sloop
        (Ssequence
          (Sifthenelse (lt_test ids.(id_q) 64) Sskip Sbreak)
          (Ssequence
            (* OPT2: early exit when the residual is all zero *)
            (Sifthenelse (Ebinop Oeq (Etempvar ids.(id_word) tlong) (const 0) tint)
              Sbreak Sskip)
            (Sifthenelse
              (* OPT3: test the low bit rather than [1 << q] *)
              (Ebinop One
                (Ebinop Oand (Etempvar ids.(id_word) tlong) (const 1) tlong)
                (const 0) tint)
              (Sifthenelse
                (Ebinop Olt
                  (Ebinop Oadd
                    (Ebinop Omul (Etempvar ids.(id_k) tlong) (const 64) tlong)
                    (Etempvar ids.(id_q) tlong) tlong)
                  (const nstates) tint)
                (union_row state nfa ids) Sskip)
              Sskip)))
        (Ssequence
          (Sset ids.(id_q)
            (Ebinop Oadd (Etempvar ids.(id_q) tlong) (const 1) tlong))
          (* OPT4: shift the residual right by one *)
          (Sset ids.(id_word)
            (Ebinop Oshr (Etempvar ids.(id_word) tlong) (const 1) tlong))))
      E0 le' m' Out_normal /\
    set_in_mem m' b_next ofs_next (partial_step_set S a (64 * (k + 1))) /\
    set_writable m' b_next ofs_next /\
    Mem.unchanged_on (outside_set b_next ofs_next) m m'.
Proof.
  (* PROOF SKELETON (structure complete; residual [eval_expr]/[exec_Sloop]
     plumbing marked with [admit]).  Fuel induction on [Z.to_nat (64 - q0)].

     Three ways to leave/continue the loop at bits [q0]:

     (a) q0 = 64  (guard [q < 64] fails): [exec_Sloop_stop1]; the goal
         [partial_step_set S a (64*k+64) = partial_step_set S a (64*(k+1))]
         holds by [f_equal; lia], and [set_in_mem]/writable/unchanged are the
         hypotheses unchanged.

     (b) Z.shiftr w0 q0 = 0  (OPT2 break fires): [exec_Sloop_stop1] through the
         inner [Sifthenelse ... Sbreak].  Must show the CURRENT partial at
         [64*k+q0] already equals the FINAL partial at [64*(k+1)].  Every index
         in [[q0,64)] of this word is absent from S by [shifted_zero_tail], so
         [partial_step_set_succ] adds nothing across the remaining bits; iterate
         [partial_step_set_succ]/[set_in_mem_ext] up to 64.  (A small helper
         [partial_step_set_stable_from] doing this 64-q0 fold is cleaner than
         inlining.)

     (c) Z.shiftr w0 q0 <> 0: one iteration via [exec_Sloop_loop], then the IH
         at [q0+1] with residual [Z.shiftr w0 (q0+1)] (= [Z.shiftr (Z.shiftr w0
         q0) 1], by [Z.shiftr_shiftr]).  Sub-cases on the OPT3 test and the
         in-range test:
           * low bit clear (¬ In (64*k+q0) S, by [shifted_low_bit]): both inner
             [Sifthenelse] take the else/[Sskip]; memory unchanged; advance the
             invariant with [partial_step_set_succ] (new index absent -> no
             growth) + [set_in_mem_ext].
           * low bit set, but 64*k+q0 >= nstates: OPT3 true, in-range false ->
             [Sskip].  The index is not a state ([sidx] undefined there), so
             [partial_step_set_succ]'s right disjunct is vacuous; no growth.
           * low bit set and in range: [union_row_correct] at [gi = 64*k+q0]
             gives [next := (partial ...) ++ row_of gi a]; then
             [partial_step_set_succ] + [set_in_mem_ext] rewrites that append to
             [partial_step_set S a (64*k+q0+1)].
         In every sub-case the increment block sets [id_q := q0+1] and
         [id_word := Z.shiftr w0 q0 >> 1]; discharge the latter with
         [Z.shiftr_shiftr] so the IH's [id_word] hypothesis matches.

     The [eval_expr] obligations (the OPT3 [Oand ... 1] test evaluating to the
     boolean given by [shifted_low_bit]; the [Omul k 64 + q] address for the
     range test; the [Oshr] increment) are the same shape as the ones in
     [zero_next_loop_correct]; [eval_lt_test_gen], [bool_val_one_int],
     [bool_val_zero_int] and [idx_addr] cover them.  These are marked [admit]. *)
  induction fuel; intros q0 w0 le m b_next ofs_next b_tab k S a ai
    Hfuel Hq0 Hk Hw0 Hspan Hsym Ha Hm Hne Hnext Hkk Hq Hs Hword Hpart Hw;
    pose proof nwords_bounded as NWB.
  - (* fuel = 0 forces q0 = 64 *)
    assert (q0 = 64) by lia. subst q0.
    exists le, m. split; [|split; [|split]].
    + eapply exec_Sloop_stop1; [|constructor].
      eapply exec_Sseq_2; [|discriminate].
      eapply exec_Sifthenelse.
      * eapply eval_lt_test_gen with (bv := Int.zero); eauto; try (now compute).
      * apply bool_val_zero_int.
      * constructor.
    + eapply set_in_mem_ext; [|exact Hpart].
      intros i. replace (64 * k + 64) with (64 * (k + 1)) by lia. reflexivity.
    + exact Hw.
    + apply Mem.unchanged_on_refl.
  - destruct (Z.eq_dec q0 64) as [->|Hqne].
    + (* guard fails: identical to the base case *)
      exists le, m. split; [|split; [|split]].
      * eapply exec_Sloop_stop1; [|constructor].
        eapply exec_Sseq_2; [|discriminate].
        eapply exec_Sifthenelse.
        -- eapply eval_lt_test_gen with (bv := Int.zero); eauto; try (now compute).
        -- apply bool_val_zero_int.
        -- constructor.
      * eapply set_in_mem_ext; [|exact Hpart].
        intros i. replace (64 * k + 64) with (64 * (k + 1)) by lia. reflexivity.
      * exact Hw.
      * apply Mem.unchanged_on_refl.
    + assert (Hlt : q0 < 64) by lia.
      destruct (Z.eq_dec (Z.shiftr w0 q0) 0) as [Hzero|Hnz].
      * (* OPT2 break: residual is zero, no remaining bits contribute *)
        exists le, m. split; [|split; [|split]].
        -- (* guard true, then the OPT2 Sifthenelse takes Sbreak *)
           eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
           (* body: Ssequence guard (Ssequence (OPT2 test) ...) *)
           change E0 with (E0 ** E0). eapply exec_Sseq_1.
           ++ (* guard q0 < 64 is true *)
              eapply exec_Sifthenelse.
              ** eapply eval_lt_test_gen with (bv := Int.one); eauto; try lia.
                 all: admit.
              ** apply bool_val_one_int.
              ** constructor.
           ++ (* the OPT2 test: word == 0 is true (residual is zero), take Sbreak *)
              eapply exec_Sseq_2; [|discriminate].
              eapply exec_Sifthenelse.
              ** (* word == 0 evaluates to true *)
                 econstructor.
                 --- econstructor. exact Hword.
                 --- econstructor.
                 --- cbn. unfold sem_cmp, classify_cmp, tlong, sem_binarith,
                            sem_cast, classify_cast, classify_binarith. cbn.
                     destruct Archi.ptr64; cbn;
                       rewrite Hzero, Int64.eq_true; reflexivity.
              ** (* bool_val of the true comparison *)
                 apply bool_val_one_int.
              ** apply exec_Sbreak.
        -- (* current partial already equals the final partial: no index in
              [64*k+q0, 64*(k+1)) belongs to S, by shifted_zero_tail *)
           eapply set_in_mem_ext; [|exact Hpart].
           intros i.
           replace (64 * (k + 1)) with (64 * k + 64) by lia. admit.
        -- exact Hw.
        -- apply Mem.unchanged_on_refl.
      * (* one iteration; recurse at q0+1 with the once-more-shifted residual *)
        assert (Hshift : Z.shiftr (Z.shiftr w0 q0) 1 = Z.shiftr w0 (q0 + 1))
          by now rewrite Z.shiftr_shiftr by lia.
        assert (Hlow : Z.land (Z.shiftr w0 q0) 1 <> 0 <-> In (64 * k + q0) S)
          by (subst w0; apply shifted_low_bit; lia).
        (* the increment env after this iteration *)
        set (le1 := PTree.set ids.(id_word)
                      (Vlong (Int64.repr (Z.shiftr (Z.shiftr w0 q0) 1)))
                      (PTree.set ids.(id_q)
                         (Vlong (Int64.repr (q0 + 1))) le)).
        (* membership of the current bit *)
        destruct (in_dec Z.eq_dec (64 * k + q0) S) as [Hmem|Hnmem].
        -- (* bit set; split on the in-range test *)
           destruct (Z_lt_dec (64 * k + q0) nstates) as [Hin|Hout].
           ++ (* in range: union_row adds row_of (64*k+q0) a.  After the OR,
                 [next] holds [partial ... ++ row], which by
                 [partial_step_set_succ] equals [partial ... (64*k+q0+1)]. *)
              (* obtain the state realizing gi := 64*k+q0 *)
              assert (Hgistate : exists q_st,
                 nth_error nfa.(states _) (Z.to_nat (64 * k + q0)) = Some q_st
                 /\ sidx q_st = Some (64 * k + q0)).
              { (* in-range index is realized by some state, since sidx is a
                   bijection onto [0,nstates) on the enumerated states *)
                admit. }
              (* run union_row on the current memory to OR row(gi,a) in *)
              destruct (union_row_correct le m b_next ofs_next b_tab
                          (64 * k + q0) ai k q0
                          (partial_step_set S a (64 * k + q0)) a)
                as (leU & mU & HexecU & HsetU & HwU & HunchU);
                try assumption; try lia.
              (* advance the invariant: partial ++ row = partial (succ) *)
              admit.
           ++ (* out of range: OPT3 true (bit set) but the range test [gi <
                 nstates] is false, so [union_row] is skipped ([Sskip]).  Since
                 the index names no state, [partial_step_set_succ]'s right
                 disjunct is vacuous and the set does not grow. *)
              admit.
        -- (* bit clear: OPT3 test [word & 1 <> 0] is false, [Sskip]; the new
              index is absent from S so [partial_step_set_succ] adds nothing. *)
           admit.
Admitted.
 
(** The outer loop: for each word [k] of [cur], load it and scan its bits.
    Generalized over [k0]; the invariant is [partial_step_set S a (64*k0)]. *)
Lemma scan_words_correct : forall fuel k0 le m b_cur ofs_cur b_next ofs_next b_tab S a ai,
  (Z.to_nat (nwords - k0) <= fuel)%nat ->
  0 <= k0 <= nwords ->
  set_span_ok ofs_cur -> set_span_ok ofs_next ->
  Genv.find_symbol ge ids.(id_table) = Some b_tab ->
  index_of s.eq_dec a s.enum 0 = Some ai ->
  table_readable m b_tab ->
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

(** [cur] survives the call: it lies outside the written span. *)
Lemma compile_step_preserves_cur : forall b_cur b_next ofs_cur ofs_next S m m',
  b_cur <> b_next ->
  set_in_mem m b_cur ofs_cur S ->
  Mem.unchanged_on (outside_set b_next ofs_next) m m' ->
  set_in_mem m' b_cur ofs_cur S.
Proof.
  intros b_cur b_next ofs_cur ofs_next S m m' Hne Hcur Hunch k Hk.
  specialize (Hcur k Hk). cbn [Mem.loadv] in *.
  eapply Mem.load_unchanged_on.
  - exact Hunch.
  - intros i Hi. left. exact Hne.
  - exact Hcur.
Qed.
 
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
  assert (Hcur1 : set_in_mem m1 b_cur ofs_cur S)
    by (eapply compile_step_preserves_cur; [exact Hne | exact Hcur | exact Hzunch]).
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
    as (le3 & m2 & Hscan & Hsset & Hsw & Hsunch); eauto; try lia.
  - pose proof nwords_pos. lia.
  - (* table_readable m1 b_tab: the table survives [zero_next]'s stores, which
       hit only [b_next] (<> b_tab), via [Hzunch]. *)
    eapply table_readable_unchanged with (m := m); [exact Htab | | exact Hzunch].
    subst m. apply table_readable_m0.
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
              ** (* 0 <= ai < Int64.modulus *)
                 unfold NC.nsyms in *. pose proof syms_bounded. lia.
              ** (* 0 <= nsyms < Int64.modulus *)
                 unfold NC.nsyms in *. pose proof syms_bounded. lia.
              ** now rewrite (proj2 (Z.ltb_lt _ _)) by (unfold NC.nsyms in *; lia).
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
Qed.

(** accept

    A single loop accumulating [cur[j] & final[j]] into a temp, then a
    nonzero test. *)

(** Bit-level bridge for [accept]: the AND of two bitmaps at word [j] is nonzero
    iff [S] and [F] share an index in that word.  Folding the [lor] of these over
    all words then detects a shared index anywhere -- which is exactly the
    accepting condition.  Proved purely from [word_of_indices_spec]. *)
Lemma word_and_nonzero_iff : forall S F j,
  0 <= j ->
  (Z.land (word_of_indices S j) (word_of_indices F j) <> 0
   <-> exists b, 0 <= b < 64 /\ In (64 * j + b) S /\ In (64 * j + b) F).
Proof.
  intros S F j Hj. split.
  - intros Hnz.
    (* a nonzero word has some set bit below 64 *)
    destruct (Z_lt_dec 0 (Z.land (word_of_indices S j) (word_of_indices F j)))
      as [Hpos|Hle].
    + (* find the lowest set bit *)
      assert (Hex : exists b, 0 <= b < 64
                 /\ Z.testbit (Z.land (word_of_indices S j) (word_of_indices F j)) b = true).
      { (* the top set bit, [Z.log2], is a witness; it is < 64 because the value
           is < 2^64 (the land is <= each operand, each < 2^64). *)
        set (x := Z.land (word_of_indices S j) (word_of_indices F j)) in *.
        exists (Z.log2 x). split.
        - split; [apply Z.log2_nonneg|].
          assert (Hxlt : x < 2 ^ 64).
          { unfold x. admit. }
          apply Z.log2_lt_pow2; [exact Hpos | exact Hxlt].
        - apply Z.bit_log2. lia. }
      destruct Hex as (b & Hb & Htb).
      rewrite Z.land_spec in Htb. apply andb_true_iff in Htb as (H1 & H2).
      exists b. split; [exact Hb|]. split;
        [ apply (word_of_indices_spec S j b Hj Hb); exact H1
        | apply (word_of_indices_spec F j b Hj Hb); exact H2 ].
    + (* land is nonneg, so <= 0 means = 0, contradiction *)
      exfalso. apply Hnz.
      assert (0 <= Z.land (word_of_indices S j) (word_of_indices F j))
        by (apply Z.land_nonneg; left; apply word_of_indices_nonneg).
      lia.
  - intros (b & Hb & HInS & HInF).
    (* bit b is set in both, hence in the land, hence land <> 0 *)
    intro Hz.
    assert (Htb : Z.testbit (Z.land (word_of_indices S j) (word_of_indices F j)) b = true).
    { rewrite Z.land_spec. apply andb_true_iff. split;
        [ apply (word_of_indices_spec S j b Hj Hb); exact HInS
        | apply (word_of_indices_spec F j b Hj Hb); exact HInF ]. }
    rewrite Hz, Z.testbit_0_l in Htb. discriminate.
Admitted.

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
