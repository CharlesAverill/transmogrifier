From lstar Require Import Automata.
From compcert Require Import AST Clight Ctypes Integers Cop Maps.
From compcert Require Import ClightBigstep Values Events Coqlib.
From compcert Require Import Globalenvs Memory.
From Transmogrifier Require Import Monads.
From Transmogrifier.compiler Require Import dfa.
From Stdlib Require Import List ZArith Lia.
Import ListNotations.
Open Scope result_scope.
Open Scope Z_scope.

(** Correctness of the DFA -> Clight compiler. *)

Module Correctness (s : Symbol) (DFA : DFAType s).

Module DC := DFACompiler s DFA.
Import DC DFA.

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

Lemma index_of_func : forall l x i j k,
  index_of eq_dec x l k = Some i ->
  index_of eq_dec x l k = Some j ->
  i = j.
Proof. intros. congruence. Qed.

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

Lemma enumerate_nth : forall (l : list X) i x,
  0 <= i < Z.of_nat (length l) ->
  nth_error l (Z.to_nat i) = Some x ->
  In (i, x) (enumerate l).
Proof.
  clear. intros. unfold enumerate. apply nth_error_In with (n := Z.to_nat i).
  rewrite nth_error_combine, H0, nth_error_map, nth_error_seq. simpl.
  unfold Datatypes.option_map. replace (_ <? _)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  now rewrite Z2Nat.id by lia.
Qed.

Lemma index_of_nth_error : forall (l : list X) x i k,
  index_of eq_dec x l k = Some i ->
  nth_error l (Z.to_nat (i - k)) = Some x.
Proof.
  induction l; intros; simpl in *.
    discriminate.
  destruct eq_dec.
    inversion H. rewrite Z.sub_diag. now subst.
  pose proof (index_of_ge _ _ _ _ H).
  apply IHl in H.
  now replace (Z.to_nat (i - k)) with (S (Z.to_nat (i - Z.succ k))) by lia.
Qed.

Lemma enumerate_spec : forall (l : list X) x i,
  index_of eq_dec x l 0 = Some i -> In (i, x) (enumerate l).
Proof.
  intros. apply enumerate_nth.
    eauto using index_of_bounds.
  apply index_of_nth_error in H. now rewrite Z.sub_0_r in H.
Qed.

Lemma enumerate_In_bounds : forall (l : list X) i x,
  In (i, x) (enumerate l) -> 0 <= i < Z.of_nat (length l).
Proof.
  intros. unfold enumerate in H. apply in_combine_l, in_map_iff in H.
  destruct H, H. apply in_seq in H0. lia.
Qed.

Lemma map_fst_combine : forall (A B : Type) (la : list A) (lb : list B),
  length la = length lb ->
  map fst (combine la lb) = la.
Proof.
  induction la; intros; simpl in *.
    reflexivity.
  destruct lb; simpl in *.
    discriminate.
  f_equal. apply IHla. now inversion H.
Qed.

Lemma list_seq_norepet : forall y x,
  list_norepet (seq x y).
Proof.
  induction y; intros.
    constructor.
  simpl. constructor.
    rewrite in_seq. lia.
  apply IHy.
Qed.

Lemma enumerate_index_norepet : forall (l : list X),
  list_norepet (map fst (enumerate l)).
Proof.
  intros. unfold enumerate.
  rewrite map_fst_combine by (rewrite length_map, length_seq; lia).
  apply list_map_norepet.
    apply list_seq_norepet.
  intros. intro Contra. now apply Nat2Z.inj in Contra.
Qed.

End index.

Section correctness.
Variable state : Type.
Variable dfa : DFA.t state.
Variable state_eq_dec : forall (x y : state), {x = y} + {x <> y}.

(** Well-formedness: the state and symbol enumerations fit in [tlong] *)
Variable states_bounded : Z.of_nat (length dfa.(states _)) < Int64.modulus.
Variable syms_bounded   : 0 < Z.of_nat (length s.enum) < Int64.modulus.

Variable base : ident.
Variable p : Clight.program.
Variable Hp : compile_program state dfa state_eq_dec base = Ok p.

Definition ge : genv := Clight.globalenv p.

Definition ids : idents := alloc_idents base.

Lemma compile_program_defs :
  prog_defs p =
    [ (ids.(id_table),  Gvar (compile_table state dfa state_eq_dec));
      (ids.(id_atable), Gvar (compile_atable state dfa));
      (ids.(id_delta),  Gfun (compile_delta state dfa ids));
      (ids.(id_accept), Gfun (compile_accept state dfa ids));
      (ids.(id_q0),     Gvar (compile_q0 state dfa state_eq_dec));
      (ids.(id_run),    Gfun (compile_run state dfa state_eq_dec ids));
      (ids.(id_main),   Gfun (compile_main ids)) ].
Proof.
  unfold ids. unfold compile_program in Hp.
  destruct Ctypes.make_program eqn:E; [|discriminate].
  inversion Hp; subst; clear Hp.
  unfold Ctypes.make_program in E.
  cbn in E.
  now inversion E.
Qed.

Lemma global_idents_norepet :
  list_norepet (map fst (prog_defs p)).
Proof.
  rewrite compile_program_defs.
  cbv [ids alloc_idents id_delta id_accept id_q0 id_run map fst].
  repeat constructor; cbn - [Pos.succ Pos.add]; intro H;
    repeat (destruct H as [H|H]; [lia|]); contradiction.
Qed.

Lemma compile_program_defs_ast :
  AST.prog_defs (program_of_program p) =
    [ (ids.(id_table),  Gvar (compile_table state dfa state_eq_dec));
      (ids.(id_atable), Gvar (compile_atable state dfa));
      (ids.(id_delta),  Gfun (compile_delta state dfa ids));
      (ids.(id_accept), Gfun (compile_accept state dfa ids));
      (ids.(id_q0),     Gvar (compile_q0 state dfa state_eq_dec));
      (ids.(id_run),    Gfun (compile_run state dfa state_eq_dec ids));
      (ids.(id_main),   Gfun (compile_main ids)) ].
Proof. exact compile_program_defs. Qed.

Lemma defmap_delta :
  (prog_defmap p) ! (ids.(id_delta)) =
    Some (Gfun (compile_delta state dfa ids)).
Proof.
  unfold prog_defmap. rewrite compile_program_defs_ast.
  apply PTree_Properties.of_list_norepet.
    rewrite <- compile_program_defs. apply global_idents_norepet.
  right. right. now left.
Qed.

Lemma find_delta_def :
  exists b,
    Genv.find_symbol ge ids.(id_delta) = Some b /\
    Genv.find_def ge b = Some (Gfun (compile_delta state dfa ids)).
Proof.
  apply Genv.find_def_symbol. apply defmap_delta.
Qed.

Lemma find_delta :
  exists b,
    Genv.find_symbol ge ids.(id_delta) = Some b /\
    Genv.find_funct ge (Vptr b Ptrofs.zero) =
      Some (compile_delta state dfa ids).
Proof.
  destruct find_delta_def as (b & Hsym & Hdef).
  exists b. split.
    assumption.
  unfold Genv.find_funct. rewrite pred_dec_true by reflexivity.
  now apply Genv.find_funct_ptr_iff.
Qed.

(* index of a state *)
Definition sidx (q : state) : option Z :=
  index_of state_eq_dec q dfa.(states _) 0.

(* index of a symbol *)
Definition symidx (a : s.t) : option Z :=
  index_of s.eq_dec a s.enum 0.

Lemma repr_inj_in_range : forall a b,
  0 <= a < Int64.modulus -> 0 <= b < Int64.modulus ->
  Int64.repr a = Int64.repr b -> a = b.
Proof.
  intros.
  rewrite <- Int64.unsigned_repr by (unfold Int64.max_unsigned; lia).
  rewrite <- Int64.unsigned_repr at 1 by (unfold Int64.max_unsigned; lia).
  now rewrite H1.
Qed.

Lemma bool_val_one : forall m, bool_val (Vint Int.one) tuint m = Some true.
Proof.
  intros m. unfold bool_val, tlong. simpl.
  destruct Archi.ptr64; cbn; rewrite Int.eq_false by apply Int.one_not_zero; reflexivity.
Qed.

Lemma bool_val_zero : forall m, bool_val (Vint Int.zero) tuint m = Some false.
Proof.
  intros m. unfold bool_val, tuint. simpl.
  destruct Archi.ptr64; cbn; rewrite Int.eq_true; reflexivity.
Qed.

Lemma bool_val_one_int : forall m, bool_val (Vint Int.one) tint m = Some true.
Proof.
  intros m. unfold bool_val, tint. cbn.
  destruct Archi.ptr64; cbn; rewrite Int.eq_false by apply Int.one_not_zero; reflexivity.
Qed.

Lemma bool_val_zero_int : forall m, bool_val (Vint Int.zero) tint m = Some false.
Proof.
  intros m. unfold bool_val, tint. cbn.
  destruct Archi.ptr64; cbn; rewrite Int.eq_true; reflexivity.
Qed.

Lemma fold_left_preserves_head : forall (A B : Type) (f : A -> B -> A) (P : A -> Prop) (l : list B) (a : A),
  P a ->
  (forall x b, In b l -> P x -> P (f x b)) ->
  P (fold_left f l a).
Proof.
  induction l; intros; simpl in *.
    assumption.
  apply IHl.
    apply H0. now left. assumption.
  intros. apply H0. now right. assumption.
Qed.

(* delta lookup table *)

Lemma nth_error_flat_map_uniform :
  forall (A B : Type) (f : A -> list B) (l : list A) (k : nat),
  (forall x, In x l -> length (f x) = k) ->
  forall i j x,
  nth_error l i = Some x ->
  (j < k)%nat ->
  nth_error (flat_map f l) (i * k + j) = nth_error (f x) j.
Proof. clear.
  induction l; intros k Hk i j x Hi Hj; simpl in *.
    now destruct i.
  destruct i; simpl in *.
  - (* head row: index j lands inside (f a) *)
    inversion Hi; subst; clear Hi.
    rewrite nth_error_app1.
      reflexivity.
    rewrite Hk by now left. assumption.
  - (* later row: skip past (f a), which has length k *)
    rewrite nth_error_app2.
      rewrite Hk by now left.
      replace (k + i * k + j - k)%nat with (i * k + j)%nat by lia. eauto.
    rewrite Hk. lia. now left.
Qed.

Lemma enumerate_nth_error_pair : forall (X : Type) (l : list X) i,
  0 <= i < Z.of_nat (length l) ->
  exists x, nth_error (enumerate l) (Z.to_nat i) = Some (i, x)
            /\ nth_error l (Z.to_nat i) = Some x.
Proof.
  intros. unfold enumerate.
  destruct (nth_error l (Z.to_nat i)) eqn:E.
  - exists x. split; [|reflexivity].
    rewrite nth_error_combine, E, nth_error_map, nth_error_seq.
    cbn. replace (match Datatypes.length l with
           | 0%nat => false
           | S m' => (Z.to_nat i <=? m')%nat
           end) with true.
      cbn. now rewrite Z2Nat.id by lia.
    symmetry. destruct (Datatypes.length l) eqn:El.
      lia.
    apply Nat.leb_le. lia.
  - exfalso. apply nth_error_None in E. lia.
Qed.

Lemma table_row_length : forall q,
  length (table_row state dfa state_eq_dec q) = length s.enum.
Proof.
  intros. unfold table_row, sym_table, enumerate.
  rewrite length_map, length_combine, length_map, length_seq. lia.
Qed.

Lemma table_entry_correct : forall q sym q_idx s_idx,
  sidx q = Some q_idx ->
  symidx sym = Some s_idx ->
  nth_error (table_init state dfa state_eq_dec)
    (Z.to_nat (q_idx * nsyms + s_idx))
  = Some (Init_int64 (Int64.repr (table_entry state dfa state_eq_dec q sym))).
Proof.
  intros q sym q_idx s_idx Hq Hs.
  assert (Hqb : 0 <= q_idx < Z.of_nat (length dfa.(states _)))
    by (unfold sidx in Hq; eauto using index_of_bounds).
  assert (Hsb : 0 <= s_idx < Z.of_nat (length s.enum))
    by (unfold symidx in Hs; eauto using index_of_bounds).
  (* the q_idx-th row of state_table is (q_idx, q) *)
  assert (Hrow : nth_error (state_table state dfa) (Z.to_nat q_idx) = Some (q_idx, q)).
    { unfold state_table.
      destruct (enumerate_nth_error_pair _ (states state dfa) q_idx Hqb)
        as (q' & Hpair & Hnth).
      unfold sidx in Hq. apply index_of_nth_error in Hq.
      rewrite Z.sub_0_r in Hq. rewrite Hq in Hnth.
      inversion Hnth; subst. exact Hpair. }
  (* the s_idx-th entry of the row is delta q sym *)
  assert (Hcol : nth_error (table_row state dfa state_eq_dec q) (Z.to_nat s_idx)
                 = Some (Init_int64 (Int64.repr (table_entry state dfa state_eq_dec q sym)))).
    { unfold table_row, sym_table.
      rewrite nth_error_map.
      destruct (enumerate_nth_error_pair _ s.enum s_idx Hsb)
        as (sym' & Hpair & Hnth).
      unfold symidx in Hs. apply index_of_nth_error in Hs.
      rewrite Z.sub_0_r in Hs. rewrite Hs in Hnth.
      inversion Hnth; subst.
      now rewrite Hpair. }
  unfold table_init.
  replace (Z.to_nat (q_idx * nsyms + s_idx))
    with (Z.to_nat q_idx * length s.enum + Z.to_nat s_idx)%nat
    by (unfold nsyms; lia).
  rewrite nth_error_flat_map_uniform with (k := length s.enum) (x := (q_idx, q)).
  - exact Hcol.
  - intros (qi & qq) _. apply table_row_length.
  - exact Hrow.
  - lia.
Qed.

Variable m0 : mem.
Variable Hinit : Genv.init_mem p = Some m0.

Lemma find_table :
  exists b,
    Genv.find_symbol ge ids.(id_table) = Some b /\
    Genv.find_def ge b = Some (Gvar (compile_table state dfa state_eq_dec)).
Proof.
  apply Genv.find_def_symbol.
  apply prog_defmap_norepet.
    apply global_idents_norepet.
  pose proof compile_program_defs as Hdefs.
  change (AST.prog_defs p) with (prog_defs p).
  rewrite Hdefs. now left.
Qed.

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
    now rewrite Z.add_0_r.
  - destruct (Hall a) as (x & Hx); [now left|]. subst a.
    destruct Hlsid as (_ & Hrest). cbn - [Z.of_nat] in Hrest.
    replace (base_ofs + 8 * Z.of_nat (S n))
      with ((base_ofs + 8) + 8 * Z.of_nat n) by lia.
    eapply IHil; eauto.
Qed.

Lemma init_data_list_nth_load_int32 :
  forall (F V : Type) (ge' : Genv.t F V) b il n v m base_ofs,
  (forall id, In id il -> exists x, id = Init_int32 x) ->
  Genv.load_store_init_data ge' m b base_ofs il ->
  nth_error il n = Some (Init_int32 v) ->
  Mem.load Mint32 m b (base_ofs + 4 * Z.of_nat n) = Some (Vint v).
Proof. clear.
  induction il; intros n v m base_ofs Hall Hlsid Hnth.
    now destruct n.
  destruct n; cbn - [Z.of_nat Z.mul] in *.
  - inversion Hnth; subst; clear Hnth.
    destruct Hlsid as (Hload & _).
    now rewrite Z.mul_0_r, Z.add_0_r.
  - destruct (Hall a) as (x & Hx); [now left|]. subst a.
    destruct Hlsid as (_ & Hrest). cbn - [Z.of_nat] in Hrest.
    replace (base_ofs + 4 * Z.of_nat (S n))
      with ((base_ofs + 4) + 4 * Z.of_nat n) by lia.
    eapply IHil; eauto.
Qed.

Lemma table_init_all_int64 : forall id,
  In id (table_init state dfa state_eq_dec) -> exists x, id = Init_int64 x.
Proof.
  intros. unfold table_init in H.
  apply in_flat_map in H. destruct H as ((qi & q) & _ & Hin).
  unfold table_row in Hin. apply in_map_iff in Hin.
  destruct Hin as ((si & sy) & Heq & _). subst. eauto.
Qed.

Variable table_bounded : 8 * (Z.of_nat (length dfa.(states _)) * Z.of_nat (length s.enum))
                         < Ptrofs.modulus.

Lemma table_in_mem : forall b k v,
  Genv.find_symbol ge ids.(id_table) = Some b ->
  nth_error (table_init state dfa state_eq_dec) (Z.to_nat k) = Some (Init_int64 v) ->
  0 <= k < (nstates state dfa) * nsyms ->
  Mem.loadv Mint64 m0 (Vptr b (Ptrofs.repr (8 * k))) = Some (Vlong v).
Proof.
  intros b k v Hsym Hnth Hk.
  destruct find_table as (b' & Hsym' & Hdef).
  assert (b' = b) by congruence. subst b'.
  assert (Hvi : Genv.find_var_info ge b = Some (compile_table state dfa state_eq_dec)).
    { apply Genv.find_var_info_iff. exact Hdef. }
  destruct (Genv.init_mem_characterization _ _ Hvi Hinit)
    as (_ & _ & Hlsid & _).
  specialize (Hlsid eq_refl).
  cbn [Mem.loadv].
  rewrite Ptrofs.unsigned_repr.
  - replace (8 * k) with (0 + 8 * Z.of_nat (Z.to_nat k)) by lia.
    eapply init_data_list_nth_load; eauto.
    apply table_init_all_int64.
  - unfold Ptrofs.max_unsigned. unfold nstates, nsyms in Hk. lia.
Qed.

Lemma atable_entry_correct : forall q q_idx,
  sidx q = Some q_idx ->
  nth_error (atable_init state dfa) (Z.to_nat q_idx)
  = Some (Init_int32 (Int.repr (accept_entry state dfa q))).
Proof.
  intros q q_idx Hq.
  assert (Hqb : 0 <= q_idx < Z.of_nat (length dfa.(states _)))
    by (unfold sidx in Hq; eauto using index_of_bounds).
  unfold atable_init, state_table. rewrite nth_error_map.
  destruct (enumerate_nth_error_pair _ (states state dfa) q_idx Hqb)
    as (q' & Hpair & Hnth).
  unfold sidx in Hq. apply index_of_nth_error in Hq.
  rewrite Z.sub_0_r in Hq. rewrite Hq in Hnth.
  inversion Hnth; subst.
  now rewrite Hpair.
Qed.

Lemma alloc_idents_norepet : forall base,
  Coqlib.list_norepet [(alloc_idents base).(id_q); (alloc_idents base).(id_s)].
Proof.
  intros. cbv [id_q alloc_idents id_s].
  repeat constructor. intros [H|[]]. lia. now intro.
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
    subst; destruct (j <? k) eqn:E;
      [ rewrite zlt_true by lia | rewrite zlt_false by lia
      | rewrite zlt_true by lia | rewrite zlt_false by lia ];
      reflexivity.
Qed.

Lemma nsyms_bound : 0 <= DC.nsyms <= Int64.max_unsigned.
Proof.
  unfold DC.nsyms, Int64.max_unsigned.
  pose proof (Nat2Z.is_nonneg (Datatypes.length s.enum)). lia.
Qed.

Lemma nstates_bound : 0 <= DC.nstates state dfa <= Int64.max_unsigned.
Proof.
  unfold DC.nstates, Int64.max_unsigned.
  pose proof (Nat2Z.is_nonneg (Datatypes.length (states state dfa))). lia.
Qed.

Lemma mul_repr_in_range : forall a b,
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.mul (Int64.repr a) (Int64.repr b) = Int64.repr (a * b).
Proof.
  intros. unfold Int64.mul. now rewrite !Int64.unsigned_repr by assumption.
Qed.

Lemma add_repr_in_range : forall a b,
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  intros. rewrite Int64.add_unsigned. now rewrite !Int64.unsigned_repr by assumption.
Qed.

Lemma ptrofs_le_int64 : Ptrofs.modulus <= Int64.modulus.
Proof.
  unfold Ptrofs.modulus, Int64.modulus, Ptrofs.wordsize, Int64.wordsize,
         Wordsize_Ptrofs.wordsize, Wordsize_64.wordsize, two_power_nat.
  destruct Archi.ptr64; cbn; lia.
Qed.

Lemma ptr_add_normalize : forall ofs i,
  0 <= ofs -> 0 <= i -> ofs + 8 * i < Ptrofs.modulus ->
  Ptrofs.add (Ptrofs.repr ofs)
    (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr i)))
  = Ptrofs.repr (ofs + 8 * i).
Proof.
  intros.
  pose proof ptrofs_le_int64.
  unfold Ptrofs.add, Ptrofs.mul, Ptrofs.of_int64.
  rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; lia).
  repeat rewrite Ptrofs.unsigned_repr_eq.
  rewrite (Zmod_small ofs) by lia.
  rewrite (Zmod_small i) by lia.
  rewrite (Zmod_small 8).
  - now rewrite (Zmod_small (8 * i)) by lia.
  - unfold Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize, two_power_nat.
    destruct Archi.ptr64; cbn; lia.
Qed.

Lemma table_entry_sidx : forall q sym next_idx,
  sidx (dfa.(transition _) q sym) = Some next_idx ->
  table_entry state dfa state_eq_dec q sym = next_idx.
Proof. intros. unfold table_entry, sidx in *. now rewrite H. Qed.

(** delta is correct on valid indices *)

Lemma compile_delta_correct : forall q sym q_idx s_idx next_idx,
  sidx q = Some q_idx ->
  symidx sym = Some s_idx ->
  sidx (dfa.(transition _) q sym) = Some next_idx ->
  eval_funcall function_entry2 ge m0
    (compile_delta state dfa ids)
    [Vlong (Int64.repr q_idx); Vlong (Int64.repr s_idx)] E0 m0
    (Vlong (Int64.repr next_idx)).
Proof.
  set (nstates := nstates state dfa).
  intros. destruct find_table as (tb & Hsym & _).
  assert (Hq : 0 <= q_idx < nstates) by (unfold sidx, nstates, DC.nstates in *; apply index_of_bounds in H; lia).
  assert (Hs : 0 <= s_idx < nsyms) by (unfold symidx, nsyms, DC.nstates in *; apply index_of_bounds in H0; lia).
  assert (Hprod : 0 <= q_idx * DC.nsyms + s_idx < DC.nstates state dfa * DC.nsyms).
    { unfold DC.nstates, DC.nsyms in *. nia. }
  assert (Hpb : 8 * (q_idx * DC.nsyms + s_idx) < Ptrofs.modulus).
    { unfold DC.nstates, DC.nsyms in *. nia. }
  econstructor; try easy.
  - econstructor; cbn - [Pos.add]; try solve [constructor].
      apply alloc_idents_norepet.
      now repeat intro.
  - cbn [fn_body]. econstructor.
    + (* guard: (q < |Q|) & (s < |Sigma|) evaluates to Int.one *)
      econstructor.
      * (* left conjunct *)
        eapply eval_lt_test_gen with (j := q_idx) (bv := Int.one).
        -- cbn - [Pos.add].
           rewrite PTree.gso by (cbv [ids alloc_idents id_q id_s]; lia).
           apply PTree.gss.
        -- unfold nstates, DC.nstates in Hq. lia.
        -- unfold DC.nstates. lia.
        -- now rewrite (proj2 (Z.ltb_lt _ _)) by (unfold DC.nstates in Hq; lia).
      * (* right conjunct *)
        eapply eval_lt_test_gen with (j := s_idx) (bv := Int.one).
        -- cbn - [Pos.add]. apply PTree.gss.
        -- unfold DC.nsyms in Hs. lia.
        -- unfold DC.nsyms. lia.
        -- now rewrite (proj2 (Z.ltb_lt _ _)).
      * (* sem_binary_operation Oand *)
        cbn. unfold sem_and, sem_binarith, sem_cast, classify_cast,
                    classify_binarith, tint. cbn.
        destruct Archi.ptr64; cbn; reflexivity.
    + apply bool_val_one_int.
    + eapply exec_Sreturn_some.
      eapply eval_Elvalue.
      * (* eval_lvalue of the Ederef *)
        econstructor.   (* eval_Ederef: needs eval_expr of the Ebinop *)
        econstructor.   (* eval_Ebinop *)
        -- (* Evar table decays to Vptr tb 0 *)
           eapply eval_Elvalue.
             eapply eval_Evar_global.
               apply PTree.gempty.
               exact Hsym.
             eapply deref_loc_reference. reflexivity.
        -- (* q * |Sigma| + s *)
           unfold table_index.
           assert (Hqb : 0 <= q_idx <= Int64.max_unsigned).
             { pose proof nstates_bound. unfold DC.nstates in Hq. lia. }
           assert (Hsb : 0 <= s_idx <= Int64.max_unsigned).
             { pose proof nsyms_bound. unfold nsyms, DC.nsyms in Hs.
              unfold Int64.max_unsigned. lia. }
           assert (Hmb : 0 <= q_idx * DC.nsyms <= Int64.max_unsigned).
             { pose proof nsyms_bound. pose proof ptrofs_le_int64.
               unfold DC.nstates, DC.nsyms, Int64.max_unsigned in *. nia. }
           econstructor.
           ++ econstructor.
              ** econstructor. cbn - [Pos.add].
                 rewrite PTree.gso by (cbv [ids alloc_idents id_q id_s]; lia).
                 apply PTree.gss.
              ** econstructor.
              ** cbn. unfold sem_mul, sem_binarith, sem_cast, classify_cast,
                             classify_binarith, tlong. cbn.
                 destruct Archi.ptr64; cbn;
                   rewrite mul_repr_in_range by (assumption || apply nsyms_bound);
                   reflexivity.
           ++ econstructor. cbn - [Pos.add]. apply PTree.gss.
           ++ cbn. unfold sem_add, classify_add, tlong. cbn.
              unfold sem_binarith, sem_cast, classify_cast, classify_binarith. cbn.
              destruct Archi.ptr64; cbn;
                rewrite add_repr_in_range by assumption;
                reflexivity.
        -- (* sem_add: table + 8*(q*|Sigma|+s) *)
           cbn. unfold sem_add, classify_add, table_type, tlong. cbn.
           destruct Archi.ptr64 eqn:E; [|discriminate].
           unfold sem_add_ptr_long. cbn.
           do 2 f_equal.
      * (* deref_loc: the actual load *)
        eapply deref_loc_value with (chunk := Mint64).
          reflexivity.
        change Ptrofs.zero with (Ptrofs.repr 0).
        rewrite ptr_add_normalize by
          (pose proof ptrofs_le_int64; unfold DC.nstates, DC.nsyms in *; nia).
        rewrite Z.add_0_l.
        eapply table_in_mem.
        -- exact Hsym.
        -- apply table_entry_correct; eassumption.
        -- unfold DC.nstates, DC.nsyms in *. nia.
  - cbn. split. discriminate.
    unfold tlong, sem_cast, classify_cast. destruct Archi.ptr64; simpl;
      now rewrite (table_entry_sidx q sym next_idx H1).
  - reflexivity.
Qed.

Lemma atable_init_all_int32 : forall id,
  In id (atable_init state dfa) -> exists x, id = Init_int32 x.
Proof.
  intros. unfold atable_init in H.
  apply in_map_iff in H. destruct H as ((qi & q) & Heq & _). subst. eauto.
Qed.

Lemma find_atable :
  exists b,
    Genv.find_symbol ge ids.(id_atable) = Some b /\
    Genv.find_def ge b = Some (Gvar (compile_atable state dfa)).
Proof.
  apply Genv.find_def_symbol.
  apply prog_defmap_norepet.
    apply global_idents_norepet.
  pose proof compile_program_defs as Hdefs.
  change (AST.prog_defs p) with (prog_defs p).
  rewrite Hdefs. right. now left.
Qed.

Lemma atable_in_mem : forall b k v,
  Genv.find_symbol ge ids.(id_atable) = Some b ->
  nth_error (atable_init state dfa) (Z.to_nat k) = Some (Init_int32 v) ->
  0 <= k < nstates state dfa ->
  Mem.loadv Mint32 m0 (Vptr b (Ptrofs.repr (4 * k))) = Some (Vint v).
Proof.
  intros b k v Hsym Hnth Hk.
  destruct find_atable as (b' & Hsym' & Hdef).
  assert (b' = b) by congruence. subst b'.
  assert (Hvi : Genv.find_var_info ge b = Some (compile_atable state dfa)).
    { apply Genv.find_var_info_iff. exact Hdef. }
  destruct (Genv.init_mem_characterization _ _ Hvi Hinit)
    as (_ & _ & Hlsid & _).
  specialize (Hlsid eq_refl).
  cbn [Mem.loadv].
  rewrite Ptrofs.unsigned_repr.
  - replace (4 * k) with (0 + 4 * Z.of_nat (Z.to_nat k)) by lia.
    eapply init_data_list_nth_load_int32; eauto.
    apply atable_init_all_int32.
  - assert (Hq8 : 8 * Z.of_nat (Datatypes.length (states state dfa))
                  <= 8 * (Z.of_nat (Datatypes.length (states state dfa))
                          * Z.of_nat (Datatypes.length s.enum))) by nia.
    unfold Ptrofs.max_unsigned, DC.nstates in *. lia.
Qed.

Lemma ptr_add_normalize_gen : forall sz ofs i,
  0 < sz -> 0 <= ofs -> 0 <= i ->
  ofs + sz * i < Ptrofs.modulus ->
  sz < Ptrofs.modulus ->
  Ptrofs.add (Ptrofs.repr ofs)
    (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_int64 (Int64.repr i)))
  = Ptrofs.repr (ofs + sz * i).
Proof.
  intros sz ofs i Hsz Hofs Hi Hbound Hszb.
  pose proof ptrofs_le_int64.
  assert (Hib : i < Ptrofs.modulus) by nia.
  unfold Ptrofs.add, Ptrofs.mul, Ptrofs.of_int64.
  rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; lia).
  repeat rewrite Ptrofs.unsigned_repr_eq.
  rewrite (Zmod_small ofs) by lia.
  rewrite (Zmod_small i) by lia.
  rewrite (Zmod_small sz) by lia.
  now rewrite (Zmod_small (sz * i)) by nia.
Qed.

Lemma accept_entry_val : forall q,
  Int.repr (accept_entry state dfa q) = (if dfa.(accept _) q then Int.one else Int.zero).
Proof. intros. unfold accept_entry. destruct accept; reflexivity. Qed.

Lemma compile_accept_correct : forall q q_idx,
  sidx q = Some q_idx ->
  eval_funcall function_entry2 ge m0
    (compile_accept state dfa ids)
    [Vlong (Int64.repr q_idx)] E0 m0
    (Vint (if dfa.(accept _) q then Int.one else Int.zero)).
Proof.
  intros q q_idx Hq.
  destruct find_atable as (ab & Hsym & _).
  assert (Hqb : 0 <= q_idx < DC.nstates state dfa)
    by (unfold sidx in Hq; apply index_of_bounds in Hq; unfold DC.nstates; lia).
  econstructor.
  - econstructor; cbn - [Pos.add]; try solve [constructor].
      constructor. now intro. constructor.
      now repeat intro.
  - cbn [fn_body]. econstructor.
    + eapply eval_lt_test_gen with (j := q_idx) (bv := Int.one).
      * cbn - [Pos.add]. apply PTree.gss.
      * pose proof nstates_bound. unfold Int64.max_unsigned in *. lia.
      * pose proof nstates_bound. unfold Int64.max_unsigned in *. lia.
      * now rewrite (proj2 (Z.ltb_lt _ _)) by lia.
    + apply bool_val_one_int.
    + eapply exec_Sreturn_some.
      eapply eval_Elvalue.
      * econstructor. econstructor.
        -- eapply eval_Elvalue.
             eapply eval_Evar_global.
               apply PTree.gempty.
               exact Hsym.
             eapply deref_loc_reference. reflexivity.
        -- econstructor. cbn - [Pos.add]. apply PTree.gss.
        -- cbn. unfold sem_add, classify_add, atable_type, tbool, tlong. cbn.
           destruct Archi.ptr64 eqn:E; [|discriminate].
           reflexivity.
      * eapply deref_loc_value with (chunk := Mint32).
          reflexivity.
        change Ptrofs.zero with (Ptrofs.repr 0).
        rewrite ptr_add_normalize_gen with (sz := 4); try lia.
        rewrite Z.add_0_l.
          eapply atable_in_mem; eauto using atable_entry_correct.
          unfold DC.nstates in *.
        assert (Hq8 : 8 * Z.of_nat (Datatypes.length (states state dfa))
                <= 8 * (Z.of_nat (Datatypes.length (states state dfa))
                        * Z.of_nat (Datatypes.length s.enum)))
            by nia.
          lia.
        assert (Hq8 : 8 * DC.nstates state dfa
                            <= 8 * (DC.nstates state dfa * DC.nsyms)) by
                (unfold DC.nstates, DC.nsyms in *; nia).
              unfold DC.nstates, DC.nsyms in *; lia.
  - cbn. split. discriminate. unfold accept_entry. destruct accept.
      now rewrite Int.eq_false.
      now rewrite Int.eq_true.
  - reflexivity.
Qed.

(** delta returns the sink on out-of-range indices *)

Lemma compile_delta_sink : forall q_idx s_idx m,
  0 <= q_idx < Int64.modulus ->
  0 <= s_idx < Int64.modulus ->
  q_idx >= DC.nstates state dfa ->
  eval_funcall function_entry2 ge m
    (compile_delta state dfa ids)
    [Vlong (Int64.repr q_idx); Vlong (Int64.repr s_idx)] E0 m
    (Vlong (Int64.repr (sink_index state dfa))).
Proof.
  intros q_idx s_idx m Hq Hs Hoob.
  econstructor.
  - econstructor; cbn - [Pos.add]; try solve [constructor].
      apply alloc_idents_norepet.
      now repeat intro.
  - cbn [fn_body]. eapply exec_Sifthenelse with (b := false).
    + (* guard: (q < |Q|) & (s < |Sigma|) evaluates to Int.zero *)
      econstructor.
      * eapply eval_lt_test_gen with (j := q_idx) (bv := Int.zero).
        -- cbn - [Pos.add].
           rewrite PTree.gso by (cbv [ids alloc_idents id_q id_s]; lia).
           apply PTree.gss.
        -- assumption.
        -- pose proof nstates_bound. unfold Int64.max_unsigned in *. lia.
        -- now rewrite (proj2 (Z.ltb_ge _ _)) by lia.
      * eapply eval_lt_test_gen with (j := s_idx).
        -- cbn - [Pos.add]. apply PTree.gss.
        -- assumption.
        -- pose proof nsyms_bound. unfold Int64.max_unsigned in *. lia.
        -- reflexivity.
      * cbn. unfold sem_and, sem_binarith, sem_cast, classify_cast,
                    classify_binarith, tint. cbn.
        destruct Archi.ptr64; cbn; destruct (s_idx <? DC.nsyms); reflexivity.
    + apply bool_val_zero_int.
    + eapply exec_Sreturn_some. econstructor.
  - cbn. split. discriminate.
    unfold tlong, sem_cast, classify_cast. now destruct Archi.ptr64.
  - reflexivity.
Qed.

Lemma index_of_complete : forall {A} (l : list A) x k eq_dec,
  In x l -> exists i, index_of eq_dec x l k = Some i.
Proof.
  induction l; intros. contradiction.
  simpl in *. destruct eq_dec; subst.
    now exists k.
  destruct H. congruence. eauto.
Qed.

(** Top level *)

Lemma sidx_run : forall w, exists i, sidx (DFA.run dfa w) = Some i.
Proof.
  intros. unfold sidx.
  apply index_of_complete.
  apply DFA.run_in_states.
Qed.

Lemma symidx_total : forall a, exists i, symidx a = Some i.
Proof.
  intros. unfold symidx.
  apply index_of_complete.
  apply s.t_enumerable.
Qed.

Lemma run_snoc : forall w a,
  DFA.run dfa (w ++ [a]) = dfa.(transition _) (DFA.run dfa w) a.
Proof.
  intros. unfold DFA.run.
  now rewrite fold_left_app.
Qed.

Lemma delta_step_correct : forall w a q_idx a_idx,
  sidx (DFA.run dfa w) = Some q_idx ->
  symidx a = Some a_idx ->
  exists r_idx,
    sidx (DFA.run dfa (w ++ [a])) = Some r_idx /\
    eval_funcall function_entry2 ge m0
      (compile_delta state dfa ids)
      [Vlong (Int64.repr q_idx); Vlong (Int64.repr a_idx)] E0 m0
      (Vlong (Int64.repr r_idx)).
Proof.
  intros. destruct (sidx_run (w ++ [a])).
  exists x. split.
    assumption.
  eapply compile_delta_correct; eauto.
  now rewrite <- run_snoc.
Qed.

Lemma q0_index_correct :
  sidx dfa.(initial _) = Some (q0_index _ dfa state_eq_dec).
Proof.
  intros. unfold sidx, q0_index.
  destruct index_of eqn:E. reflexivity.
  exfalso.
  assert (Hin : In (initial state dfa) (states state dfa)).
    apply (dfa.(states_complete _) []).
  destruct (index_of_complete _ _ 0 state_eq_dec Hin) as [i Hi].
  congruence.
Qed.

Lemma q0_index_bounds :
  0 <= q0_index state dfa state_eq_dec < Int64.modulus.
Proof.
  pose proof q0_index_correct as H. unfold sidx in H.
  apply index_of_bounds in H. lia.
Qed.

Definition sym_indices (w : list s.t) (l : list Z) : Prop :=
  Forall2 (fun a i => symidx a = Some i) w l.

Definition word_in_mem (m : mem) (b : block) (ofs : Z) (l : list Z) : Prop :=
  forall n i, nth_error l n = Some i ->
    Mem.loadv Mint64 m (Vptr b (Ptrofs.repr (ofs + 8 * Z.of_nat n)))
      = Some (Vlong (Int64.repr i)).

Lemma sym_indices_length : forall w l,
  sym_indices w l -> length w = length l.
Proof. intros. eapply Forall2_length; eassumption. Qed.

Lemma sym_indices_bounds : forall w l i,
  sym_indices w l -> In i l -> 0 <= i < Int64.modulus.
Proof.
  induction 1; intros. contradiction.
  destruct H1; subst.
    unfold symidx in H. apply index_of_bounds in H. lia.
  eauto.
Qed.

Lemma sym_indices_nth : forall w l n a,
  sym_indices w l ->
  nth_error w n = Some a ->
  exists i, nth_error l n = Some i /\ symidx a = Some i.
Proof.
  induction w; intros; destruct n; cbn in *; try discriminate;
    inversion H; inversion H0; subst; eauto.
Qed.

(* Pointer arithmetic *)

Lemma eval_index_lvalue : forall e le m b ofs i,
  le ! (ids.(id_w)) = Some (Vptr b (Ptrofs.repr ofs)) ->
  le ! (ids.(id_i)) = Some (Vlong (Int64.repr i)) ->
  0 <= ofs -> 0 <= i -> ofs + 8 * i < Ptrofs.modulus ->
  eval_lvalue ge e le m
    (Ederef (Ebinop Oadd (Etempvar ids.(id_w) w_type) (Etempvar ids.(id_i) tlong) w_type) tlong)
    b (Ptrofs.repr (ofs + 8 * i)) Full.
Proof.
  intros. econstructor. econstructor.
    econstructor. eassumption.
    econstructor. eassumption.
  cbn.
  destruct Archi.ptr64 eqn:E; [|discriminate].
  f_equal. f_equal.
  now apply ptr_add_normalize.
Qed.

(* Loop guard *)

Lemma eval_lt_test : forall e le m i len bv,
  le ! (ids.(id_i)) = Some (Vlong (Int64.repr i)) ->
  le ! (ids.(id_len)) = Some (Vlong (Int64.repr len)) ->
  0 <= i < Int64.modulus -> 0 <= len < Int64.modulus ->
  bv = (if i <? len then Int.one else Int.zero) ->
  eval_expr ge e le m
    (Ebinop Olt (Etempvar ids.(id_i) tlong) (Etempvar ids.(id_len) tlong) tint)
    (Vint bv).
Proof.
  intros. econstructor.
    econstructor. eassumption.
    econstructor. eassumption.
  cbn. unfold sem_cmp, classify_cmp, tlong, sem_binarith, sem_cast,
              classify_cast, classify_binarith. cbn.
  destruct Archi.ptr64; cbn;
    unfold Val.of_bool, Int64.ltu;
    repeat rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; lia);
    subst; destruct (i <? len) eqn:E;
      [ rewrite zlt_true by lia | rewrite zlt_false by lia
      | rewrite zlt_true by lia | rewrite zlt_false by lia ];
      reflexivity.
Qed.

(* Loop body *)

Definition run_body := run_body ids.
Definition run_loop : statement := Sloop run_body Sskip.

Lemma run_body_step : forall le m b ofs l i q_idx a_idx r_idx len,
  le ! (ids.(id_w))   = Some (Vptr b (Ptrofs.repr ofs)) ->
  le ! (ids.(id_len)) = Some (Vlong (Int64.repr len)) ->
  le ! (ids.(id_i))   = Some (Vlong (Int64.repr i)) ->
  le ! (ids.(id_q))   = Some (Vlong (Int64.repr q_idx)) ->
  word_in_mem m b ofs l ->
  nth_error l (Z.to_nat i) = Some a_idx ->
  0 <= ofs -> 0 <= i < len -> len < Int64.modulus ->
  ofs + 8 * i < Ptrofs.modulus ->
  eval_funcall function_entry2 ge m
    (compile_delta state dfa ids)
    [Vlong (Int64.repr q_idx); Vlong (Int64.repr a_idx)] E0 m
    (Vlong (Int64.repr r_idx)) ->
  exec_stmt function_entry2 ge empty_env le m run_body E0
    (PTree.set ids.(id_i) (Vlong (Int64.repr (i + 1)))
      (PTree.set ids.(id_q) (Vlong (Int64.repr r_idx)) le))
    m Out_normal.
Proof.
  intros. unfold run_body, DC.run_body.
  change E0 with (E0 ** E0).
  econstructor.
  - econstructor.
      eapply eval_lt_test with (bv := Int.one); eauto; try lia.
        now rewrite (proj2 (Z.ltb_lt i len)) by lia.
      apply bool_val_one_int.
      constructor.
  - change E0 with (E0 ** E0).
    destruct find_delta as (loc & Sym & Funct). econstructor.
    + (* q = delta(q, w[i]) *)
      econstructor; eauto.
      * reflexivity.
      * (* the callee expression *)
        eapply eval_Elvalue.
          eapply eval_Evar_global.
            apply PTree.gempty.
            eassumption.
          now eapply deref_loc_reference.
      * (* the arguments *)
        econstructor.
          econstructor. eassumption.
          cbn. unfold sem_cast, classify_cast, tlong. now destruct Archi.ptr64.
        econstructor.
          eapply eval_Elvalue.
            eapply eval_index_lvalue; eauto; lia.
          econstructor.
            specialize (H3 (Z.to_nat i) a_idx H4).
            rewrite Z2Nat.id in H3 by lia.
            reflexivity.
          specialize (H3 (Z.to_nat i) a_idx H4).
            rewrite Z2Nat.id in H3 by lia. apply H3.
          cbn. unfold sem_cast, classify_cast, tlong. now destruct Archi.ptr64.
        econstructor.
      * reflexivity.
    + (* i = i + 1 *)
      econstructor. econstructor.
        econstructor.
          rewrite PTree.gso by (cbv [ids alloc_idents id_i id_q]; lia).
          eassumption.
        econstructor.
      cbn. unfold sem_binarith, sem_cast, classify_cast, classify_binarith, tlong. cbn.
      destruct Archi.ptr64; cbn; do 2 f_equal;
      rewrite Int64.add_unsigned;
      rewrite !Int64.unsigned_repr by (unfold Int64.max_unsigned; lia);
      reflexivity.
Qed.

Lemma run_loop_correct : forall suf pre l_pre l_suf b ofs le q_idx,
  sym_indices pre l_pre ->
  sym_indices suf l_suf ->
  word_in_mem m0 b ofs (l_pre ++ l_suf) ->
  sidx (DFA.run dfa pre) = Some q_idx ->
  le ! (ids.(id_w))   = Some (Vptr b (Ptrofs.repr ofs)) ->
  le ! (ids.(id_len)) = Some (Vlong (Int64.repr (Z.of_nat (length (pre ++ suf))))) ->
  le ! (ids.(id_i))   = Some (Vlong (Int64.repr (Z.of_nat (length pre)))) ->
  le ! (ids.(id_q))   = Some (Vlong (Int64.repr q_idx)) ->
  0 <= ofs ->
  Z.of_nat (length (pre ++ suf)) < Int64.modulus ->
  ofs + 8 * Z.of_nat (length (pre ++ suf)) < Ptrofs.modulus ->
  exists r_idx le',
    sidx (DFA.run dfa (pre ++ suf)) = Some r_idx /\
    le' ! (ids.(id_q)) = Some (Vlong (Int64.repr r_idx)) /\
    exec_stmt function_entry2 ge empty_env le m0 run_loop E0 le' m0 Out_normal.
Proof.
  induction suf; intros.
  - (* empty suffix: the guard fails and the loop breaks *)
    exists q_idx, le. rewrite app_nil_r in *. repeat split; try assumption.
    econstructor.
      econstructor.
        econstructor.
          eapply eval_lt_test with (bv := Int.zero); eauto; try lia.
            now rewrite (proj2 (Z.ltb_ge _ _)) by lia.
          apply bool_val_zero_int.
          constructor.
        discriminate.
    constructor.
  - (* one iteration, then the loop at prefix [pre ++ [a]] *)
    inversion H0; subst; clear H0.
    pose proof (delta_step_correct pre a q_idx y H2 H12)
      as (r_idx & Hr & Hcall).
    assert (Hlp : length pre = length l_pre) by eauto using sym_indices_length.
    assert (Hnth : nth_error (l_pre ++ y :: l') (Z.to_nat (Z.of_nat (length pre)))
                   = Some y).
      { rewrite Nat2Z.id, Hlp, nth_error_app2 by lia.
        now rewrite Nat.sub_diag. }
    edestruct (IHsuf (pre ++ [a]) (l_pre ++ [y]) l' b ofs
      (PTree.set ids.(id_i) (Vlong (Int64.repr (Z.of_nat (length pre) + 1)))
        (PTree.set ids.(id_q) (Vlong (Int64.repr r_idx)) le)) r_idx)
      as (r' & le' & Hr' & Hq' & Hexec); eauto.
    + apply Forall2_app; [assumption|now constructor].
    + now rewrite <- app_assoc.
    + rewrite PTree.gso, PTree.gso by (cbv [ids alloc_idents id_w id_i id_q]; lia).
      assumption.
    + rewrite PTree.gso, PTree.gso by (cbv [ids alloc_idents id_len id_i id_q]; lia).
      rewrite <- app_assoc. assumption.
    + rewrite PTree.gss. rewrite length_app. cbn.
      now replace (Z.of_nat (length pre) + 1) with (Z.of_nat (length pre + 1)) by lia.
    + rewrite PTree.gso, PTree.gss by (cbv [ids alloc_idents id_i id_q]; lia).
      reflexivity.
    + now rewrite <- app_assoc.
    + now rewrite <- app_assoc.
    + exists r', le'. rewrite <- app_assoc in Hr'. repeat split; eauto.
      unfold run_loop.
      change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop with (out1 := Out_normal).
      * eapply run_body_step with (l := l_pre ++ y :: l')
          (a_idx := y) (r_idx := r_idx); eauto;
          rewrite length_app in *; cbn - [Pos.succ Pos.add Z.mul] in *; try lia.
      * constructor.
      * constructor.
      * assumption.
Qed.

(* run *)

Lemma alloc_idents_run_norepet :
  list_norepet [ids.(id_w); ids.(id_len)] /\
  list_norepet [ids.(id_i); ids.(id_q)] /\
  list_disjoint [ids.(id_w); ids.(id_len)] [ids.(id_i); ids.(id_q)].
Proof.
  cbv [ids alloc_idents id_w id_len id_i id_q].
  repeat split.
  - repeat constructor; cbn - [Pos.add]; intro H;
      repeat (destruct H as [H|H]; [lia|]); contradiction.
  - repeat constructor; cbn - [Pos.add]; intro H;
      repeat (destruct H as [H|H]; [lia|]); contradiction.
  - repeat intro. cbn - [Pos.add] in *.
    repeat (destruct H as [H|H]; subst; try contradiction);
    repeat (destruct H0 as [H0|H0]; subst; try contradiction); lia.
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
      (compile_run state dfa state_eq_dec ids)
      [Vptr b (Ptrofs.repr ofs); Vlong (Int64.repr (Z.of_nat (length w)))] E0 m0
      (Vlong (Int64.repr r_idx)).
Proof.
  intros. destruct alloc_idents_run_norepet, H5.
  (* [le0]: the temp env after [function_entry2] binds the parameters. *)
  set (le0 := PTree.set ids.(id_len) (Vlong (Int64.repr (Z.of_nat (length w))))
               (PTree.set ids.(id_w) (Vptr b (Ptrofs.repr ofs))
                 (create_undef_temps [(ids.(id_i), tlong); (ids.(id_q), tlong)]))).
  (* [le1]: after the prologue sets [i := 0] and [q := q0]. *)
  set (le1 := PTree.set ids.(id_q) (Vlong (Int64.repr (q0_index state dfa state_eq_dec)))
               (PTree.set ids.(id_i) (Vlong (Int64.repr 0)) le0)).
  assert (Hw1 : le1 ! (ids.(id_w)) = Some (Vptr b (Ptrofs.repr ofs))).
    { subst le1 le0.
      rewrite PTree.gso, PTree.gso by (cbv [ids alloc_idents id_w id_i id_q]; lia).
      rewrite PTree.gso by (cbv [ids alloc_idents id_w id_len]; lia).
      apply PTree.gss. }
  assert (Hlen1 : le1 ! (ids.(id_len))
                  = Some (Vlong (Int64.repr (Z.of_nat (length w))))).
    { subst le1 le0.
      rewrite PTree.gso, PTree.gso by (cbv [ids alloc_idents id_len id_i id_q]; lia).
      apply PTree.gss. }
  assert (Hi1 : le1 ! (ids.(id_i)) = Some (Vlong (Int64.repr 0))).
    { subst le1.
      rewrite PTree.gso by (cbv [ids alloc_idents id_i id_q]; lia).
      apply PTree.gss. }
  assert (Hq1 : le1 ! (ids.(id_q))
                = Some (Vlong (Int64.repr (q0_index state dfa state_eq_dec)))).
    { subst le1. apply PTree.gss. }
  edestruct (run_loop_correct w [] [] l b ofs le1
    (q0_index state dfa state_eq_dec)) as (r_idx & le' & Hr & Hq & Hexec); eauto.
  - constructor.
  - unfold run. simpl. apply q0_index_correct.
  - cbn - [Pos.add] in *.
    exists r_idx. split.
      assumption.
    unfold compile_run. econstructor.
    + (* function_entry2 *)
      econstructor; cbn - [Pos.add]; assumption || constructor.
    + unfold DC.run_body. cbn [fn_body].
      change E0 with (E0 ** E0).
      eapply exec_Sseq_1.
      * (* prologue ; loop *)
        change E0 with (E0 ** E0).
        eapply exec_Sseq_1.
        -- (* Sset i 0 ; Sset q q0 *)
           change E0 with (E0 ** E0).
           eapply exec_Sseq_1.
            econstructor. econstructor.
            econstructor. unfold compiled_q0. econstructor.
        -- eassumption.
      * eapply exec_Sreturn_some. econstructor. eassumption.
    + cbn. split. discriminate.
      unfold tlong, sem_cast, classify_cast. now destruct Archi.ptr64.
    + reflexivity.
Qed.

End correctness.
End Correctness.