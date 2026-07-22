From lstar Require Import automata.Mealy.
From compcert Require Import AST Clight Ctypes Integers Cop Maps.
From compcert Require Import ClightBigstep Values Events Coqlib.
From compcert Require Import Globalenvs Memory.
From Transmogrifier.compiler Require Import mealy.
From Stdlib Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

(** Correctness of the Mealy -> Clight compiler. *)

Module Correctness (s : Symbol) (O : Output) (Mealy : MealyType s O).

Module MC := MealyCompiler s O Mealy.
Import MC Mealy.

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

Lemma index_of_complete : forall (l : list X) x k,
  In x l -> exists i, index_of eq_dec x l k = Some i.
Proof.
  induction l; intros. contradiction.
  simpl in *. destruct eq_dec; subst.
    now exists k.
  destruct H. congruence. eauto.
Qed.

Lemma enumerate_nth_error_pair : forall (l : list X) i,
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

End index.

Section outputs.
Variable state : Type.
Variable m : Mealy.t state.

Lemma outputs_snoc : forall w a q,
  outputs m q (w ++ [a])
  = outputs m q w ++ [m.(output _) (fold_left m.(transition _) w q) a].
Proof.
  induction w; intros; cbn.
    reflexivity.
  now rewrite IHw.
Qed.

Lemma run_outputs_snoc : forall w a,
  run_outputs m (w ++ [a])
  = run_outputs m w ++ [m.(output _) (Mealy.run m w) a].
Proof.
  intros. unfold run_outputs, Mealy.run. apply outputs_snoc.
Qed.

Lemma outputs_length : forall w q,
  length (outputs m q w) = length w.
Proof. induction w; intros; cbn; auto. Qed.

Lemma run_outputs_length : forall w,
  length (run_outputs m w) = length w.
Proof. intros. apply outputs_length. Qed.

End outputs.

Section correctness.
Variable state : Type.
Variable mealy : Mealy.t state.
Variable state_eq_dec : forall (x y : state), {x = y} + {x <> y}.

Variable states_bounded : Z.of_nat (length mealy.(states _)) < Int64.modulus.
Variable syms_bounded   : 0 < Z.of_nat (length s.enum) < Int64.modulus.
Variable O_bounded      : 0 < Z.of_nat (length O.enum) < Int64.modulus.

Variable base : ident.
Variable p : Clight.program.
Variable Hp : compile_program state mealy state_eq_dec base = Ok p.

Definition ge : genv := Clight.globalenv p.
Definition ids : idents := alloc_idents base.

Definition sidx (q : state) : option Z :=
  index_of state_eq_dec q mealy.(states _) 0.
Definition symidx (a : s.t) : option Z :=
  index_of s.eq_dec a s.enum 0.
Definition oidx (o : O.t) : option Z :=
  index_of O.eq_dec o O.enum 0.

Lemma compile_program_defs :
  prog_defs p =
    [ (ids.(id_table),  Gvar (compile_table state mealy state_eq_dec));
      (ids.(id_otable), Gvar (compile_otable state mealy));
      (ids.(id_delta),  Gfun (compile_delta state mealy ids));
      (ids.(id_q0),     Gvar (compile_q0 state mealy state_eq_dec));
      (ids.(id_run),    Gfun (compile_run state mealy state_eq_dec ids));
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
  cbv [ids alloc_idents id_table id_otable id_delta id_q0 id_run id_main map fst].
  repeat constructor; cbn - [Pos.succ Pos.add]; intro H;
    repeat (destruct H as [H|H]; [lia|]); contradiction.
Qed.

Definition nsyms : Z := Z.of_nat (length s.enum).
Definition nstates : Z := Z.of_nat (length mealy.(states _)).
Definition nouts : Z := Z.of_nat (length O.enum).

Lemma table_row_length : forall q,
  length (table_row state mealy state_eq_dec q) = length s.enum.
Proof.
  intros. unfold table_row, sym_table, enumerate.
  rewrite length_map, length_combine, length_map, length_seq. lia.
Qed.

Lemma nth_error_flat_map_uniform :
  forall (A B : Type) (f : A -> list B) (l : list A) (k : nat),
  (forall x, In x l -> length (f x) = k) ->
  forall i j x,
  nth_error l i = Some x -> (j < k)%nat ->
  nth_error (flat_map f l) (i * k + j) = nth_error (f x) j.
Proof.
  induction l; intros k Hk i j x Hi Hj; simpl in *.
    now destruct i.
  destruct i; simpl in *.
  - inversion Hi; subst; clear Hi.
    rewrite nth_error_app1. reflexivity. rewrite Hk by now left. assumption.
  - rewrite nth_error_app2.
      rewrite Hk by now left.
      replace (k + i * k + j - k)%nat with (i * k + j)%nat by lia. eauto.
    rewrite Hk. lia. now left.
Qed.

Lemma table_entry_correct : forall q sym q_idx s_idx,
  sidx q = Some q_idx -> symidx sym = Some s_idx ->
  nth_error (table_init state mealy state_eq_dec)
    (Z.to_nat (q_idx * nsyms + s_idx))
  = Some (Init_int64 (Int64.repr (table_entry state mealy state_eq_dec q sym))).
Proof.
  intros q sym q_idx s_idx Hq Hs.
  assert (Hqb : 0 <= q_idx < Z.of_nat (length mealy.(states _)))
    by (unfold sidx in Hq; eauto using index_of_bounds).
  assert (Hsb : 0 <= s_idx < Z.of_nat (length s.enum))
    by (unfold symidx in Hs; eauto using index_of_bounds).
  assert (Hrow : nth_error (state_table state mealy) (Z.to_nat q_idx) = Some (q_idx, q)).
    { unfold state_table.
      destruct (enumerate_nth_error_pair _ (states state mealy) q_idx Hqb)
        as (q' & Hpair & Hnth).
      unfold sidx in Hq. apply index_of_nth_error in Hq.
      rewrite Z.sub_0_r in Hq. rewrite Hq in Hnth. inversion Hnth; subst. eauto. }
  assert (Hcol : nth_error (table_row state mealy state_eq_dec q) (Z.to_nat s_idx)
                 = Some (Init_int64 (Int64.repr (table_entry state mealy state_eq_dec q sym)))).
    { unfold table_row, sym_table. rewrite nth_error_map.
      destruct (enumerate_nth_error_pair _ s.enum s_idx Hsb)
        as (sym' & Hpair & Hnth).
      unfold symidx in Hs. apply index_of_nth_error in Hs.
      rewrite Z.sub_0_r in Hs. rewrite Hs in Hnth. inversion Hnth; subst. now rewrite Hpair. }
  unfold table_init.
  replace (Z.to_nat (q_idx * nsyms + s_idx))
    with (Z.to_nat q_idx * length s.enum + Z.to_nat s_idx)%nat
    by (unfold nsyms; lia).
  rewrite nth_error_flat_map_uniform with (k := length s.enum) (x := (q_idx, q)); eauto.
  - intros (qi & qq) _. apply table_row_length.
  - lia.
Qed.

Lemma otable_row_length : forall q,
  length (otable_row state mealy q) = length s.enum.
Proof.
  intros. unfold otable_row, sym_table, enumerate.
  rewrite length_map, length_combine, length_map, length_seq. lia.
Qed.

(** The output table has the same 2-D shape as [table]: entry [q*nsyms+s] holds
    the index in [O.enum] of [output q s]. *)
Lemma otable_entry_correct : forall q sym q_idx s_idx,
  sidx q = Some q_idx -> symidx sym = Some s_idx ->
  nth_error (otable_init state mealy)
    (Z.to_nat (q_idx * nsyms + s_idx))
  = Some (Init_int64 (Int64.repr (otable_entry state mealy q sym))).
Proof.
  intros q sym q_idx s_idx Hq Hs.
  assert (Hqb : 0 <= q_idx < Z.of_nat (length mealy.(states _)))
    by (unfold sidx in Hq; eauto using index_of_bounds).
  assert (Hsb : 0 <= s_idx < Z.of_nat (length s.enum))
    by (unfold symidx in Hs; eauto using index_of_bounds).
  assert (Hrow : nth_error (state_table state mealy) (Z.to_nat q_idx) = Some (q_idx, q)).
    { unfold state_table.
      destruct (enumerate_nth_error_pair _ (states state mealy) q_idx Hqb)
        as (q' & Hpair & Hnth).
      unfold sidx in Hq. apply index_of_nth_error in Hq.
      rewrite Z.sub_0_r in Hq. rewrite Hq in Hnth. inversion Hnth; subst. eauto. }
  assert (Hcol : nth_error (otable_row state mealy q) (Z.to_nat s_idx)
                 = Some (Init_int64 (Int64.repr (otable_entry state mealy q sym)))).
    { unfold otable_row, sym_table. rewrite nth_error_map.
      destruct (enumerate_nth_error_pair _ s.enum s_idx Hsb)
        as (sym' & Hpair & Hnth).
      unfold symidx in Hs. apply index_of_nth_error in Hs.
      rewrite Z.sub_0_r in Hs. rewrite Hs in Hnth. inversion Hnth; subst. now rewrite Hpair. }
  unfold otable_init.
  replace (Z.to_nat (q_idx * nsyms + s_idx))
    with (Z.to_nat q_idx * length s.enum + Z.to_nat s_idx)%nat
    by (unfold nsyms; lia).
  rewrite nth_error_flat_map_uniform with (k := length s.enum) (x := (q_idx, q)); eauto.
  - intros (qi & qq) _. apply otable_row_length.
  - lia.
Qed.

Lemma otable_entry_oidx : forall q sym o_idx,
  oidx (mealy.(output _) q sym) = Some o_idx ->
  otable_entry state mealy q sym = o_idx.
Proof. intros. unfold otable_entry, oidx in *. now rewrite H. Qed.

Lemma table_entry_sidx : forall q sym next_idx,
  sidx (mealy.(transition _) q sym) = Some next_idx ->
  table_entry state mealy state_eq_dec q sym = next_idx.
Proof. intros. unfold table_entry, sidx in *. now rewrite H. Qed.

Lemma sidx_run : forall w, exists i, sidx (Mealy.run mealy w) = Some i.
Proof.
  intros. unfold sidx. apply index_of_complete. apply Mealy.run_in_states.
Qed.

Lemma symidx_total : forall a, exists i, symidx a = Some i.
Proof. intros. unfold symidx. apply index_of_complete. apply s.t_enumerable. Qed.

Lemma oidx_total : forall o, exists i, oidx o = Some i.
Proof. intros. unfold oidx. apply index_of_complete. apply O.t_enumerable. Qed.

Lemma q0_index_correct :
  sidx mealy.(initial _) = Some (q0_index _ mealy state_eq_dec).
Proof.
  unfold sidx, q0_index.
  destruct index_of eqn:E. reflexivity.
  exfalso.
  assert (Hin : In (initial state mealy) (states state mealy))
    by apply (mealy.(states_complete _) []).
  destruct (index_of_complete _ state_eq_dec _ (initial state mealy) 0 Hin) as [i Hi].
  congruence.
Qed.

Variable m0 : mem.
Variable Hinit : Genv.init_mem p = Some m0.
Variable table_bounded :
  8 * (Z.of_nat (length mealy.(states _)) * Z.of_nat (length s.enum)) < Ptrofs.modulus.

Lemma find_table :
  exists b,
    Genv.find_symbol ge ids.(id_table) = Some b /\
    Genv.find_def ge b = Some (Gvar (compile_table state mealy state_eq_dec)).
Proof.
  apply Genv.find_def_symbol.
  apply prog_defmap_norepet.
    apply global_idents_norepet.
  pose proof compile_program_defs as Hdefs.
  change (AST.prog_defs p) with (prog_defs p).
  rewrite Hdefs. now left.
Qed.

Lemma find_otable :
  exists b,
    Genv.find_symbol ge ids.(id_otable) = Some b /\
    Genv.find_def ge b = Some (Gvar (compile_otable state mealy)).
Proof.
  apply Genv.find_def_symbol.
  apply prog_defmap_norepet.
    apply global_idents_norepet.
  pose proof compile_program_defs as Hdefs.
  change (AST.prog_defs p) with (prog_defs p).
  rewrite Hdefs. right. now left.
Qed.

Lemma find_delta :
  exists b,
    Genv.find_symbol ge ids.(id_delta) = Some b /\
    Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (compile_delta state mealy ids).
Proof.
  assert (Hd : (prog_defmap p) ! (ids.(id_delta))
               = Some (Gfun (compile_delta state mealy ids))).
  { apply prog_defmap_norepet.
      apply global_idents_norepet.
    pose proof compile_program_defs as Hdefs.
    change (AST.prog_defs p) with (prog_defs p).
    rewrite Hdefs. right. right. now left. }
  destruct (proj1 (Genv.find_def_symbol _ _ _) Hd) as (b & Hsym & Hdef).
  exists b. split. eauto.
  unfold Genv.find_funct. rewrite pred_dec_true by reflexivity.
  now apply Genv.find_funct_ptr_iff.
Qed.

Lemma init_data_list_nth_load_int64 :
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

Lemma table_init_all_int64 : forall id,
  In id (table_init state mealy state_eq_dec) -> exists x, id = Init_int64 x.
Proof.
  intros. unfold table_init in H.
  apply in_flat_map in H. destruct H as ((qi & q) & _ & Hin).
  unfold table_row in Hin. apply in_map_iff in Hin.
  destruct Hin as ((si & sy) & Heq & _). subst. eauto.
Qed.

Lemma otable_init_all_int64 : forall id,
  In id (otable_init state mealy) -> exists x, id = Init_int64 x.
Proof.
  intros. unfold otable_init in H.
  apply in_flat_map in H. destruct H as ((qi & q) & _ & Hin).
  unfold otable_row in Hin. apply in_map_iff in Hin.
  destruct Hin as ((si & sy) & Heq & _). subst. eauto.
Qed.

Lemma nsyms_bound : 0 <= MC.nsyms <= Int64.max_unsigned.
Proof.
  unfold MC.nsyms, Int64.max_unsigned.
  pose proof (Nat2Z.is_nonneg (Datatypes.length s.enum)). lia.
Qed.

Lemma nstates_bound : 0 <= MC.nstates state mealy <= Int64.max_unsigned.
Proof.
  unfold MC.nstates, Int64.max_unsigned.
  pose proof (Nat2Z.is_nonneg (Datatypes.length (states state mealy))). lia.
Qed.

Lemma table_in_mem : forall b k v,
  Genv.find_symbol ge ids.(id_table) = Some b ->
  nth_error (table_init state mealy state_eq_dec) (Z.to_nat k) = Some (Init_int64 v) ->
  0 <= k < nstates * nsyms ->
  Mem.loadv Mint64 m0 (Vptr b (Ptrofs.repr (8 * k))) = Some (Vlong v).
Proof.
  intros b k v Hsym Hnth Hk.
  destruct find_table as (b' & Hsym' & Hdef).
  assert (b' = b) by congruence. subst b'.
  assert (Hvi : Genv.find_var_info ge b = Some (compile_table state mealy state_eq_dec)).
    { apply Genv.find_var_info_iff. eauto. }
  destruct (Genv.init_mem_characterization _ _ Hvi Hinit)
    as (_ & _ & Hlsid & _).
  specialize (Hlsid eq_refl).
  cbn [Mem.loadv].
  rewrite Ptrofs.unsigned_repr.
  - replace (8 * k) with (0 + 8 * Z.of_nat (Z.to_nat k)) by lia.
    eapply init_data_list_nth_load_int64; eauto.
    apply table_init_all_int64.
  - unfold Ptrofs.max_unsigned, nstates, nsyms in *. nia.
Qed.

Lemma otable_in_mem : forall b k v,
  Genv.find_symbol ge ids.(id_otable) = Some b ->
  nth_error (otable_init state mealy) (Z.to_nat k) = Some (Init_int64 v) ->
  0 <= k < nstates * nsyms ->
  Mem.loadv Mint64 m0 (Vptr b (Ptrofs.repr (8 * k))) = Some (Vlong v).
Proof.
  intros b k v Hsym Hnth Hk.
  destruct find_otable as (b' & Hsym' & Hdef).
  assert (b' = b) by congruence. subst b'.
  assert (Hvi : Genv.find_var_info ge b = Some (compile_otable state mealy)).
    { apply Genv.find_var_info_iff. eauto. }
  destruct (Genv.init_mem_characterization _ _ Hvi Hinit)
    as (_ & _ & Hlsid & _).
  specialize (Hlsid eq_refl).
  cbn [Mem.loadv].
  rewrite Ptrofs.unsigned_repr.
  - replace (8 * k) with (0 + 8 * Z.of_nat (Z.to_nat k)) by lia.
    eapply init_data_list_nth_load_int64; eauto.
    apply otable_init_all_int64.
  - unfold Ptrofs.max_unsigned, nstates, nsyms in *. nia.
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

(* delta(q,a,out): write the output index through [out], return the successor
   index. [b_o <> b_t/b_ot] keep the store from clobbering either table, so the
   return still reads [table] from the post-store memory. *)
Theorem compile_delta_correct :
  forall q sym q_idx s_idx next_idx o_idx b_o ofs_o b_t b_ot m,
  sidx q = Some q_idx ->
  symidx sym = Some s_idx ->
  sidx (mealy.(transition _) q sym) = Some next_idx ->
  oidx (mealy.(output _) q sym) = Some o_idx ->
  Genv.find_symbol ge ids.(id_table) = Some b_t ->
  Genv.find_symbol ge ids.(id_otable) = Some b_ot ->
  Mem.loadv Mint64 m (Vptr b_t (Ptrofs.repr (8 * (q_idx * nsyms + s_idx))))
    = Some (Vlong (Int64.repr next_idx)) ->
  Mem.loadv Mint64 m (Vptr b_ot (Ptrofs.repr (8 * (q_idx * nsyms + s_idx))))
    = Some (Vlong (Int64.repr o_idx)) ->
  Mem.range_perm m b_o ofs_o (ofs_o + 8) Cur Writable ->
  (align_chunk Mint64 | ofs_o) ->
  0 <= ofs_o -> ofs_o + 8 < Ptrofs.modulus ->
  b_o <> b_t -> b_o <> b_ot ->
  exists m',
    Mem.storev Mint64 m (Vptr b_o (Ptrofs.repr ofs_o)) (Vlong (Int64.repr o_idx)) = Some m' /\
    eval_funcall function_entry2 ge m
      (compile_delta state mealy ids)
      [Vlong (Int64.repr q_idx); Vlong (Int64.repr s_idx); Vptr b_o (Ptrofs.repr ofs_o)]
      E0 m' (Vlong (Int64.repr next_idx)) /\
    Mem.unchanged_on (fun b o => b <> b_o \/ o < ofs_o \/ ofs_o + 8 <= o) m m'.
Proof.
  intros q sym q_idx s_idx next_idx o_idx b_o ofs_o b_t b_ot m
    Hq Hs Hnext Ho Hbt Hbot Hloadt Hloadot Hperm Halign Hofs0 Hofsb Hdt Hdot.
  assert (Hqb : 0 <= q_idx < nstates)
    by (unfold sidx, nstates, MC.nstates in *; apply index_of_bounds in Hq; lia).
  assert (Hsb : 0 <= s_idx < nsyms)
    by (unfold symidx, nsyms, MC.nstates in *; apply index_of_bounds in Hs; lia).
  assert (Hprod : 0 <= q_idx * MC.nsyms + s_idx < MC.nstates state mealy * MC.nsyms)
    by (unfold MC.nstates, MC.nsyms, nstates, nsyms in *; nia).
  assert (Hpb : 8 * (q_idx * MC.nsyms + s_idx) < Ptrofs.modulus)
    by (unfold MC.nstates, MC.nsyms in *; nia).
  (* the write through [out] *)
  destruct (Mem.valid_access_store m Mint64 b_o ofs_o (Vlong (Int64.repr o_idx)))
    as (m' & Hstore).
  { split; [| eauto]. intros z Hz. eapply Mem.perm_implies.
      apply Hperm. cbn in Hz. lia.
    constructor. }
  exists m'. split. unfold Mem.storev. replace (Ptrofs.unsigned _) with ofs_o. assumption.
  symmetry. rewrite Ptrofs.unsigned_repr_eq. rewrite Z.mod_small. reflexivity.
  split. assumption. lia. split.
  - (* the function call *)
    econstructor.
    + econstructor; cbn - [Pos.add]; try solve [constructor].
        repeat constructor; cbn - [Pos.add]; intro Hin;
          repeat (destruct Hin as [Hin|Hin]; [lia|]); contradiction.
      now repeat intro.
    + cbn [fn_body]. econstructor.
      * (* guard: (q < |Q|) & (s < |Sigma|) evaluates to Int.one *)
        econstructor.
        -- eapply eval_lt_test_gen with (j := q_idx) (bv := Int.one).
           ++ cbn - [Pos.add].
              rewrite PTree.gso by (cbv [ids alloc_idents id_q id_s id_out]; lia).
              rewrite PTree.gso by (cbv [ids alloc_idents id_q id_s id_out]; lia).
              apply PTree.gss.
           ++ unfold nstates, MC.nstates in Hqb. lia.
           ++ unfold MC.nstates. lia.
           ++ rewrite (proj2 (Z.ltb_lt _ _)). reflexivity.
              unfold MC.nstates. unfold nstates in *. lia.
        -- eapply eval_lt_test_gen with (j := s_idx) (bv := Int.one).
           ++ cbn - [Pos.add].
              rewrite PTree.gso by (cbv [ids alloc_idents id_s id_out]; lia).
              apply PTree.gss.
           ++ unfold MC.nsyms, nsyms in *. lia.
           ++ unfold MC.nsyms. lia.
           ++ now rewrite (proj2 (Z.ltb_lt _ _)).
        -- cbn. unfold sem_and, sem_binarith, sem_cast, classify_cast,
                      classify_binarith, tint. cbn.
           destruct Archi.ptr64; cbn; reflexivity.
      * apply bool_val_one_int.
      * (* the store: *out = otable[q*nsyms+s], then the return *)
        assert (Hqb' : 0 <= q_idx <= Int64.max_unsigned)
          by (pose proof nstates_bound; unfold MC.nstates, nstates in *; lia).
        assert (Hsb' : 0 <= s_idx <= Int64.max_unsigned)
          by (pose proof nsyms_bound; unfold nsyms, MC.nsyms in Hsb;
              unfold Int64.max_unsigned; lia).
        assert (Hmb : 0 <= q_idx * MC.nsyms <= Int64.max_unsigned)
          by (pose proof nsyms_bound; pose proof ptrofs_le_int64;
              unfold MC.nstates, MC.nsyms, Int64.max_unsigned in *; nia).
        change E0 with (E0 ** E0).
        eapply exec_Sseq_1.
        -- (* *out = otable[q*nsyms+s], read from [m] *)
           econstructor.
           ++ (* lvalue: *out, i.e. [b_o, ofs_o] *)
              econstructor. econstructor. cbn - [Pos.add]. apply PTree.gss.
           ++ (* rvalue: otable[q*nsyms+s], read from [m] *)
              eapply eval_Elvalue.
              ** econstructor. econstructor.
                 --- eapply eval_Elvalue.
                       eapply eval_Evar_global.
                         apply PTree.gempty.
                         eauto.
                       eapply deref_loc_reference. reflexivity.
                 --- unfold table_index. econstructor.
                     +++ econstructor.
                         *** econstructor. cbn - [Pos.add].
                             rewrite PTree.gso
                               by (cbv [ids alloc_idents id_q id_s id_out]; lia).
                             rewrite PTree.gso
                               by (cbv [ids alloc_idents id_q id_s id_out]; lia).
                             apply PTree.gss.
                         *** econstructor.
                         *** cbn. unfold sem_mul, sem_binarith, sem_cast,
                                    classify_cast, classify_binarith, tlong. cbn.
                             destruct Archi.ptr64; cbn;
                               rewrite mul_repr_in_range by (assumption || apply nsyms_bound);
                               reflexivity.
                     +++ econstructor. cbn - [Pos.add].
                         rewrite PTree.gso
                           by (cbv [ids alloc_idents id_s id_out]; lia).
                         apply PTree.gss.
                     +++ cbn. unfold sem_add, classify_add, tlong. cbn.
                         unfold sem_binarith, sem_cast, classify_cast, classify_binarith. cbn.
                         destruct Archi.ptr64; cbn;
                           rewrite add_repr_in_range by assumption; reflexivity.
                 --- cbn. unfold sem_add, classify_add, table_type, tlong. cbn.
                     destruct Archi.ptr64 eqn:E; [| discriminate].
                     unfold sem_add_ptr_long. cbn. do 2 f_equal.
              ** eapply deref_loc_value with (chunk := Mint64).
                   reflexivity.
                 change Ptrofs.zero with (Ptrofs.repr 0).
                 rewrite ptr_add_normalize by
                   (pose proof ptrofs_le_int64; unfold MC.nstates, MC.nsyms in *; nia).
                 rewrite Z.add_0_l. eauto.
           ++ cbn. unfold sem_cast, classify_cast, tlong. destruct Archi.ptr64; reflexivity.
           ++ (* assign_loc: the actual store to [b_o, ofs_o] *)
              eapply assign_loc_value with (chunk := Mint64).
                reflexivity.
              unfold Mem.storev. rewrite Ptrofs.unsigned_repr_eq.
              rewrite Z.mod_small. eassumption. lia.
        -- (* the return: table[q*nsyms+s], now read from [m'] *)
           eapply exec_Sreturn_some.
           eapply eval_Elvalue.
           ++ econstructor. econstructor.
              ** eapply eval_Elvalue.
                   eapply eval_Evar_global.
                     apply PTree.gempty.
                     eauto.
                   eapply deref_loc_reference. reflexivity.
              ** unfold table_index. econstructor.
                 --- econstructor.
                     +++ econstructor. cbn - [Pos.add].
                         rewrite PTree.gso
                           by (cbv [ids alloc_idents id_q id_s id_out]; lia).
                         rewrite PTree.gso
                           by (cbv [ids alloc_idents id_q id_s id_out]; lia).
                         apply PTree.gss.
                     +++ econstructor.
                     +++ cbn. unfold sem_mul, sem_binarith, sem_cast, classify_cast,
                                classify_binarith, tlong. cbn.
                         destruct Archi.ptr64; cbn;
                           rewrite mul_repr_in_range by (assumption || apply nsyms_bound);
                           reflexivity.
                 --- econstructor. cbn - [Pos.add].
                     rewrite PTree.gso by (cbv [ids alloc_idents id_s id_out]; lia).
                     apply PTree.gss.
                 --- cbn. unfold sem_add, classify_add, tlong. cbn.
                     unfold sem_binarith, sem_cast, classify_cast, classify_binarith. cbn.
                     destruct Archi.ptr64; cbn;
                       rewrite add_repr_in_range by assumption; reflexivity.
              ** cbn. unfold sem_add, classify_add, table_type, tlong. cbn.
                 destruct Archi.ptr64 eqn:E; [| discriminate].
                 unfold sem_add_ptr_long. cbn. do 2 f_equal.
           ++ eapply deref_loc_value with (chunk := Mint64).
                reflexivity.
              change Ptrofs.zero with (Ptrofs.repr 0).
              rewrite ptr_add_normalize by
                (pose proof ptrofs_le_int64; unfold MC.nstates, MC.nsyms in *; nia).
              rewrite Z.add_0_l.
              unfold Mem.loadv.
              erewrite Mem.load_store_other; eauto.
    + cbn. split. discriminate.
      unfold tlong, sem_cast, classify_cast. now destruct Archi.ptr64.
    + reflexivity.
  - (* Mem.unchanged_on *)
    eapply Mem.store_unchanged_on; eauto.
    intros i Hi [Hb | Hrange]; eauto.
    cbn [size_chunk] in *. lia.
Qed.

(* out-of-range input: write |O| through [out], return |Q|; reads no table *)
Lemma compile_delta_sink :
  forall q_idx s_idx b_o ofs_o m,
  0 <= q_idx < Int64.modulus -> 0 <= s_idx < Int64.modulus ->
  q_idx >= nstates ->
  Mem.range_perm m b_o ofs_o (ofs_o + 8) Cur Writable ->
  (align_chunk Mint64 | ofs_o) -> 0 <= ofs_o -> ofs_o + 8 < Ptrofs.modulus ->
  exists m',
    Mem.storev Mint64 m (Vptr b_o (Ptrofs.repr ofs_o)) (Vlong (Int64.repr nouts)) = Some m' /\
    eval_funcall function_entry2 ge m
      (compile_delta state mealy ids)
      [Vlong (Int64.repr q_idx); Vlong (Int64.repr s_idx); Vptr b_o (Ptrofs.repr ofs_o)]
      E0 m' (Vlong (Int64.repr (sink_index state mealy))) /\
    Mem.unchanged_on (fun b o => b <> b_o \/ o < ofs_o \/ ofs_o + 8 <= o) m m'.
Proof.
  intros q_idx s_idx b_o ofs_o m Hq Hs Hoob Hperm Halign Hofs0 Hofsb.
  destruct (Mem.valid_access_store m Mint64 b_o ofs_o (Vlong (Int64.repr nouts)))
    as (m' & Hstore).
  { split; [| eauto]. intros z Hz. eapply Mem.perm_implies.
      apply Hperm. cbn in Hz. lia.
    constructor. }
  exists m'. split.
    unfold Mem.storev. now rewrite Ptrofs.unsigned_repr_eq, Z.mod_small by lia.
  split.
  - econstructor.
    + econstructor; cbn - [Pos.add]; try solve [constructor].
        repeat constructor; cbn - [Pos.add]; intro Hin;
          repeat (destruct Hin as [Hin|Hin]; [lia|]); contradiction.
        now repeat intro.
    + cbn [fn_body]. eapply exec_Sifthenelse with (b := false).
      * (* guard evaluates to false *)
        econstructor.
        -- eapply eval_lt_test_gen with (j := q_idx) (bv := Int.zero).
           ++ cbn - [Pos.add].
              rewrite PTree.gso by (cbv [ids alloc_idents id_q id_s id_out]; lia).
              rewrite PTree.gso by (cbv [ids alloc_idents id_q id_s id_out]; lia).
              apply PTree.gss.
           ++ assumption.
           ++ pose proof nstates_bound. unfold Int64.max_unsigned in *. lia.
           ++ unfold MC.nstates, nstates in *.
              now rewrite (proj2 (Z.ltb_ge _ _)) by lia.
        -- eapply eval_lt_test_gen with (j := s_idx).
           ++ cbn - [Pos.add].
              rewrite PTree.gso by (cbv [ids alloc_idents id_s id_out]; lia).
              apply PTree.gss.
           ++ assumption.
           ++ pose proof nsyms_bound. unfold Int64.max_unsigned in *. lia.
           ++ reflexivity.
        -- cbn. unfold sem_and, sem_binarith, sem_cast, classify_cast,
                      classify_binarith, tint. cbn.
           destruct Archi.ptr64; cbn; destruct (s_idx <? MC.nsyms); reflexivity.
      * apply bool_val_zero_int.
      * (* the store: *out = |O|, then the return *)
        change E0 with (E0 ** E0).
        eapply exec_Sseq_1.
        -- econstructor.
           ++ econstructor. econstructor. cbn - [Pos.add]. apply PTree.gss.
           ++ econstructor.
           ++ cbn. unfold sem_cast, classify_cast, tlong. destruct Archi.ptr64; reflexivity.
           ++ eapply assign_loc_value with (chunk := Mint64).
                reflexivity.
              unfold Mem.storev. rewrite Ptrofs.unsigned_repr_eq, Z.mod_small by lia.
              eassumption.
        -- eapply exec_Sreturn_some. econstructor.
    + cbn. split. discriminate.
      unfold tlong, sem_cast, classify_cast. now destruct Archi.ptr64.
    + reflexivity.
  - eapply Mem.store_unchanged_on; eauto.
    intros i Hi [Hb | Hrange]. now apply Hb.
    simpl size_chunk in Hi. lia.
Qed.

(* [out[0..len-1]] hold the given index list. *)
Definition buf_in_mem (m : mem) (b : block) (ofs : Z) (l : list Z) : Prop :=
  forall n i, nth_error l n = Some i ->
    Mem.loadv Mint64 m (Vptr b (Ptrofs.repr (ofs + 8 * Z.of_nat n)))
      = Some (Vlong (Int64.repr i)).

Definition sym_indices (w : list s.t) (l : list Z) : Prop :=
  Forall2 (fun a i => symidx a = Some i) w l.

Definition word_in_mem (m : mem) (b : block) (ofs : Z) (l : list Z) : Prop :=
  forall n i, nth_error l n = Some i ->
    Mem.loadv Mint64 m (Vptr b (Ptrofs.repr (ofs + 8 * Z.of_nat n)))
      = Some (Vlong (Int64.repr i)).

Definition loop_frame (b_o b_out : block) (lo hi : Z) : block -> Z -> Prop :=
  fun b o => b <> b_o /\ (b <> b_out \/ o < lo \/ hi <= o).

Definition perms_eq (m m' : mem) : Prop :=
  forall b ofs k pp, Mem.perm m b ofs k pp <-> Mem.perm m' b ofs k pp.

Lemma perms_eq_refl : forall m, perms_eq m m.
Proof. intros m b ofs k pp. reflexivity. Qed.

Lemma perms_eq_trans : forall m1 m2 m3,
  perms_eq m1 m2 -> perms_eq m2 m3 -> perms_eq m1 m3.
Proof.
  intros m1 m2 m3 H12 H23 b ofs k pp.
  etransitivity. apply H12. apply H23.
Qed.

Lemma perms_eq_store : forall chunk m b ofs v m',
  Mem.store chunk m b ofs v = Some m' -> perms_eq m m'.
Proof.
  intros chunk m b ofs v m' Hst b' ofs' k pp. split; intro Hp'.
  - eapply Mem.perm_store_1; eauto.
  - eapply Mem.perm_store_2; eauto.
Qed.

Lemma run_loop_correct :
  forall w2 w1 l2 lo2 e le b_w ofs_w b_out ofs_out b_o b_t b_ot m,
  sym_indices w2 l2 ->
  Forall2 (fun o i => oidx o = Some i)
          (outputs mealy (Mealy.run mealy w1) w2) lo2 ->
  (forall n i, nth_error l2 n = Some i ->
     Mem.loadv Mint64 m (Vptr b_w (Ptrofs.repr
        (ofs_w + 8 * Z.of_nat (length w1 + n)))) = Some (Vlong (Int64.repr i))) ->
  Genv.find_symbol ge ids.(id_table)  = Some b_t ->
  Genv.find_symbol ge ids.(id_otable) = Some b_ot ->
  (forall k v, nth_error (table_init state mealy state_eq_dec) (Z.to_nat k)
       = Some (Init_int64 v) -> 0 <= k < nstates * nsyms ->
       Mem.loadv Mint64 m (Vptr b_t (Ptrofs.repr (8*k))) = Some (Vlong v)) ->
  (forall k v, nth_error (otable_init state mealy) (Z.to_nat k)
       = Some (Init_int64 v) -> 0 <= k < nstates * nsyms ->
       Mem.loadv Mint64 m (Vptr b_ot (Ptrofs.repr (8*k))) = Some (Vlong v)) ->
  e ! (id_o ids) = Some (b_o, tlong) ->
  le ! (id_i ids)   = Some (Vlong (Int64.repr (Z.of_nat (length w1)))) ->
  (exists qi, sidx (Mealy.run mealy w1) = Some qi
     /\ le ! (id_q ids) = Some (Vlong (Int64.repr qi))) ->
  le ! (id_w ids)   = Some (Vptr b_w   (Ptrofs.repr ofs_w)) ->
  le ! (id_out ids) = Some (Vptr b_out (Ptrofs.repr ofs_out)) ->
  le ! (id_len ids) = Some (Vlong (Int64.repr (Z.of_nat (length w1 + length w2)))) ->
  e ! (id_delta ids) = None ->
  b_w <> b_t -> b_w <> b_ot -> b_out <> b_t -> b_out <> b_ot -> b_w <> b_out ->
  b_o <> b_t -> b_o <> b_ot -> b_o <> b_out -> b_o <> b_w ->
  Mem.range_perm m b_o 0 8 Cur Writable ->
  Mem.range_perm m b_out (ofs_out + 8 * Z.of_nat (length w1))
     (ofs_out + 8 * Z.of_nat (length w1 + length w2)) Cur Writable ->
  (align_chunk Mint64 | ofs_out) ->
  0 <= ofs_w -> 0 <= ofs_out ->
  Z.of_nat (length w1 + length w2) < Int64.modulus ->
  ofs_w   + 8 * Z.of_nat (length w1 + length w2) < Ptrofs.modulus ->
  ofs_out + 8 * Z.of_nat (length w1 + length w2) < Ptrofs.modulus ->
  exists m' le',
    exec_stmt function_entry2 ge e le m (run_loop ids) E0 le' m' Out_normal /\
    buf_in_mem m' b_out (ofs_out + 8 * Z.of_nat (length w1)) lo2 /\
    perms_eq m m' /\
    Mem.unchanged_on
      (loop_frame b_o b_out (ofs_out + 8 * Z.of_nat (length w1))
                            (ofs_out + 8 * Z.of_nat (length w1 + length w2))) m m'.
Proof.
  induction w2 as [| a w2' IH];
    intros w1 l2 lo2 e le b_w ofs_w b_out ofs_out b_o b_t b_ot m
      Hsym Hout Hword Hbt Hbot Htload Hotload Ho Hi Hq Hw Hout' Hlen Hdelta_id
      Hbwt Hbwot Hboutt Hboutot Hbwo
      Hbot_t Hbot_ot Hbo_out Hbo_w
      Hperm_o Hperm_out Halign Hofsw Hofsout
      Hlenmod Hwmod Houtmod.

  - cbn [length outputs] in *. rewrite Nat.add_0_r in *.
    inversion Hout; subst; clear Hout.
    exists m, le. split; [| split; [| split]].
    + eapply exec_Sloop_stop1; [| constructor].
      unfold run_loop, MC.run_body.
      eapply exec_Sseq_2; [| discriminate].
      eapply exec_Sifthenelse with (b := false).
      * econstructor; [ econstructor; eauto | econstructor; eauto |].
        cbn. unfold sem_cmp, classify_cmp, tlong, sem_binarith, sem_cast,
                   classify_cast, classify_binarith. cbn.
        destruct Archi.ptr64; cbn; unfold Val.of_bool, Int64.ltu;
          rewrite !Int64.unsigned_repr by (unfold Int64.max_unsigned; lia);
          rewrite zlt_false by lia; reflexivity.
      * apply bool_val_zero_int.
      * constructor.
    + intros n i Hn. now destruct n.
    + apply perms_eq_refl.
    + apply Mem.unchanged_on_refl.

  - inversion Hsym as [| a0 si w0 l2' Hsi Hsym' [Ea El]]; subst; clear Hsym.
    cbn [outputs] in Hout.
    set (qw := Mealy.run mealy w1) in *.
    inversion Hout as [| o0 oi outs lo2' Hoi Hout'' [Eo Elo]]; subst; clear Hout.
    destruct Hq as (qi & Hqi & Hqle).

    (* the index of the successor state *)
    destruct (sidx_run (w1 ++ [a])) as (ni & Hni).
    assert (Hnext : sidx (mealy.(transition _) qw a) = Some ni).
    { rewrite <- Hni. unfold qw, Mealy.run. now rewrite fold_left_app. }

    assert (Hqib : 0 <= qi < nstates) by
      (unfold sidx, nstates, MC.nstates in *; apply index_of_bounds in Hqi; lia).
    assert (Hsib : 0 <= si < nsyms) by
      (unfold symidx, nsyms in *; apply index_of_bounds in Hsi; lia).
    assert (Hcell : 0 <= qi * nsyms + si < nstates * nsyms) by
      (clear - Hqib Hsib;
       unfold nstates, nsyms in *; nia).

    (* the two table cells [delta] will read, at the current memory [m] *)
    assert (Hloadt :
      Mem.loadv Mint64 m (Vptr b_t (Ptrofs.repr (8 * (qi * nsyms + si))))
        = Some (Vlong (Int64.repr ni))).
    { apply Htload with (k := qi * nsyms + si); [| eauto].
      erewrite table_entry_correct by eauto.
      do 2 f_equal. now erewrite table_entry_sidx by eauto. }
    assert (Hloadot :
      Mem.loadv Mint64 m (Vptr b_ot (Ptrofs.repr (8 * (qi * nsyms + si))))
        = Some (Vlong (Int64.repr oi))).
    { apply Hotload with (k := qi * nsyms + si); [| eauto].
      erewrite otable_entry_correct by eauto.
      do 2 f_equal. now erewrite otable_entry_oidx by eauto. }

    assert (H8lt : 0 + 8 < Ptrofs.modulus).
    { unfold Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize, two_power_nat.
      destruct Archi.ptr64; cbn; lia. }

    destruct (compile_delta_correct
                qw a qi si ni oi b_o 0 b_t b_ot m
                Hqi Hsi Hnext Hoi Hbt Hbot Hloadt Hloadot
                Hperm_o (Z.divide_0_r _) (Z.le_refl 0) H8lt Hbot_t Hbot_ot)
      as (m1 & Hstore_o & Hdelta & Hunch1).
    assert (Hstore_o' : Mem.store Mint64 m b_o 0 (Vlong (Int64.repr oi)) = Some m1).
    { unfold Mem.storev in Hstore_o.
      rewrite Ptrofs.unsigned_repr in Hstore_o
        by (unfold Ptrofs.max_unsigned; pose proof Ptrofs.modulus_pos; lia).
      eauto. }

    (* the symbol w[i] sits at ofs_w + 8|w1| and survives delta's write *)
    assert (Hwi :
      Mem.loadv Mint64 m (Vptr b_w (Ptrofs.repr (ofs_w + 8 * Z.of_nat (length w1))))
        = Some (Vlong (Int64.repr si))).
    { specialize (Hword O si eq_refl). now rewrite Nat.add_0_r in Hword. }

    assert (Hperm_out1 : Mem.range_perm m1 b_out
              (ofs_out + 8 * Z.of_nat (length w1))
              (ofs_out + 8 * Z.of_nat (length w1) + 8) Cur Writable).
    { intros z Hz. eapply Mem.perm_store_1; eauto.
      apply Hperm_out. cbn [length] in *. rewrite Nat.add_succ_r. lia. }
    destruct (Mem.valid_access_store m1 Mint64 b_out
                (ofs_out + 8 * Z.of_nat (length w1)) (Vlong (Int64.repr oi)))
      as (m2 & Hstore_out).
    { split.
      - intros z Hz. eapply Mem.perm_implies; [| constructor].
        apply Hperm_out1. cbn [size_chunk] in Hz. lia.
      - apply Z.divide_add_r; eauto.
        apply Z.divide_mul_l. apply Z.divide_refl. }

    (* permissions are untouched by both stores *)
    assert (Hpe2 : perms_eq m m2).
    { eapply perms_eq_trans;
        [ eapply perms_eq_store; eauto
        | eapply perms_eq_store; eauto ]. }

    (* the frame for this single iteration *)
    assert (Hunch2 : Mem.unchanged_on
              (loop_frame b_o b_out (ofs_out + 8 * Z.of_nat (length w1))
                                    (ofs_out + 8 * Z.of_nat (length w1) + 8)) m m2).
    { eapply Mem.unchanged_on_trans.
      - eapply Mem.unchanged_on_implies; eauto.
        intros b o (Hbo & _) _. now left.
      - eapply Mem.store_unchanged_on; eauto.
        intros z Hz (_ & [Hb | [Hlt | Hge]]); 
          [congruence | cbn [size_chunk] in Hz; lia | cbn [size_chunk] in Hz; lia]. }

    assert (Hword2 : forall n j, nth_error l2' n = Some j ->
       Mem.loadv Mint64 m2 (Vptr b_w (Ptrofs.repr
          (ofs_w + 8 * Z.of_nat (length (w1 ++ [a]) + n))))
          = Some (Vlong (Int64.repr j))).
    { intros n j Hn. unfold Mem.loadv in *.
      erewrite Mem.load_unchanged_on; [reflexivity | eauto | |].
      - intros z _. split; [congruence | now left].
      - rewrite length_app. cbn [length]. rewrite Nat.add_1_r.
        specialize (Hword (S n) j).
        replace (S (length w1) + n)%nat with (length w1 + S n)%nat by lia.
        apply Hword. cbn [nth_error]. eauto. }
    assert (Htload2 : forall k v,
       nth_error (table_init state mealy state_eq_dec) (Z.to_nat k)
         = Some (Init_int64 v) -> 0 <= k < nstates * nsyms ->
       Mem.loadv Mint64 m2 (Vptr b_t (Ptrofs.repr (8*k))) = Some (Vlong v)).
    { intros k v Hk Hkb. unfold Mem.loadv in *.
      erewrite Mem.load_unchanged_on; [reflexivity | eauto | | now apply Htload].
      intros z _. split; [congruence | now left]. }
    assert (Hotload2 : forall k v,
       nth_error (otable_init state mealy) (Z.to_nat k)
         = Some (Init_int64 v) -> 0 <= k < nstates * nsyms ->
       Mem.loadv Mint64 m2 (Vptr b_ot (Ptrofs.repr (8*k))) = Some (Vlong v)).
    { intros k v Hk Hkb. unfold Mem.loadv in *.
      erewrite Mem.load_unchanged_on; [reflexivity | eauto | | now apply Hotload].
      intros z _. split; [congruence | now left]. }
    assert (Hperm_o2 : Mem.range_perm m2 b_o 0 8 Cur Writable).
    { intros z Hz. apply Hpe2. now apply Hperm_o. }
    assert (Hperm_out2 : Mem.range_perm m2 b_out
              (ofs_out + 8 * Z.of_nat (length (w1 ++ [a])))
              (ofs_out + 8 * Z.of_nat (length (w1 ++ [a]) + length w2')) Cur Writable).
    { intros z Hz. apply Hpe2. apply Hperm_out.
      rewrite length_app in Hz. cbn [length] in *.
      rewrite Nat.add_1_r, Nat.add_succ_r in *. lia. }

    (* the temp env after this iteration *)
    set (le2 := PTree.set (id_i ids)
                  (Vlong (Int64.repr (Z.of_nat (length w1) + 1)))
                  (PTree.set (id_q ids) (Vlong (Int64.repr ni)) le)) in *.

    edestruct (IH (w1 ++ [a]) l2' lo2' e le2
                 b_w ofs_w b_out ofs_out b_o b_t b_ot m2)
      as (m' & le' & Hexec' & Hbuf' & Hpe' & Hunch').
    all: subst le2; eauto.
    + (* the outputs of w2' start from run (w1 ++ [a]) *)
      unfold Mealy.run in *. now rewrite fold_left_app.
    + (* i = |w1 ++ [a]| *)
      rewrite PTree.gss. rewrite length_app. cbn [length]. do 3 f_equal. lia.
    + (* q = sidx (run (w1 ++ [a])) *)
      exists ni. split; eauto.
      rewrite PTree.gso by (cbv [ids alloc_idents id_i id_q]; lia).
      apply PTree.gss.
    + rewrite PTree.gso by (cbv [ids alloc_idents id_w id_i]; lia).
      rewrite PTree.gso by (cbv [ids alloc_idents id_w id_q]; lia). eauto.
    + rewrite PTree.gso by (cbv [ids alloc_idents id_out id_i]; lia).
      rewrite PTree.gso by (cbv [ids alloc_idents id_out id_q]; lia). eauto.
    + rewrite PTree.gso by (cbv [ids alloc_idents id_len id_i]; lia).
      rewrite PTree.gso by (cbv [ids alloc_idents id_len id_q]; lia).
      rewrite Hlen. do 3 f_equal. rewrite length_app. cbn [length]. lia.
    + rewrite length_app in *. cbn [length] in *.
      rewrite Nat.add_1_r, Nat.add_succ_r in *. lia.
    + rewrite length_app in *. cbn [length] in *.
      rewrite Nat.add_1_r, Nat.add_succ_r in *. lia.
    + rewrite length_app in *. cbn [length] in *.
      rewrite Nat.add_1_r, Nat.add_succ_r in *. lia.

    + destruct find_delta as (b_d & Hdsym & Hdfun).
      exists m', le'. split; [| split; [| split]].
      * (* one turn of the loop, then the rest *)
        change E0 with (E0 ** E0 ** E0).
        eapply exec_Sloop_loop with (out1 := Out_normal); revgoals.
        -- eauto.
        -- constructor.
        -- constructor.
        -- (* the body: guard; q = delta(q, w[i], &o); out[i] = o; i++ *)
           unfold MC.run_body.
           change E0 with (E0 ** E0).
           eapply exec_Sseq_1.
           ++ (* the guard is true *)
              eapply exec_Sifthenelse with (b := true).
              ** econstructor; [ econstructor; eauto | econstructor; eauto |].
                 cbn. unfold sem_cmp, classify_cmp, tlong, sem_binarith, sem_cast,
                            classify_cast, classify_binarith. cbn.
                 destruct Archi.ptr64; cbn; unfold Val.of_bool, Int64.ltu;
                   rewrite !Int64.unsigned_repr by
                     (unfold Int64.max_unsigned; cbn [length] in *; lia);
                   rewrite zlt_true by (cbn [length]; lia); reflexivity.
              ** apply bool_val_one_int.
              ** constructor.
           ++ change E0 with (E0 ** E0).
              eapply exec_Sseq_1.
              ** (* q = delta(q, w[i], &o) *)
                 eapply exec_Scall with
                   (vargs := [Vlong (Int64.repr qi); Vlong (Int64.repr si);
                              Vptr b_o Ptrofs.zero]).
                 --- reflexivity.
                 --- eapply eval_Elvalue.
                       eapply eval_Evar_global; eauto.
                     eapply deref_loc_reference. reflexivity.
                 --- (* the three arguments *)
                     econstructor.
                     +++ econstructor. eauto.
                     +++ cbn. unfold sem_cast, classify_cast, tlong.
                         now destruct Archi.ptr64.
                     +++ econstructor.
                         *** eapply eval_Elvalue.
                             ---- econstructor. econstructor.
                                  ++++ econstructor. eauto.
                                  ++++ econstructor. eauto.
                                  ++++ cbn. unfold sem_add, classify_add, w_type, tlong. cbn.
                                       destruct Archi.ptr64 eqn:E; [| discriminate].
                                       unfold sem_add_ptr_long. cbn. do 3 f_equal.
                             ---- eapply deref_loc_value with (chunk := Mint64); eauto.
                                  rewrite ptr_add_normalize by lia. apply Hwi.
                         *** cbn. unfold sem_cast, classify_cast, tlong.
                             now destruct Archi.ptr64.
                         *** econstructor.
                             ---- econstructor. econstructor. eauto.
                             ---- cbn. unfold sem_cast, classify_cast, tlptr. cbn.
                                  now destruct Archi.ptr64.
                             ---- econstructor.
                 --- unfold Genv.find_funct in Hdfun |- *. eauto.
                 --- reflexivity.
                 --- eauto.
              ** change E0 with (E0 ** E0).
                 eapply exec_Sseq_1.
                 --- (* out[i] = o *)
                     econstructor.
                     +++ (* lvalue out + i *)
                         econstructor. econstructor.
                         *** econstructor. cbn - [Pos.add].
                             rewrite PTree.gso
                               by (cbv [ids alloc_idents id_out id_q]; lia).
                             eauto.
                         *** econstructor. cbn - [Pos.add].
                             rewrite PTree.gso
                               by (cbv [ids alloc_idents id_i id_q]; lia).
                             eauto.
                         *** cbn. unfold sem_add, classify_add, tlptr, tlong. cbn.
                             destruct Archi.ptr64 eqn:E; [| discriminate].
                             unfold sem_add_ptr_long. cbn. do 3 f_equal.
                     +++ (* rvalue: the scratch [o], read back out of m1 *)
                         eapply eval_Elvalue.
                         *** econstructor. eauto.
                         *** eapply deref_loc_value with (chunk := Mint64).
                               reflexivity.
                             cbn [Mem.loadv]. rewrite Ptrofs.unsigned_zero.
                             rewrite (Mem.load_store_same _ _ _ _ _ _ Hstore_o').
                             reflexivity.
                     +++ cbn. unfold sem_cast, classify_cast, tlong.
                         now destruct Archi.ptr64.
                     +++ eapply assign_loc_value with (chunk := Mint64).
                           reflexivity.
                         cbn [Mem.storev]. rewrite ptr_add_normalize by lia.
                         rewrite Ptrofs.unsigned_repr by
                          (unfold Ptrofs.max_unsigned, nsyms, nstates in *; lia).
                         apply Hstore_out.
                 --- (* i++ *)
                     econstructor. econstructor.
                     +++ econstructor. cbn - [Pos.add].
                         rewrite PTree.gso by (cbv [ids alloc_idents id_i id_q]; lia).
                         eauto.
                     +++ econstructor.
                     +++ cbn. unfold sem_binarith, sem_cast, classify_cast,
                                classify_binarith, tlong. cbn.
                         destruct Archi.ptr64; cbn; do 2 f_equal;
                           rewrite add_repr_in_range;
                           solve [ reflexivity
                                 | unfold Int64.max_unsigned;
                                   cbn [length] in *; rewrite Nat.add_succ_r in *; lia ].
      * (* buf_in_mem for [oi :: lo2'] *)
        intros n j Hn. destruct n as [| n'].
        -- (* the entry just stored, preserved across the recursive call *)
           cbn [nth_error] in Hn. inversion Hn; subst j; clear Hn.
           cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r.
           unfold Mem.loadv.
           erewrite Mem.load_unchanged_on; [| eauto | |].
           ++ reflexivity.
           ++ intros z Hz. split. congruence. right. left.
              rewrite length_app. cbn [length]. rewrite Nat.add_1_r.
              cbn [size_chunk] in Hz.
              rewrite Ptrofs.unsigned_repr in Hz. lia.
              unfold Ptrofs.max_unsigned, nstates, nsyms in *.
              lia.
           ++ pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore_out).
              rewrite Ptrofs.unsigned_repr by
                (unfold Ptrofs.max_unsigned, nstates, nsyms in *; lia).
              apply H.
        -- (* the rest, from the recursive call *)
           cbn [nth_error] in Hn.
           specialize (Hbuf' n' j Hn).
           rewrite length_app in Hbuf'. cbn [length] in Hbuf'.
           rewrite Nat.add_1_r in Hbuf'.
           replace (ofs_out + 8 * Z.of_nat (length w1) + 8 * Z.of_nat (S n'))
             with (ofs_out + 8 * Z.of_nat (S (length w1)) + 8 * Z.of_nat n')
             by (rewrite !Nat2Z.inj_succ; lia).
           eauto.
      * (* permissions *) eapply perms_eq_trans; [eauto | eauto].
      * (* the composite frame *)
        eapply Mem.unchanged_on_trans.
        -- eapply Mem.unchanged_on_implies; eauto.
           intros b o (Hbo & Hrest) _. split; eauto.
           destruct Hrest as [Hb | [Hlt | Hge]]; [now left | now right; left |].
           right. right. cbn [length] in Hge. rewrite Nat.add_succ_r in Hge. lia.
        -- eapply Mem.unchanged_on_implies; eauto.
           intros b o (Hbo & Hrest) _. split; eauto.
           destruct Hrest as [Hb | [Hlt | Hge]]; [now left | |].
           ++ right. left. rewrite length_app. cbn [length]. rewrite Nat.add_1_r.
              rewrite Nat2Z.inj_succ. lia.
           ++ right. right. rewrite length_app. cbn [length] in *.
              rewrite Nat.add_1_r, Nat.add_succ_r in *. lia.
Qed.

Lemma elements_singleton : forall (A : Type) (i : positive) (v : A),
  PTree.elements (PTree.set i v (PTree.empty A)) = [(i, v)].
Proof.
  intros A i v.
  assert (Hin : In (i, v) (PTree.elements (PTree.set i v (PTree.empty A))))
    by (apply PTree.elements_correct; apply PTree.gss).
  assert (Hall : forall x, In x (PTree.elements (PTree.set i v (PTree.empty A)))
                   -> x = (i, v)).
  { intros (j & w) Hj. apply PTree.elements_complete in Hj.
    destruct (peq j i) as [-> | Hne].
    - rewrite PTree.gss in Hj. now inversion Hj.
    - rewrite PTree.gso in Hj by eauto.
      rewrite PTree.gempty in Hj. discriminate. }
  pose proof (PTree.elements_keys_norepet (PTree.set i v (PTree.empty A))) as Hnr.
  destruct (PTree.elements (PTree.set i v (PTree.empty A)))
    as [| x [| y tl]] eqn:E.
  - destruct Hin.
  - now rewrite (Hall x (or_introl eq_refl)).
  - exfalso.
    rewrite (Hall x (or_introl eq_refl)) in Hnr.
    rewrite (Hall y (or_intror (or_introl eq_refl))) in Hnr.
    cbn in Hnr. inversion Hnr as [| ? ? Hni ?]; subst. apply Hni. now left.
Qed.

(* run: the output buffer ends holding the run's outputs *)
Theorem compile_run_correct :
  forall w l lo b_w ofs_w b_out ofs_out b_t b_ot m,
  sym_indices w l ->
  Forall2 (fun o i => oidx o = Some i) (run_outputs mealy w) lo ->
  word_in_mem m b_w ofs_w l ->
  Genv.find_symbol ge ids.(id_table) = Some b_t ->
  Genv.find_symbol ge ids.(id_otable) = Some b_ot ->
  (forall k v, nth_error (table_init state mealy state_eq_dec) (Z.to_nat k) = Some (Init_int64 v) ->
     0 <= k < nstates * nsyms -> Mem.loadv Mint64 m (Vptr b_t (Ptrofs.repr (8 * k))) = Some (Vlong v)) ->
  (forall k v, nth_error (otable_init state mealy) (Z.to_nat k) = Some (Init_int64 v) ->
     0 <= k < nstates * nsyms -> Mem.loadv Mint64 m (Vptr b_ot (Ptrofs.repr (8 * k))) = Some (Vlong v)) ->
  b_w <> b_t -> b_w <> b_ot -> b_out <> b_t -> b_out <> b_ot ->
  Mem.valid_block m b_w -> Mem.valid_block m b_out ->
  Mem.valid_block m b_t -> Mem.valid_block m b_ot ->
  Mem.range_perm m b_out ofs_out (ofs_out + 8 * Z.of_nat (length w)) Cur Writable ->
  (align_chunk Mint64 | ofs_out) ->
  0 <= ofs_w -> 0 <= ofs_out ->
  b_w <> b_out ->
  Z.of_nat (length w) < Int64.modulus ->
  ofs_w + 8 * Z.of_nat (length w) < Ptrofs.modulus ->
  ofs_out + 8 * Z.of_nat (length w) < Ptrofs.modulus ->
  exists m',
    eval_funcall function_entry2 ge m
      (compile_run state mealy state_eq_dec ids)
      [Vptr b_w (Ptrofs.repr ofs_w); Vlong (Int64.repr (Z.of_nat (length w)));
       Vptr b_out (Ptrofs.repr ofs_out)] E0 m' Vundef /\
    buf_in_mem m' b_out ofs_out lo /\
    Mem.unchanged_on (fun b _ => b <> b_out) m m'.
Proof.
  intros w l lo b_w ofs_w b_out ofs_out b_t b_ot m
    Hsym Hout Hword Hbt Hbot Htload Hotload
    Hbwt Hbwot Hboutt Hboutot Hvw Hvout Hvt Hvot
    Hperm_out Halign Hofsw Hofsout Hbwo Hlenmod Hwmod Houtmod.

  destruct (Mem.alloc m 0 (sizeof ge tlong)) as (m1 & b_o) eqn:Halloc.
  set (e := PTree.set (id_o ids) (b_o, tlong) (PTree.empty (block * type))).

  assert (Hfresh : ~ Mem.valid_block m b_o)
    by (eapply Mem.fresh_block_alloc; eauto).
  assert (Hbo_w   : b_o <> b_w)   by (intro; subst; contradiction).
  assert (Hbo_out : b_o <> b_out) by (intro; subst; contradiction).
  assert (Hbo_t   : b_o <> b_t)   by (intro; subst; contradiction).
  assert (Hbo_ot  : b_o <> b_ot)  by (intro; subst; contradiction).

  assert (Hunch_alloc : forall P, Mem.unchanged_on P m m1)
    by (intro P; eapply Mem.alloc_unchanged_on; eauto).

  assert (Hword1 : forall n i, nth_error l n = Some i ->
     Mem.loadv Mint64 m1 (Vptr b_w (Ptrofs.repr
        (ofs_w + 8 * Z.of_nat (0 + n)))) = Some (Vlong (Int64.repr i))).
  { intros n i Hn. cbn [Nat.add]. unfold Mem.loadv in *.
    erewrite Mem.load_unchanged_on;
      [reflexivity | apply Hunch_alloc | intros; exact I | now apply Hword]. }
  assert (Htload1 : forall k v,
     nth_error (table_init state mealy state_eq_dec) (Z.to_nat k) = Some (Init_int64 v) ->
     0 <= k < nstates * nsyms ->
     Mem.loadv Mint64 m1 (Vptr b_t (Ptrofs.repr (8*k))) = Some (Vlong v)).
  { intros k v Hk Hkb. unfold Mem.loadv in *.
    erewrite Mem.load_unchanged_on;
      [reflexivity | apply Hunch_alloc | intros; exact I | now apply Htload]. }
  assert (Hotload1 : forall k v,
     nth_error (otable_init state mealy) (Z.to_nat k) = Some (Init_int64 v) ->
     0 <= k < nstates * nsyms ->
     Mem.loadv Mint64 m1 (Vptr b_ot (Ptrofs.repr (8*k))) = Some (Vlong v)).
  { intros k v Hk Hkb. unfold Mem.loadv in *.
    erewrite Mem.load_unchanged_on;
      [reflexivity | apply Hunch_alloc | intros; exact I | now apply Hotload]. }
  assert (Hperm_out1 : Mem.range_perm m1 b_out ofs_out
            (ofs_out + 8 * Z.of_nat (0 + length w)) Cur Writable).
  { intros z Hz. eapply Mem.perm_alloc_1; eauto. }
  assert (Hperm_o1 : Mem.range_perm m1 b_o 0 8 Cur Writable).
  { intros z Hz. eapply Mem.perm_implies.
      eapply Mem.perm_alloc_2; eauto. constructor. }

  (* temp env *)
  set (le0 := PTree.set (id_out ids) (Vptr b_out (Ptrofs.repr ofs_out))
               (PTree.set (id_len ids) (Vlong (Int64.repr (Z.of_nat (length w))))
                 (PTree.set (id_w ids) (Vptr b_w (Ptrofs.repr ofs_w))
                   (create_undef_temps
                      [(ids.(id_i), tlong); (ids.(id_q), tlong)])))).
  set (le1 := PTree.set (id_q ids)
                (Vlong (Int64.repr (q0_index state mealy state_eq_dec)))
                (PTree.set (id_i ids) (Vlong (Int64.repr 0)) le0)).

  (* loop *)
  edestruct (run_loop_correct w [] l lo e le1
               b_w ofs_w b_out ofs_out b_o b_t b_ot m1)
    as (m2 & le' & Hexec & Hbuf & Hpe & Hunch_loop).
  all: eauto.
  + (* o = b_o *)
    subst e. now rewrite PTree.gss.
  + (* i = 0 *)
    subst le1. rewrite PTree.gso by (cbv [ids alloc_idents id_i id_q]; lia).
    apply PTree.gss.
  + (* q = q0 *)
    exists (q0_index state mealy state_eq_dec). split.
      cbn [Mealy.run fold_left]. apply q0_index_correct.
    subst le1. apply PTree.gss.
  + (* w = &ofs_w *)
    subst le1. rewrite PTree.gso by (cbv [ids alloc_idents id_w id_q]; lia).
    rewrite PTree.gso by (cbv [ids alloc_idents id_w id_i]; lia).
    subst le0. rewrite PTree.gso by (cbv [ids alloc_idents id_w id_out]; lia).
    rewrite PTree.gso by (cbv [ids alloc_idents id_w id_len]; lia).
    now rewrite PTree.gss.
  + subst le1. rewrite PTree.gso by (cbv [ids alloc_idents id_out id_q]; lia).
    rewrite PTree.gso by (cbv [ids alloc_idents id_out id_i]; lia).
    subst le0. now rewrite PTree.gss.
  + subst le1. rewrite PTree.gso by (cbv [ids alloc_idents id_len id_q]; lia).
    rewrite PTree.gso by (cbv [ids alloc_idents id_len id_i]; lia).
    subst le0. rewrite PTree.gso by (cbv [ids alloc_idents id_len id_out]; lia).
    now rewrite PTree.gss.
  + subst e. rewrite PTree.gso by (cbv [ids alloc_idents id_o id_delta]; lia).
    apply PTree.gempty.
  + cbn [length Z.of_nat]. rewrite Z.mul_0_r, Nat.add_0_l, Z.add_0_r. assumption.
  + (* return *)
    cbn [length Z.of_nat] in Hbuf. rewrite Z.mul_0_r, Z.add_0_r in Hbuf.
    assert (Hfree : exists m3, Mem.free m2 b_o 0 8 = Some m3).
    { pose proof (Mem.range_perm_free m2 b_o 0 8). destruct X.
        intros z Hz. apply Hpe. eapply Mem.perm_alloc_2; eassumption.
      now exists x. }
    destruct Hfree as (m3 & Hfree).
    assert (Hblocks : blocks_of_env ge e = [(b_o, 0, 8)]).
    { unfold blocks_of_env, e. rewrite elements_singleton. reflexivity. }
    exists m3. split; [| split].
    * (* the call itself *)
      eapply eval_funcall_internal with (e := e) (le1 := le0) (m1 := m1).
      -- (* function_entry2 *)
         econstructor; cbn - [Pos.add].
         ++ repeat constructor. now intro.
         ++ repeat constructor; cbn - [Pos.add]; intro Hin;
              repeat (destruct Hin as [Hin|Hin]; [lia|]); contradiction.
         ++ repeat intro. cbn - [Pos.add] in *.
            repeat (destruct H as [H|H]; subst; try contradiction);
            repeat (destruct H0 as [H0|H0]; subst; try contradiction); lia.
         ++ econstructor; [eauto | constructor].
         ++ reflexivity.
      -- (* the body: prologue then loop *)
         unfold compile_run. cbn [fn_body].
         change E0 with (E0 ** E0).
         eapply exec_Sseq_1.
         ++ (* i := 0; q := q0 *)
            change E0 with (E0 ** E0).
            eapply exec_Sseq_1.
            ** econstructor. econstructor.
            ** econstructor. unfold compiled_q0. econstructor.
         ++ eauto.
      -- (* the outcome of a void function that falls off the end *)
         cbn. auto.
      -- rewrite Hblocks. cbn [Mem.free_list]. now rewrite Hfree.
    * intros n i Hn. specialize (Hbuf n i Hn).
      unfold Mem.loadv in *. erewrite Mem.load_free; eauto.
    * apply (Mem.unchanged_on_implies
               (fun b _ => b <> b_out /\ Mem.valid_block m b)).
      -- eapply Mem.unchanged_on_trans; [| eapply Mem.unchanged_on_trans].
         ++ (* m -> m1 : allocation changes nothing already present *) 
            eapply Mem.unchanged_on_implies.
              eapply Mem.alloc_unchanged_on; eauto.
            intros b ofs Hb _. exact I.
         ++ (* m1 -> m2 : the loop's frame, weakened using freshness of b_o *)
            eapply Mem.unchanged_on_implies; eauto.
            intros b ofs (Hbout & Hvb) _. split.
              intro; subst b; contradiction.
            now left.
         ++ (* m2 -> m3 : the free touches only b_o, which is not valid in m *)
            eapply Mem.unchanged_on_implies.
              eapply (Mem.free_unchanged_on
                        (fun b _ => b <> b_out /\ Mem.valid_block m b)); eauto.
              intros i _ (_ & Hvb). apply Hfresh, Hvb.
            intros b ofs Hb _. eauto.
      -- intros b ofs Hb Hvb. split; assumption.
Qed.

End correctness.
End Correctness.
