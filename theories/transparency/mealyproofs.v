From lstar Require Import automata.Mealy.
From compcert Require Import AST Clight Ctypes Integers Cop Maps.
From compcert Require Import ClightBigstep Values Events Coqlib.
From compcert Require Import Globalenvs Memory.
From Transmogrifier Require Import Monads.
From Transmogrifier.compiler Require Import mealy.
From Stdlib Require Import List ZArith Lia.
Import ListNotations.
Open Scope result_scope.
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

(** One step pushed onto the end: the analogue of Moore's [run_snoc]. Proved
    by list induction; validated numerically before porting. *)
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
      rewrite Z.sub_0_r in Hq. rewrite Hq in Hnth. inversion Hnth; subst. exact Hpair. }
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
  rewrite nth_error_flat_map_uniform with (k := length s.enum) (x := (q_idx, q)).
  - exact Hcol.
  - intros (qi & qq) _. apply table_row_length.
  - exact Hrow.
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
      rewrite Z.sub_0_r in Hq. rewrite Hq in Hnth. inversion Hnth; subst. exact Hpair. }
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
  rewrite nth_error_flat_map_uniform with (k := length s.enum) (x := (q_idx, q)).
  - exact Hcol.
  - intros (qi & qq) _. apply otable_row_length.
  - exact Hrow.
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

Lemma compile_delta_correct :
  forall q sym q_idx s_idx next_idx o_idx b_o ofs_o m,
  sidx q = Some q_idx ->
  symidx sym = Some s_idx ->
  sidx (mealy.(transition _) q sym) = Some next_idx ->
  oidx (mealy.(output _) q sym) = Some o_idx ->
  Mem.range_perm m b_o ofs_o (ofs_o + 8) Cur Writable ->
  (align_chunk Mint64 | ofs_o) ->
  0 <= ofs_o -> ofs_o + 8 < Ptrofs.modulus ->
  exists m',
    Mem.storev Mint64 m (Vptr b_o (Ptrofs.repr ofs_o)) (Vlong (Int64.repr o_idx)) = Some m' /\
    eval_funcall function_entry2 ge m
      (compile_delta state mealy ids)
      [Vlong (Int64.repr q_idx); Vlong (Int64.repr s_idx); Vptr b_o (Ptrofs.repr ofs_o)]
      E0 m' (Vlong (Int64.repr next_idx)) /\
    Mem.unchanged_on (fun b o => b <> b_o \/ o < ofs_o \/ ofs_o + 8 <= o) m m'.
Proof.
Admitted.

(** [delta] on out-of-range input writes [|O|] and returns [|Q|]. *)
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
Admitted.

(** [out[0..len-1]] hold the given index list. *)
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

(** After [run(w, len, out)], the buffer [out] holds the [run_outputs]
    index string, and only the buffer changed. *)
Lemma compile_run_correct :
  forall w l lo b_w ofs_w b_out ofs_out m,
  sym_indices w l ->
  Forall2 (fun o i => oidx o = Some i) (run_outputs mealy w) lo ->
  word_in_mem m b_w ofs_w l ->
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
    Mem.unchanged_on (fun b o => b <> b_out) m m'.
Proof.
Admitted.

End correctness.
End Correctness.
