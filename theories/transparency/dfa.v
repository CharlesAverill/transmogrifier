From lstar Require Import Automata.
From compcert Require Import AST Clight Ctypes Integers Cop Maps.
From compcert Require Import ClightBigstep Values Events Coqlib.
From compcert Require Import Globalenvs.
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
Variable syms_bounded   : Z.of_nat (length s.enum) < Int64.modulus.

Variable base : ident.
Variable p : Clight.program.
Variable Hp : compile_program state dfa state_eq_dec base = Ok p.

Definition ge : genv := Clight.globalenv p.

Definition ids : idents := alloc_idents base.

Lemma compile_program_defs :
  prog_defs p =
    [ (ids.(id_delta),  Gfun (compile_delta state dfa state_eq_dec ids));
      (ids.(id_accept), Gfun (compile_accept state dfa ids));
      (ids.(id_q0),     Gvar (compile_q0 state dfa state_eq_dec));
      (ids.(id_run),    Gfun (compile_run state dfa state_eq_dec ids)) ].
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
    [ (ids.(id_delta),  Gfun (compile_delta state dfa state_eq_dec ids));
      (ids.(id_accept), Gfun (compile_accept state dfa ids));
      (ids.(id_q0),     Gvar (compile_q0 state dfa state_eq_dec));
      (ids.(id_run),    Gfun (compile_run state dfa state_eq_dec ids)) ].
Proof. exact compile_program_defs. Qed.

Lemma defmap_delta :
  (prog_defmap p) ! (ids.(id_delta)) =
    Some (Gfun (compile_delta state dfa state_eq_dec ids)).
Proof.
  unfold prog_defmap. rewrite compile_program_defs_ast.
  apply PTree_Properties.of_list_norepet.
    rewrite <- compile_program_defs. apply global_idents_norepet.
  now left.
Qed.

Lemma find_delta_def :
  exists b,
    Genv.find_symbol ge ids.(id_delta) = Some b /\
    Genv.find_def ge b = Some (Gfun (compile_delta state dfa state_eq_dec ids)).
Proof.
  apply Genv.find_def_symbol. apply defmap_delta.
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

Lemma eval_eq_test_true : forall e le m v k,
  le ! v = Some (Vlong (Int64.repr k)) ->
  eval_expr ge e le m (eq_test v k) (Vint Int.one).
Proof.
  intros. unfold eq_test. econstructor.
    econstructor. eassumption.
    econstructor.
  simpl.
  unfold sem_cmp, classify_cmp, tlong, sem_binarith, sem_cast,
         classify_cast, classify_binarith. simpl.
  destruct Archi.ptr64; simpl;
  unfold Val.of_bool; now rewrite Int64.eq_true.
Qed.

Lemma eval_eq_test_false : forall e le m v k j,
  le ! v = Some (Vlong (Int64.repr j)) ->
  0 <= j < Int64.modulus -> 0 <= k < Int64.modulus ->
  j <> k ->
  eval_expr ge e le m (eq_test v k) (Vint Int.zero).
Proof.
  intros. unfold eq_test. econstructor.
    econstructor. eassumption.
    econstructor.
  simpl. unfold sem_cmp, sem_binarith, classify_binarith, tlong,
                sem_cast, classify_cast, classify_cmp. simpl.
  destruct Archi.ptr64; simpl;
    now rewrite Int64.eq_false by (intro X; apply H2; eapply repr_inj_in_range; eauto).
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

Lemma sym_branch_exec : forall ids e le m tbl acc q sym s_idx next_idx,
  le ! (ids.(id_s)) = Some (Vlong (Int64.repr s_idx)) ->
  sidx (dfa.(transition _) q sym) = Some next_idx ->
  In (s_idx, sym) tbl ->
  (forall i a, In (i, a) tbl -> 0 <= i < Int64.modulus) ->
  list_norepet (map fst tbl) ->
  exec_stmt function_entry2 ge e le m
    (fold_left (fun (acc : statement) '(si, sy) =>
       match sidx (dfa.(transition _) q sy) with
       | Some ni => Sifthenelse (eq_test ids.(id_s) si)
                      (Sreturn (Some (Econst_long (Int64.repr ni) tlong)))
                      acc
       | None => acc
       end) tbl acc)
    E0 le m (Out_return (Some (Vlong (Int64.repr next_idx), tlong))).
Proof.
  induction tbl; intros; simpl in *. contradiction.
  inversion H3; subst; clear H3.
  destruct H1; subst.
  - (* head is the matching entry: si = s_idx, sy = sym *)
    rewrite H0. apply fold_left_preserves_head.
    + econstructor.
        eauto using eval_eq_test_true.
        apply bool_val_one.
        simpl. econstructor. econstructor.
    + intros. destruct b as (si & sy), (sidx (transition state dfa q sy)) eqn:E; auto.
      econstructor.
        eapply eval_eq_test_false; eauto.
          intro. subst. apply H6. simpl.
          change si with (fst (si, sy)).
          now apply in_map.
        apply bool_val_zero.
        assumption.
  - (* the match is later in the table *)
    destruct a as (si & sy), (sidx (dfa.(transition _) q sy)) eqn:E;
      eapply IHtbl; eauto; intros; eapply H2; right; eassumption.
Qed.

(** The state branch tree *)

Lemma delta_tree_exec : forall ids e le m tbl acc q sym q_idx s_idx next_idx,
  le ! (ids.(id_q)) = Some (Vlong (Int64.repr q_idx)) ->
  le ! (ids.(id_s)) = Some (Vlong (Int64.repr s_idx)) ->
  sidx q = Some q_idx ->
  symidx sym = Some s_idx ->
  sidx (dfa.(transition _) q sym) = Some next_idx ->
  In (q_idx, q) tbl ->
  (forall i x, In (i, x) tbl -> 0 <= i < Int64.modulus) ->
  list_norepet (map fst tbl) ->
  exec_stmt function_entry2 ge e le m
    (fold_left (fun (acc : statement) '(qi, qq) =>
       Sifthenelse (eq_test ids.(id_q) qi) (sym_branch state dfa ids state_eq_dec qi qq) acc)
       tbl acc)
    E0 le m (Out_return (Some (Vlong (Int64.repr next_idx), tlong))).
Proof.
  induction tbl; intros; simpl in *. contradiction.
  inversion H6; subst; clear H6. destruct H4; subst.
  - apply fold_left_preserves_head.
      econstructor.
        eapply eval_eq_test_true; eauto.
        apply bool_val_one.
        simpl. unfold sym_branch.
        eapply sym_branch_exec; eauto.
          eapply enumerate_spec; eauto.
          intros. pose proof (enumerate_In_bounds _ _ _ _ H4). lia.
          apply enumerate_index_norepet.
        intros. destruct b as (qi & qq). econstructor.
          eapply eval_eq_test_false; eauto.
            intro. subst. apply H9. simpl.
            change qi with (fst (qi, qq)). now apply in_map.
          apply bool_val_zero.
        assumption.
  - eapply IHtbl; eauto.
Qed.

Lemma alloc_idents_norepet : forall base,
  Coqlib.list_norepet [(alloc_idents base).(id_q); (alloc_idents base).(id_s)].
Proof.
  intros. cbv [id_q alloc_idents id_s].
  repeat constructor. intros [H|[]]. lia. now intro.
Qed.

(** delta is correct on valid indices *)

Lemma compile_delta_correct :
  forall base q sym q_idx s_idx next_idx m,
    sidx q = Some q_idx ->
    symidx sym = Some s_idx ->
    sidx (dfa.(transition _) q sym) = Some next_idx ->
    eval_funcall function_entry2 ge m
      (compile_delta state dfa state_eq_dec (alloc_idents base))
      [Vlong (Int64.repr q_idx); Vlong (Int64.repr s_idx)] E0 m
      (Vlong (Int64.repr next_idx)).
Proof.
  intros. unfold compile_delta.
  econstructor.
  - econstructor; cbn - [Pos.succ Pos.add]; try solve [constructor].
      apply alloc_idents_norepet.
      now repeat intro.
  - cbn [fn_body].
    eapply delta_tree_exec with (q := q) (sym := sym); eauto.
    + cbn - [Pos.succ Pos.add].
      rewrite PTree.gso by (unfold alloc_idents; cbn - [Pos.succ Pos.add]; lia).
      rewrite PTree.gss. reflexivity.
    + cbn - [Pos.succ]. rewrite PTree.gss. reflexivity.
    + eauto using enumerate_spec.
    + intros.
      pose proof (enumerate_In_bounds _ _ _ _ H2). lia.
    + apply enumerate_index_norepet.
  - cbn. split. discriminate.
    unfold tlong, sem_cast, classify_cast.
    now destruct Archi.ptr64; simpl.
  - reflexivity.
Qed.

(** accept is correct on valid indices *)

Lemma accept_tree_exec : forall ids e le m tbl acc q q_idx,
  le ! (ids.(id_q)) = Some (Vlong (Int64.repr q_idx)) ->
  sidx q = Some q_idx ->
  In (q_idx, q) tbl ->
  (forall i x, In (i, x) tbl -> 0 <= i < Int64.modulus) ->
  list_norepet (map fst tbl) ->
  exec_stmt function_entry2 ge e le m acc E0 le m
    (Out_return (Some (Vint Int.zero, tbool))) ->
  exec_stmt function_entry2 ge e le m
    (fold_left (fun (acc : statement) '(qi, qq) =>
       if dfa.(accept _) qq
       then Sifthenelse (eq_test ids.(id_q) qi)
              (Sreturn (Some (Econst_int Int.one tbool))) acc
       else acc) tbl acc)
    E0 le m (Out_return (Some (Vint (if dfa.(accept _) q then Int.one else Int.zero), tbool))).
Proof.
  induction tbl; intros; simpl in *. contradiction.
  inversion H3; subst; clear H3.
  destruct H1; subst.
  - apply fold_left_preserves_head.
    destruct accept.
      econstructor.
        eapply eval_eq_test_true; eauto.
        apply bool_val_one.
        simpl. econstructor. econstructor.
      assumption.
    intros. destruct b, accept in |- *; [|assumption].
    econstructor.
      eapply eval_eq_test_false; eauto.
      intro. subst. apply H7. simpl.
        change z with (fst (z, s)). now apply in_map.
        apply bool_val_zero.
        assumption.
  - destruct a as (qi & qq). assert (Hne : qi <> q_idx).
      { intro. subst. apply H7. simpl.
        change q_idx with (fst (q_idx, q)).
        now apply in_map. }
    destruct accept in |- *.
      eapply IHtbl; eauto.
        econstructor.
          eapply eval_eq_test_false; eauto.
          apply bool_val_zero.
          assumption.
    eapply IHtbl; eauto.
Qed.

Lemma compile_accept_correct :
  forall base q q_idx m,
    sidx q = Some q_idx ->
    eval_funcall function_entry2 ge m
      (compile_accept state dfa (alloc_idents base))
      [Vlong (Int64.repr q_idx)] E0 m
      (Vint (if dfa.(accept _) q then Int.one else Int.zero)).
Proof.
  intros. unfold compile_accept.
  econstructor.
  - econstructor; cbn - [Pos.succ Pos.add]; try solve [constructor].
      constructor. now intro. constructor.
      now repeat intro.
  - cbn [fn_body].
    eapply accept_tree_exec; eauto.
    + cbn. now rewrite PTree.gss.
    + eauto using enumerate_spec.
    + intros. pose proof (enumerate_In_bounds _ _ _ _ H0). lia.
    + apply enumerate_index_norepet.
    + eapply exec_Sreturn_some. econstructor.
  - cbn. split. discriminate.
    destruct accept eqn:E. now rewrite Int.eq_false.
    now rewrite Int.eq_true.
  - reflexivity.
Qed.

(** delta returns the sink on out-of-range indices *)

Lemma compile_delta_sink :
  forall base q_idx s_idx m,
    0 <= q_idx < Int64.modulus ->
    q_idx >= Z.of_nat (length dfa.(states _)) ->
    eval_funcall function_entry2 ge m
      (compile_delta state dfa state_eq_dec (alloc_idents base))
      [Vlong (Int64.repr q_idx); Vlong (Int64.repr s_idx)] E0 m
      (Vlong (Int64.repr (sink_index state dfa))).
Proof.
  intros. unfold compile_delta.
  econstructor.
  - econstructor; cbn - [Pos.succ Pos.add]; try solve [constructor].
      apply alloc_idents_norepet.
      now repeat intro.
  - cbn [fn_body]. apply fold_left_preserves_head.
      econstructor. econstructor.
    intros. destruct b as (qi & qq). econstructor.
      eapply eval_eq_test_false; eauto.
        cbn - [Pos.succ Pos.add]. rewrite PTree.gso by lia.
          now rewrite PTree.gss.
        pose proof (enumerate_In_bounds _ _ _ _ H1). lia.
        intro. subst.
          pose proof (enumerate_In_bounds _ _ _ _ H1). lia.
      apply bool_val_zero.
      assumption.
  - cbn. split. discriminate.
    unfold sem_cast, tlong, classify_cast. now destruct Archi.ptr64.
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

Lemma delta_step_correct :
  forall base w a q_idx a_idx m,
    sidx (DFA.run dfa w) = Some q_idx ->
    symidx a = Some a_idx ->
    exists r_idx,
      sidx (DFA.run dfa (w ++ [a])) = Some r_idx /\
      eval_funcall function_entry2 ge m
        (compile_delta state dfa state_eq_dec (alloc_idents base))
        [Vlong (Int64.repr q_idx); Vlong (Int64.repr a_idx)] E0 m
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

End correctness.
End Correctness.
