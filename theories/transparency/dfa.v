From lstar Require Import Automata.
From compcert Require Import AST Clight Ctypes Integers Cop Maps ClightBigstep Values Events Coqlib.
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

(** Index lemmas

    [index_of] carries an accumulator, so every lemma about it is stated with
    the accumulator generalized and proved by induction on the list. *)

Section index.
Variable X : Type.
Variable eq_dec : forall x y : X, {x = y} + {x <> y}.

Lemma index_of_ge : forall l x i k,
  index_of eq_dec x l k = Some i -> k <= i.
Proof.
  induction l as [| h t IH]; intros x i k H; cbn in H.
  - discriminate.
  - destruct (eq_dec x h).
    + injection H as <-. lia.
    + apply IH in H. lia.
Qed.

Lemma index_of_lt : forall l x i k,
  index_of eq_dec x l k = Some i -> i < k + Z.of_nat (length l).
Proof.
  induction l as [| h t IH]; intros x i k H; cbn in H.
  - discriminate.
  - destruct (eq_dec x h).
    + injection H as <-. cbn. lia.
    + apply IH in H. cbn. lia.
Qed.

Lemma index_of_bounds : forall l x i,
  index_of eq_dec x l 0 = Some i -> 0 <= i < Z.of_nat (length l).
Proof.
  intros l x i H. split.
  - eapply index_of_ge; eauto.
  - apply index_of_lt in H. lia.
Qed.

(** Injectivity: an index determines the element. *)
Lemma index_of_inj : forall l x y i k,
  index_of eq_dec x l k = Some i ->
  index_of eq_dec y l k = Some i ->
  x = y.
Proof.
  induction l as [| h t IH]; intros x y i k Hx Hy; cbn in Hx, Hy.
  - discriminate.
  - destruct (eq_dec x h) as [->|Hxh]; destruct (eq_dec y h) as [->|Hyh].
    + reflexivity.
    + injection Hx as <-. apply index_of_ge in Hy. lia.
    + injection Hy as <-. apply index_of_ge in Hx. lia.
    + eapply IH; eauto.
Qed.

(** Functionality: an element determines its index. *)
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
  induction la as [| a la IH]; intros lb n.
  - cbn. destruct n; reflexivity.
  - destruct lb as [| b lb]; cbn.
    + destruct n; cbn; [reflexivity | destruct (nth_error la n); reflexivity].
    + destruct n; cbn.
      * reflexivity.
      * apply IH.
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
  induction l as [| h t IH]; intros x i k H; cbn in H.
  - discriminate.
  - destruct (eq_dec x h) as [->|Hne].
    + injection H as <-. rewrite Z.sub_diag. reflexivity.
    + pose proof (index_of_ge _ _ _ _ H).
      apply IH in H.
      replace (Z.to_nat (i - k)) with (S (Z.to_nat (i - Z.succ k))) by lia.
      simpl. apply H.
Qed.

Lemma enumerate_spec : forall (l : list X) x i,
  index_of eq_dec x l 0 = Some i -> In (i, x) (enumerate l).
Proof.
  intros l x i H.
  apply enumerate_nth.
  - eapply index_of_bounds; eauto.
  - apply index_of_nth_error in H.
    rewrite Z.sub_0_r in H.
    exact H.
Qed.

Lemma enumerate_In_bounds : forall (l : list X) i x,
  In (i, x) (enumerate l) -> 0 <= i < Z.of_nat (length l).
Proof.
    intros. unfold enumerate in H. apply in_combine_l, in_map_iff in H.
    destruct H as (x' & Eq & HIn). apply in_seq in HIn. lia.
Qed.

Lemma map_fst_combine : forall (A B : Type) (la : list A) (lb : list B),
  length la = length lb ->
  map fst (combine la lb) = la.
Proof.
  induction la as [| a la IH]; intros lb Hlen.
  - reflexivity.
  - destruct lb as [| b lb]; cbn in Hlen.
    + discriminate.
    + cbn. f_equal. apply IH. injection Hlen as ->. reflexivity.
Qed.

Lemma list_seq_norepet : forall y x,
  list_norepet (seq x y).
Proof.
  induction y as [| y IH]; intros x.
  - constructor.
  - cbn. constructor.
    + rewrite in_seq. lia.
    + apply IH.
Qed.

Lemma enumerate_index_norepet : forall (l : list X),
  list_norepet (map fst (enumerate l)).
Proof.
  intros l.
  unfold enumerate.
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

(** Well-formedness: the state and symbol enumerations fit in [tuint] *)
Variable states_bounded : Z.of_nat (length dfa.(states _)) < Int.modulus.
Variable syms_bounded   : Z.of_nat (length s.enum) < Int.modulus.

Variable ge : genv.

Definition sidx (q : state) : option Z :=
  index_of state_eq_dec q dfa.(states _) 0.

Definition symidx (a : s.t) : option Z :=
  index_of s.eq_dec a s.enum 0.

(** Guard evaluation

    [eq_test v k] evaluates to [Vint Int.one] exactly when the temp [v] holds
    [Vint (Int.repr k)], given that both indices are in range. *)

Lemma repr_inj_in_range : forall a b,
  0 <= a < Int.modulus -> 0 <= b < Int.modulus ->
  Int.repr a = Int.repr b -> a = b.
Proof.
  intros a b Ha Hb H.
  rewrite <- (Int.unsigned_repr a) by (unfold Int.max_unsigned; lia).
  rewrite <- (Int.unsigned_repr b) by (unfold Int.max_unsigned; lia).
  rewrite H. reflexivity.
Qed.

Lemma eval_eq_test_true : forall e le m v k,
  le ! v = Some (Vint (Int.repr k)) ->
  eval_expr ge e le m (eq_test v k) (Vint Int.one).
Proof.
  intros e le m v k Hle.
  unfold eq_test.
  econstructor.
  - econstructor. exact Hle.
  - econstructor.
  - cbn.
    destruct Archi.ptr64 eqn:Hp; cbn;
      unfold sem_binarith, sem_cast, classify_cast, classify_binarith; cbn;
      rewrite Hp; cbn;
      unfold Val.of_bool; rewrite Int.eq_true; reflexivity.
Qed.

Lemma eval_eq_test_false : forall e le m v k j,
  le ! v = Some (Vint (Int.repr j)) ->
  0 <= j < Int.modulus -> 0 <= k < Int.modulus ->
  j <> k ->
  eval_expr ge e le m (eq_test v k) (Vint Int.zero).
Proof.
  intros e le m v k j Hle Hj Hk Hne.
  unfold eq_test.
  econstructor.
  - econstructor. exact Hle.
  - econstructor.
  - cbn. unfold sem_binarith, classify_binarith, tuint. cbn.
    unfold sem_cast, classify_cast. now destruct Archi.ptr64; cbn;
    rewrite Int.eq_false by (intro H; apply Hne; eapply repr_inj_in_range; eauto).
Qed.

(** Boolean projection of the guard value at [tuint]. *)
Lemma bool_val_one : forall m, bool_val (Vint Int.one) tuint m = Some true.
Proof.
  intros m. unfold bool_val, tuint. cbn.
  destruct Archi.ptr64; cbn; rewrite Int.eq_false by apply Int.one_not_zero; reflexivity.
Qed.

Lemma bool_val_zero : forall m, bool_val (Vint Int.zero) tuint m = Some false.
Proof.
  intros m. unfold bool_val, tuint. cbn.
  destruct Archi.ptr64; cbn; rewrite Int.eq_true; reflexivity.
Qed.

(** The symbol branch tree

    [sym_branch q_idx q] is a fold over [sym_table] wrapping the sink default.
    We prove it executes to [next_idx] when [sym] is at index [s_idx] and the
    temp [id_s] holds that index.  The accumulator is generalized. *)

Lemma fold_left_preserves_head : forall (A B : Type) (f : A -> B -> A) (P : A -> Prop) (l : list B) (a : A),
  P a ->
  (forall x b, In b l -> P x -> P (f x b)) ->
  P (fold_left f l a).
Proof.
  intros A B f P l.
  induction l as [| b t IH]; intros a Ha Hstep.
  - exact Ha.
  - cbn. apply IH.
    + apply Hstep. left. reflexivity. exact Ha.
    + intros x b' Hin Hx. apply Hstep. right. exact Hin. exact Hx.
Qed.

Lemma sym_branch_exec : forall ids e le m tbl acc q sym s_idx next_idx,
  le ! (ids.(id_s)) = Some (Vint (Int.repr s_idx)) ->
  sidx (dfa.(transition _) q sym) = Some next_idx ->
  In (s_idx, sym) tbl ->
  (forall i a, In (i, a) tbl -> 0 <= i < Int.modulus) ->
  list_norepet (map fst tbl) ->
  exec_stmt function_entry2 ge e le m
    (fold_left (fun (acc : statement) '(si, sy) =>
       match sidx (dfa.(transition _) q sy) with
       | Some ni => Sifthenelse (eq_test ids.(id_s) si)
                      (Sreturn (Some (Econst_int (Int.repr ni) tuint)))
                      acc
       | None => acc
       end) tbl acc)
    E0 le m (Out_return (Some (Vint (Int.repr next_idx), tuint))).
Proof.
  intros ids e le m tbl.
  induction tbl as [| [si sy] t IH]; intros acc q sym s_idx next_idx Hle Hnext Hin Hbnd Hnr.
  - contradiction.
  - cbn [fold_left].
    cbn [map fst] in Hnr. inversion Hnr as [| ? ? Hnotin Hnr']; subst.
    destruct Hin as [Heq | Hin].
    + (* head is the matching entry: si = s_idx, sy = sym *)
      inversion Heq. subst si sy.
      rewrite Hnext.
      apply fold_left_preserves_head with (P := fun st =>
        exec_stmt function_entry2 ge e le m st E0 le m
          (Out_return (Some (Vint (Int.repr next_idx), tuint)))).
      * (* the head branch executes to next_idx *)
        eapply exec_Sifthenelse.
        -- eapply eval_eq_test_true; exact Hle.
        -- apply bool_val_one.
        -- cbn. eapply exec_Sreturn_some. econstructor.
      * (* later entries guard on a different index and fall through *)
        intros st [si' sy'] Hin' Hst.
        destruct (sidx (dfa.(transition _) q sy')) as [ni'|] eqn:Hni'; [| exact Hst].
        eapply exec_Sifthenelse.
        -- eapply eval_eq_test_false with (j := s_idx).
           ++ exact Hle.
           ++ eapply Hbnd. left. reflexivity.
           ++ eapply Hbnd. right. exact Hin'.
           ++ intro Hcontra. subst si'.
              apply Hnotin.
              change s_idx with (fst (s_idx, sy')).
              apply in_map. exact Hin'.
        -- apply bool_val_zero.
        -- cbn. exact Hst.
    + (* the match is later in the table *)
      destruct (sidx (dfa.(transition _) q sy)) as [ni|] eqn:Hni.
      * eapply IH; eauto.
        intros i a Hia. eapply Hbnd. right. exact Hia.
      * eapply IH; eauto.
        intros i a Hia. eapply Hbnd. right. exact Hia.
Qed.

(** The state branch tree *)

Lemma delta_tree_exec : forall ids e le m tbl acc q sym q_idx s_idx next_idx,
  le ! (ids.(id_q)) = Some (Vint (Int.repr q_idx)) ->
  le ! (ids.(id_s)) = Some (Vint (Int.repr s_idx)) ->
  sidx q = Some q_idx ->
  symidx sym = Some s_idx ->
  sidx (dfa.(transition _) q sym) = Some next_idx ->
  In (q_idx, q) tbl ->
  (forall i x, In (i, x) tbl -> 0 <= i < Int.modulus) ->
  list_norepet (map fst tbl) ->
  exec_stmt function_entry2 ge e le m
    (fold_left (fun (acc : statement) '(qi, qq) =>
       Sifthenelse (eq_test ids.(id_q) qi) (sym_branch state dfa ids state_eq_dec qi qq) acc)
       tbl acc)
    E0 le m (Out_return (Some (Vint (Int.repr next_idx), tuint))).
Proof.
  intros ids e le m tbl.
  induction tbl as [| [qi qq] t IH]; intros acc q sym q_idx s_idx next_idx Hq Hs Hsq Hss Hnext Hin Hbnd Hnr.
  - contradiction.
  - cbn [fold_left].
    cbn [map fst] in Hnr. inversion Hnr as [| ? ? Hnotin Hnr']; subst.
    destruct Hin as [Heq | Hin].
    + inversion Heq; subst; clear Heq.
      apply fold_left_preserves_head with (P := fun st =>
        exec_stmt function_entry2 ge e le m st E0 le m
          (Out_return (Some (Vint (Int.repr next_idx), tuint)))).
      * eapply exec_Sifthenelse.
        -- eapply eval_eq_test_true; exact Hq.
        -- apply bool_val_one.
        -- cbn. unfold sym_branch.
           eapply sym_branch_exec with (sym := sym); eauto.
           ++ eapply enumerate_spec; exact Hss.
           ++ intros i a Hia.
              pose proof (enumerate_In_bounds _ _ _ _ Hia).
              pose proof syms_bounded. lia.
           ++ apply enumerate_index_norepet.
      * intros st [qi' qq'] Hin' Hst.
        eapply exec_Sifthenelse.
        -- eapply eval_eq_test_false with (j := q_idx).
           ++ exact Hq.
           ++ eapply Hbnd. left. reflexivity.
           ++ eapply Hbnd. right. exact Hin'.
           ++ intro Hc. subst qi'.
              apply Hnotin.
              apply (in_map fst t (q_idx, qq')). exact Hin'.
        -- apply bool_val_zero.
        -- cbn. exact Hst.
    + eapply IH; eauto.
      intros i x Hix. eapply Hbnd. right. exact Hix.
Qed.

Lemma alloc_idents_norepet : forall base,
  Coqlib.list_norepet [(alloc_idents base).(id_q); (alloc_idents base).(id_s)].
Proof.
  intros. cbv [id_q alloc_idents id_s]. repeat constructor. intros [H|[]]. lia. now intro.
Qed.

(** delta is correct on valid indices *)

Lemma compile_delta_correct :
  forall base q sym q_idx s_idx next_idx m,
    sidx q = Some q_idx ->
    symidx sym = Some s_idx ->
    sidx (dfa.(transition _) q sym) = Some next_idx ->
    eval_funcall function_entry2 ge m
      (compile_delta state dfa (alloc_idents base) state_eq_dec)
      [Vint (Int.repr q_idx); Vint (Int.repr s_idx)] E0 m
      (Vint (Int.repr next_idx)).
Proof.
  intros base q sym q_idx s_idx next_idx m Hq Hs Hnext.
  unfold compile_delta.
  eapply eval_funcall_internal.
  - econstructor; cbn - [Pos.succ Pos.add]; try solve [constructor].
        apply alloc_idents_norepet.
        now repeat intro.
  - cbn [fn_body].
    eapply delta_tree_exec with (q := q) (sym := sym); eauto.
    + cbn - [Pos.succ Pos.add].
      rewrite PTree.gso by (unfold alloc_idents; cbn - [Pos.succ Pos.add]; lia).
      rewrite PTree.gss. reflexivity.
    + cbn - [Pos.succ]. rewrite PTree.gss. reflexivity.
    + eapply enumerate_spec; exact Hq.
    + intros i x Hix.
      pose proof (enumerate_In_bounds _ _ _ _ Hix).
      pose proof states_bounded. lia.
    + apply enumerate_index_norepet.
  - cbn. split. discriminate. unfold tuint, sem_cast, classify_cast. now destruct Archi.ptr64; simpl.
  - cbn. reflexivity.
Qed.

(** accept is correct on valid indices *)

Lemma accept_tree_exec : forall ids e le m tbl acc q q_idx,
  le ! (ids.(id_q)) = Some (Vint (Int.repr q_idx)) ->
  sidx q = Some q_idx ->
  In (q_idx, q) tbl ->
  (forall i x, In (i, x) tbl -> 0 <= i < Int.modulus) ->
  list_norepet (map fst tbl) ->
  exec_stmt function_entry2 ge e le m acc E0 le m
    (Out_return (Some (Vint Int.zero, tuint))) ->
  exec_stmt function_entry2 ge e le m
    (fold_left (fun (acc : statement) '(qi, qq) =>
       if dfa.(accept _) qq
       then Sifthenelse (eq_test ids.(id_q) qi)
              (Sreturn (Some (Econst_int Int.one tuint))) acc
       else acc) tbl acc)
    E0 le m (Out_return (Some (Vint (if dfa.(accept _) q then Int.one else Int.zero), tuint))).
Proof.
  intros ids e le m tbl.
  induction tbl as [| [qi qq] t IH]; intros acc q q_idx Hle Hsq Hin Hbnd Hnr Hacc.
  - contradiction.
  - cbn [fold_left].
    cbn [map fst] in Hnr. inversion Hnr as [| ? ? Hnotin Hnr']; subst.
    assert (Hlater : forall st, In (q_idx, q) t \/ True ->
      exec_stmt function_entry2 ge e le m st E0 le m
        (Out_return (Some (Vint (if dfa.(accept _) q then Int.one else Int.zero), tuint))) ->
      forall x b, In b t ->
      exec_stmt function_entry2 ge e le m x E0 le m
        (Out_return (Some (Vint (if dfa.(accept _) q then Int.one else Int.zero), tuint))) ->
      True) by (intros; exact I).
    clear Hlater.
    destruct Hin as [Heq | Hin].
    + inversion Heq; subst; clear Heq.
      apply fold_left_preserves_head with (P := fun st =>
        exec_stmt function_entry2 ge e le m st E0 le m
          (Out_return (Some (Vint (if dfa.(accept _) q then Int.one else Int.zero), tuint)))).
      * destruct (dfa.(accept _) q) eqn:Hq.
        -- eapply exec_Sifthenelse.
           ++ eapply eval_eq_test_true; exact Hle.
           ++ apply bool_val_one.
           ++ cbn. eapply exec_Sreturn_some. econstructor.
        -- exact Hacc.
      * intros st [qi' qq'] Hin' Hst.
        destruct (dfa.(accept _) qq'); [| exact Hst].
        eapply exec_Sifthenelse.
        -- eapply eval_eq_test_false with (j := q_idx).
           ++ exact Hle.
           ++ eapply Hbnd. left. reflexivity.
           ++ eapply Hbnd. right. exact Hin'.
           ++ intro Hc. subst qi'.
              apply Hnotin.
              apply (in_map fst t (q_idx, qq')). exact Hin'.
        -- apply bool_val_zero.
        -- cbn. exact Hst.
    + assert (Hne : qi <> q_idx).
      { intro Hc. subst qi. apply Hnotin.
        apply (in_map fst t (q_idx, q)). exact Hin. }
      destruct (dfa.(accept _) qq) eqn:Hqq.
      * eapply IH; eauto.
        -- intros i x Hix. eapply Hbnd. right. exact Hix.
        -- eapply exec_Sifthenelse.
           ++ eapply eval_eq_test_false with (j := q_idx).
              ** exact Hle.
              ** eapply Hbnd. right. exact Hin.
              ** eapply Hbnd. left. reflexivity.
              ** exact (fun Hc => Hne (eq_sym Hc)).
           ++ apply bool_val_zero.
           ++ cbn. exact Hacc.
      * eapply IH; eauto.
        intros i x Hix. eapply Hbnd. right. exact Hix.
Qed.

Lemma compile_accept_correct :
  forall base q q_idx m,
    sidx q = Some q_idx ->
    eval_funcall function_entry2 ge m
      (compile_accept state dfa (alloc_idents base))
      [Vint (Int.repr q_idx)] E0 m
      (Vint (if dfa.(accept _) q then Int.one else Int.zero)).
Proof.
  intros base q q_idx m Hq.
  unfold compile_accept.
  eapply eval_funcall_internal.
  - econstructor; cbn - [Pos.succ Pos.add]; try solve [constructor].
        constructor. now intro. constructor.
        now repeat intro.
  - cbn [fn_body].
    eapply accept_tree_exec with (q := q); eauto.
    + cbn. rewrite PTree.gss. reflexivity.
    + eapply enumerate_spec; exact Hq.
    + intros i x Hix.
      pose proof (enumerate_In_bounds _ _ _ _ Hix).
      pose proof states_bounded. lia.
    + apply enumerate_index_norepet.
    + eapply exec_Sreturn_some. econstructor.
  - cbn. split. discriminate. unfold sem_cast, tuint, classify_cast. now destruct Archi.ptr64; simpl.
  - cbn. reflexivity.
Qed.

(** delta returns the sink on out-of-range indices *)

Lemma compile_delta_sink :
  forall base q_idx s_idx m,
    0 <= q_idx < Int.modulus ->
    q_idx >= Z.of_nat (length dfa.(states _)) ->
    eval_funcall function_entry2 ge m
      (compile_delta state dfa (alloc_idents base) state_eq_dec)
      [Vint (Int.repr q_idx); Vint (Int.repr s_idx)] E0 m
      (Vint (Int.repr (sink_index state dfa))).
Proof.
  intros base q_idx s_idx m Hrange Hge.
  unfold compile_delta.
  eapply eval_funcall_internal.
  - econstructor; cbn - [Pos.succ Pos.add]; try solve [constructor].
        apply alloc_idents_norepet.
        now repeat intro.
  - cbn [fn_body].
    match goal with
    | [ |- exec_stmt _ _ ?E ?LE _ _ _ _ _ _ ] =>
      apply fold_left_preserves_head with (P := fun st =>
        exec_stmt function_entry2 ge E LE m st E0 LE m
          (Out_return (Some (Vint (Int.repr (sink_index state dfa)), tuint))))
    end.
    + eapply exec_Sreturn_some. econstructor.
    + intros st [qi qq] Hin Hst.
      eapply exec_Sifthenelse.
      * eapply eval_eq_test_false with (j := q_idx).
        -- cbn - [Pos.succ Pos.add]. rewrite PTree.gso by lia.
           rewrite PTree.gss. reflexivity.
        -- exact Hrange.
        -- pose proof (enumerate_In_bounds _ _ _ _ Hin).
           pose proof states_bounded. lia.
        -- intro Hc. subst qi.
           pose proof (enumerate_In_bounds _ _ _ _ Hin). lia.
      * apply bool_val_zero.
      * cbn. exact Hst.
  - cbn. split. discriminate. unfold sem_cast, tuint, classify_cast. now destruct Archi.ptr64.
  - cbn. reflexivity.
Qed.

Lemma index_of_complete : forall {A} (l : list A) x k eq_dec,
  In x l -> exists i, index_of eq_dec x l k = Some i.
Proof.
  induction l as [| h t IH]; intros x k eq_dec Hin.
  - contradiction.
  - cbn. destruct (eq_dec x h) as [->|Hne].
    + exists k. reflexivity.
    + destruct Hin as [Heq | Hin'].
      * congruence.
      * apply IH. exact Hin'.
Qed.

(** Top level *)

Lemma sidx_run : forall w, exists i, sidx (DFA.run dfa w) = Some i.
Proof.
  intros w. unfold sidx.
  apply index_of_complete.
  apply DFA.run_in_states.
Qed.

Lemma symidx_total : forall a, exists i, symidx a = Some i.
Proof.
  intros a. unfold symidx.
  apply index_of_complete.
  apply s.t_enumerable.
Qed.

Lemma run_snoc : forall w a,
  DFA.run dfa (w ++ [a]) = dfa.(transition _) (DFA.run dfa w) a.
Proof.
  intros w a. unfold DFA.run.
  rewrite fold_left_app. reflexivity.
Qed.

Lemma delta_step_correct :
  forall base w a q_idx a_idx m,
    sidx (DFA.run dfa w) = Some q_idx ->
    symidx a = Some a_idx ->
    exists r_idx,
      sidx (DFA.run dfa (w ++ [a])) = Some r_idx /\
      eval_funcall function_entry2 ge m
        (compile_delta state dfa (alloc_idents base) state_eq_dec)
        [Vint (Int.repr q_idx); Vint (Int.repr a_idx)] E0 m
        (Vint (Int.repr r_idx)).
Proof.
  intros base w a q_idx a_idx m Hq Ha.
  destruct (sidx_run (w ++ [a])) as [r_idx Hr].
  exists r_idx. split.
  - exact Hr.
  - eapply compile_delta_correct with (q := DFA.run dfa w) (sym := a); eauto.
    rewrite <- run_snoc. exact Hr.
Qed.

Lemma q0_index_correct :
  sidx dfa.(initial _) = Some (q0_index _ dfa state_eq_dec).
Proof.
  intros. unfold sidx, q0_index.
  destruct index_of eqn:E. reflexivity.
  exfalso.
  assert (Hin : In (initial state dfa) (states state dfa)).
  { pose proof (states_complete state dfa []) as H. exact H. }
  destruct (index_of_complete _ _ 0 state_eq_dec Hin) as [i Hi].
  congruence.
Qed.

End correctness.
End Correctness.
