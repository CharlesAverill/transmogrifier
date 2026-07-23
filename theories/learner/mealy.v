From lstar Require Import automata.Mealy Teacher.
From Transmogrifier Require Import compiler.mealy transparency.mealyproofs.
From compcert Require Import AST Clight Ctypes Integers Values Coqlib.
From compcert Require Import ClightBigstep Events Globalenvs Memory.
From Stdlib Require Import List ZArith Lia.
Import ListNotations.

Module Type MealyLearner (s : Symbol) (O : Output) (L : MealyLanguage s O) (Tch : MealyTeacher s O L).
    Parameter learn : unit -> {state : Type & {m : L.M.t state | L.minimal m}}.
End MealyLearner.

Module CompileLearnedMealy (s : Symbol) (O : Output) (L : MealyLanguage s O)
                           (Tch : MealyTeacher s O L)
                           (Learner : MealyLearner s O L Tch).

Module M <: MealyType s O := L.M.

Module Correctness := Correctness s O M.
Import Correctness L M MC.

Definition learned : { St : Type & { m : M.t St | minimal m } } :=
    Learner.learn tt.

Definition LSt : Type := projT1 learned.
Definition learned_mealy : L.M.t LSt := proj1_sig (projT2 learned).

Definition base : positive := 1.

Section correctness.
Variable p : Clight.program.
Variable m0 : mem.
Definition ge := ge p.

(* The learned Mealy machine has compiled successfully and is well-formed. *)
Variable state_eq_dec : forall (x y : LSt), {x = y} + {x <> y}.
Variable compile_ok :
    compile_program LSt learned_mealy state_eq_dec base = Ok p.
Variable m0_ok :
    Genv.init_mem p = Some m0.
Variable states_ok :
    Z.of_nat (Datatypes.length (M.states LSt learned_mealy)) < Int64.modulus.
Variable alphabet_ok :
    0 < Z.of_nat (Datatypes.length s.enum) < Int64.modulus.
Variable output_alphabet_ok :
    0 < Z.of_nat (length O.enum) < Int64.modulus.
Variable states_alphabet_ok :
    8 * (Z.of_nat (Datatypes.length (M.states LSt learned_mealy)) *
         Z.of_nat (Datatypes.length s.enum)) < Ptrofs.modulus.

(* Every symbol of the input has an index -- [s.enum] is exhaustive. *)
Lemma sym_indices_total : forall w, exists l, sym_indices w l.
Proof.
  induction w as [| a w IH].
  - exists []. constructor.
  - destruct IH as (l & Hl).
    destruct (symidx_total a) as (i & Hi).
    exists (i :: l). now constructor.
Qed.

(* Every output the run emits has an index -- [O.enum] is exhaustive. *)
Lemma out_indices_total : forall w,
  exists lo, Forall2 (fun o i => oidx o = Some i)
                     (run_outputs learned_mealy w) lo.
Proof.
  intros w. induction (run_outputs learned_mealy w) as [| o os IH].
  - now exists [].
  - destruct IH as (lo & Hlo).
    destruct (oidx_total o) as (i & Hi).
    exists (i :: lo). now constructor.
Qed.

(* Running the compiled machine on a word leaves, in the caller's [out]
   buffer, the O.enum indices of the machine's output string -- and touches
   nothing else. This is the Mealy analogue of Moore's [run_equiv]: the payload
   is the whole emitted string, not a single terminal state. *)
Theorem run_equiv : forall w l lo b_w ofs_w b_out ofs_out b_t b_ot m,
  sym_indices w l ->
  Forall2 (fun o i => oidx o = Some i)
          (run_outputs learned_mealy w) lo ->
  word_in_mem m b_w ofs_w l ->
  Genv.find_symbol ge (id_table (alloc_idents base)) = Some b_t ->
  Genv.find_symbol ge (id_otable (alloc_idents base)) = Some b_ot ->
  (forall k v, nth_error (table_init LSt learned_mealy state_eq_dec) (Z.to_nat k)
       = Some (Init_int64 v) ->
     0 <= k < nstates LSt learned_mealy * nsyms ->
     Mem.loadv Mint64 m (Vptr b_t (Ptrofs.repr (8 * k))) = Some (Vlong v)) ->
  (forall k v, nth_error (otable_init LSt learned_mealy) (Z.to_nat k)
       = Some (Init_int64 v) ->
     0 <= k < nstates LSt learned_mealy * nsyms ->
     Mem.loadv Mint64 m (Vptr b_ot (Ptrofs.repr (8 * k))) = Some (Vlong v)) ->
  b_w <> b_t -> b_w <> b_ot -> b_out <> b_t -> b_out <> b_ot ->
  Mem.valid_block m b_w -> Mem.valid_block m b_out ->
  Mem.valid_block m b_t -> Mem.valid_block m b_ot ->
  Mem.range_perm m b_out ofs_out
    (ofs_out + 8 * Z.of_nat (length w)) Cur Writable ->
  (align_chunk Mint64 | ofs_out) ->
  0 <= ofs_w -> 0 <= ofs_out -> b_w <> b_out ->
  Z.of_nat (length w) < Int64.modulus ->
  ofs_w + 8 * Z.of_nat (length w) < Ptrofs.modulus ->
  ofs_out + 8 * Z.of_nat (length w) < Ptrofs.modulus ->
  exists m',
    eval_funcall function_entry2 ge m
      (compile_run LSt learned_mealy state_eq_dec (alloc_idents base))
      [Vptr b_w (Ptrofs.repr ofs_w); Vlong (Int64.repr (Z.of_nat (length w)));
       Vptr b_out (Ptrofs.repr ofs_out)] E0 m' Vundef /\
    buf_in_mem m' b_out ofs_out lo /\
    Mem.unchanged_on (fun b _ => b <> b_out) m m'.
Proof.
  intros. eauto using compile_run_correct.
Qed.

Lemma last_cons : forall (A : Type) (x : A) l d,
  last (x :: l) d = last l x.
Proof.
  induction l; intros.
    reflexivity.
  simpl in *. destruct l.
    reflexivity.
  apply IHl.
Qed.

Lemma outputs_nonnil : forall (q : LSt) a w,
  outputs learned_mealy q (a :: w) <> [].
Proof. intros q a w. cbn [outputs]. discriminate. Qed.

Lemma last_of_outputs : forall w (q : LSt) a d,
  last (outputs learned_mealy q (a :: w)) d
  = M.last_output_from learned_mealy q a w.
Proof.
  induction w as [| b w IH]; intros q a d.
  - reflexivity.
  - cbn [outputs M.last_output_from].
    rewrite last_cons. apply IH.
Qed.

Lemma nth_error_last : forall (A : Type) (l : list A) (d : A),
  l <> [] -> nth_error l (length l - 1) = Some (last l d).
Proof.
  induction l as [| x l IH]; intros d Hne; [contradiction |].
  destruct l as [| y l'].
  - reflexivity.
  - specialize (IH d ltac:(discriminate)).
    cbn [length last nth_error] in *. simpl. rewrite <- IH.
    replace (S (length l') - 1)%nat with (length l'). reflexivity.
    lia.
Qed.

(* Forall2 relates elements at equal positions. *)
Lemma forall2_nth_error_l : forall (A B : Type) (R : A -> B -> Prop) la lb n x,
  Forall2 R la lb -> nth_error la n = Some x ->
  exists y, nth_error lb n = Some y /\ R x y.
Proof.
  intros A B R la lb n x HF. revert n x.
  induction HF as [| a b la lb Hab HF IH]; intros n x Hn.
  - destruct n; discriminate.
  - destruct n; cbn in Hn.
    + inversion Hn; subst. exists b. split; [reflexivity | assumption].
    + apply IH. exact Hn.
Qed.

(* Run the compiled machine on [a :: w]; the buffer's final cell is
   the O.enum index of the target language's output on that last edge. *)
Theorem run_output_encodes : forall a w l lo b_w ofs_w b_out ofs_out b_t b_ot m,
  sym_indices (a :: w) l ->
  Forall2 (fun o i => oidx o = Some i)
          (run_outputs learned_mealy (a :: w)) lo ->
  word_in_mem m b_w ofs_w l ->
  Genv.find_symbol ge (id_table (alloc_idents base)) = Some b_t ->
  Genv.find_symbol ge (id_otable (alloc_idents base)) = Some b_ot ->
  (forall k v, nth_error (table_init LSt learned_mealy state_eq_dec) (Z.to_nat k)
       = Some (Init_int64 v) ->
     0 <= k < nstates LSt learned_mealy * nsyms ->
     Mem.loadv Mint64 m (Vptr b_t (Ptrofs.repr (8 * k))) = Some (Vlong v)) ->
  (forall k v, nth_error (otable_init LSt learned_mealy) (Z.to_nat k)
       = Some (Init_int64 v) ->
     0 <= k < nstates LSt learned_mealy * nsyms ->
     Mem.loadv Mint64 m (Vptr b_ot (Ptrofs.repr (8 * k))) = Some (Vlong v)) ->
  b_w <> b_t -> b_w <> b_ot -> b_out <> b_t -> b_out <> b_ot ->
  Mem.valid_block m b_w -> Mem.valid_block m b_out ->
  Mem.valid_block m b_t -> Mem.valid_block m b_ot ->
  Mem.range_perm m b_out ofs_out
    (ofs_out + 8 * Z.of_nat (length (a :: w))) Cur Writable ->
  (align_chunk Mint64 | ofs_out) ->
  0 <= ofs_w -> 0 <= ofs_out -> b_w <> b_out ->
  Z.of_nat (length (a :: w)) < Int64.modulus ->
  ofs_w + 8 * Z.of_nat (length (a :: w)) < Ptrofs.modulus ->
  ofs_out + 8 * Z.of_nat (length (a :: w)) < Ptrofs.modulus ->
  exists m' o_idx,
    (* the compiled run leaves the output indices in [out] and touches only [out] *)
    eval_funcall function_entry2 ge m
      (compile_run LSt learned_mealy state_eq_dec (alloc_idents base))
      [Vptr b_w (Ptrofs.repr ofs_w); Vlong (Int64.repr (Z.of_nat (length (a :: w))));
       Vptr b_out (Ptrofs.repr ofs_out)] E0 m' Vundef /\
    Mem.unchanged_on (fun b _ => b <> b_out) m m' /\
    (* the final cell holds the O.enum index of the LANGUAGE's output on that edge *)
    Mem.loadv Mint64 m' (Vptr b_out (Ptrofs.repr (ofs_out + 8 * Z.of_nat (length w))))
      = Some (Vlong (Int64.repr o_idx)) /\
    nth_error O.enum (Z.to_nat o_idx) = Some (tgt_last output_lang [] a w).
Proof.
  intros a w l lo b_w ofs_w b_out ofs_out b_t b_ot m
    Hsym Hout Hword Hbt Hbot Htload Hotload
    Hbwt Hbwot Hboutt Hboutot Hvw Hvout Hvt Hvot
    Hperm Halign Hofsw Hofsout Hbwo Hlenmod Hwmod Houtmod.

  assert (Henc : encodes learned_mealy)
    by (destruct (proj2_sig (projT2 learned)) as [He _]; exact He).

  edestruct run_equiv
    as (m' & Hexec & Hbuf & Hunch); [ eassumption .. |].

  (* the machine's last-emitted output on [a :: w] *)
  set (olast := M.last_output_from learned_mealy (M.initial LSt learned_mealy) a w) in *.
  destruct (oidx_total olast) as (o_idx & Hoidx).
  exists m', o_idx.

  (* [lo]'s final cell (index |w|) is [o_idx]. run_outputs (a::w) has length
     |a::w| = S|w|, and its last element is [olast]. *)
  assert (Hrolen : length (run_outputs learned_mealy (a :: w)) = S (length w))
    by (rewrite run_outputs_length; reflexivity).
  assert (Hlolen : length lo = S (length w))
    by (apply Forall2_length in Hout; rewrite Hrolen in Hout; lia).
  assert (Hro_ne : run_outputs learned_mealy (a :: w) <> [])
    by (intro Hc; rewrite Hc in Hrolen; cbn in Hrolen; lia).
 
  assert (Hlolast : nth_error lo (length w) = Some o_idx).
  { (* the last elements of [run_outputs (a::w)] and [lo] correspond under oidx *)
    assert (Hlast_ro : last (run_outputs learned_mealy (a :: w))
                            (learned_mealy.(output _) (M.initial _ learned_mealy) a)
                       = olast).
    { unfold run_outputs, olast. apply last_of_outputs. }
    (* [run_outputs (a::w) = outputs init (a::w)], so [last_of_outputs] applies *)
    (* pull the final pair out of Hout via nth_error at index |w| *)
    pose proof (nth_error_last _ (run_outputs learned_mealy (a :: w))
                  (learned_mealy.(output _) (M.initial _ learned_mealy) a)
                  Hro_ne) as Hnro.
    replace (length (run_outputs learned_mealy (a :: w)) - 1)%nat
       with (length w) in Hnro by (rewrite Hrolen; lia).
    rewrite Hlast_ro in Hnro.
    (* Forall2 preserves nth_error: olast at |w| maps to lo's |w| *)
    destruct (forall2_nth_error_l _ _ _ _ _ _ _ Hout Hnro) as (j & Hj & Hoj).
    rewrite Hj. unfold olast in Hoj, Hoidx. rewrite Hoidx in Hoj. now inversion Hoj. }
 
  split; [exact Hexec | split; [exact Hunch | split]].
  - unfold buf_in_mem in Hbuf. specialize (Hbuf (length w) o_idx Hlolast).
    now rewrite Z.mul_comm with (n := 8) in Hbuf |- *.
  - unfold oidx in Hoidx.
    pose proof (index_of_nth_error _ O.eq_dec O.enum olast o_idx 0 Hoidx) as Hnth.
    rewrite Z.sub_0_r in Hnth. rewrite Hnth. f_equal.
    (* olast = last_output m a w = tgt_last output_lang [] a w, directly by encodes *)
    unfold olast. change (M.last_output_from learned_mealy
        (M.initial LSt learned_mealy) a w)
      with (M.last_output learned_mealy a w).
    apply Henc.
Qed.

End correctness.
End CompileLearnedMealy.
