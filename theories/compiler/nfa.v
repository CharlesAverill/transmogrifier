From lstar Require Import Automata.
From compcert Require Import AST Clight Ctypes Integers Cop Maps.
From Transmogrifier Require Import Monads.
From Stdlib Require Import String List ZArith.
Import ListNotations.
Open Scope result_scope.
Open Scope string_scope.
Open Scope Z_scope.

(** Compile an NFA into a Clight program.

    State variables are compiled as bitsets

    \Sigma : alphabet, indices 0..|\Sigma|-1
    Q      : state set, indices 0..|Q|-1; state [i] lives in bit [i mod 64] of
             word [i / 64]
    I      : the initial set, exported as a read-only bitmap global
    F      : the accepting set, exported as a read-only bitmap global; a run
             accepts iff its final set intersects it
    \delta : compiled to
                void step(unsigned long long *cur, unsigned long long s,
                          unsigned long long *next);
             where [cur] and [next] are [nwords]-word bitmaps *)

Module Type NFAType (s : Symbol).
  Record t (state : Type) : Type := {
        transition : state -> s.t -> list state;
        initial : list state;
        accept : state -> bool;
        states : list state;
        states_complete : forall w q,
            In q (fold_left (fun qs a => flat_map (fun q => transition q a) qs) w initial) ->
            In q states
    }.

  Definition step {state : Type} (trans : state -> s.t -> list state)
      (qs : list state) (a : s.t) : list state :=
      flat_map (fun q => trans q a) qs.

  Definition run {state : Type} (n : t state) (w : list s.t) : list state :=
      fold_left (step n.(transition state)) w n.(initial state).

  Parameter run_in_states : forall {state : Type} (n : t state) (w : list s.t) q,
      In q (run n w) -> In q (states state n).
End NFAType.

Module NFACompiler (s : Symbol) (NFA : NFAType s).

Import NFA.

(* Identifier allocation *)

Record idents : Type := {
  id_step   : ident;
  id_accept : ident;
  id_table  : ident;
  id_init   : ident;
  id_final  : ident;
  id_cur    : ident;
  id_next   : ident;
  id_s      : ident;
  id_q      : ident;
  id_k      : ident;
  id_j      : ident;
  id_word   : ident;
  id_w      : ident;
  id_len    : ident;
  id_i      : ident;
  id_acc    : ident;
  id_out    : ident;
  id_run    : ident;
  id_main   : ident
}.

Definition alloc_idents (base : ident) : idents := {|
  id_step   := base;
  id_accept := 1 + base;
  id_table  := 2 + base;
  id_init   := 3 + base;
  id_final  := 4 + base;
  id_cur    := 5 + base;
  id_next   := 6 + base;
  id_s      := 7 + base;
  id_q      := 8 + base;
  id_k      := 9 + base;
  id_j      := 10 + base;
  id_word   := 11 + base;
  id_w      := 12 + base;
  id_len    := 13 + base;
  id_i      := 14 + base;
  id_acc    := 15 + base;
  id_out    := 16 + base;
  id_run    := 17 + base;
  id_main   := 18 + base
|}%positive.

(* Types *)

Definition tlong : type := Tlong Unsigned noattr.
Definition tuint : type := Tint I32 Unsigned noattr.
Definition tint : type := Tint I32 Signed noattr.
Definition tvoid : type := Tvoid.
Definition tsetptr : type := Tpointer tlong noattr.
Definition tbool : type := Tint IBool Unsigned noattr.

Section compiler.
Variable state : Type.
Variable nfa : NFA.t state.
Variable state_eq_dec : forall x y : state, {x = y} + {x <> y}.

Fixpoint index_of {X : Type} (eq_dec : forall x y : X, {x = y} + {x <> y})
                  (target : X) (l : list X) (idx : Z) : option Z :=
  match l with
  | [] => None
  | h :: t => if eq_dec target h then Some idx else index_of eq_dec target t (Z.succ idx)
  end.

Definition enumerate {X : Type} (l : list X) : list (Z * X) :=
  combine (map Z.of_nat (seq 0 (length l))) l.

Definition state_table : list (Z * state) := enumerate nfa.(states _).
Definition sym_table   : list (Z * s.t)   := enumerate s.enum.

Definition nsyms : Z := Z.of_nat (length s.enum).
Definition nstates : Z := Z.of_nat (length nfa.(states _)).

(** Words per bitmap: [ceil(nstates / 64)] *)
Definition nwords : Z := Z.max 1 ((nstates + 63) / 64).

(* Bitmaps *)

Definition state_index (q : state) : option Z :=
  index_of state_eq_dec q nfa.(states _) 0.

(** Word [k] of the bitmap holding index set [idxs]. *)
Definition word_of_indices (idxs : list Z) (k : Z) : Z :=
  fold_left
    (fun acc i =>
       if andb (Z.leb (64 * k) i) (Z.ltb i (64 * (k + 1)))
       then Z.lor acc (Z.shiftl 1 (i - 64 * k))
       else acc)
    idxs 0.

(** The [nwords] init_data of the bitmap for [idxs], word 0 first. *)
Definition bitmap_init (idxs : list Z) : list init_data :=
  map (fun k => Init_int64 (Int64.repr (word_of_indices idxs k)))
      (map Z.of_nat (seq 0 (Z.to_nat nwords))).

(** Indices of a list of states, dropping any not in [states]. *)
Definition indices_of (qs : list state) : list Z :=
  fold_right (fun q acc =>
                match state_index q with
                | Some i => i :: acc
                | None => acc
                end) [] qs.

(* delta

   Row (q, a) is the [nwords]-word bitmap of [transition q a].
   Word [j] of row [(q, a)] sits at [(q * |Sigma| + a) * nwords + j]. *)

Definition table_row (q : state) (sym : s.t) : list init_data :=
  bitmap_init (indices_of (nfa.(transition _) q sym)).

Definition table_init : list init_data :=
  flat_map (fun '(_, q) =>
              flat_map (fun '(_, sym) => table_row q sym) sym_table)
           state_table.

Definition table_type : type :=
  Tarray tlong (nstates * nsyms * nwords) noattr.

Definition compile_table : globvar type := {|
  gvar_info     := table_type;
  gvar_init     := table_init;
  gvar_readonly := true;
  gvar_volatile := false
|}.

(* The initial and accepting bitmaps *)

Definition set_type : type := Tarray tlong nwords noattr.

Definition init_init : list init_data := bitmap_init (indices_of nfa.(initial _)).

Definition compile_init : globvar type := {|
  gvar_info     := set_type;
  gvar_init     := init_init;
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition accepting_states : list state := filter nfa.(accept _) nfa.(states _).

Definition final_init : list init_data := bitmap_init (indices_of accepting_states).

Definition compile_final : globvar type := {|
  gvar_info     := set_type;
  gvar_init     := final_init;
  gvar_readonly := true;
  gvar_volatile := false
|}.

(* Expression helpers *)

Definition idx (base : Clight.expr) (off : Clight.expr) : Clight.expr :=
  Ederef (Ebinop Oadd base off tsetptr) tlong.

Definition const (z : Z) : Clight.expr := Econst_long (Int64.repr z) tlong.

Definition lt_test (v : ident) (k : Z) : Clight.expr :=
  Ebinop Olt (Etempvar v tlong) (const k) tint.

(* void step(unsigned long long *cur, unsigned long long s,
             unsigned long long *next) {
     unsigned long long k, j, q, word;
     for (j = 0; j < nwords; j++) next[j] = 0;
     if (!(s < |Sigma|)) return;
     for (k = 0; k < nwords; k++) {
       word = cur[k];
       for (q = 0; q < 64; q++) {
         if (word & (1 << q))
           for (j = 0; j < nwords; j++)
             next[j] |= table[((k*64 + q) * |Sigma| + s) * nwords + j];
       }
     }
   } *)

Definition zero_next (ids : idents) : statement :=
  Ssequence
    (Sset ids.(id_j) (const 0))
    (Sloop
      (Ssequence
        (Sifthenelse (lt_test ids.(id_j) nwords) Sskip Sbreak)
        (Sassign (idx (Etempvar ids.(id_next) tsetptr) (Etempvar ids.(id_j) tlong))
                 (const 0)))
      (Sset ids.(id_j)
        (Ebinop Oadd (Etempvar ids.(id_j) tlong) (const 1) tlong))).

(** [next[j] |= table[((k*64 + q) * nsyms + s) * nwords + j]] for all [j]. *)
Definition union_row (ids : idents) : statement :=
  Ssequence
    (Sset ids.(id_j) (const 0))
    (Sloop
      (Ssequence
        (Sifthenelse (lt_test ids.(id_j) nwords) Sskip Sbreak)
        (Sassign
          (idx (Etempvar ids.(id_next) tsetptr) (Etempvar ids.(id_j) tlong))
          (Ebinop Oor
            (idx (Etempvar ids.(id_next) tsetptr) (Etempvar ids.(id_j) tlong))
            (idx (Evar ids.(id_table) table_type)
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
        (Ebinop Oadd (Etempvar ids.(id_j) tlong) (const 1) tlong))).

Definition step_body (ids : idents) : statement :=
  Ssequence
    (zero_next ids)
    (Ssequence
      (Sifthenelse (lt_test ids.(id_s) nsyms) Sskip (Sreturn None))
      (Ssequence
        (Sset ids.(id_k) (const 0))
        (Sloop
          (Ssequence
            (Sifthenelse (lt_test ids.(id_k) nwords) Sskip Sbreak)
            (Ssequence
              (Sset ids.(id_word)
                (idx (Etempvar ids.(id_cur) tsetptr) (Etempvar ids.(id_k) tlong)))
              (Ssequence
                (Sset ids.(id_q) (const 0))
                (Sloop
                  (Ssequence
                    (Sifthenelse (lt_test ids.(id_q) 64) Sskip Sbreak)
                    (Sifthenelse
                      (Ebinop One
                        (Ebinop Oand (Etempvar ids.(id_word) tlong)
                          (Ebinop Oshl (const 1) (Etempvar ids.(id_q) tlong) tlong)
                          tlong)
                        (const 0) tint)
                      (Sifthenelse
                        (Ebinop Olt
                          (Ebinop Oadd
                            (Ebinop Omul (Etempvar ids.(id_k) tlong) (const 64) tlong)
                            (Etempvar ids.(id_q) tlong) tlong)
                          (const nstates) tint)
                        (union_row ids)
                        Sskip)
                      Sskip))
                  (Sset ids.(id_q)
                    (Ebinop Oadd (Etempvar ids.(id_q) tlong) (const 1) tlong))))))
          (Sset ids.(id_k)
            (Ebinop Oadd (Etempvar ids.(id_k) tlong) (const 1) tlong))))).

Definition compile_step (ids : idents) : Clight.fundef :=
  Internal {|
    fn_return   := tvoid;
    fn_callconv := AST.cc_default;
    fn_params   := [(ids.(id_cur), tsetptr); (ids.(id_s), tlong);
                    (ids.(id_next), tsetptr)];
    fn_vars     := [];
    fn_temps    := [(ids.(id_k), tlong); (ids.(id_j), tlong);
                    (ids.(id_q), tlong); (ids.(id_word), tlong)];
    fn_body     := step_body ids
  |}.

Definition step_type : type :=
  Tfunction [tsetptr; tlong; tsetptr] tvoid AST.cc_default.

(* unsigned long long accept(unsigned long long *cur) {
     unsigned long long j, acc = 0;
     for (j = 0; j < nwords; j++) acc |= cur[j] & final[j];
     return acc != 0;
   } *)

Definition accept_body (ids : idents) : statement :=
  Ssequence
    (Sset ids.(id_acc) (const 0))
    (Ssequence
      (Ssequence
        (Sset ids.(id_j) (const 0))
        (Sloop
          (Ssequence
            (Sifthenelse (lt_test ids.(id_j) nwords) Sskip Sbreak)
            (Sset ids.(id_acc)
              (Ebinop Oor (Etempvar ids.(id_acc) tlong)
                (Ebinop Oand
                  (idx (Etempvar ids.(id_cur) tsetptr) (Etempvar ids.(id_j) tlong))
                  (idx (Evar ids.(id_final) set_type) (Etempvar ids.(id_j) tlong))
                  tlong)
                tlong)))
          (Sset ids.(id_j)
            (Ebinop Oadd (Etempvar ids.(id_j) tlong) (const 1) tlong))))
      (Sreturn (Some
        (Ebinop One (Etempvar ids.(id_acc) tlong) (const 0) tint)))).

Definition compile_accept (ids : idents) : Clight.fundef :=
  Internal {|
    fn_return   := tbool;
    fn_callconv := AST.cc_default;
    fn_params   := [(ids.(id_cur), tsetptr)];
    fn_vars     := [];
    fn_temps    := [(ids.(id_j), tlong); (ids.(id_acc), tlong)];
    fn_body     := accept_body ids
  |}.

Definition accept_type : type :=
  Tfunction [tsetptr] tbool AST.cc_default.

(* void run(unsigned long long *w, unsigned long long len,
             unsigned long long *out) {
     unsigned long long cur[nwords], next[nwords], i, j;
     for (j = 0; j < nwords; j++) cur[j] = init[j];
     for (i = 0; i < len; i++) {
       step(cur, w[i], next);
       for (j = 0; j < nwords; j++) cur[j] = next[j];
     }
     for (j = 0; j < nwords; j++) out[j] = cur[j];
   }

   [run] yields the reached set through the [out] parameter. *)

Definition w_type : type := Tpointer tlong noattr.

Definition copy_loop (ids : idents) (dst src : Clight.expr) : statement :=
  Ssequence
    (Sset ids.(id_j) (const 0))
    (Sloop
      (Ssequence
        (Sifthenelse (lt_test ids.(id_j) nwords) Sskip Sbreak)
        (Sassign (idx dst (Etempvar ids.(id_j) tlong))
                 (idx src (Etempvar ids.(id_j) tlong))))
      (Sset ids.(id_j)
        (Ebinop Oadd (Etempvar ids.(id_j) tlong) (const 1) tlong))).

Definition run_prologue (ids : idents) : statement :=
  Ssequence
    (copy_loop ids (Evar ids.(id_cur) set_type) (Evar ids.(id_init) set_type))
    (Sset ids.(id_i) (const 0)).

Definition run_body (ids : idents) : statement :=
  Ssequence
    (Sifthenelse
      (Ebinop Olt (Etempvar ids.(id_i) tlong) (Etempvar ids.(id_len) tlong) tint)
      Sskip Sbreak)
    (Ssequence
      (Scall None (Evar ids.(id_step) step_type)
         [ Evar ids.(id_cur) set_type;
           idx (Etempvar ids.(id_w) w_type) (Etempvar ids.(id_i) tlong);
           Evar ids.(id_next) set_type ])
      (Ssequence
        (copy_loop ids (Evar ids.(id_cur) set_type) (Evar ids.(id_next) set_type))
        (Sset ids.(id_i)
          (Ebinop Oadd (Etempvar ids.(id_i) tlong) (const 1) tlong)))).

Definition run_loop (ids : idents) : statement := Sloop (run_body ids) Sskip.

Definition compile_run (ids : idents) : Clight.fundef :=
  let final_body :=
    Ssequence
      (Ssequence (run_prologue ids) (run_loop ids))
      (copy_loop ids (Etempvar ids.(id_out) tsetptr) (Evar ids.(id_cur) set_type)) in
  Internal {|
    fn_return   := tvoid;
    fn_callconv := AST.cc_default;
    fn_params   := [(ids.(id_w), w_type); (ids.(id_len), tlong);
                    (ids.(id_out), tsetptr)];
    fn_vars     := [(ids.(id_cur), set_type); (ids.(id_next), set_type)];
    fn_temps    := [(ids.(id_i), tlong); (ids.(id_j), tlong)];
    fn_body     := final_body
  |}.

Definition run_type : type :=
  Tfunction [w_type; tlong; tsetptr] tvoid AST.cc_default.

(* Program assembly *)

Definition tint32s : type := Tint I32 Signed noattr.

Definition compile_main (ids : idents) : Clight.fundef :=
  Internal {|
    fn_return   := tint32s;
    fn_callconv := AST.cc_default;
    fn_params   := [];
    fn_vars     := [];
    fn_temps    := [];
    fn_body     := Sreturn (Some (Econst_int Int.zero tint32s))
  |}.

Definition compile_program (base : ident) : result Clight.program :=
  let ids := alloc_idents base in
  let defs : list (ident * globdef Clight.fundef type) :=
    [ (ids.(id_table),  Gvar (compile_table));
      (ids.(id_init),   Gvar (compile_init));
      (ids.(id_final),  Gvar (compile_final));
      (ids.(id_step),   Gfun (compile_step ids));
      (ids.(id_accept), Gfun (compile_accept ids));
      (ids.(id_run),    Gfun (compile_run ids));
      (ids.(id_main),   Gfun (compile_main ids)) ] in
  match Ctypes.make_program [] defs
          [ids.(id_step); ids.(id_accept); ids.(id_table); ids.(id_init);
           ids.(id_final); ids.(id_run); ids.(id_main)]
          ids.(id_main) with
  | Errors.OK p => return p
  | Errors.Error msg => fail E_msg "make_program failed"
  end.

End compiler.
End NFACompiler.
