From lstar Require Import Automata.
From compcert Require Import AST Clight Ctypes Integers Cop Maps.
From Transmogrifier Require Import Monads.
From Stdlib Require Import String List ZArith.
Import ListNotations.
Open Scope result_scope.
Open Scope string_scope.
Open Scope Z_scope.

(** Compile a DFA into a Clight program.

    \Sigma : alphabet, represented as integer indices 0..|\Sigma|-1
    Q      : state set, represented as integer indices 0..|Q|-1
    q_0    : exported as a read-only global; see [q0_index]
    \delta : compiled to
                unsigned int delta(unsigned int q, unsigned int s);
    F      : compiled to
                unsigned int accept(unsigned int q); *)

Module Type DFAType (s : Symbol).
  Record t (state : Type) : Type := {
        transition : state -> s.t -> state;
        initial : state;
        accept : state -> bool;
        states : list state;
        states_complete : forall w, In (fold_left transition w initial) (states)
    }.

  Definition run {state : Type} (dfa : t state) (s : list s.t) : state :=
        fold_left dfa.(transition state) s dfa.(initial state).

  Parameter run_in_states : forall {state : Type} (d : t state) (w : list s.t),
        In (run d w) (states state d).
End DFAType.

Module DFACompiler (s : Symbol) (DFA : DFAType s).

Import DFA.

(* Identifier allocation *)

Record idents : Type := {
  id_delta  : ident;
  id_accept : ident;
  id_q0     : ident;
  id_table  : ident;
  id_q      : ident;
  id_s      : ident;
  id_w      : ident;
  id_len    : ident;
  id_i      : ident;
  id_run    : ident;
  id_main   : ident
}.

Definition alloc_idents (base : ident) : idents := {|
  id_delta  := base;
  id_accept := 1 + base;
  id_q0     := 2 + base;
  id_table  := 3 + base;
  id_q      := 4 + base;
  id_s      := 5 + base;
  id_w      := 6 + base;
  id_len    := 7 + base;
  id_i      := 8 + base;
  id_run    := 9 + base;
  id_main   := 10 + base
|}%positive.

(* Types *)

Definition tlong : type := Tlong Unsigned noattr.
Definition tuint : type := Tint I32 Unsigned noattr.
Definition tint : type := Tint I32 Signed noattr.
Definition tbool : type := Tint IBool Unsigned noattr.

Section compiler.
Variable state : Type.
Variable dfa : DFA.t state.
Variable state_eq_dec : forall x y : state, {x = y} + {x <> y}.

(* Return value for out-of-bounds transition inputs *)
Definition sink_index : Z := Z.of_nat (length dfa.(states _)).

Fixpoint index_of {X : Type} (eq_dec : forall x y : X, {x = y} + {x <> y})
                  (target : X) (l : list X) (idx : Z) : option Z :=
  match l with
  | [] => None
  | h :: t => if eq_dec target h then Some idx else index_of eq_dec target t (Z.succ idx)
  end.

Definition enumerate {X : Type} (l : list X) : list (Z * X) :=
  combine (map Z.of_nat (seq 0 (length l))) l.

Definition state_table : list (Z * state) := enumerate dfa.(states _).
Definition sym_table   : list (Z * s.t)   := enumerate s.enum.

Definition compiled_enum {X : Type} (l : list X) : list Clight.expr :=
  map (fun '(i, _) => Econst_long (Int64.repr i) tlong) (enumerate l).

Definition compiled_sigma : list Clight.expr := compiled_enum s.enum.
Definition compiled_Q     : list Clight.expr := compiled_enum dfa.(states _).

Definition q0_index : Z :=
  match index_of state_eq_dec dfa.(initial _) dfa.(states _) 0 with
  | Some i => i
  | None => sink_index
  end.

Definition compiled_q0 : Clight.expr :=
  Econst_long (Int64.repr q0_index) tlong.

(*  delta

    Emitted as a 2D lookup table *)

Definition nsyms : Z := Z.of_nat (length s.enum).
Definition nstates : Z := Z.of_nat (length dfa.(states _)).

(* The transition table, flattened row-major: entry [q * |Sigma| + s]
   holds the index of [delta q s]. Rows are indexed by state, columns
   by symbol. *)
Definition table_entry (q : state) (sym : s.t) : Z :=
  match index_of state_eq_dec (dfa.(transition _) q sym) dfa.(states _) 0 with
  | Some i => i
  | None => sink_index
  end.

Definition table_row (q : state) : list init_data :=
  map (fun '(_, sym) => Init_int64 (Int64.repr (table_entry q sym))) sym_table.

Definition table_init : list init_data :=
  flat_map (fun '(_, q) => table_row q) state_table.

Definition table_type : type :=
  Tarray tlong (nstates * nsyms) noattr.

Definition compile_table : globvar type := {|
  gvar_info     := table_type;
  gvar_init     := table_init;
  gvar_readonly := true;
  gvar_volatile := false
|}.

(* unsigned long long delta(unsigned long long q, unsigned long long s) {
     if (q < |Q| && s < |Sigma|)
       return table[q * |Sigma| + s];
     else
       return |Q|;
   } *)
Definition lt_test (v : ident) (k : Z) : Clight.expr :=
  Ebinop Olt (Etempvar v tlong) (Econst_long (Int64.repr k) tlong) tint.

Definition table_index (ids : idents) : Clight.expr :=
  Ebinop Oadd
    (Ebinop Omul (Etempvar ids.(id_q) tlong) (Econst_long (Int64.repr nsyms) tlong) tlong)
    (Etempvar ids.(id_s) tlong)
    tlong.

Definition compile_delta (ids : idents) : Clight.fundef :=
  let body :=
    Sifthenelse
      (Ebinop Oand (lt_test ids.(id_q) nstates) (lt_test ids.(id_s) nsyms) tint)
      (Sreturn (Some
        (Ederef
          (Ebinop Oadd (Evar ids.(id_table) table_type) (table_index ids)
            (Tpointer tlong noattr))
          tlong)))
      (Sreturn (Some (Econst_long (Int64.repr sink_index) tlong)))
  in
  Internal {|
    fn_return   := tlong;
    fn_callconv := AST.cc_default;
    fn_params   := [(ids.(id_q), tlong); (ids.(id_s), tlong)];
    fn_vars     := [];
    fn_temps    := [];
    fn_body     := body
  |}.

Definition delta_type : type :=
  Tfunction [tlong; tlong] tlong AST.cc_default.

(* accept *)

Definition eq_test (v : ident) (k : Z) : Clight.expr :=
  Ebinop Oeq (Etempvar v tlong) (Econst_long (Int64.repr k) tlong) tuint.

Definition compile_accept (ids : idents) : Clight.fundef :=
  let body :=
    fold_left (fun (acc : Clight.statement) '(q_idx, q) =>
      if dfa.(accept _) q then
        Clight.Sifthenelse (eq_test ids.(id_q) q_idx)
          (Clight.Sreturn (Some (Econst_int Int.one tbool)))
          acc
      else acc
    ) state_table (Clight.Sreturn (Some (Econst_int Int.zero tbool)))
  in
  Internal {|
    fn_return   := tbool;
    fn_callconv := AST.cc_default;
    fn_params   := [(ids.(id_q), tlong)];
    fn_vars     := [];
    fn_temps    := [];
    fn_body     := body
  |}.

(* q0 *)

Definition compile_q0 : globvar type := {|
  gvar_info     := tlong;
  gvar_init     := [Init_int64 (Int64.repr q0_index)];
  gvar_readonly := true;
  gvar_volatile := false
|}.

(* run *)

Definition w_type : type :=
  Tpointer tlong noattr.

(* int run(int *w, int len) {
     int i = 0;
     int q = q0;
     while(i < len) {
       q = delta(q, w[i]);
       i++;
     }
     return q;
   } *)
Definition run_body (ids : idents) : statement :=
  Ssequence
    (Sifthenelse
      (Ebinop Olt (Etempvar ids.(id_i) tlong) (Etempvar ids.(id_len) tlong) tint)
      Sskip Sbreak)
    (Ssequence
      (Scall (Some ids.(id_q)) (Evar ids.(id_delta) delta_type)
         [ Etempvar ids.(id_q) tlong;
           Ederef (Ebinop Oadd (Etempvar ids.(id_w) w_type)
                     (Etempvar ids.(id_i) tlong) w_type) tlong ])
      (Sset ids.(id_i)
        (Ebinop Oadd (Etempvar ids.(id_i) tlong) (Econst_long (Int64.repr 1) tlong) tlong))).

Definition run_loop (ids : idents) : statement := Sloop (run_body ids) Sskip.

Definition run_prologue (ids : idents) : statement :=
  Ssequence
    (Sset ids.(id_i) (Econst_long (Int64.repr 0) tlong))
    (Sset ids.(id_q) compiled_q0).

Definition compile_run (ids : idents) : Clight.fundef :=
  let final_body :=
    Ssequence
      (Ssequence (run_prologue ids) (run_loop ids))
      (Sreturn (Some (Etempvar ids.(id_q) tlong))) in
  Internal {|
    fn_return   := tlong;
    fn_callconv := AST.cc_default;
    fn_params   := [(ids.(id_w), w_type); (ids.(id_len), tlong)];
    fn_vars     := [];
    fn_temps    := [(ids.(id_i), tlong); (ids.(id_q), tlong)];
    fn_body     := final_body
  |}.

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
      (ids.(id_delta),  Gfun (compile_delta ids));
      (ids.(id_accept), Gfun (compile_accept ids));
      (ids.(id_q0),     Gvar (compile_q0));
      (ids.(id_run),    Gfun (compile_run ids));
      (ids.(id_main),   Gfun (compile_main ids)) ] in
  match Ctypes.make_program [] defs
          [ids.(id_delta); ids.(id_accept); ids.(id_q0); ids.(id_table);
           ids.(id_run); ids.(id_main)]
          ids.(id_main) with
  | Errors.OK p => return p
  | Errors.Error msg => fail E_msg "make_program failed"
  end.

End compiler.
End DFACompiler.
