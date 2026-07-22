From lstar Require Import automata.Mealy.
From compcert Require Import AST Clight Ctypes Integers Cop Maps.
From Transmogrifier Require Import Monads.
From Stdlib Require Import String List ZArith.
Import ListNotations.
Open Scope result_scope.
Open Scope string_scope.
Open Scope Z_scope.

(** Compile a Mealy machine into a Clight program.

    \Sigma : alphabet, indices 0..|\Sigma|-1
    O      : output alphabet, indices 0..|O|-1
    Q      : state set, indices 0..|Q|-1
    q_0    : exported as a read-only global
    \delta : compiled to
                unsigned long long delta(unsigned long long q,
                                         unsigned long long s,
                                         unsigned long long *out);
             which returns the next state's index and writes the output symbol's
             index through [out].
    run    : emits the output string into a caller-provided buffer. *)

Module Type MealyType (s : Symbol) (O : Output).
  Record t (state : Type) : Type := {
        transition : state -> s.t -> state;
        initial : state;
        output : state -> s.t -> O.t;
        states : list state;
        states_complete : forall w, In (fold_left transition w initial) states
    }.

  Definition run {state : Type} (m : t state) (w : list s.t) : state :=
      fold_left m.(transition state) w m.(initial state).

  Theorem run_in_states : forall {state : Type} (m : t state) (w : list s.t),
      In (run m w) (states state m).
  Proof. apply states_complete. Qed.
End MealyType.

Module MealyCompiler (s : Symbol) (O : Output) (Mealy : MealyType s O).

Import Mealy.

(** The output string: at each step, emit [output] of the current state and
    the symbol read, then advance. *)
Fixpoint outputs {state : Type} (m : t state) (q : state) (w : list s.t)
    : list O.t :=
    match w with
    | [] => []
    | a :: rest =>
        m.(output state) q a :: outputs m (m.(transition state) q a) rest
    end.

Definition run_outputs {state : Type} (m : t state) (w : list s.t) : list O.t :=
    outputs m m.(initial state) w.

(* Identifier allocation *)

Record idents : Type := {
  id_delta  : ident;
  id_q0     : ident;
  id_table  : ident;
  id_otable : ident;
  id_q      : ident;
  id_s      : ident;
  id_out    : ident;
  id_w      : ident;
  id_len    : ident;
  id_i      : ident;
  id_o      : ident;
  id_run    : ident;
  id_main   : ident
}.

Definition alloc_idents (base : ident) : idents := {|
  id_delta  := base;
  id_q0     := 1 + base;
  id_table  := 2 + base;
  id_otable := 3 + base;
  id_q      := 4 + base;
  id_s      := 5 + base;
  id_out    := 6 + base;
  id_w      := 7 + base;
  id_len    := 8 + base;
  id_i      := 9 + base;
  id_o      := 10 + base;
  id_run    := 11 + base;
  id_main   := 12 + base
|}%positive.

(* Types *)

Definition tlong : type := Tlong Unsigned noattr.
Definition tuint : type := Tint I32 Unsigned noattr.
Definition tint : type := Tint I32 Signed noattr.
Definition tbool : type := Tint IBool Unsigned noattr.
Definition tlptr : type := Tpointer tlong noattr.

Section compiler.
Variable state : Type.
Variable mealy : Mealy.t state.
Variable state_eq_dec : forall x y : state, {x = y} + {x <> y}.

(** Sink index, returned for out-of-range inputs. *)
Definition sink_index : Z := Z.of_nat (length mealy.(states _)).

Fixpoint index_of {X : Type} (eq_dec : forall x y : X, {x = y} + {x <> y})
                  (target : X) (l : list X) (idx : Z) : option Z :=
  match l with
  | [] => None
  | h :: t => if eq_dec target h then Some idx else index_of eq_dec target t (Z.succ idx)
  end.

Definition enumerate {X : Type} (l : list X) : list (Z * X) :=
  combine (map Z.of_nat (seq 0 (length l))) l.

Definition state_table : list (Z * state) := enumerate mealy.(states _).
Definition sym_table   : list (Z * s.t)   := enumerate s.enum.
Definition out_table   : list (Z * O.t)   := enumerate O.enum.

Definition q0_index : Z :=
  match index_of state_eq_dec mealy.(initial _) mealy.(states _) 0 with
  | Some i => i
  | None => sink_index
  end.

Definition compiled_q0 : Clight.expr :=
  Econst_long (Int64.repr q0_index) tlong.

Definition nsyms : Z := Z.of_nat (length s.enum).
Definition nstates : Z := Z.of_nat (length mealy.(states _)).
Definition nouts : Z := Z.of_nat (length O.enum).

(* The transition table, flattened row-major: entry [q * |Sigma| + s] holds the
   index of [delta q s]. *)
Definition table_entry (q : state) (sym : s.t) : Z :=
  match index_of state_eq_dec (mealy.(transition _) q sym) mealy.(states _) 0 with
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

(* The output table: entry [q * |Sigma| + s] holds the index in [O.enum]
   of [output q s]. *)
Definition otable_entry (q : state) (sym : s.t) : Z :=
  match index_of O.eq_dec (mealy.(output _) q sym) O.enum 0 with
  | Some i => i
  | None => nouts
  end.

Definition otable_row (q : state) : list init_data :=
  map (fun '(_, sym) => Init_int64 (Int64.repr (otable_entry q sym))) sym_table.

Definition otable_init : list init_data :=
  flat_map (fun '(_, q) => otable_row q) state_table.

Definition compile_otable : globvar type := {|
  gvar_info     := table_type;
  gvar_init     := otable_init;
  gvar_readonly := true;
  gvar_volatile := false
|}.

(* delta

   unsigned long long delta(unsigned long long q, unsigned long long s,
                            unsigned long long *out) {
     if (q < |Q| && s < |Sigma|) {
       *out = otable[q * |Sigma| + s];
       return table[q * |Sigma| + s];
     } else {
       *out = |O|;
       return |Q|;
     }
   }

   The output symbol is written through [out]; the next state is returned. On
   out-of-range input both take their sink value. *)

Definition lt_test (v : ident) (k : Z) : Clight.expr :=
  Ebinop Olt (Etempvar v tlong) (Econst_long (Int64.repr k) tlong) tint.

Definition table_index (ids : idents) : Clight.expr :=
  Ebinop Oadd
    (Ebinop Omul (Etempvar ids.(id_q) tlong) (Econst_long (Int64.repr nsyms) tlong) tlong)
    (Etempvar ids.(id_s) tlong)
    tlong.

(** Load [tbl[q * nsyms + s]], where [tbl] is a table-typed global. *)
Definition table_load (ids : idents) (tbl : ident) : Clight.expr :=
  Ederef
    (Ebinop Oadd (Evar tbl table_type) (table_index ids) tlptr)
    tlong.

(** Store [v] through the [out] pointer parameter. *)
Definition store_out (ids : idents) (v : Clight.expr) : statement :=
  Sassign (Ederef (Etempvar ids.(id_out) tlptr) tlong) v.

Definition compile_delta (ids : idents) : Clight.fundef :=
  let body :=
    Sifthenelse
      (Ebinop Oand (lt_test ids.(id_q) nstates) (lt_test ids.(id_s) nsyms) tint)
      (Ssequence
        (store_out ids (table_load ids ids.(id_otable)))
        (Sreturn (Some (table_load ids ids.(id_table)))))
      (Ssequence
        (store_out ids (Econst_long (Int64.repr nouts) tlong))
        (Sreturn (Some (Econst_long (Int64.repr sink_index) tlong))))
  in
  Internal {|
    fn_return   := tlong;
    fn_callconv := AST.cc_default;
    fn_params   := [(ids.(id_q), tlong); (ids.(id_s), tlong); (ids.(id_out), tlptr)];
    fn_vars     := [];
    fn_temps    := [];
    fn_body     := body
  |}.

Definition delta_type : type :=
  Tfunction [tlong; tlong; tlptr] tlong AST.cc_default.

(* q0 *)

Definition compile_q0 : globvar type := {|
  gvar_info     := tlong;
  gvar_init     := [Init_int64 (Int64.repr q0_index)];
  gvar_readonly := true;
  gvar_volatile := false
|}.

(* run

   Emits the output string, not just the final state -- that is what makes a
   Mealy machine a transducer.

   void run(unsigned long long *w, unsigned long long len,
            unsigned long long *out) {
     unsigned long long i = 0, q = q0, o;
     while (i < len) {
       q = delta(q, w[i], &o);
       out[i] = o;
       i++;
     }
   }

   [out] is a caller buffer of [len] output indices; [o] is a scratch temp that
   receives each step's output before it is stored. *)

Definition w_type : type := Tpointer tlong noattr.

Definition run_body (ids : idents) : statement :=
  Ssequence
    (Sifthenelse
      (Ebinop Olt (Etempvar ids.(id_i) tlong) (Etempvar ids.(id_len) tlong) tint)
      Sskip Sbreak)
    (Ssequence
      (* q = delta(q, w[i], &o) *)
      (Scall (Some ids.(id_q)) (Evar ids.(id_delta) delta_type)
         [ Etempvar ids.(id_q) tlong;
           Ederef (Ebinop Oadd (Etempvar ids.(id_w) w_type)
                     (Etempvar ids.(id_i) tlong) w_type) tlong;
           Eaddrof (Evar ids.(id_o) tlong) tlptr ])
      (Ssequence
        (* out[i] = o *)
        (Sassign
          (Ederef (Ebinop Oadd (Etempvar ids.(id_out) tlptr)
                     (Etempvar ids.(id_i) tlong) tlptr) tlong)
          (Evar ids.(id_o) tlong))
        (Sset ids.(id_i)
          (Ebinop Oadd (Etempvar ids.(id_i) tlong) (Econst_long (Int64.repr 1) tlong) tlong)))).

Definition run_loop (ids : idents) : statement := Sloop (run_body ids) Sskip.

Definition run_prologue (ids : idents) : statement :=
  Ssequence
    (Sset ids.(id_i) (Econst_long (Int64.repr 0) tlong))
    (Sset ids.(id_q) compiled_q0).

Definition compile_run (ids : idents) : Clight.fundef :=
  let final_body :=
    Ssequence (run_prologue ids) (run_loop ids) in
  Internal {|
    fn_return   := Tvoid;
    fn_callconv := AST.cc_default;
    fn_params   := [(ids.(id_w), w_type); (ids.(id_len), tlong); (ids.(id_out), tlptr)];
    fn_vars     := [(ids.(id_o), tlong)];
    fn_temps    := [(ids.(id_i), tlong); (ids.(id_q), tlong)];
    fn_body     := final_body
  |}.

Definition run_type : type :=
  Tfunction [w_type; tlong; tlptr] Tvoid AST.cc_default.

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
      (ids.(id_otable), Gvar (compile_otable));
      (ids.(id_delta),  Gfun (compile_delta ids));
      (ids.(id_q0),     Gvar (compile_q0));
      (ids.(id_run),    Gfun (compile_run ids));
      (ids.(id_main),   Gfun (compile_main ids)) ] in
  match Ctypes.make_program [] defs
          [ids.(id_delta); ids.(id_q0); ids.(id_table);
           ids.(id_otable); ids.(id_run); ids.(id_main)]
          ids.(id_main) with
  | Errors.OK p => return p
  | Errors.Error msg => fail E_msg "make_program failed"
  end.

End compiler.
End MealyCompiler.
