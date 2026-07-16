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
  id_q      : ident;
  id_s      : ident
}.

Definition alloc_idents (base : ident) : idents := {|
  id_delta  := base;
  id_accept := 1 + base;
  id_q0     := 2 + base;
  id_q      := 3 + base;
  id_s      := 4 + base
|}%positive.

Definition idents_next (base : ident) : ident :=
    (5 + base)%positive.

(* Types *)

Definition tuint : type := Tint I32 Unsigned noattr.

Section compiler.
Variable state : Type.
Variable dfa : DFA.t state.

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
  map (fun '(i, _) => Econst_int (Int.repr i) tuint) (enumerate l).

Definition compiled_sigma : list Clight.expr := compiled_enum s.enum.
Definition compiled_Q     : list Clight.expr := compiled_enum dfa.(states _).

Definition q0_index (state_eq_dec : forall x y : state, {x = y} + {x <> y}) : Z :=
  match index_of state_eq_dec dfa.(initial _) dfa.(states _) 0 with
  | Some i => i
  | None => sink_index
  end.

Definition compiled_q0 (state_eq_dec : forall x y : state, {x = y} + {x <> y})
    : Clight.expr :=
  Econst_int (Int.repr (q0_index state_eq_dec)) tuint.

(*  delta

    Emitted as nested [Sifthenelse] on the state, then on the symbol. *)

Definition eq_test (v : ident) (k : Z) : Clight.expr :=
  Ebinop Oeq (Etempvar v tuint) (Econst_int (Int.repr k) tuint) tuint.

Definition sym_branch ids state_eq_dec (q_idx : Z) (q : state) : Clight.statement :=
    fold_left (fun (acc : Clight.statement) '(s_idx, sym) =>
      match index_of state_eq_dec (dfa.(transition _) q sym)
                     dfa.(states _) 0 with
      | Some next_idx =>
          Clight.Sifthenelse (eq_test ids.(id_s) s_idx)
            (Clight.Sreturn (Some (Econst_int (Int.repr next_idx) tuint)))
            acc
      | None => acc
      end
    ) sym_table (Clight.Sreturn (Some (Econst_int (Int.repr sink_index) tuint))).

Definition compile_delta (ids : idents) state_eq_dec : Clight.fundef :=
  let body :=
    fold_left (fun (acc : Clight.statement) '(q_idx, q) =>
      Clight.Sifthenelse (eq_test ids.(id_q) q_idx)
        (sym_branch ids state_eq_dec q_idx q)
        acc
    ) state_table (Clight.Sreturn (Some (Econst_int (Int.repr sink_index) tuint)))
  in
  Internal {|
    fn_return   := tuint;
    fn_callconv := AST.cc_default;
    fn_params   := [(ids.(id_q), tuint); (ids.(id_s), tuint)];
    fn_vars     := [];
    fn_temps    := [];
    fn_body     := body
  |}.

(* accept *)

Definition compile_accept (ids : idents) : Clight.fundef :=
  let body :=
    fold_left (fun (acc : Clight.statement) '(q_idx, q) =>
      if dfa.(accept _) q then
        Clight.Sifthenelse (eq_test ids.(id_q) q_idx)
          (Clight.Sreturn (Some (Econst_int Int.one tuint)))
          acc
      else acc
    ) state_table (Clight.Sreturn (Some (Econst_int Int.zero tuint)))
  in
  Internal {|
    fn_return   := tuint;
    fn_callconv := AST.cc_default;
    fn_params   := [(ids.(id_q), tuint)];
    fn_vars     := [];
    fn_temps    := [];
    fn_body     := body
  |}.

(** The initial state index, exported as a read-only global so that a caller
    has something to start [delta] from. *)
Definition compile_q0 (state_eq_dec : forall x y : state, {x = y} + {x <> y})
    : globvar type := {|
  gvar_info     := tuint;
  gvar_init     := [Init_int32 (Int.repr (q0_index state_eq_dec))];
  gvar_readonly := true;
  gvar_volatile := false
|}.

(* Program assembly *)

Definition delta_sig : type :=
  Tfunction [tuint; tuint] tuint AST.cc_default.
Definition accept_sig : type :=
  Tfunction [tuint] tuint AST.cc_default.

Definition compile_program (base : ident) state_eq_dec : result Clight.program :=
  let ids := alloc_idents base in
  let defs : list (ident * globdef Clight.fundef type) :=
    [ (ids.(id_delta),  Gfun (compile_delta ids state_eq_dec));
      (ids.(id_accept), Gfun (compile_accept ids));
      (ids.(id_q0),     Gvar (compile_q0 state_eq_dec)) ] in
  match Ctypes.make_program [] defs
          [ids.(id_delta); ids.(id_accept); ids.(id_q0)]
          ids.(id_accept) with
  | Errors.OK p => return p
  | Errors.Error msg => fail E_invalid_type "make_program failed"
  end.

End compiler.
End DFACompiler.
