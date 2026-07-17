open Moore0
open Automata
open Teacher
open Dfa
open Monads

(** A learner turns a teacher into a state machine over an opaque state type *)
module type MOORELEARNER = functor (Tch : MOORETEACHER) -> sig
  val learn : unit -> Obj.t Tch.M.t
end

(** A learner turns a teacher into a DFA over an opaque state type *)
module type DFALEARNER = functor (Tch : DFATEACHER) -> sig
  val learn : unit -> Obj.t Tch.D.t
end

let string_of_error = function
  | E_msg c
  | E_unsupported c
  | E_invalid_type c
  | E_invalid_value c
  | E_multiply_defined c
  | E_bad_identifier c ->
      c

let pretty_print (clight_prog : Clight.program) (output_fn : string) : unit =
  PrintClight.destination :=
    if output_fn = "" then
      None
    else
      Some output_fn ;
  PrintClight.print_if clight_prog

module MoorePipeline
    (S : Symbol)
    (O : Symbol)
    (Tch : MOORETEACHER with module S = S and module O = O)
    (L : MOORELEARNER) =
struct
  module Compiler = MooreCompiler (S) (O) (Tch.M)
  module Lrn = L (Tch)

  let learned : Obj.t Tch.M.t option ref = ref None

  let learn () =
    match !learned with
    | None ->
        let d = Lrn.learn () in
        learned := Some d ;
        d
    | Some d ->
        d

  let state_eq_dec = Obj.magic Tch.M.str_eq

  let name_idents (base : BinNums.positive) : unit =
    let open Camlcoq in
    let reg (offset : int) (name : string) =
      let a = P.of_int (P.to_int base + offset) in
      Hashtbl.replace string_of_atom a name
    in
    (* Must track [alloc_idents] in theories/compiler/dfa.v. *)
    reg 0 "delta" ;
    reg 1 "output" ;
    reg 2 "q0" ;
    reg 3 "table" ;
    reg 4 "atable" ;
    reg 10 "run"

  (** Compile the learned DFA to Clight and print it to [output_fn] or [stdout]

      [base] is the first identifier the compiler may allocate; it must not
      collide with any interned CompCert prelude symbol.

      [state_eq_dec] decides equality on the learned DFA's state type. [(=)] should
      be fine *)
  let compile ?(base = BinNums.Coq_xH)
      ?(eq_dec : 'A -> 'A -> bool = state_eq_dec) (output_fn : string) :
      (unit, string) Stdlib.result =
    let d = learn () in
    name_idents base ;
    match Compiler.compile_program d eq_dec base with
    | Error e ->
        Stdlib.Error ("Error: " ^ string_of_error e)
    | Ok p ->
        pretty_print p output_fn ; Stdlib.Ok ()
end

module DFAPipeline
    (S : Symbol)
    (Tch : DFATEACHER with module S = S)
    (L : DFALEARNER) =
struct
  module Compiler = DFACompiler (S) (Tch.D)
  module Lrn = L (Tch)

  let moore_of_dfa (d : 'a Tch.D.t) : 'a Compiler.Moore.t =
    { Compiler.Moore.transition= d.Tch.D.transition
    ; Compiler.Moore.initial= d.Tch.D.initial
    ; Compiler.Moore.output= d.Tch.D.accept
    ; Compiler.Moore.states= d.Tch.D.states }

  let learned : Obj.t Tch.D.t option ref = ref None

  let learn () =
    match !learned with
    | None ->
        let d = Lrn.learn () in
        learned := Some d ;
        d
    | Some d ->
        d

  let state_eq_dec = Obj.magic Tch.D.str_eq

  let name_idents (base : BinNums.positive) : unit =
    let open Camlcoq in
    let reg (offset : int) (name : string) =
      let a = P.of_int (P.to_int base + offset) in
      Hashtbl.replace string_of_atom a name
    in
    (* Must track [alloc_idents] in theories/compiler/dfa.v. *)
    reg 0 "delta" ;
    reg 1 "accept" ;
    reg 2 "q0" ;
    reg 3 "table" ;
    reg 4 "atable" ;
    reg 10 "run"

  (** Compile the learned DFA to Clight and print it to [output_fn] or [stdout]

      [base] is the first identifier the compiler may allocate; it must not
      collide with any interned CompCert prelude symbol.

      [state_eq_dec] decides equality on the learned DFA's state type. [(=)] should
      be fine *)
  let compile ?(base = BinNums.Coq_xH)
      ?(eq_dec : 'A -> 'A -> bool = state_eq_dec) (output_fn : string) :
      (unit, string) Stdlib.result =
    let d = learn () in
    name_idents base ;
    match Compiler.compile_program (moore_of_dfa d) eq_dec base with
    | Error e ->
        Stdlib.Error ("Error: " ^ string_of_error e)
    | Ok p ->
        pretty_print p output_fn ; Stdlib.Ok ()
end
