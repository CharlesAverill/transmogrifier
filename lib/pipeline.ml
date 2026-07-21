open Moore0
open Alphabet
open Teacher
open Dfa
open Nfa
open Mealy
open Monads

(** A learner turns a teacher into a state machine over an opaque state type *)
module type MOORELEARNER = functor (Tch : MOORETEACHER) -> sig
  val learn : unit -> Obj.t Tch.M.t
end

module type DFALEARNER = functor (Tch : DFATEACHER) -> sig
  val learn : unit -> Obj.t Tch.D.t
end

module type NFALEARNER = functor (Tch : NFATEACHER) -> sig
  val learn : unit -> Obj.t Tch.R.t
end

module type MEALYLEARNER = functor (Tch : MEALYTEACHER) -> sig
  val learn : unit -> Obj.t Tch.M.t
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

module MealyPipeline
    (S : Symbol)
    (O : Symbol)
    (Tch : MEALYTEACHER with module S = S and module O = O)
    (L : MEALYLEARNER) =
struct
  module Compiler = MealyCompiler (S) (O) (Tch.M)
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
    (* Must track [alloc_idents] in theories/compiler/mealy.v. *)
    reg 0 "delta" ;
    reg 1 "q0" ;
    reg 2 "table" ;
    reg 3 "otable" ;
    reg 11 "run"

  (** Compile the learned Mealy machine to Clight and print it to [output_fn]
      or [stdout]

      [base] is the first identifier the compiler may allocate; it must not
      collide with any interned CompCert prelude symbol.

      [state_eq_dec] decides equality on the learned machine's state type.
      [(=)] should be fine *)
  let compile ?(base = BinNums.Coq_xH)
      ?(eq_dec : 'A -> 'A -> bool = state_eq_dec) (output_fn : string) :
      (unit, string) Stdlib.result =
    let m = learn () in
    name_idents base ;
    match Compiler.compile_program m eq_dec base with
    | Error e ->
        Stdlib.Error ("Error: " ^ string_of_error e)
    | Ok p ->
        pretty_print p output_fn ; Stdlib.Ok ()
end

module NFAPipeline
    (S : Symbol)
    (Tch : NFATEACHER with module S = S)
    (L : NFALEARNER) =
struct
  module Compiler = NFACompiler (S) (Tch.R.N)
  module Lrn = L (Tch)

  let learned : Obj.t Tch.R.t option ref = ref None

  let learn () =
    match !learned with
    | None ->
        let d = Lrn.learn () in
        learned := Some d ;
        d
    | Some d ->
        d

  let state_eq_dec = Obj.magic Tch.R.N.str_eq

  let name_idents (base : BinNums.positive) : unit =
    let open Camlcoq in
    let reg (offset : int) (name : string) =
      let a = P.of_int (P.to_int base + offset) in
      Hashtbl.replace string_of_atom a name
    in
    (* Must track [alloc_idents] in theories/compiler/nfa.v -- this is NOT
       DFA's/Moore's layout, and was previously copy-pasted from there: the
       function at offset 0 is [step] (an NFA transition takes and returns a
       *set*, unlike a DFA's single-state [delta]), and the two bitmap globals
       at offsets 3/4 are [init]/[final], not [q0]/[atable]. include/nfa.h.in
       declares exactly these five names, so getting them wrong here doesn't
       break the self-contained example (it never references [init]/[final]
       by name) but silently breaks any consumer that follows the documented
       header API and links against the emitted .c. *)
    reg 0 "delta" ;
    reg 1 "accept" ;
    reg 2 "table" ;
    reg 3 "init" ;
    reg 4 "final" ;
    reg 17 "run"

  (** Compile the learned NFA to Clight and print it to [output_fn] or [stdout]

      [base] is the first identifier the compiler may allocate; it must not
      collide with any interned CompCert prelude symbol.

      [state_eq_dec] decides equality on the learned DFA's state type. [(=)] should
      be fine *)
  let compile ?(base = BinNums.Coq_xH)
      ?(eq_dec : 'A -> 'A -> bool = state_eq_dec) (output_fn : string) :
      (unit, string) Stdlib.result =
    let n = learn () in
    name_idents base ;
    match Compiler.compile_program n eq_dec base with
    | Error e ->
        Stdlib.Error ("Error: " ^ string_of_error e)
    | Ok p ->
        pretty_print p output_fn ; Stdlib.Ok ()
end
