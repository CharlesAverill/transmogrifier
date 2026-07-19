(* A hand-built NFA, compiled to Clight.

   L = { w : the second-to-last symbol is 'a' }
*)

open Lstar
open Alphabet
open NFA
open Teacher
open Transmogrifier.Pipeline
open Stdlib

module S = struct
  type t = A | B

  let string_of_t = function A -> "a" | B -> "b"

  let t_of_string : string -> (t, string) Datatypes.result = function
    | "a" -> Ok A
    | "b" -> Ok B
    | _ -> Error "t_of_string"

  let eq_dec x y = x = y

  let enum = [A; B]

  type str = t list

  let string_of_str s = String.concat "" (List.map string_of_t s)
end

type q = Q0 | Q1 | Q2

let delta q (a : S.t) : q list =
  match (q, a) with
  | Q0, S.A -> [Q0; Q1] (* nondeterministic: stay, or guess *)
  | Q0, S.B -> [Q0]
  | Q1, _ -> [Q2]
  | Q2, _ -> []

let is_accepting = function Q2 -> true | _ -> false

(* The single source of truth for the state count: the machine below and the
   generated header both read it, so they cannot drift. *)
let q_enum = [Q0; Q1; Q2]

module Teacher : NFATEACHER with module S = S = struct
  module S = S
  module R = RFSA (S)

  (** The spec: the second-to-last symbol is 'a'. *)
  let member (w : S.str) : bool =
    let rec second_last = function
      | [x; _] -> x = S.A
      | _ :: tl -> second_last tl
      | [] -> false
    in
    second_last w

  let equiv_query (_ : 'a R.t) : S.str option = None

  let fuel : int = Int.max_int
end

(** The machine, handed over as-is instead of being learned. *)
let handbuilt : Obj.t Teacher.R.t =
  Obj.magic
    { Teacher.R.N.transition= delta
    ; Teacher.R.N.initial= [Q0]
    ; Teacher.R.N.accept= is_accepting
    ; Teacher.R.N.states= q_enum }

module Handbuilt : NFALEARNER =
functor
  (T : NFATEACHER)
  ->
  struct
    let learn () : Obj.t T.R.t = Obj.magic handbuilt
  end

module P = NFAPipeline (S) (Teacher) (Handbuilt)

let rec enumerate n =
  if n <= 0 then [[]]
  else
    let prev = enumerate (n - 1) in
    List.map (fun s -> S.A :: s) prev @ List.map (fun s -> S.B :: s) prev

let step qs a = List.concat_map (fun q -> delta q a) qs

let run w = List.fold_left step [Q0] w

let accepts w = List.exists is_accepting (run w)

module GenHeader = Transmogrifier.Emit_header.MakeNFA (S)

(** Compile the hand-built NFA to Clight and write it out as C, plus a header.

    [nstates] is a literal in the generated C and appears in no symbol, so the
    header cannot recover it -- it comes from the machine itself. *)
let compile_to_c () =
  let out = "examples/secondlast.c" in
  let out_h = "examples/secondlast.h" in
  Printf.printf "\n=== Compiling to C ===\n" ;
  ( match
      P.compile ~eq_dec:(Obj.magic (( = ) : q -> q -> bool)) out
    with
  | Stdlib.Ok () ->
      Printf.printf "Wrote %s\n" out
  | Stdlib.Error e ->
      Printf.eprintf "Compilation failed: %s\n" e ) ;
  let nstates = List.length q_enum in
  match
    GenHeader.fill_file ~machine_name:"secondlast" ~nstates
      ~template_fn:"include/nfa.h.in" ~out_fn:out_h ()
  with
  | Stdlib.Ok () ->
      Printf.printf "Wrote %s (%d states, %d word(s) per set)\n" out_h nstates
        (GenHeader.nwords nstates)
  | Stdlib.Error e ->
      Printf.eprintf "Header generation failed: %s\n" e

(** The OCaml side of the benchmark. The C side lives in
    examples/perftests/secondlast.c and runs the same word through the compiled
    automaton.

    Note this measures something the DFA benchmarks do not: [step] here is a
    [concat_map] building a fresh list per symbol, against the compiled version's
    fixed-width bitmap. The gap should be wider than the DFA case, where OCaml
    only threads a single state. *)
let run_performance_test () =
  let test_size = 1_000_000 in
  print_endline "\n=== Generating OCaml Test Vector (secondlast) ===" ;
  (* alternating a,b,a,b,... so the last two symbols are "ab" -> accepted *)
  let test_vector =
    List.init test_size (fun i -> if i mod 2 = 0 then S.A else S.B)
  in
  print_endline "=== OCaml Benchmark ===" ;
  let start_time = Sys.time () in
  let result = accepts test_vector in
  let end_time = Sys.time () in
  Printf.printf "Processed Elements : %d\n" test_size ;
  Printf.printf "Accepted           : %b\n" result ;
  Printf.printf "Execution Time     : %.6f seconds\n" (end_time -. start_time)

let () =
  Printf.printf "=== NFA: second-to-last symbol is 'a' ===\n" ;
  List.iter
    (fun n ->
      List.iter
        (fun w ->
          let got = accepts w and exp = Teacher.member w in
          Printf.printf "  %-6s got=%-5b exp=%-5b %s\n"
            (Printf.sprintf "[%s]" (S.string_of_str w))
            got exp
            (if got = exp then "" else "  <-- MISMATCH") )
        (enumerate n) )
    [0; 1; 2; 3] ;
  compile_to_c () ;
  run_performance_test ()
