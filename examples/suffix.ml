open Lstar
open DFA
open NFA
open Specif
open Teacher
open Transmogrifier.Pipeline
open Stdlib

(** L_n = Sigma* a Sigma^n over Sigma = {a, b}: the words carrying an [a] in the
    (n+1)-th position from the right. *)

let n = 2

(** Alphabet *)
module S = struct
  type t = A | B

  let string_of_t = function A -> "a" | B -> "b"

  let t_of_string : string -> (t, string) Datatypes.result = function
    | "a" ->
        Ok A
    | "b" ->
        Ok B
    | _ ->
        Error "t_of_string"

  let eq_dec x y = x = y

  let enum = [A; B]

  type str = t list

  let string_of_str s = String.concat "" (List.map string_of_t s)
end

(** Language membership: the (n+1)-th symbol from the right is [a]. Words
    shorter than n+1 have no such position and are rejected. *)
let member (s : S.str) : bool =
  match List.nth_opt (List.rev s) n with Some S.A -> true | _ -> false

let counterexample (accepts : S.str -> bool) : S.str option =
  let rec bfs depth queue =
    if depth >= 256 then
      None
    else
      match queue with
      | [] ->
          None
      | s :: rest ->
          if accepts s <> member s then
            Some s
          else
            bfs (depth + 1) (rest @ List.map (fun c -> s @ [c]) S.enum)
  in
  bfs 0 [[]]

(** Teacher for the deterministic learners *)
module DTeacher : DFATEACHER with module S = S = struct
  module S = S
  module D = DFA (S)

  let member = member

  let equiv_query (dfa : 'a D.t) : S.str option =
    counterexample (D.accept_string dfa)

  let fuel : int = Int.max_int
end

(** Teacher for the nondeterministic learner *)
module NTeacher : NFATEACHER with module S = S = struct
  module S = S
  module R = RFSA (S)

  let member = member

  let equiv_query (nfa : 'a R.N.t) : S.str option =
    counterexample (R.N.accept_string nfa)

  let fuel : int = Int.max_int
end

(** L* implementation *)
module Lstar = LstarLearner (DTeacher)

(** NL* implementation *)
module NLstar = NLstarLearner (NTeacher)

module DP = DFAPrinter (DTeacher)
module NP = NFAPrinter (NTeacher)

(** Generate all strings of length [k] *)
let rec enumerate (k : int) : S.str list =
  if k <= 0 then
    [[]]
  else
    let prev = enumerate (k - 1) in
    List.concat_map (fun c -> List.map (fun s -> c :: s) prev) S.enum

(** Run a hypothesis on test cases and pretty-print the results *)
let print_table (accepts : S.str -> bool) (k : int) =
  let strings = enumerate k in
  let col_w = max 10 (k + 2) in
  let header =
    Printf.sprintf "%-*s  %-8s  %-8s  %-8s" col_w "Input" "Expected" "Got"
      "Correct"
  in
  print_endline header ;
  List.iter
    (fun (c : S.str) ->
      let exp = member c in
      let comp = accepts c in
      Printf.printf "%-*s  %-8b  %-8b  %s\n" col_w
        (Printf.sprintf "[%s]" (S.string_of_str c))
        exp comp
        ( if exp = comp then
            "Y"
          else
            "N" ) )
    strings ;
  let correct =
    List.length (List.filter (fun c -> member c = accepts c) strings)
  in
  Printf.printf "Accuracy: %d/%d\n" correct (List.length strings)

let report_dfa name dfa k =
  Printf.printf "\n=== %s ===\n" name ;
  print_endline "DFA found" ;
  DP.print_dfa dfa ;
  Printf.printf "DOT file at %s\n" (DP.to_dot ~name:(name ^ "_suffix") dfa) ;
  print_table (DTeacher.D.accept_string dfa) k

let report_nfa name nfa k =
  Printf.printf "\n=== %s ===\n" name ;
  print_endline "RFSA found" ;
  NP.print_nfa nfa ;
  Printf.printf "DOT file at %s\n" (NP.to_dot ~name:(name ^ "_suffix") nfa) ;
  print_table (NTeacher.R.N.accept_string nfa) k

let learned : __ NTeacher.R.t Lazy.t = lazy (NLstar.nlstar ())

module NLstarAdapter : NFALEARNER =
functor
  (T : NFATEACHER)
  ->
  struct
    let learn () : __ T.R.t = Obj.magic (Lazy.force learned)
  end

module GenHeader = Transmogrifier.Emit_header.MakeNFA (S)
module P = NFAPipeline (S) (NTeacher) (NLstarAdapter)

(** Compile the hand-built NFA to Clight and write it out as C, plus a header.

    [nstates] is a literal in the generated C and appears in no symbol, so the
    header cannot recover it -- it comes from the machine itself. *)
let compile_to_c () =
  let out = "examples/suffix.c" in
  let out_h = "examples/suffix.h" in
  Printf.printf "\n=== Compiling to C ===\n" ;
  ( match
      P.compile ~eq_dec:(Obj.magic ( = )) out
    with
  | Stdlib.Ok () ->
      Printf.printf "Wrote %s\n" out
  | Stdlib.Error e ->
      Printf.eprintf "Compilation failed: %s\n" e ) ;
  let nstates = List.length ((Lazy.force learned).states) in
  match
    GenHeader.fill_file ~machine_name:"suffix" ~nstates
      ~template_fn:"include/nfa.h.in" ~out_fn:out_h ()
  with
  | Stdlib.Ok () ->
      Printf.printf "Wrote %s (%d states, %d word(s) per set)\n" out_h nstates
        (GenHeader.nwords nstates)
  | Stdlib.Error e ->
      Printf.eprintf "Header generation failed: %s\n" e

let run_performance_test () =
  let test_size = 16 in
  print_endline "\n=== Generating OCaml Test Vector (suffix) ===" ;
  (* alternating a,b,a,b,... so the last two symbols are "ab" -> accepted *)
  let test_vector =
    List.init test_size (fun i -> if i mod 2 = 0 then S.A else S.B)
  in
  print_endline "=== OCaml Benchmark ===" ;
  let start_time = Sys.time () in
  let result = NTeacher.R.N.accept_string (Lazy.force learned) test_vector in
  let end_time = Sys.time () in
  Printf.printf "Processed Elements : %d\n" test_size ;
  Printf.printf "Accepted           : %b\n" result ;
  Printf.printf "Execution Time     : %.6f seconds\n" (end_time -. start_time)

let () =
  let dfa = Lstar.lstar () in
  let nfa = NLstar.nfa () in
  report_dfa "L*" dfa (n + 2) ;
  report_nfa "NL*" nfa (n + 2) ;
  let dfa_states, _ = DP.discover dfa in
  let nfa_states, _ = NP.discover nfa in
  Printf.printf "\n=== succinctness ===\n" ;
  Printf.printf "L_%d = Sigma* a Sigma^%d over {a, b}\n" n n ;
  Printf.printf "  minimal DFA     %d states (2^%d = %d)\n"
    (List.length dfa_states) (n + 1)
    (1 lsl (n + 1)) ;
  Printf.printf "  canonical RFSA  %d states (%d + 2 = %d)\n"
    (List.length nfa_states) n (n + 2);
  compile_to_c () ;
  run_performance_test ()
