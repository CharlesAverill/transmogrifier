open Lstar_DFA
open Alphabet
open DFA
open Specif
open Teacher
open Transmogrifier.Pipeline
open Stdlib

(** Alphabet: decimal digits *)
module S = struct
  type t = D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8 | D9

  let all = [D0; D1; D2; D3; D4; D5; D6; D7; D8; D9]

  let to_int = function
    | D0 ->
        0
    | D1 ->
        1
    | D2 ->
        2
    | D3 ->
        3
    | D4 ->
        4
    | D5 ->
        5
    | D6 ->
        6
    | D7 ->
        7
    | D8 ->
        8
    | D9 ->
        9

  let of_int : int -> (t, string) Datatypes.result = function
    | 0 ->
        Ok D0
    | 1 ->
        Ok D1
    | 2 ->
        Ok D2
    | 3 ->
        Ok D3
    | 4 ->
        Ok D4
    | 5 ->
        Ok D5
    | 6 ->
        Ok D6
    | 7 ->
        Ok D7
    | 8 ->
        Ok D8
    | 9 ->
        Ok D9
    | _ ->
        Error "of_int"

  let string_of_t t = string_of_int (to_int t)

  let t_of_string s : (t, string) Datatypes.result =
    match int_of_string_opt s with
    | None ->
        Error "t_of_string"
    | Some d ->
        of_int d

  let eq_dec x y = x = y

  let enum = all

  type str = t list

  let string_of_str s = String.concat "" (List.map string_of_t s)
end

(** Language: decimal strings (with leading zeros) whose numeric value is
    divisible by 7. The minimal DFA has exactly 7 states - one per residue
    class mod 7. The transition on reading digit d from state r is:
        r' = (r * 10 + d) mod 7
    which is the standard streaming divisibility DFA. *)
module Teacher : DFATEACHER with module S = S = struct
  module S = S
  module D = DFA (S)

  let member (s : S.str) : bool =
    match s with
    | [] ->
        false
    | _ ->
        let value = List.fold_left (fun acc d -> (acc * 10) + S.to_int d) 0 s in
        value mod 7 = 0

  let equiv_query (dfa : 'a D.t) : S.str option =
    let rec bfs depth queue =
      if depth >= 4096 then
        None
      else
        match queue with
        | [] ->
            None
        | s :: rest ->
            if D.accept_string dfa s <> member s then
              Some s
            else
              let children = List.map (fun c -> s @ [c]) S.enum in
              bfs (depth + 1) (rest @ children)
    in
    bfs 0 [[]]

  let fuel = Int.max_int
end

(** L* implementation *)
module Lstar = LstarLearner (Teacher)

(** The learned DFA, computed once and shared by the printer and the
    compiler.  [Pipeline] caches its own learner run, so going through
    [Pipeline.compile] directly would learn a second time. *)
let learned : __ Teacher.D.t Lazy.t = lazy (Lstar.lstar ())

(** [LstarLearner] exposes [lstar]; [LEARNER] asks for [learn].  This adapter
    also pins the result to [learned] so the compiled automaton is exactly
    the one printed above. *)
module LstarAdapter : DFALEARNER =
functor
  (T : DFATEACHER)
  ->
  struct
    let learn () : __ T.D.t = Obj.magic (Lazy.force learned)
  end

(** Learn-then-compile pipeline for this teacher *)
module P = DFAPipeline (S) (Teacher) (LstarAdapter)

module DP = DFAPrinter (Teacher)

(** All digit strings of exactly length [n] *)
let rec enumerate_exact n =
  if n = 0 then
    [[]]
  else
    let prev = enumerate_exact (n - 1) in
    List.concat_map (fun d -> List.map (fun s -> d :: s) prev) S.enum

(** Collect interesting multiples of 7 for display *)
let interesting_cases =
  let nums = [0; 7; 14; 21; 35; 42; 49; 56; 63; 70; 77; 84; 91; 98] in
  List.map
    (fun n ->
      let s = string_of_int n in
      String.to_seq s
      |> Seq.map (fun c ->
          match c with
          | '0' ->
              S.D0
          | '1' ->
              S.D1
          | '2' ->
              S.D2
          | '3' ->
              S.D3
          | '4' ->
              S.D4
          | '5' ->
              S.D5
          | '6' ->
              S.D6
          | '7' ->
              S.D7
          | '8' ->
              S.D8
          | _ ->
              S.D9 )
      |> List.of_seq )
    nums

let print_results name dfa =
  Printf.printf "\n=== %s ===\n" name ;
  print_endline "DFA found" ;
  DP.print_dfa dfa ;
  Printf.printf "DOT file at %s\n" (DP.to_dot ~name:(name ^ "_div7") dfa) ;
  let multiples = interesting_cases @ [[S.D0; S.D7]] in
  let non_multiples =
    List.filteri
      (fun i _ -> i < 8)
      (List.filter (fun s -> not (Teacher.member s)) (enumerate_exact 2))
  in
  let cases = multiples @ non_multiples in
  let col_w = 12 in
  let header =
    Printf.sprintf "%-*s  %-8s  %-8s  %-8s" col_w "Input" "Expected" "Got"
      "Correct"
  in
  print_endline header ;
  List.iter
    (fun (c : S.str) ->
      let exp = Teacher.member c in
      let comp = Teacher.D.accept_string dfa c in
      Printf.printf "%-*s  %-8b  %-8b  %s\n" col_w (S.string_of_str c) exp comp
        ( if exp = comp then
            "Y"
          else
            "N" ) )
    cases ;
  let correct =
    List.length
      (List.filter
         (fun (c : S.str) -> Teacher.member c = Teacher.D.accept_string dfa c)
         cases )
  in
  Printf.printf "Accuracy: %d/%d\n" correct (List.length cases)

module GenHeader = Transmogrifier.Emit_header.MakeDFA (S)

(** Compile the learned DFA to Clight and write it out as C, plus a header *)
let compile_to_c () =
  let out = "examples/div7.c" in
  let out_h = "examples/div7.h" in
  Printf.printf "\n=== Compiling to C ===\n" ;
  ( match P.compile out with
  | Stdlib.Ok () ->
      Printf.printf "Wrote %s\n" out
  | Stdlib.Error e ->
      Printf.eprintf "Compilation failed: %s\n" e ) ;
  let nstates = Stdlib.List.length (Teacher.D.states (Lazy.force learned)) in
  match
    GenHeader.fill_file ~machine_name:"div7" ~nstates
      ~template_fn:"include/dfa.h.in" ~out_fn:out_h ()
  with
  | Stdlib.Ok () ->
      Printf.printf "Wrote %s (%d states)\n" out_h nstates
  | Stdlib.Error e ->
      Printf.eprintf "Header generation failed: %s\n" e

let run_performance_test () =
  let dfa = Lazy.force learned in
  let test_size = 1_000_000 in
  
  print_endline "\n=== Generating OCaml Test Vector ===";
  (* Constructing an identical stream sequence *)
  let rec gen_vector i acc =
    if i < 0 then acc
    else
      let digit_int = (i * 3 + 1) mod 10 in
      let digit = match S.of_int digit_int with Ok d -> d | Error _ -> S.D0 in
      gen_vector (i - 1) (digit :: acc)
  in
  let test_vector = gen_vector (test_size - 1) [] in

  print_endline "=== OCaml Benchmark ===";
  let start_time = Sys.time () in
  let result = Teacher.D.accept_string dfa test_vector in
  let end_time = Sys.time () in

  Printf.printf "Processed Elements : %d\n" test_size;
  Printf.printf "Accepted           : %b\n" result;
  Printf.printf "Execution Time     : %.6f seconds\n" (end_time -. start_time)

let () =
  print_results "L*" (Lazy.force learned) ;
  compile_to_c ();
  run_performance_test ()
