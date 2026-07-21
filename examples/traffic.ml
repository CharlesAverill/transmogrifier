(* European-style 4-phase traffic light *)

open Lstar
open Alphabet
open Moore
open Specif
open Teacher
open Transmogrifier.Pipeline
open Stdlib

(** Input alphabet: a clock [Tick] and a [Reset] line *)
module S = struct
  type t = Tick | Reset

  let string_of_t = function Tick -> "t" | Reset -> "r"

  let t_of_string : string -> (t, string) Datatypes.result = function
    | "t" ->
        Ok Tick
    | "r" ->
        Ok Reset
    | _ ->
        Error "t_of_string"

  let eq_dec x y = x = y

  let enum = [Tick; Reset]

  type str = t list

  let string_of_str s = String.concat "" (List.map string_of_t s)
end

(** Output alphabet: the light state *)
module O = struct
  type t = Red | Green | Yellow | RedYellow

  let string_of_t = function
    | Red ->
        "RED"
    | Green ->
        "GREEN"
    | Yellow ->
        "YELLOW"
    | RedYellow ->
        "RED+YELLOW"

  let t_of_string : string -> (t, string) Datatypes.result = function
    | "RED" ->
        Ok Red
    | "GREEN" ->
        Ok Green
    | "YELLOW" ->
        Ok Yellow
    | "RED+YELLOW" ->
        Ok RedYellow
    | _ ->
        Error "t_of_string"

  let eq_dec x y = x = y

  type str = t list

  let enum = [Red; Green; Yellow; RedYellow]
end

module Teacher : MOORETEACHER with module S = S and module O = O = struct
  module S = S
  module O = O
  module M = Moore (S) (O)

  (** Phases cycle on [Tick]:
        Red -> Red+Yellow -> Green -> Yellow -> Red -> ...
      [Reset] forces the lamp back to Red *)
  let output_lang (s : S.str) : O.t =
    let phase =
      List.fold_left
        (fun p -> function S.Reset -> 0 | S.Tick -> (p + 1) mod 4)
        0 s
    in
    [|O.Red; O.RedYellow; O.Green; O.Yellow|].(phase)

  let equiv_query (m : 'a M.t) : S.str option =
    let rec find_counter_example depth current_strings =
      if depth >= int_of_float (2. ** 12.) then
        None
      else
        match current_strings with
        | [] ->
            None
        | s :: rest ->
            let moore_out = M.output_string m s in
            let spec_out = output_lang s in
            if moore_out <> spec_out then
              Some s
            else
              let next_gen = List.map (fun c -> s @ [c]) [S.Tick; S.Reset] in
              find_counter_example (depth + 1) (rest @ next_gen)
    in
    find_counter_example 0 [[]]

  let fuel : int = Int.max_int
end

(** Moore L* implementation *)
module Learner = MooreLstarLearner (Teacher)

let learned : __ Teacher.M.t Lazy.t = lazy (Learner.mlstar ())

module LstarAdapter : MOORELEARNER =
functor
  (T : MOORETEACHER)
  ->
  struct
    let learn () : __ T.M.t = Obj.magic (Lazy.force learned)
  end

(** Learn-then-compile pipeline for this teacher *)
module P = MoorePipeline (S) (O) (Teacher) (LstarAdapter)

module MP = MoorePrinter (Teacher)

(** Generate all input sequences of length up to [n] *)
let rec enumerate (n : int) : S.str list =
  if n <= 0 then
    [[]]
  else
    let prev = enumerate (n - 1) in
    let prepend c l = List.map (fun s -> [c] @ s) l in
    [[]] @ prepend S.Tick prev @ prepend S.Reset prev

let dedup l =
  List.fold_left
    (fun acc x ->
      if List.mem x acc then
        acc
      else
        x :: acc )
    [] l
  |> List.rev

(** Run the learned controller on test cases and pretty-print results *)
let print_results name m n =
  Printf.printf "\n=== %s ===\n" name ;
  print_endline "Moore machine found" ;
  MP.print_moore m ;
  Printf.printf "DOT file at %s\n" (MP.to_dot ~name:(name ^ "_traffic") m) ;
  let strings = dedup (enumerate n) in
  let col_w = max 12 (n + 2) in
  let header =
    Printf.sprintf "%-*s  %-11s  %-11s  %-8s" col_w "Input" "Expected" "Got"
      "Correct"
  in
  print_endline header ;
  List.iter
    (fun (c : S.str) ->
      let exp = Teacher.output_lang c in
      let comp = Teacher.M.output_string m c in
      Printf.printf "%-*s  %-11s  %-11s  %s\n" col_w
        (Printf.sprintf "[%s]" (S.string_of_str c))
        (O.string_of_t exp) (O.string_of_t comp)
        ( if exp = comp then
            "Y"
          else
            "N" ) )
    strings ;
  let correct =
    List.length
      (List.filter
         (fun (c : S.str) -> Teacher.output_lang c = Teacher.M.output_string m c)
         strings )
  in
  Printf.printf "Accuracy: %d/%d\n" correct (List.length strings)

module GenHeader = Transmogrifier.Emit_header.MakeMoore (S) (O)

(** Compile the learned DFA to Clight and write it out as C, plus a header *)
let compile_to_c () =
  let out = "examples/traffic.c" in
  let out_h = "examples/traffic.h" in
  Printf.printf "\n=== Compiling to C ===\n" ;
  ( match P.compile out with
  | Stdlib.Ok () ->
      Printf.printf "Wrote %s\n" out
  | Stdlib.Error e ->
      Printf.eprintf "Compilation failed: %s\n" e ) ;
  let nstates = Stdlib.List.length (Teacher.M.states (Lazy.force learned)) in
  match
    GenHeader.fill_file ~machine_name:"traffic" ~nstates
      ~template_fn:"include/moore.h.in" ~out_fn:out_h ()
  with
  | Stdlib.Ok () ->
      Printf.printf "Wrote %s (%d states)\n" out_h nstates
  | Stdlib.Error e ->
      Printf.eprintf "Header generation failed: %s\n" e

let run_performance_test () =
  let dfa = Lazy.force learned in
  let test_size = 1_000_000 in
  
  print_endline "\n=== Generating OCaml Test Vector (traffic) ===";
  let rec gen_vector i acc =
    if i < 0 then acc
    else
      let phase_int = i mod 4 in
      let symbol = match phase_int with 0 -> S.Reset | _ -> S.Tick in
      gen_vector (i - 1) (symbol :: acc)
  in
  let test_vector = gen_vector (test_size - 1) [] in

  print_endline "=== OCaml Benchmark ===";
  let start_time = Sys.time () in
  let result = Teacher.M.output_string dfa test_vector in
  let end_time = Sys.time () in

  Printf.printf "Processed Elements : %d\n" test_size;
  Printf.printf "Final State        : %s\n" (O.string_of_t result);
  Printf.printf "Execution Time     : %.6f seconds\n" (end_time -. start_time)

let () =
  print_results "L* Traffic Light Controller" (Lazy.force learned) 4;
  compile_to_c ();
  run_performance_test ()
