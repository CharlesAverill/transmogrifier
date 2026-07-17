open Lstar
open Automata
open Specif
open Teacher
open Transmogrifier.Pipeline
open Stdlib

(** Alphabet *)
module S = struct
  type t = Zero | One

  let string_of_t = function Zero -> "0" | One -> "1"

  let t_of_string : string -> (t, string) Datatypes.result = function
    | "0" ->
        Ok Zero
    | "1" ->
        Ok One
    | _ ->
        Error "t_of_string"

  let eq_dec x y = x = y

  let enum = [Zero; One]

  type str = t list

  let string_of_str s = String.concat "" (List.map string_of_t s)
end

module Teacher : DFATEACHER with module S = S = struct
  module S = S
  module D = DFA (S)

  (** Language membership: the string is "alternating" *)
  let member (s : S.str) : bool =
    match s with
    | [] ->
        true
    | h :: t ->
        snd
          (List.fold_left
             (fun (last, mem) i -> (i, mem && last <> i))
             (h, true) t )

  (** Teacher equivalence query, typed against D.t (not a fresh DFA(S)) *)
  let equiv_query (dfa : 'a D.t) : S.str option =
    let rec find_counter_example depth current_strings =
      if depth >= int_of_float (2. ** 12.) then
        None
      else
        match current_strings with
        | [] ->
            None
        | s :: rest ->
            let dfa_acc = D.accept_string dfa s in
            let spec_acc = member s in
            if dfa_acc <> spec_acc then
              Some s
            else
              let next_gen = List.map (fun c -> s @ [c]) [S.Zero; S.One] in
              find_counter_example (depth + 1) (rest @ next_gen)
    in
    find_counter_example 0 [[]]

  let fuel : int = Int.max_int
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

(** Generate all bit strings of length [n] *)
let rec enumerate (n : int) : S.str list =
  if n <= 0 then
    [[]]
  else
    let prev = enumerate (n - 1) in
    let prepend c l = List.map (fun s -> [c] @ s) l in
    prepend S.Zero prev @ prepend S.One prev

(** Run the DFA on test cases and pretty-print the results *)
let print_results name dfa n =
  Printf.printf "\n=== %s ===\n" name ;
  print_endline "DFA found" ;
  DP.print_dfa dfa ;
  Printf.printf "DOT file at %s\n" (DP.to_dot ~name:(name ^ "_alternating") dfa) ;
  let strings = enumerate n in
  let col_w = max 10 (n + 2) in
  let header =
    Printf.sprintf "%-*s  %-8s  %-8s  %-8s" col_w "Input" "Expected" "Got"
      "Correct"
  in
  print_endline header ;
  List.iter
    (fun (c : S.str) ->
      let exp = Teacher.member c in
      let comp = Teacher.D.accept_string dfa c in
      Printf.printf "%-*s  %-8b  %-8b  %s\n" col_w
        (Printf.sprintf "[%s]" (S.string_of_str c))
        exp comp
        ( if exp = comp then
            "Y"
          else
            "N" ) )
    strings ;
  let correct =
    List.length
      (List.filter
         (fun (c : S.str) -> Teacher.member c = Teacher.D.accept_string dfa c)
         strings )
  in
  Printf.printf "Accuracy: %d/%d\n" correct (List.length strings)

(** Compile the learned DFA to Clight and write it out as C. *)
let compile_to_c () =
  let out = "examples/alternating.c" in
  Printf.printf "\n=== Compiling to C ===\n" ;
  match P.compile out with
  | Stdlib.Ok () ->
      Printf.printf "Wrote %s\n" out
  | Stdlib.Error e ->
      Printf.eprintf "Compilation failed: %s\n" e

let () =
  print_results "L*" (Lazy.force learned) 3 ;
  compile_to_c ()
