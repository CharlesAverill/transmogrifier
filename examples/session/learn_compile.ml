open Lstar_Mealy
open Alphabet
open Mealy
open Specif
open Teacher
open Transmogrifier.Pipeline
open Stdlib

(** Input alphabet: one message opcode per symbol. *)
module S = struct
  type t = Hello | Auth | Request | Keepalive | Close

  let string_of_t = function
    | Hello ->
        "h"
    | Auth ->
        "a"
    | Request ->
        "r"
    | Keepalive ->
        "k"
    | Close ->
        "x"

  let t_of_string : string -> (t, string) Datatypes.result = function
    | "h" ->
        Ok Hello
    | "a" ->
        Ok Auth
    | "r" ->
        Ok Request
    | "k" ->
        Ok Keepalive
    | "x" ->
        Ok Close
    | _ ->
        Error "t_of_string"

  let eq_dec x y = x = y

  let enum = [Hello; Auth; Request; Keepalive; Close]

  type str = t list

  let string_of_str s = String.concat "" (List.map string_of_t s)
end

(** Output alphabet: the connection's disposition for one message. *)
module O = struct
  type t = Deny | Wait | Proceed | Grant | Bye

  let string_of_t = function
    | Deny ->
        "DENY"
    | Wait ->
        "WAIT"
    | Proceed ->
        "PROCEED"
    | Grant ->
        "GRANT"
    | Bye ->
        "BYE"

  let t_of_string : string -> (t, string) Datatypes.result = function
    | "DENY" ->
        Ok Deny
    | "WAIT" ->
        Ok Wait
    | "PROCEED" ->
        Ok Proceed
    | "GRANT" ->
        Ok Grant
    | "BYE" ->
        Ok Bye
    | _ ->
        Error "t_of_string"

  let eq_dec x y = x = y

  type str = t list

  let enum = [Deny; Wait; Proceed; Grant; Bye]
end

(** The wire encoding of a symbol for the legacy binary. AUTH is a
    length-prefixed token field; we always present the real secret so the
    authenticating edge is reachable. Other opcodes are a single byte. *)
let secret = "s3cr3t-handshake-key"

let bytes_of_sym : S.t -> string = function
  | S.Hello ->
      "h"
  | S.Auth ->
      "a" ^ String.make 1 (Char.chr (String.length secret)) ^ secret
  | S.Request ->
      "r"
  | S.Keepalive ->
      "k"
  | S.Close ->
      "x"

(** Path to the compiled legacy oracle, overridable via the environment. *)
let legacy_bin =
  match Sys.getenv_opt "SESSION_LEGACY" with
  | Some p ->
      p
  | None ->
      "./session_legacy"

(** Parse one disposition line printed by the legacy binary. *)
let out_of_line : string -> O.t option = function
  | "DENY" ->
      Some O.Deny
  | "WAIT" ->
      Some O.Wait
  | "PROCEED" ->
      Some O.Proceed
  | "GRANT" ->
      Some O.Grant
  | "BYE" ->
      Some O.Bye
  | _ ->
      None

(** Run the legacy binary on a word and collect one disposition per opcode. *)
let run_legacy_uncached (w : S.str) : O.t list =
  let inp = String.concat "" (List.map bytes_of_sym w) in
  let r_out, w_in = Unix.open_process legacy_bin in
  let acc = ref [] in
  ( try
      (* send the word and signal EOF so the child drains and exits *)
      output_string w_in inp ;
      flush w_in ;
      close_out w_in ;
      try
        while true do
          match out_of_line (input_line r_out) with
          | Some o ->
              acc := o :: !acc
          | None ->
              ()
        done
      with End_of_file -> ()
    with Sys_error _ | Unix.Unix_error _ -> () ) ;
  (* Always reap the child. [close_process] re-closes [w_in]; on some versions
     that raises Sys_error before the internal waitpid, which would leak a
     zombie and a pipe pair -- after a few thousand queries the fd table fills
     and the learner appears to hang. Swallow the error, then reap explicitly
     if needed. *)
  ( try ignore (Unix.close_process (r_out, w_in))
    with Sys_error _ | Unix.Unix_error _ -> (
      try ignore (Unix.wait ()) with Unix.Unix_error _ -> () ) ) ;
  List.rev !acc

(** Oracle results are memoized: L* asks the same word many times (once per
    observation-table cell, and again during equivalence checks), and every miss
    costs a fork+exec of the legacy binary. Without this the learner spends
    essentially all its wall time creating processes. *)
let oracle_cache : (S.str, O.t list) Hashtbl.t = Hashtbl.create 4096

let oracle_calls = ref 0

(** Set SESSION_TRACE=1 to watch oracle traffic; useful if the learner stalls. *)
let trace = Sys.getenv_opt "SESSION_TRACE" <> None

let run_legacy (w : S.str) : O.t list =
  match Hashtbl.find_opt oracle_cache w with
  | Some r ->
      r
  | None ->
      incr oracle_calls ;
      if trace then (
        Printf.eprintf "[oracle %4d] %s\n%!" !oracle_calls (S.string_of_str w) ) ;
      let r = run_legacy_uncached w in
      Hashtbl.add oracle_cache w r ;
      r

module Teacher : MEALYTEACHER with module S = S and module O = O = struct
  module S = S
  module O = O
  module M = Mealy (S) (O)

  (** Having already consumed [s], what disposition does reading [a] emit?
      That is the last disposition the oracle prints for the word [s @ [a]]. *)
  let output_lang (s : S.str) (a : S.t) : O.t =
    match List.rev (run_legacy (s @ [a])) with last :: _ -> last | [] -> O.Deny

  (** Breadth-first search for a word on which the hypothesis mispredicts.

      Bounded by word length rather than by a count of words dequeued: a count
      bound can stop part-way through a length and skip the word that
      distinguishes the hypothesis from the target, which either yields a wrong
      machine or leaves L* refining against a counterexample it never confirms.

      [max_len = 4] covers all 780 words of length <= 4 over the 5-symbol
      alphabet, the same coverage as the accuracy table below. Each candidate is
      an oracle query, but the cache makes repeats free. *)
  let equiv_query (m : 'a M.t) : S.str option =
    let max_len = 4 in
    let rec bfs (queue : S.str list) : S.str option =
      match queue with
      | [] ->
          None
      | s :: rest -> (
        match List.rev s with
        | [] ->
            (* empty word: nothing to compare; seed the frontier *)
            bfs (rest @ List.map (fun c -> [c]) S.enum)
        | a :: rprefix ->
            let prefix = List.rev rprefix in
            let hd, tl =
              match s with hd :: tl -> (hd, tl) | [] -> assert false
            in
            let mealy_out = M.last_output m hd tl in
            let spec_out = output_lang prefix a in
            if mealy_out <> spec_out then
              Some s
            else if List.length s >= max_len then
              bfs rest
            else
              let next_gen = List.map (fun c -> s @ [c]) S.enum in
              bfs (rest @ next_gen) )
    in
    bfs [[]]

  (** Round cap. The learner converges in a handful of rounds for a machine
      this size; the bound keeps a teacher bug from looping indefinitely. *)
  let fuel : int = 64
end

(** Mealy L* implementation *)
module Learner = MealyLstarLearner (Teacher)

let learned : __ Teacher.M.t Lazy.t = lazy (Learner.mlstar ())

module LstarAdapter : MEALYLEARNER =
functor
  (T : MEALYTEACHER)
  ->
  struct
    let learn () : __ T.M.t = Obj.magic (Lazy.force learned)
  end

(** Learn-then-compile pipeline for this teacher *)
module P = MealyPipeline (S) (O) (Teacher) (LstarAdapter)

(** Split a non-empty word into its prefix and final symbol *)
let unsnoc (s : S.str) : (S.str * S.t) option =
  match List.rev s with [] -> None | a :: rprefix -> Some (List.rev rprefix, a)

(** Generate all input sequences of length up to [n] *)
let rec enumerate (n : int) : S.str list =
  if n <= 0 then
    [[]]
  else
    let prev = enumerate (n - 1) in
    let prepend c l = List.map (fun s -> [c] @ s) l in
    [[]] @ List.concat_map (fun c -> prepend c prev) S.enum

let dedup l =
  List.fold_left
    (fun acc x -> if List.mem x acc then acc else x :: acc)
    [] l
  |> List.rev

(** Run the learned machine against the oracle on test cases and tabulate. *)
let print_results name m n =
  Printf.printf "\n=== %s ===\n" name ;
  print_endline "Mealy machine found" ;
  let strings =
    dedup (enumerate n) |> List.filter (fun (s : S.str) -> s <> [])
  in
  let col_w = max 16 (n + 2) in
  Printf.printf "%-*s  %-9s  %-9s  %s\n" col_w "Input" "Expected" "Got" "OK" ;
  List.iter
    (fun (c : S.str) ->
      match unsnoc c with
      | None ->
          ()
      | Some (prefix, a) ->
          let exp = Teacher.output_lang prefix a in
          let comp =
            match c with [] -> exp | hd :: tl -> Teacher.M.last_output m hd tl
          in
          Printf.printf "%-*s  %-9s  %-9s  %s\n" col_w
            (Printf.sprintf "[%s]" (S.string_of_str c))
            (O.string_of_t exp) (O.string_of_t comp)
            (if exp = comp then "Y" else "N") )
    strings ;
  let correct =
    List.length
      (List.filter
         (fun (c : S.str) ->
           match unsnoc c with
           | None ->
               true
           | Some (prefix, a) -> (
             match c with
             | [] ->
                 true
             | hd :: tl ->
                 Teacher.output_lang prefix a = Teacher.M.last_output m hd tl ) )
         strings )
  in
  Printf.printf "Accuracy: %d/%d\n" correct (List.length strings)

module GenHeader = Transmogrifier.Emit_header.MakeMoore (S) (O)

(** Path helpers: default to the repo-relative locations used by [dune exec]
    from the project root, but let a dune rule override them (sandbox CWD) via
    the environment. *)
let env_or key default =
  match Sys.getenv_opt key with Some v -> v | None -> default

(** Compile the learned Mealy machine to Clight (C) plus a header. *)
let compile_to_c () =
  let out = env_or "SESSION_OUT_C" "examples/session/session.c" in
  let out_h = env_or "SESSION_OUT_H" "examples/session/session.h" in
  let template = env_or "MEALY_H_TEMPLATE" "include/mealy.h.in" in
  Printf.printf "\n=== Compiling to C ===\n" ;
  ( match P.compile out with
  | Stdlib.Ok () ->
      Printf.printf "Wrote %s\n" out
  | Stdlib.Error e ->
      Printf.eprintf "Compilation failed: %s\n" e ) ;
  let nstates = Stdlib.List.length (Teacher.M.states (Lazy.force learned)) in
  match
    GenHeader.fill_file ~machine_name:"session" ~nstates
      ~template_fn:template ~out_fn:out_h ()
  with
  | Stdlib.Ok () ->
      Printf.printf "Wrote %s (%d states)\n" out_h nstates
  | Stdlib.Error e ->
      Printf.eprintf "Header generation failed: %s\n" e

let () =
  print_results "L* Session Handshake Validator" (Lazy.force learned) 4 ;
  compile_to_c ()
