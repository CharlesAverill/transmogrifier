(* Fill the .h.in templates. Placeholders are @UPPER@; unknown ones are left
   alone rather than silently blanked, so a typo shows up in the output. *)

open Stdlib.List

let c_ident_of_name (s : string) : string =
  let b = Buffer.create (String.length s + 8) in
  String.iter
    (fun c ->
      match c with
      | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' ->
          Buffer.add_char b c
      | _ ->
          Buffer.add_char b '_' )
    s ;
  let s' = Buffer.contents b in
  if s' = "" then
    "_"
  else if match s'.[0] with '0' .. '9' -> true | _ -> false then
    "_" ^ s'
  else
    s'

(* Sanitizing is not injective ("RED+YELLOW" vs "RED_YELLOW"), and a duplicate
   enumerator is a compile error in the emitted header rather than here. *)
let uniquify names =
  let seen = Hashtbl.create 16 in
  Stdlib.List.mapi
    (fun i n ->
      if Hashtbl.mem seen n then begin
        let n' = Printf.sprintf "%s_%d" n i in
        Hashtbl.replace seen n' () ; n'
      end else begin
        Hashtbl.replace seen n () ; n
      end )
    names

let subst (tbl : (string * string) list) (s : string) : string =
  List.fold_left
    (fun acc (k, v) ->
      Str.global_replace (Str.regexp_string ("@" ^ k ^ "@")) v acc )
    tbl s

module MakeMoore (S : Alphabet.Symbol) (O : Alphabet.Symbol) = struct
  (* An index is a position in the enum -- accept_entry is
     [index_of O.eq_dec (output q) O.enum 0] -- so mapi reproduces exactly the
     values accept returns, given the same enum the machine was compiled with. *)
  let render_enum ~prefix ~type_name ~count_doc (names : string list) : string =
    let p = String.uppercase_ascii (c_ident_of_name prefix) in
    let idents =
      uniquify
        (Stdlib.List.map
           (fun n -> String.uppercase_ascii (c_ident_of_name n))
           names )
    in
    let b = Buffer.create 512 in
    Buffer.add_string b "typedef enum {\n" ;
    iteri
      (fun i n ->
        Buffer.add_string b
          (Printf.sprintf "    %s_%s = %dULL, /* %S */\n" p
             ( if n.[0] = '_' && String.length n > 1 then
                 String.sub n 1 (String.length n - 1)
               else
                 n )
             i (Stdlib.List.nth names i) ) )
      idents ;
    Buffer.add_string b
      (Printf.sprintf "    %s_COUNT = %dULL /* %s */\n" p
         (Stdlib.List.length names) count_doc ) ;
    Buffer.add_string b (Printf.sprintf "} %s;" type_name) ;
    Buffer.contents b

  let symbol_enum () =
    render_enum ~prefix:"SYM" ~type_name:"input_sym_t"
      ~count_doc:"|Sigma|; delta's out-of-range threshold"
      (Stdlib.List.map S.string_of_t S.enum)

  let output_enum () =
    render_enum ~prefix:"OUT" ~type_name:"output_sym_t"
      ~count_doc:"|O|; accept_entry's out-of-range fallback"
      (Stdlib.List.map O.string_of_t O.enum)

  (* O.enum has no nodup guarantee (enum_nodup is commented out in Automata.v).
     index_of takes the first match, so a duplicate makes the emitted enumerator
     disagree with accept. Worth checking before emitting. *)
  let check (nstates : int) : (unit, string) result =
    let dup (type a) (eq : a -> a -> bool) (l : a list) name =
      let rec go i = function
        | [] ->
            Ok ()
        | x :: tl -> (
            let rec pos j = function
              | [] ->
                  None
              | y :: ys ->
                  if eq x y then
                    Some j
                  else
                    pos (j + 1) ys
            in
            match pos 0 l with
            | Some j when j = i ->
                go (i + 1) tl
            | Some j ->
                Error
                  (Printf.sprintf "%s: element %d duplicates element %d" name i
                     j )
            | None ->
                Error (Printf.sprintf "%s: element %d not found" name i) )
      in
      go 0 l
    in
    if nstates <= 0 then
      Error "machine has no states"
    else if S.enum = [] then
      Error "Sigma.enum is empty"
    else if O.enum = [] then
      Error "O.enum is empty; accept has no valid return"
    else
      match dup S.eq_dec S.enum "Sigma.enum" with
      | Error e ->
          Error e
      | Ok () ->
          dup O.eq_dec O.enum "O.enum"

  (** Fill [template] (contents of moore.h.in). [nstates] must be the length of
      the compiled machine's state list -- it is a literal in the generated C,
      recorded nowhere the header can read.

      [extra] is appended to the substitution table and wins over the defaults
      below, so a specialization (see [MakeDFA]) can rename or drop entries
      without rebuilding the list. *)
  let fill ?(extra = []) ~(machine_name : string) ~(nstates : int)
      (template : string) : string =
    subst
      ( extra
      @ [ ("MACHINE_NAME", machine_name)
        ; ("NSTATES", string_of_int nstates)
        ; ("NSYMS", string_of_int (Stdlib.List.length S.enum))
        ; ("NOUTS", string_of_int (Stdlib.List.length O.enum))
        ; ("SYMBOL_ENUM", symbol_enum ())
        ; ("OUTPUT_ENUM", output_enum ()) ] )
      template

  let fill_file ?(extra = []) ~machine_name ~nstates ~(template_fn : string)
      ~(out_fn : string) () : (unit, string) result =
    match check nstates with
    | Error e ->
        Error e
    | Ok () ->
        let ic = open_in_bin template_fn in
        let n = in_channel_length ic in
        let tmpl = really_input_string ic n in
        close_in ic ;
        let oc = open_out_bin out_fn in
        output_string oc (fill ~extra ~machine_name ~nstates tmpl) ;
        close_out oc ;
        Ok ()
end

(* A DFA is a Moore machine over bool, so the enums and dimensions come straight
   from MakeMoore. Only the *spelling* differs: the DFA header namespaces its
   types dfa_* rather than moore_*, and names the bool output alphabet
   TRUE/FALSE rather than the generic OUT_*. Those are the overrides here. *)
module MakeDFA (S : Alphabet.Symbol) = struct
  module O = struct
    type t = bool

    let eq_dec = ( = )

    let enum = [true; false]

    type str = t list

    (* Out.enum is [true; false], so index 0 is accepting and 1 is rejecting --
       the inversion the DFA header warns about. *)
    let string_of_t = string_of_bool

    let t_of_string : string -> (t, string) Datatypes.result = function
      | "true" ->
          Ok true
      | "false" ->
          Ok false
      | e ->
          Error ("Unrecognized bool " ^ e)
  end

  module MMoore = MakeMoore (S) (O)
  include MMoore

  (* Shadow MakeMoore's enums with DFA-flavoured names. *)
  let symbol_enum () =
    MMoore.render_enum ~prefix:"SYM" ~type_name:"dfa_input_sym_t"
      ~count_doc:"|Sigma|; delta's out-of-range threshold"
      (Stdlib.List.map S.string_of_t S.enum)

  let output_enum () =
    MMoore.render_enum ~prefix:"DFA" ~type_name:"dfa_bool"
      ~count_doc:"|O|; accept_entry's out-of-range fallback"
      (Stdlib.List.map O.string_of_t O.enum)

  let fill ~(machine_name : string) ~(nstates : int) (template : string) :
      string =
    MMoore.fill
      ~extra:[("SYMBOL_ENUM", symbol_enum ()); ("OUTPUT_ENUM", output_enum ())]
      ~machine_name ~nstates template

  let fill_file ~machine_name ~nstates ~template_fn ~out_fn =
    MMoore.fill_file
      ~extra:[("SYMBOL_ENUM", symbol_enum ()); ("OUTPUT_ENUM", output_enum ())]
      ~machine_name ~nstates ~template_fn ~out_fn
end

(* An NFA has no output alphabet -- acceptance is a set intersection, not an
   output symbol -- so MakeNFA takes only the input alphabet. It reuses
   MakeMoore's machinery by pairing S with a dummy one-element output, which is
   never rendered: nfa.h.in has no @OUTPUT_ENUM@ placeholder.

   The one genuinely new substitution is @NWORDS@, the width of a state set. *)
module MakeNFA (S : Alphabet.Symbol) = struct
  module O = struct
    type t = unit

    let eq_dec = ( = )

    let enum = [()]

    type str = t list

    let string_of_t () = "unit"

    let t_of_string : string -> (t, string) Datatypes.result = function
      | "unit" -> Ok ()
      | e -> Error ("Unrecognized unit " ^ e)
  end

  module MMoore = MakeMoore (S) (O)
  include MMoore

  (* ceil(nstates / 64), at least 1 -- must track [nwords] in
     theories/compiler/nfa.v. *)
  let nwords (nstates : int) : int =
    if nstates <= 0 then 1 else max 1 ((nstates + 63) / 64)

  let symbol_enum () =
    MMoore.render_enum ~prefix:"SYM" ~type_name:"nfa_input_sym_t"
      ~count_doc:"|Sigma|; step's out-of-range threshold"
      (Stdlib.List.map S.string_of_t S.enum)

  let fill ~(machine_name : string) ~(nstates : int) (template : string) :
      string =
    MMoore.fill
      ~extra:
        [ ("SYMBOL_ENUM", symbol_enum ())
        ; ("NWORDS", string_of_int (nwords nstates)) ]
      ~machine_name ~nstates template

  let fill_file ~machine_name ~nstates ~template_fn ~out_fn =
    MMoore.fill_file
      ~extra:
        [ ("SYMBOL_ENUM", symbol_enum ())
        ; ("NWORDS", string_of_int (nwords nstates)) ]
      ~machine_name ~nstates ~template_fn ~out_fn
end
