(** Convert Cminor ASTs to Rocq source files *)

let prog_to_rocq (emit_prog : Buffer.t -> unit) : string =
  let b = Buffer.create 4096 in
  Buffer.add_string b "Require Import ImportPrelude.\n" ;
  Buffer.add_string b "Local Open Scope positive.\n" ;
  Buffer.add_string b "Definition prog : program :=\n\t" ;
  emit_prog b ;
  Buffer.add_string b ".\n" ;
  Buffer.contents b

let a0 b ctor = Buffer.add_string b ctor

let a1 b ctor fa a =
  Buffer.add_char b '(' ;
  Buffer.add_string b ctor ;
  Buffer.add_char b ' ' ;
  fa b a ;
  Buffer.add_char b ')'

let a2 b ctor fa a fb x =
  Buffer.add_char b '(' ;
  Buffer.add_string b ctor ;
  Buffer.add_char b ' ' ;
  fa b a ;
  Buffer.add_char b ' ' ;
  fb b x ;
  Buffer.add_char b ')'

let a3 b ctor fa a fb x fc y =
  Buffer.add_char b '(' ;
  Buffer.add_string b ctor ;
  Buffer.add_char b ' ' ;
  fa b a ;
  Buffer.add_char b ' ' ;
  fb b x ;
  Buffer.add_char b ' ' ;
  fc b y ;
  Buffer.add_char b ')'

let a4 b ctor fa a fb x fc y fd z =
  Buffer.add_char b '(' ;
  Buffer.add_string b ctor ;
  Buffer.add_char b ' ' ;
  fa b a ;
  Buffer.add_char b ' ' ;
  fb b x ;
  Buffer.add_char b ' ' ;
  fc b y ;
  Buffer.add_char b ' ' ;
  fd b z ;
  Buffer.add_char b ')'

let emit_string b (s : string) =
  let buf = Buffer.create (String.length s + 2) in
  String.iter
    (fun c ->
      if c = '"' then
        Buffer.add_string buf "\"\""
      else
        Buffer.add_char buf c )
    s ;
  Buffer.add_char b '"' ;
  Buffer.add_buffer b buf ;
  Buffer.add_char b '"'

let emit_option fa b = function
  | None ->
      a0 b "None"
  | Some x ->
      a1 b "Some" fa x

let emit_pair fa fb b (x, y) =
  Buffer.add_char b '(' ;
  fa b x ;
  Buffer.add_string b ", " ;
  fb b y ;
  Buffer.add_char b ')'

let emit_list_tail fa b (xs : 'a list) (tail : string) =
  Buffer.add_char b '(' ;
  List.iter (fun x -> fa b x ; Buffer.add_string b " :: ") xs ;
  Buffer.add_string b tail ;
  Buffer.add_char b ')'

let emit_list fa b xs = emit_list_tail fa b xs "nil"

let rec int_of_positive = function
  | BinNums.Coq_xH ->
      1
  | BinNums.Coq_xO p ->
      2 * int_of_positive p
  | BinNums.Coq_xI p ->
      (2 * int_of_positive p) + 1

let int_of_z = function
  | BinNums.Z0 ->
      0
  | BinNums.Zpos p ->
      int_of_positive p
  | BinNums.Zneg p ->
      -int_of_positive p

let rec int_of_nat = function
  | Datatypes.O ->
      0
  | Datatypes.S n ->
      1 + int_of_nat n

let z_of_int (i : Integers.Int.int) = i

let z_of_int64 (i : Integers.Int64.int) = i

let emit_signed_repr b (ctor : string) (n : int) =
  if n < 0 then (
    Buffer.add_string b ("(" ^ ctor ^ " (") ;
    Buffer.add_string b (string_of_int n) ;
    Buffer.add_string b "))"
  ) else (
    Buffer.add_string b ("(" ^ ctor ^ " ") ;
    Buffer.add_string b (string_of_int n) ;
    Buffer.add_char b ')'
  )

let emit_int b i = emit_signed_repr b "Int.repr" (int_of_z (z_of_int i))

let emit_int64 b i = emit_signed_repr b "Int64.repr" (int_of_z (z_of_int64 i))

let emit_ptrofs b (p : BinNums.coq_Z) =
  emit_signed_repr b "Ptrofs.repr" (int_of_z p)

let emit_positive b p = Buffer.add_string b (string_of_int (int_of_positive p))

let emit_z b z =
  let n = int_of_z z in
  if n < 0 then (
    Buffer.add_char b '(' ;
    Buffer.add_string b (string_of_int n) ;
    Buffer.add_char b ')'
  ) else
    Buffer.add_string b (string_of_int n)

let emit_nat b n = Buffer.add_string b (string_of_int (int_of_nat n))

let emit_float (_ : Buffer.t) (_ : Floats.float) : unit =
  failwith "emit_float: float printing not implemented"

let emit_float32 (_ : Buffer.t) (_ : Floats.float32) : unit =
  failwith "emit_float32: float32 printing not implemented"

let emit_bool b = function true -> a0 b "true" | false -> a0 b "false"

let emit_comparison b (c : Integers.comparison) =
  a0 b
    ( match c with
    | Integers.Ceq ->
        "Ceq"
    | Integers.Cne ->
        "Cne"
    | Integers.Clt ->
        "Clt"
    | Integers.Cle ->
        "Cle"
    | Integers.Cgt ->
        "Cgt"
    | Integers.Cge ->
        "Cge" )

let emit_typ b (t : AST.typ) =
  a0 b
    ( match t with
    | AST.Tint ->
        "Tint"
    | AST.Tfloat ->
        "Tfloat"
    | AST.Tlong ->
        "Tlong"
    | AST.Tsingle ->
        "Tsingle"
    | AST.Tany32 ->
        "Tany32"
    | AST.Tany64 ->
        "Tany64" )

let emit_xtype b (x : AST.xtype) =
  a0 b
    ( match x with
    | AST.Xbool ->
        "Xbool"
    | AST.Xint8signed ->
        "Xint8signed"
    | AST.Xint8unsigned ->
        "Xint8unsigned"
    | AST.Xint16signed ->
        "Xint16signed"
    | AST.Xint16unsigned ->
        "Xint16unsigned"
    | AST.Xint ->
        "Xint"
    | AST.Xlong ->
        "Xlong"
    | AST.Xfloat ->
        "Xfloat"
    | AST.Xsingle ->
        "Xsingle"
    | AST.Xptr ->
        "Xptr"
    | AST.Xany32 ->
        "Xany32"
    | AST.Xany64 ->
        "Xany64"
    | AST.Xvoid ->
        "Xvoid" )

let emit_memory_chunk b (c : AST.memory_chunk) =
  a0 b
    ( match c with
    | AST.Mbool ->
        "Mbool"
    | AST.Mint8signed ->
        "Mint8signed"
    | AST.Mint8unsigned ->
        "Mint8unsigned"
    | AST.Mint16signed ->
        "Mint16signed"
    | AST.Mint16unsigned ->
        "Mint16unsigned"
    | AST.Mint32 ->
        "Mint32"
    | AST.Mint64 ->
        "Mint64"
    | AST.Mfloat32 ->
        "Mfloat32"
    | AST.Mfloat64 ->
        "Mfloat64"
    | AST.Many32 ->
        "Many32"
    | AST.Many64 ->
        "Many64" )

let emit_callconv b (cc : AST.calling_convention) =
  Buffer.add_char b '(' ;
  Buffer.add_string b "mkcallconv" ;
  Buffer.add_char b ' ' ;
  emit_option emit_z b cc.AST.cc_vararg ;
  Buffer.add_char b ' ' ;
  emit_bool b cc.AST.cc_unproto ;
  Buffer.add_char b ' ' ;
  emit_bool b cc.AST.cc_structret ;
  Buffer.add_char b ')'

let emit_signature b (s : AST.signature) =
  Buffer.add_char b '(' ;
  Buffer.add_string b "mksignature" ;
  Buffer.add_char b ' ' ;
  emit_list emit_xtype b s.AST.sig_args ;
  Buffer.add_char b ' ' ;
  emit_xtype b s.AST.sig_res ;
  Buffer.add_char b ' ' ;
  emit_callconv b s.AST.sig_cc ;
  Buffer.add_char b ')'

let emit_unop b (u : Clight.unary_operation) =
  let open Clight in
  a0 b
    ( match u with
    | Ocast8unsigned ->
        "Ocast8unsigned"
    | Ocast8signed ->
        "Ocast8signed"
    | Ocast16unsigned ->
        "Ocast16unsigned"
    | Ocast16signed ->
        "Ocast16signed"
    | Onegint ->
        "Onegint"
    | Onotint ->
        "Onotint"
    | Onegf ->
        "Onegf"
    | Oabsf ->
        "Oabsf"
    | Onegfs ->
        "Onegfs"
    | Oabsfs ->
        "Oabsfs"
    | Osingleoffloat ->
        "Osingleoffloat"
    | Ofloatofsingle ->
        "Ofloatofsingle"
    | Ointoffloat ->
        "Ointoffloat"
    | Ointuoffloat ->
        "Ointuoffloat"
    | Ofloatofint ->
        "Ofloatofint"
    | Ofloatofintu ->
        "Ofloatofintu"
    | Olongofint ->
        "Olongofint"
    | Olongofintu ->
        "Olongofintu"
    | Ointoflong ->
        "Ointoflong"
    | _ ->
        failwith "emit_unop: unhandled unary_operation" )

(* binary ops: most Debug==ctor, but comparisons carry a comparison arg *)
let emit_binop b (op : Cminor.binary_operation) =
  let open Cminor in
  match op with
  | Ocmp c ->
      a1 b "Ocmp" emit_comparison c
  | Ocmpu c ->
      a1 b "Ocmpu" emit_comparison c
  | Ocmpf c ->
      a1 b "Ocmpf" emit_comparison
        c (* NB: Rust had a typo "OcmOcmpfpu"; corrected *)
  | Ocmpfs c ->
      a1 b "Ocmpfs" emit_comparison c
  | Ocmpl c ->
      a1 b "Ocmpl" emit_comparison c
  | Ocmplu c ->
      a1 b "Ocmplu" emit_comparison c
  | Oadd ->
      a0 b "Oadd"
  | Osub ->
      a0 b "Osub"
  | Omul ->
      a0 b "Omul"
  | Odiv ->
      a0 b "Odiv"
  | Odivu ->
      a0 b "Odivu"
  | Omod ->
      a0 b "Omod"
  | Omodu ->
      a0 b "Omodu"
  | Oand ->
      a0 b "Oand"
  | Oor ->
      a0 b "Oor"
  | Oxor ->
      a0 b "Oxor"
  | Oshl ->
      a0 b "Oshl"
  | Oshr ->
      a0 b "Oshr"
  | Oshru ->
      a0 b "Oshru"
  | Oaddl ->
      a0 b "Oaddl"
  | Osubl ->
      a0 b "Osubl"
  | Omull ->
      a0 b "Omull"
  | Odivl ->
      a0 b "Odivl"
  | Odivlu ->
      a0 b "Odivlu"
  | Omodl ->
      a0 b "Omodl"
  | Omodlu ->
      a0 b "Omodlu"
  | Oandl ->
      a0 b "Oandl"
  | Oorl ->
      a0 b "Oorl"
  | Oxorl ->
      a0 b "Oxorl"
  | Oshll ->
      a0 b "Oshll"
  | Oshrl ->
      a0 b "Oshrl"
  | Oshrlu ->
      a0 b "Oshrlu"
  | Oaddf ->
      a0 b "Oaddf"
  | Osubf ->
      a0 b "Osubf"
  | Omulf ->
      a0 b "Omulf"
  | Odivf ->
      a0 b "Odivf"
  | Oaddfs ->
      a0 b "Oaddfs"
  | Osubfs ->
      a0 b "Osubfs"
  | Omulfs ->
      a0 b "Omulfs"
  | Odivfs ->
      a0 b "Odivfs"

let emit_constant b (c : Cminor.constant) =
  match c with
  | Cminor.Ointconst x ->
      a1 b "Ointconst" emit_int x
  | Cminor.Ofloatconst x ->
      a1 b "Ofloatconst" emit_float x
  | Cminor.Osingleconst x ->
      a1 b "Osingleconst" emit_float32 x
  | Cminor.Olongconst x ->
      a1 b "Olongconst" emit_int64 x
  | Cminor.Oaddrsymbol (id, ofs) ->
      a2 b "Oaddrsymbol" emit_positive id emit_ptrofs ofs
  | Cminor.Oaddrstack x ->
      a1 b "Oaddrstack" emit_ptrofs x

let rec emit_expr b (e : Cminor.expr) =
  match e with
  | Cminor.Evar x ->
      a1 b "Evar" emit_positive x
  | Cminor.Econst c ->
      a1 b "Econst" emit_constant c
  | Cminor.Eunop (u, a) ->
      a2 b "Eunop" emit_unop u emit_expr a
  | Cminor.Ebinop (op, a1', a2') ->
      a3 b "Ebinop" emit_binop op emit_expr a1' emit_expr a2'
  | Cminor.Eload (c, a) ->
      a2 b "Eload" emit_memory_chunk c emit_expr a

let emit_label b (l : BinNums.positive) = emit_positive b l (* Label = ident *)

let string_of_chars chars = String.of_seq (List.to_seq chars)

let rec emit_stmt b (s : Cminor.stmt) =
  match s with
  | Cminor.Sskip ->
      a0 b "Sskip"
  | Cminor.Sassign (id, e) ->
      a2 b "Sassign" emit_positive id emit_expr e
  | Cminor.Sstore (c, a, v) ->
      a3 b "Sstore" emit_memory_chunk c emit_expr a emit_expr v
  | Cminor.Scall (optret, sg, f, args) ->
      a4 b "Scall"
        (emit_option emit_positive)
        optret emit_signature sg emit_expr f (emit_list emit_expr) args
  | Cminor.Stailcall (sg, f, args) ->
      a3 b "Stailcall" emit_signature sg emit_expr f (emit_list emit_expr) args
  | Cminor.Sbuiltin (_, _, _) ->
      failwith "emit_stmt: Sbuiltin not produced by this compiler"
  | Cminor.Sseq (a, c) ->
      a2 b "Sseq" emit_stmt a emit_stmt c
  | Cminor.Sifthenelse (e, a, c) ->
      a3 b "Sifthenelse" emit_expr e emit_stmt a emit_stmt c
  | Cminor.Sloop x ->
      a1 b "Sloop" emit_stmt x
  | Cminor.Sblock x ->
      a1 b "Sblock" emit_stmt x
  | Cminor.Sexit x ->
      a1 b "Sexit" emit_nat x
  | Cminor.Sswitch (islong, e, cases, dfl) ->
      a4 b "Sswitch" emit_bool islong emit_expr e emit_switch_cases cases
        emit_nat dfl
  | Cminor.Sreturn optret ->
      a1 b "Sreturn" (emit_option emit_expr) optret
  | Cminor.Slabel (l, a) ->
      a2 b "Slabel" emit_label l emit_stmt a
  | Cminor.Sgoto l ->
      a1 b "Sgoto" emit_label l

and emit_switch_cases b (cases : (BinNums.coq_Z * Datatypes.nat) list) =
  emit_list (emit_pair emit_z emit_nat) b cases

and emit_external_function b (ef : AST.external_function) =
  match ef with
  | AST.EF_external (id, sg) ->
      a2 b "EF_external" emit_string (string_of_chars id) emit_signature sg
  | AST.EF_builtin (id, sg) ->
      a2 b "EF_builtin" emit_string (string_of_chars id) emit_signature sg
  | AST.EF_runtime (id, sg) ->
      a2 b "EF_runtime" emit_string (string_of_chars id) emit_signature sg
  | AST.EF_vload c ->
      a1 b "EF_vload" emit_memory_chunk c
  | AST.EF_vstore c ->
      a1 b "EF_vstore" emit_memory_chunk c
  | AST.EF_malloc ->
      a0 b "EF_malloc"
  | AST.EF_free ->
      a0 b "EF_free"
  | AST.EF_memcpy (sz, al) ->
      a2 b "EF_memcpy" emit_z sz emit_z al
  | AST.EF_annot (k, t, tl) ->
      a3 b "EF_annot" emit_positive k emit_string (string_of_chars t)
        (emit_list emit_typ) tl
  | AST.EF_annot_val (k, t, ty) ->
      a3 b "EF_annot_val" emit_positive k emit_string (string_of_chars t)
        emit_typ ty
  | AST.EF_inline_asm (t, sg, cl) ->
      a3 b "EF_inline_asm" emit_string (string_of_chars t) emit_signature sg
        (emit_list emit_string)
        (List.map string_of_chars cl)
  | AST.EF_debug (k, t, tl) ->
      a3 b "EF_debug" emit_positive k emit_positive t (emit_list emit_typ) tl

let emit_function b (f : Cminor.coq_function) =
  Buffer.add_char b '(' ;
  Buffer.add_string b "mkfunction" ;
  Buffer.add_char b ' ' ;
  emit_signature b f.Cminor.fn_sig ;
  Buffer.add_char b ' ' ;
  emit_list emit_positive b f.Cminor.fn_params ;
  Buffer.add_char b ' ' ;
  emit_list emit_positive b f.Cminor.fn_vars ;
  Buffer.add_char b ' ' ;
  emit_z b f.Cminor.fn_stackspace ;
  Buffer.add_char b ' ' ;
  emit_stmt b f.Cminor.fn_body ;
  Buffer.add_char b ')'

let emit_fundef b (fd : Cminor.coq_function AST.fundef) =
  match fd with
  | AST.Internal x ->
      a1 b "Internal" emit_function x
  | AST.External _ ->
      a0 b "(External _)"

(* globdef over (fundef, unit). gvar omitted unless you emit data. *)
let emit_globdef b (g : (Cminor.coq_function AST.fundef, unit) AST.globdef) =
  match g with
  | AST.Gfun x ->
      a1 b "Gfun" emit_fundef x
  | AST.Gvar _ ->
      a0 b "(Gvar _)" (* CHECK: gvar carries a globvar unit *)

(* prog_defs is a list of (ident * globdef); Rust used a custom tail
   "prelude.defs". Keep that to match. *)
let emit_prog_defs b defs =
  emit_list_tail (emit_pair emit_positive emit_globdef) b defs "prelude.defs"

let emit_program b (p : (Cminor.coq_function AST.fundef, unit) AST.program) =
  Buffer.add_char b '(' ;
  Buffer.add_string b "mkprogram" ;
  Buffer.add_char b ' ' ;
  emit_prog_defs b p.AST.prog_defs ;
  Buffer.add_char b ' ' ;
  emit_list emit_positive b p.AST.prog_public ;
  Buffer.add_char b ' ' ;
  emit_positive b p.AST.prog_main ;
  Buffer.add_char b ')'

(* Top-level entry: program -> Gallina source string. *)
let rocq_of_cminor (p : (Cminor.coq_function AST.fundef, unit) AST.program) :
    string =
  prog_to_rocq (fun b -> emit_program b p)
