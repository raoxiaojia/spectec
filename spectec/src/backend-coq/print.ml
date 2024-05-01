open Itp

let print_unit_type t : string =
  match t with
  | T_unit -> "unit"
  | T_bool -> "bool"
  | T_nat -> "nat"
  | T_int -> "int"
  | T_string -> "string"
  | T_list -> "list"
  | T_opt -> "option"
  | T_prod -> "prod"

let rec print_type (t: types) : string = 
  match t with
  | T_basic t' -> print_unit_type t'
  | T_ident id -> id
  | T_tuple ts -> 
    (match ts with
    | [] -> "unit"
    | [t'] -> print_type t'
    | t' :: tail -> "(prod " ^ (print_type t') ^ " " ^ print_type (T_tuple tail) ^ ")"
    )
  | T_app (t', ts) ->
    (match ts with
    | [] -> print_type t'
    | _ -> "(" ^ print_type t' ^ " " ^ (String.concat " " (List.map print_type ts)) ^ ")"
    )
  | T_unsupported str -> "Unsupported type: " ^ str

and print_tuple_type (ts: types list) : string = 
  "( " ^ (String.concat "*" (List.map print_type ts)) ^ " )"

let print_record_constructor (name: ident) (b: binder) : string =
  match b with
  | (ident, term) ->
    name ^ "_" ^ ident ^ " : " ^ print_type term

let print_record_decl record_def : string =
  match record_def with
  | (name, binders) ->
    "Record " ^ name ^ " : Type := \n" ^
    "{|\n  " ^ (String.concat "\n  " (List.map (print_record_constructor name) binders)) ^ "\n|}"

let print_record_constructor (b: binder) : string =
  match b with
  | (name, t) ->
    name ^ " : " ^ print_type t

let print_binder (b: binder) : string = 
  match b with
  | (name, t) ->
    "(" ^ name ^ " : " ^ print_type t ^ ")"

let print_inductive_constructor (id: ident) (ind: ind_constructor) : string =
  match ind with
  | (ind_id, ts) -> "| " ^ ind_id ^ " : " ^ (String.concat "" (List.map (fun t -> (print_type t) ^ " -> ") ts)) ^ id ^ "\n"

let print_premise (prem: premise) : string =
  prem

let print_relation_constructor (id: ident) (rel: rel_constructor) : string =
  match rel with
  | (rel_id, bs, prems, e) -> "| " ^ rel_id ^ " " ^ (String.concat " " (List.map print_binder bs)) ^ " :\n" ^
  (String.concat "" (List.map (fun p -> print_premise p ^ " ->\n") prems)) ^
  print_term e ^ "\n"

let print_def (def: itp_def) : string = 
  match def with
  | TypeD (id, t) -> "Definition " ^ id ^ " : Type := " ^ (print_type t) ^ ".\n"
  | FuncD (id, bs, t, e) -> "Definition " ^ id ^ (String.concat " " (List.map print_binder bs) ^ " : " ^ (print_type t) ^ " := " ^ (print_term e)) ^ ".\n"
  | IndTypeD (id, inds) -> "Inductive " ^ id ^ " : Set := \n" ^ (String.concat "" (List.map (print_inductive_constructor id) inds)) ^ ".\n"
  (* Technically there's no difference between types and relations, but this might not be the case in some itps *)
  | IndRelD (id, ts, rels) -> 
    "Inductive " ^ id ^ " : " ^ (String.concat "" (List.map (fun t -> (print_type t) ^ " -> ") ts)) ^ "Prop := \n" ^ 
    (String.concat "" (List.map (print_relation_constructor id) inds)) ^ ".\n" 
  | RecordD of ident * (record_constructor list)
  | MutualD of itp_def list (* Mutually recursive definitions *)
  | UnsupportedD of string

let gen_string il: string = 
  let coqs = Il2coq.translate_script il in
    "(* Coq code below *)\n\n" ^ (String.concat "\n" (List.map print_def coqs))

let gen_file file il =
  let output = gen_string il in
  let oc = Out_channel.open_text file in
  Fun.protect (fun () -> Out_channel.output_string oc output)
    ~finally:(fun () -> Out_channel.close oc)