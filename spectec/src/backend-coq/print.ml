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
  | T_unsupported str -> "(* Unsupported type: " ^ str ^ "*)"

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

let print_record_constructor (_id: ident) (r: record_constructor) : string =
  match r with
  | (f, t) ->
   "  " ^ f ^ " : " ^ print_type t ^ ";\n"

let print_binder (b: binder) : string = 
  match b with
  | (name, t) ->
    "(" ^ name ^ " : " ^ print_type t ^ ")"

let print_bool b : string = 
  match b with
  | true -> "true"
  | false -> "false"

let print_nat n : string = 
  Z.to_string n

let print_basic_term (e: basic_term) : string = 
  match e with
  | E_bool b -> print_bool b
  | E_nat n -> print_nat n
  | E_int n -> string_of_int n
  | E_string s -> s
  | E_not -> "not"
  | E_plus -> "plus"
  | E_minus -> "minus"
  | E_plusminus -> "plusminus"
  | E_minusplus -> "minusplus"
  | E_and -> "and"
  | E_or -> "or"
  | E_impl -> "impl"
  | E_equiv -> "equiv"
  | E_add -> "add"
  | E_sub -> "sub"
  | E_mul -> "mul"
  | E_div -> "div"
  | E_exp -> "exp"
  | E_eq -> "eq"
  | E_neq -> "neq"
  | E_lt -> "lt"
  | E_gt -> "gt"
  | E_le -> "le"
  | E_ge -> "ge"
  | E_in -> "in"
  | E_false -> "False"
  | E_true -> "True"
  | E_some -> "Some"
  | E_none -> "None"
  | E_listconcat -> "app"
  | E_listlookup -> "list_nth"
  | E_listupdate -> "list_upd"
  | E_listlength -> "length"

let print_patterns (pat: pattern) : string =
  String.concat " " pat

let rec print_term (e: term) : string =
  match e with
  | E_basic be -> print_basic_term be
  | E_ident id -> id
  | E_tuple es ->
    "(" ^ (String.concat "," (List.map print_term es)) ^ ")"
  | E_list es -> 
    "[" ^ (String.concat ";" (List.map print_term es)) ^ "]"
  | E_app (e0, es) ->
    "(" ^ print_term e0 ^ " " ^ (String.concat " " (List.map print_term es)) ^ ")"
  | E_match (id, clauses) ->
    "(match " ^ id ^ " with\n"^
    (String.concat "" (List.map print_match_clause clauses)) ^ 
    "end)"
  | E_unsupported s -> "(* Unsupported term: " ^ s ^ "*)"

and print_match_clause (clause: match_clause) : string = 
  match clause with
  | (pat, e) -> 
    "  | " ^ print_patterns pat ^ " => " ^ print_term e ^ "\n"

let print_inductive_constructor (id: ident) (ind: ind_constructor) : string =
  match ind with
  | (ind_id, ts) -> "  | " ^ ind_id ^ " : " ^ (String.concat "" (List.map (fun t -> (print_type t) ^ " -> ") ts)) ^ id ^ "\n"

let print_premise (prem: premise) : string =
  prem

let print_relation_constructor (_id: ident) (rel: rel_constructor) : string =
  match rel with
  | (rel_id, bs, prems, e) -> "| " ^ rel_id ^ " " ^ (String.concat " " (List.map print_binder bs)) ^ " :\n" ^
  (String.concat "" (List.map (fun p -> print_premise p ^ " ->\n") prems)) ^
  print_term e ^ "\n"

let rec print_def (def: itp_def) : string = 
  match def with
  | TypeD (id, t) -> "Definition " ^ id ^ " : Type := " ^ (print_type t) ^ ".\n"
  | FuncD (id, bs, t, e) -> "Definition " ^ id ^ " " ^ (String.concat " " (List.map print_binder bs) ^ " : " ^ (print_type t) ^ " :=\n" ^ (print_term e)) ^ ".\n"
  | IndTypeD (id, inds) -> "Inductive " ^ id ^ " : Set := \n" ^ (String.concat "" (List.map (print_inductive_constructor id) inds)) ^ ".\n"
  (* Technically there's no difference between types and relations, but this might not be the case in some itps *)
  | IndRelD (id, ts, rels) -> 
    "Inductive " ^ id ^ " : " ^ (String.concat "" (List.map (fun t -> (print_type t) ^ " -> ") ts)) ^ "Prop := \n" ^ 
    (String.concat "" (List.map (print_relation_constructor id) rels)) ^ ".\n" 
  | RecordD (id, rs) ->
    "Record " ^ id ^ " : Set := {\n" ^
    (String.concat "" (List.map (print_record_constructor id) rs)) ^ "}.\n"
  | MutualD defs ->
    "Rec {\n" ^
    (String.concat "\n" (List.map print_def defs)) ^
    "}\n" 
  | UnsupportedD s -> "(* Unsupported definition : " ^ s ^ " *)\n"

let gen_string il: string = 
  let itps = Il2itp.itp_of_script il in
    "(* Itp code below *)\n\n" ^ (String.concat "\n" (List.map print_def itps))

let gen_file file il =
  let output = gen_string il in
  let oc = Out_channel.open_text file in
  Fun.protect (fun () -> Out_channel.output_string oc output)
    ~finally:(fun () -> Out_channel.close oc)