open Util
open Source
open Il.Ast
open Itp


(* Helpers *)

let concat = String.concat
let prefix s f x = s ^ f x
let space f x = " " ^ f x ^ " "


(* Operators *)

let itp_of_unop (e: unop) : term =
  match e with
  | NotOp -> E_basic E_not
  | PlusOp _ -> E_basic E_plus
  | MinusOp _ -> E_basic E_minus
  | PlusMinusOp _ -> E_basic E_plusminus
  | MinusPlusOp _ -> E_basic E_minusplus

let itp_of_binop (e: binop) : term =
  match e with
  | AndOp -> E_basic E_and
  | OrOp -> E_basic E_or
  | ImplOp -> E_basic E_impl
  | EquivOp -> E_basic E_equiv
  | AddOp _ -> E_basic E_add
  | SubOp _ -> E_basic E_sub
  | MulOp _ -> E_basic E_mul
  | DivOp _ -> E_basic E_div
  | ExpOp _ -> E_basic E_exp

let itp_of_cmpop (e: cmpop) : term =
  match e with
  | EqOp -> E_basic E_eq
  | NeOp -> E_basic E_neq
  | LtOp _ -> E_basic E_lt
  | GtOp _ -> E_basic E_gt
  | LeOp _ -> E_basic E_le
  | GeOp _ -> E_basic E_ge

(* Check *)
let itp_of_atom (a: atom) : term =
  match a.it with
  | Atom id -> E_ident id
  | Infinity -> E_ident "infinity"
  | Bot -> E_basic E_false
  | Top -> E_basic E_true
  | Dot -> E_unsupported "."
  | Dot2 -> E_unsupported ".."
  | Dot3 -> E_unsupported "..."
  | Semicolon -> E_unsupported ";"
  | Backslash -> E_unsupported "\\"
  | In -> E_basic E_in
  | Arrow -> E_unsupported "->"
  | Arrow2 -> E_unsupported "=>"
  | ArrowSub -> E_unsupported "->_"
  | Arrow2Sub -> E_unsupported "=>_"
  | Colon -> E_unsupported ":"
  | Sub -> E_unsupported "<:"
  | Sup -> E_unsupported ":>"
  | Assign -> E_unsupported ":="
  | Equal -> E_unsupported "="
  | Equiv -> E_unsupported "=="
  | Approx -> E_unsupported "~~"
  | SqArrow -> E_unsupported "~>"
  | SqArrowStar -> E_unsupported "~>*"
  | Prec -> E_unsupported "<<"
  | Succ -> E_unsupported ">>"
  | Tilesturn -> E_unsupported "-|" 
  | Turnstile -> E_unsupported "|-"
  | Quest -> E_unsupported "?"
  | Plus -> E_unsupported "+"
  | Star -> E_unsupported "*"
  | Comma -> E_unsupported ","
  | Comp -> E_unsupported "++"
  | Bar -> E_unsupported "|"
  | BigComp -> E_unsupported "(++)"
  | BigAnd -> E_unsupported "(/\\)"
  | BigOr -> E_unsupported "(\\/)"
  | LParen -> E_unsupported "("
  | LBrack -> E_unsupported "["
  | LBrace -> E_unsupported "{"
  | RParen -> E_unsupported ")"
  | RBrack -> E_unsupported "]"
  | RBrace -> E_unsupported "}"

let itp_string_of_atom_name (a: atom) : string =
  match a.it with
  | Atom id -> id
  | _ -> ""

let itp_string_of_mixop (m: mixop) : string = 
  match m with
  | [{it = Atom id; _}]::tail when List.for_all ((=) []) tail -> id
  | mixop ->
    (let s =
      String.concat "" (List.map (
        fun atoms -> String.concat "" (List.map itp_string_of_atom_name atoms)) mixop
      )
    in
    s)



(* Types *)

let rec itp_of_iter iter : types =
  match iter with
  | Opt -> T_basic T_opt
  | List -> T_basic T_list
  | List1 -> T_unsupported "non-empty list"
  | ListN (e, None) -> T_unsupported ("^" ^ Il.Print.string_of_exp e)
  | ListN (e, Some id) ->
    T_unsupported ("^(" ^ id.it ^ "<" ^ Il.Print.string_of_exp e ^ ")")

and itp_of_numtyp t =
  match t with
  | NatT -> T_basic T_nat
  | IntT -> T_basic T_int
  | RatT -> T_unsupported "rat"
  | RealT -> T_unsupported "real"

and itp_of_typ t =
  match t.it with
  | VarT (id, as1) -> itp_of_arg_type id.it as1
  | BoolT -> T_basic T_bool
  | NumT t -> itp_of_numtyp t
  | TextT -> T_basic T_string
  | TupT ets -> T_tuple (List.map itp_of_typbind ets)
  | IterT (t1, iter) -> T_app (itp_of_iter iter, [itp_of_typ t1])

and itp_of_iters_typ iters t =
  match iters with
  | [] -> itp_of_typ t
  | iter :: tail -> T_app (itp_of_iter iter, [itp_of_iters_typ tail t])

and itp_of_arg_type id as1 = 
  let args = List.map itp_of_arg_as_type as1 in
  let args_cleaned = List.filter (fun x -> match x with | T_unsupported _ -> false | _ -> true) args in
  match args with
  | [] -> T_ident id
  | _ -> T_app (T_ident id, args_cleaned)

and itp_of_arg_as_type a =
  match a.it with
  | ExpA e -> T_unsupported ("Dependent type is currently unsupported ( arg: " ^ Il.Print.string_of_exp e ^ " )")
  | TypA t -> itp_of_typ t

and itp_of_typ_name t =
  match t.it with
  | VarT (id, _) -> T_ident id.it
  | _ -> assert false

  (*
and itp_of_typ_args t =
  match t.it with
  | TupT [] -> T_tuple 
  | TupT _ -> itp_of_typ t
  | _ -> "(" ^ itp_of_typ t ^ ")"
  *)


and itp_of_typbind (e, t) =
  match e.it with
  | VarE {it = "_"; _} -> itp_of_typ t
  | _ -> (* itp_of_exp e ^ " : " ^ *) itp_of_typ t

  (*
and itp_of_deftyp layout dt =
  match dt.it with
  | AliasT t -> itp_of_typ t
  | StructT tfs when layout = `H ->
    "{" ^ concat ", " (List.map itp_of_typfield tfs) ^ "}"
  | StructT tfs ->
    "\n{\n  " ^ concat ",\n  " (List.map itp_of_typfield tfs) ^ "\n}"
  | VariantT tcs when layout = `H ->
    "| " ^ concat " | " (List.map itp_of_typcase tcs)
  | VariantT tcs ->
    "\n  | " ^ concat "\n  | " (List.map itp_of_typcase tcs)

and itp_of_typfield (atom, (bs, t, prems), _hints) =
  itp_of_mixop [[atom]] ^ itp_of_binds bs ^ " " ^ itp_of_typ t ^
    concat "" (List.map (prefix "\n    -- " itp_of_prem) prems)

and itp_of_typcase (op, (bs, t, prems), _hints) =
  itp_of_mixop op ^ itp_of_binds bs ^ itp_of_typ_args t ^
    concat "" (List.map (prefix "\n    -- " itp_of_prem) prems)
*)

(* Expressions *)

and itp_of_exp e : term =
  match e.it with
  | VarE id -> E_ident id.it
  | BoolE b -> E_basic (E_bool b)
  | NatE n -> E_basic (E_nat n)
  | TextE t -> E_basic (E_string ("\"" ^ String.escaped t ^ "\""))
  | UnE (op, e2) -> E_app (itp_of_unop op, [itp_of_exp e2])
  | BinE (op, e1, e2) -> E_app (itp_of_binop op, [itp_of_exp e1; itp_of_exp e2])
  | CmpE (op, e1, e2) -> E_app (itp_of_cmpop op, [itp_of_exp e1; itp_of_exp e2])
  | IdxE (e1, e2) -> 
    (* This might be record lookup instead *)
    E_app (E_basic E_listlookup, [itp_of_exp e1; itp_of_exp e2])
  | SliceE (e1, e2, e3) -> E_app (itp_of_exp e1, [E_unsupported ("SliceE: [" ^ Il.Print.string_of_exp e2 ^ " : " ^ Il.Print.string_of_exp e3 ^ "]")])
  | UpdE (e1, p, e2) -> (* Need to differentiate between list and record update *)
    E_unsupported (
      Il.Print.string_of_exp e1 ^
        "UpdE: [" ^ Il.Print.string_of_path p ^ " = " ^ Il.Print.string_of_exp e2 ^ "]")
  | ExtE (e1, p, e2) ->
    E_unsupported (
      Il.Print.string_of_exp e1 ^
        "ExtE: [" ^ Il.Print.string_of_path p ^ " =.. " ^ Il.Print.string_of_exp e2 ^ "]")
  | StrE efs -> E_unsupported ("StrE: {" ^ concat ", " (List.map string_of_expfield efs) ^ "}")
  | DotE (e1, atom) ->
    E_recordlookup (itp_of_exp e1, itp_string_of_atom_name atom)
  | CompE (e1, e2) -> (* List and record concat *)
    E_app (E_basic E_listconcat, [itp_of_exp e1; itp_of_exp e2])
  | LenE e1 -> E_app (E_basic E_listlength, [itp_of_exp e1])
  | TupE es -> E_tuple (List.map itp_of_exp es)
  | CallE (id, as1) -> E_app (E_ident id.it, List.map itp_of_arg_as_exp as1)
  | IterE (e1, iter) -> E_unsupported ("IterE: " ^ Il.Print.string_of_exp e1 ^ string_of_iterexp iter)
  | ProjE (e1, i) -> E_app (E_basic E_listlookup, [itp_of_exp e1; E_basic (E_int i)])
  | UncaseE (e1, _op) -> itp_of_exp e1
    (*E_unsupported (Il.Print.string_of_exp e1 ^ "!" ^ Il.Print.string_of_mixop op ^ "_" ^ Il.Print.string_of_typ e1.note)*)
  | OptE eo -> 
    begin match eo with
    | Some e -> E_app (E_basic E_some, [itp_of_exp e])
    | None -> E_basic E_none
    end
  | TheE e1 -> E_unsupported ("TheE: !(" ^ Il.Print.string_of_exp e1 ^ ")")
  | ListE es -> E_list (List.map itp_of_exp es)
  | CatE (e1, e2) -> E_app (E_basic E_listconcat, [itp_of_exp e1; itp_of_exp e2])
  | CaseE (op, _e1) -> E_ident (itp_string_of_mixop op)
    (*E_unsupported (Il.Print.string_of_mixop op ^ "_" ^ Il.Print.string_of_typ e.note ^ string_of_exp_args e1)*)
  | SubE (e1, t1, t2) ->
    E_unsupported ("SubE: (" ^ Il.Print.string_of_exp e1 ^ " : " ^ Il.Print.string_of_typ t1 ^ " <: " ^ Il.Print.string_of_typ t2 ^ ")")

and string_of_expfield (atom, e) =
  Il.Print.string_of_mixop [[atom]] ^ " " ^ Il.Print.string_of_exp e

and string_of_iterexp (iter, bs) =
  Il.Print.string_of_iter iter ^ "{" ^ String.concat ", "
    (List.map (fun (id, t) -> id.it ^ " : " ^ Il.Print.string_of_typ t) bs) ^ "}"

and string_of_exp_args e =
  match e.it with
  | TupE [] -> ""
  | TupE _ | SubE _ | BinE _ | CmpE _ -> Il.Print.string_of_exp e
  | _ -> "(" ^ Il.Print.string_of_exp e ^ ")"

and itp_of_arg_as_exp a =
  match a.it with
  | ExpA e -> itp_of_exp e
  | TypA t -> E_unsupported ("Explicit type arguments are currently unsupported ( arg: " ^ Il.Print.string_of_typ t ^ " )")

(*
and itp_of_path p =
  match p.it with
  | RootP -> ""
  | IdxP (p1, e) ->
    itp_of_path p1 ^ "[" ^ itp_of_exp e ^ "]"
  | SliceP (p1, e1, e2) ->
    itp_of_path p1 ^ "[" ^ itp_of_exp e1 ^ " : " ^ itp_of_exp e2 ^ "]"
  | DotP ({it = RootP; note; _}, atom) ->
    itp_of_mixop [[atom]] ^ "_" ^ itp_of_typ_name note
  | DotP (p1, atom) ->
    itp_of_path p1 ^ "." ^ itp_of_mixop [[atom]] ^ "_" ^ itp_of_typ_name p1.note

and itp_of_iterexp (iter, bs) =
  itp_of_iter iter ^ "{" ^ String.concat ", "
    (List.map (fun (id, t) -> id.it ^ " : " ^ itp_of_typ t) bs) ^ "}"
*)

(* Premises *)
and itp_of_prem = Il.Print.string_of_prem

(* Definitions *)

and itp_of_bind (bind: bind) : binder =
  match bind.it with
  | ExpB (id, t, iters) ->
    (id.it, itp_of_iters_typ iters t)
  | TypB id -> ("noname", T_ident id.it)

and itp_of_binds (binds: bind list) : binder list =
  List.map itp_of_bind binds

let itp_of_param p : binder =
  match p.it with
  | ExpP (id, t) -> (id.it, itp_of_typ t)
  | TypP id -> ("noname", T_ident id.it)

let itp_of_params params : binder list =
  List.map itp_of_param params

(*
let region_comment ?(suppress_pos = false) indent at =
  if at = no_region then "" else
  let s = if suppress_pos then at.left.file else string_of_region at in
  indent ^ ";; " ^ s ^ "\n"
  *)
(*
itp_of_deftyp layout dt =
  match dt.it with
  | AliasT t -> itp_of_typ t
  | StructT tfs when layout = `H ->
    "{" ^ concat ", " (List.map itp_of_typfield tfs) ^ "}"
  | StructT tfs ->
    "\n{\n  " ^ concat ",\n  " (List.map itp_of_typfield tfs) ^ "\n}"
  | VariantT tcs when layout = `H ->
    "| " ^ concat " | " (List.map itp_of_typcase tcs)
  | VariantT tcs ->
    "\n  | " ^ concat "\n  | " (List.map itp_of_typcase tcs)

itp_of_typfield (atom, (bs, t, prems), _hints) =
  itp_of_mixop [[atom]] ^ itp_of_binds bs ^ " " ^ itp_of_typ t ^
    concat "" (List.map (prefix "\n    -- " itp_of_prem) prems)

and itp_of_typcase (op, (bs, t, prems), _hints) =
  itp_of_mixop op ^ itp_of_binds bs ^ itp_of_typ_args t ^
    concat "" (List.map (prefix "\n    -- " itp_of_prem) prems)
   *)

let itp_of_recfield (tf: typfield) : record_constructor =
  match tf with
  | (atom, (_bs, t, prems), _hints) ->
    match atom.it with 
    | Atom a -> 
      (match prems with
      | [] -> (a, itp_of_typ t)
      | _ -> assert false
      )
    | _ -> assert false

let itp_of_typ_ind ts : types list =
  match ts.it with
  | TupT [] -> []
  | _ -> [itp_of_typ ts]


let itp_of_ind (tc: typcase) : ind_constructor = 
  match tc with
  | (op, (_bs, ts, prems), _hints) ->
    (match prems with
    | [] -> (itp_string_of_mixop op, itp_of_typ_ind ts)
    | _ -> (*assert false*)(itp_string_of_mixop op (*^ "(* with unsupported premises: " ^ (String.concat " && " (List.map Il.Print.string_of_prem prems)) ^ " *)"*), itp_of_typ_ind ts)
    )

let itp_of_inst id inst =
  match inst.it with
  | InstD (_bs, _as_, dt) ->
    (match dt.it with
    | AliasT t -> TypeD (id.it, itp_of_typ t)
    | StructT tfs -> RecordD (id.it, List.map itp_of_recfield tfs)
    | VariantT tcs -> IndTypeD (id.it, List.map itp_of_ind tcs)
    )
    (*"\n" ^ region_comment ~suppress_pos "  " inst.at ^
    "  syntax " ^ id.it ^ itp_of_binds bs ^ itp_of_args as_ ^ " = " ^
      itp_of_deftyp `V dt ^ "\n"*)


let itp_of_rule rule : rel_constructor =
  match rule.it with
  | RuleD (id, bs, _mixop, e, prems) ->
    let id' = if id.it = "" then "default_name" else id.it in
    (id', List.map itp_of_bind bs, List.map Il.Print.string_of_prem prems, itp_of_exp e)
   (* "  rule " ^ id' ^ itp_of_binds bs ^ ":\n    " ^
      itp_of_mixop mixop ^ itp_of_exp_args e ^
      concat "" (List.map (prefix "\n    -- " itp_of_prem) prems)*)

let itp_of_clause _id clause =
  match clause.it with
  | DefD (_bs, as_, e, _prems) ->
    match as_ with
    | [] -> (E_basic E_unit, itp_of_exp e)
    | [arg] -> (itp_of_arg_as_exp arg, itp_of_exp e)
    | _ -> (E_list (List.map itp_of_arg_as_exp as_), itp_of_exp e)
    (*(["binds: " ^ Il.Print.string_of_binds bs ^ ", args: " ^ Il.Print.string_of_args as_ ^ ", prems: " ^ (String.concat "" (List.map Il.Print.string_of_prem prems))], itp_of_exp e)*)

let itp_of_inst_family (constr, inst) =
  match inst.it with
  | InstD (_bs, _as_, dt) ->
    (match dt.it with
    | AliasT t -> TypeD (constr, itp_of_typ t)
    | StructT tfs -> RecordD (constr, List.map itp_of_recfield tfs)
    | VariantT tcs -> IndTypeD (constr, List.map itp_of_ind tcs)
    )

let itp_get_param_name p = 
  match p.it with
  | ExpP (id, _t) -> id.it
  | TypP id -> "(* Unsupported type as param *)" ^ id.it

let itp_get_param_tuple ps = 
  match ps with
  | [] -> "Error_no_params"
  | [p] -> 
    (match p.it with
    | ExpP (id, _t) -> id.it
    | TypP id -> "(* Unsupported type as param *)" ^ id.it
    )
  | _ -> "(" ^ (String.concat " , " (List.map itp_get_param_name ps)) ^ ")"

let get_binder_name b =
  match b.it with
  | ExpB (id, _t, _its) -> id.it
  | TypB id -> id.it

let get_family_constructor_name_inst id inst = 
  match inst.it with
  | InstD (bs, _as_, _dt) ->
    (id.it ^ "_" ^ (String.concat "_" (List.map get_binder_name bs)), inst)

let transform_family_def id insts : itp_def list =
  let constructor_name_insts = List.map (get_family_constructor_name_inst id) insts in
  (List.map itp_of_inst_family constructor_name_insts) @ 
  [IndTypeD (id.it, List.map (fun (constr, _inst) -> (constr ^ "_constructor", [T_ident constr])) constructor_name_insts)]

let rec itp_of_def d =
  match d.it with
  | TypD (id, _ps, [inst]) ->
    [itp_of_inst id inst]
  (*  TypeD (id.it,)
    pre ^ "syntax " ^ id.it ^ itp_of_binds bs ^ itp_of_args as_ ^ " = " ^
      itp_of_deftyp `V dt ^ "\n"*)
  | TypD (id, _ps, insts) ->
    transform_family_def id insts
  (*  pre ^ "syntax " ^ id.it ^ itp_of_params ps ^
     concat "\n" (List.map (itp_of_inst ~suppress_pos id) insts) ^ "\n"*)
  | RelD (id, _mixop, t, rules) ->
    [IndRelD (id.it, [itp_of_typ t], List.map itp_of_rule rules)]
  | DecD (id, ps, t, clauses) ->
    [FuncD (id.it, List.map itp_of_param ps, itp_of_typ t, E_match (itp_get_param_tuple ps, List.map (itp_of_clause id) clauses))]
  | RecD ds ->
    [MutualD (List.concat_map itp_of_def ds)]
  | HintD _hints ->
    [UnsupportedD "hint_def"]


let itp_of_script ds =
  List.concat_map itp_of_def ds
  (*List.map itp_of_def ds*)
