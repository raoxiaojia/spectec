type ident = string

(* binder names *)
type name = string

type types =
  | UnitBT
  | BoolBT
  | NatBT
  | StringBT
  | TermBT of ident
  | ListBT of types
  | OptionBT of types
  | TupleBT of types list
  | RecordBT of binder

  and binder = name * types

type coq_def = string

type coq_script = coq_def list