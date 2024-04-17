type ident = string

(* binder names *)
type name = string

type types =
  | UnitT
  | BoolT
  | NatT
  | StringT
  | ListT of types
  | OptionT of types
  | TupleT of tuple_type
  | RecordT of record_type
  | InductiveT of inductive_type

and tuple_type = types list

and record_type = ident * (binder list)

and inductive_type = inductive_constructor list

and inductive_constructor = ident * (types list)

and binder = name * types

type itp_def = string

type itp_script = itp_def list