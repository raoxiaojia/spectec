type nat = Z.t

type ident = string

(* binder names *)
type name = string

(* Using snail case throughout to distinguish between the IL definitions *)
(* Distinguishing between types and terms so that itps without dependent types can be supported *)
type basic_types = 
  | T_unit
  | T_bool
  | T_nat
  | T_int
  | T_string
  | T_list
  | T_opt
  | T_prod

type basic_term = 
  | E_bool of bool
  | E_nat of nat
  | E_int of int
  | E_string of string
  | E_unit
  | E_not
  | E_plus
  | E_minus
  | E_plusminus
  | E_minusplus
  | E_and
  | E_or
  | E_impl
  | E_equiv
  | E_add
  | E_sub
  | E_mul
  | E_div
  | E_exp
  | E_eq
  | E_neq
  | E_lt
  | E_gt
  | E_le
  | E_ge
  | E_in
  | E_false
  | E_true
  | E_some
  | E_none
  | E_listconcat
  | E_listlookup
  | E_listupdate
  | E_listlength

type term =
  | E_basic of basic_term
  | E_ident of ident
  | E_tuple of (term list) (* See comments on T_tuple *)
  | E_list of (term list)
  | E_app of (term * (term list))
  | E_recordlookup of (term * ident)
  | E_match of term_match
  | E_unsupported of string
  
and term_match = ident * (match_clause list)
  
and match_clause = pattern * term

and pattern = term
  
type types =
  | T_basic of basic_types
  | T_ident of ident
  | T_tuple of (types list) (* Technically this is the same as below (with the prod constructor), but this occurs too often and is worth a separate constructor *)
  | T_app of (types * (types list)) (* Parameterised types. This does not perform any arity check but merely defines an AST. *)
  | T_term of term (* Dependent types *)
  | T_unsupported of string

type premise = string

type binder = (ident * types)

(* (Inductive) type constructors can only be of the form `ident (type)^*`. Note that this is in principle no different from below *)
type ind_constructor = ident * (types list)

(*
  (Inductive) relation constructors can only be of the form `ident (binder)^* (prem)^* relation_inst`.
  Each premise is a term, and the final relation instance is also expressed in a term.
  *)
type rel_constructor = ident * (binder list) * (premise list) * term

(*
  Definition of each field of a record is simply its identifier and type.
  *)
type record_constructor = ident * types

type itp_def = 
  | TypeD of ident * types 
  | FuncD of ident * (binder list) * types * term
  | IndTypeD of ident * (ind_constructor list)
  | IndRelD of ident * (types list) * (rel_constructor list) (* Technically there's no difference between types and relations, but this might not be the case in some itps*)
  | RecordD of ident * (record_constructor list)
  | DepFamilyD of (ident * types * (term * itp_def) list) (* Dependent family definition, currently requiring the dependent type to go into one argument *)
  | MutualD of itp_def list (* Mutually recursive definitions *)
  | UnsupportedD of string

type itp_script = (itp_def * string) list