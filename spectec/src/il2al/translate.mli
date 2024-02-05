val name_of_rule : Il.Ast.rule -> string
val name_to_kwd : string -> Il.Ast.typ -> string * string
val get_params : Il.Ast.exp -> Il.Ast.exp list
val exp_to_expr : Il.Ast.exp -> Al.Ast.expr
val exp_to_args : Il.Ast.exp -> Al.Ast.expr list
val translate : Il.Ast.script -> Al.Ast.algorithm list
