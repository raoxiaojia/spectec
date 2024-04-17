open Il.Ast
open Itp

let translate_script (il: script) : itp_script =
  List.map (fun _ -> "1") il