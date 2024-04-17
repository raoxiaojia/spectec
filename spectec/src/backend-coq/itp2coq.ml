open Itp
open Coq

let translate_script (il: itp_script) : coq_script =
  List.map (fun _ -> "1") il