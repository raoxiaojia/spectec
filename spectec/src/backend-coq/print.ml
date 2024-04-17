open Coq

let print_def (def: coq_def) : string =
  match def with
  | _ -> "placeholder for a definition\n"

let gen_string il: string = 
  let itps = Il2itp.translate_script il in
  let coqs = Itp2coq.translate_script itps in
    "(* Coq code below *)\n\n" ^ (String.concat "" (List.map print_def coqs))

let gen_file file il =
  let output = gen_string il in
  let oc = Out_channel.open_text file in
  Fun.protect (fun () -> Out_channel.output_string oc output)
    ~finally:(fun () -> Out_channel.close oc)