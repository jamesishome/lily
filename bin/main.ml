let usage = "usage: lily compile SCHEMA.li [-o OUTPUT.ml]"

let read path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ic) (fun () -> really_input_string ic (in_channel_length ic))

let module_name path =
  let base = Filename.remove_extension (Filename.basename path) in
  let ok = function 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true | _ -> false in
  Filename.extension path = ".ml" && base <> "" && (match base.[0] with 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false)
  && String.for_all ok base

let compile input output =
  match Lily.Parse.schema ~file:input (read input) |> Lily.Check.check |> Lily.Emit.emit with
  | exception Lily.Syntax.Error (at, message) ->
    prerr_endline (Lily.Syntax.describe at message);
    1
  | exception Sys_error message ->
    prerr_endline ("lily: " ^ message);
    1
  | text -> (
    match output with
    | None ->
      print_string text;
      0
    | Some path when not (module_name path) ->
      Printf.eprintf "lily: %s is not a valid OCaml module file name\n" path;
      1
    | Some path -> (
      let tmp = path ^ ".tmp" in
      match
        let oc = open_out_bin tmp in
        Fun.protect ~finally:(fun () -> close_out oc) (fun () -> output_string oc text);
        Sys.rename tmp path
      with
      | () -> 0
      | exception Sys_error message ->
        prerr_endline ("lily: " ^ message);
        1))

let () =
  let code =
    match List.tl (Array.to_list Sys.argv) with
    | [ "compile"; input ] -> compile input None
    | [ "compile"; input; "-o"; output ] | [ "compile"; "-o"; output; input ] -> compile input (Some output)
    | [ ("-h" | "--help" | "help") ] ->
      print_endline usage;
      0
    | _ ->
      prerr_endline usage;
      2
  in
  exit code
