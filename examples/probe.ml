open Term

let () =
  let arm = pair_arm ~body:(var 1) in
  Printf.printf "%s at depth 0 -> " (Arm.to_string arm);
  match Arm.subst (identity 0) arm with
  | _ -> print_endline "accepted"
  | exception Bind.Scope_error message -> Printf.printf "rejected\n  %s\n" message
