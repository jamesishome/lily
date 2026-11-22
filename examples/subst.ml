open Term

let rec spine t acc = match Term.view t with App { fn; arg } -> spine fn (arg :: acc) | _ -> t, acc

let apps = function [] -> invalid_arg "apps" | f :: args -> List.fold_left (fun fn arg -> app ~fn ~arg) f args

let rec index t =
  match Term.view t with
  | Var i -> Printf.sprintf "#%d" i
  | App _ ->
    let f, args = spine t [] in
    "(" ^ String.concat " " (List.map index (f :: args)) ^ ")"
  | Lam { body } -> "(lam " ^ index body ^ ")"
  | Let _ | LetRec _ | Case _ -> "..."

let rec named env t =
  match Term.view t with
  | Var i -> List.nth env i
  | App _ ->
    let f, args = spine t [] in
    "(" ^ String.concat " " (List.map (named env) (f :: args)) ^ ")"
  | Lam { body } -> "(lam z. " ^ named ("z" :: env) body ^ ")"
  | Let _ | LetRec _ | Case _ -> "..."

let lines env t =
  let rec go env t acc =
    match Term.view t with
    | Let { rhs; body } -> go ("a" :: env) body ((Printf.sprintf "let %s in" (index rhs), Printf.sprintf "let a = %s in" (named env rhs)) :: acc)
    | LetRec { rhs; body } ->
      let env = "f" :: env in
      go env body ((Printf.sprintf "letrec %s in" (index rhs), Printf.sprintf "letrec f = %s in" (named env rhs)) :: acc)
    | Case { scrutinee; arms; fallback } ->
      let arm a =
        match Arm.view a with
        | PairArm { body } -> Printf.sprintf "| pair %s" (index body), Printf.sprintf "| (p, q) -> %s" (named ("q" :: "p" :: env) body)
        | DefaultArm { body } -> Printf.sprintf "| _ %s" (index body), Printf.sprintf "| _ -> %s" (named env body)
      in
      let tail = match fallback with None -> [] | Some e -> [ Printf.sprintf "else %s" (index e), Printf.sprintf "else %s" (named env e) ] in
      List.rev acc @ ((Printf.sprintf "case %s" (index scrutinee), Printf.sprintf "case %s" (named env scrutinee)) :: List.map arm arms) @ tail
    | _ -> List.rev ((index t, named env t) :: acc)
  in
  go env t []

let body =
  let_ ~rhs:(var 0)
    ~body:
      (let_rec ~rhs:(apps [ var 0; var 2 ])
         ~body:
           (case ~scrutinee:(var 1)
              ~arms:[ pair_arm ~body:(apps (List.init 6 var)); default_arm ~body:(var 2) ]
              ~fallback:(Some (var 3))))

let depth = 1

let replacement = apps [ var 0; var 0 ]

let result = Term.subst0 ~depth body replacement

let rec arm_body t =
  match Term.view t with
  | Let { body; _ } | LetRec { body; _ } -> arm_body body
  | Case { arms; _ } -> List.find_map (fun a -> match Arm.view a with PairArm { body } -> Some body | _ -> None) arms
  | _ -> None

let green s = "\027[1;32m" ^ s ^ "\027[0m"

let red s = "\027[1;31m" ^ s ^ "\027[0m"

let dim s = "\027[2m" ^ s ^ "\027[0m"

let cell s = s ^ String.make (max 1 (9 - String.length s)) ' '

let row label cells tail = print_endline (Printf.sprintf "%-9s" label ^ String.concat "" cells ^ tail)

let pitfall () =
  let elements t = let f, args = spine t [] in f :: args in
  let before = elements (Option.get (arm_body body)) and after = elements (Option.get (arm_body result)) in
  let wrong = List.filteri (fun i _ -> i < 5) after @ [ var 3 ] in
  let still = Term.well_scoped ~depth:(depth + 4) (apps wrong) in
  print_endline "pair arm inside Let and LetRec: four local binders q p f a";
  print_endline (dim "subst0 ~depth:1 replaces x with (y y) and drops the x slot");
  print_newline ();
  row "" (List.map cell [ "q"; "p"; "f"; "a"; "x"; "y" ]) "";
  row "before" (List.map (fun t -> cell (index t)) before) "";
  let after = List.map (fun t -> cell (index t)) after in
  row "subst0" (List.filteri (fun i _ -> i < 4) after @ [ green (List.nth after 4); green (List.nth after 5) ]) (green "-> y");
  let wrong = List.map (fun t -> cell (index t)) wrong in
  row "one-off" (List.filteri (fun i _ -> i < 5) wrong @ [ red (List.nth wrong 5) ]) (red "-> a  captured");
  print_newline ();
  print_endline (red "illustration only: a one-off cutoff sends y to #3, the local a");
  print_endline (dim (Printf.sprintf "#3 still passes Term.well_scoped (%b), only the exact result catches it" still))

let full () =
  Printf.printf "context depth %d, free y = #0\n" depth;
  Printf.printf "replacement %s = %s at depth %d\n" (index replacement) (named [ "y" ] replacement) depth;
  Printf.printf "body at depth %d, x = #0 and y = #1\n\n" (depth + 1);
  let show title env t =
    print_endline title;
    List.iter (fun (i, n) -> Printf.printf "  %-33s %s\n" i (dim n)) (lines env t)
  in
  show "before" [ "x"; "y" ] body;
  print_newline ();
  show (Printf.sprintf "after Term.subst0 ~depth:%d" depth) [ "y" ] result;
  Printf.printf "\nwell_scoped ~depth:%d after = %b\n" depth (Term.well_scoped ~depth result)

let () =
  match Sys.argv with
  | [| _; "arm" |] -> pitfall ()
  | [| _; "full" |] -> full ()
  | [| _ |] ->
    pitfall ();
    print_newline ();
    full ()
  | _ ->
    prerr_endline "usage: subst [arm|full]";
    exit 2
