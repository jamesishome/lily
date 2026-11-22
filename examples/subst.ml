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

let lines t =
  let rec go t acc =
    match Term.view t with
    | Let { rhs; body } -> go body (Printf.sprintf "let %s in" (index rhs) :: acc)
    | LetRec { rhs; body } -> go body (Printf.sprintf "letrec %s in" (index rhs) :: acc)
    | Case { scrutinee; arms; fallback } ->
      let arm a =
        match Arm.view a with
        | PairArm { body } -> Printf.sprintf "| pair %s" (index body)
        | DefaultArm { body } -> Printf.sprintf "| _ %s" (index body)
      in
      let tail = match fallback with None -> [] | Some e -> [ Printf.sprintf "else %s" (index e) ] in
      List.rev acc @ (Printf.sprintf "case %s" (index scrutinee) :: List.map arm arms) @ tail
    | _ -> List.rev (index t :: acc)
  in
  go t []

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

let cell s = s ^ String.make (max 1 (9 - String.length s)) ' '

let row label cells tail =
  let line = Printf.sprintf "%-9s" label ^ String.concat "" cells ^ tail in
  let n = ref (String.length line) in
  while !n > 0 && line.[!n - 1] = ' ' do decr n done;
  print_endline (String.sub line 0 !n)

let pitfall () =
  let elements t = let f, args = spine t [] in f :: args in
  let before = elements (Option.get (arm_body body)) and after = elements (Option.get (arm_body result)) in
  let wrong = List.filteri (fun i _ -> i < 5) after @ [ var 3 ] in
  row "" (List.map cell [ "q"; "p"; "f"; "a"; "x"; "y" ]) "";
  row "before" (List.map (fun t -> cell (index t)) before) "";
  let after = List.map (fun t -> cell (index t)) after in
  row "subst0" (List.filteri (fun i _ -> i < 4) after @ [ green (List.nth after 4); green (List.nth after 5) ]) (green "-> y");
  let wrong = List.map (fun t -> cell (index t)) wrong in
  row "one-off" (List.filteri (fun i _ -> i < 5) wrong @ [ red (List.nth wrong 5) ]) (red "-> a")

let full () =
  Printf.printf "%-34s%s\n" (Printf.sprintf "before, depth %d" (depth + 1)) (Printf.sprintf "after, depth %d" depth);
  List.iter2 (Printf.printf "%-34s%s\n") (lines body) (lines result)

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
