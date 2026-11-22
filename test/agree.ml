let m = max_int

let rec tree : Bind.tree -> Model.tree = function
  | Bind.Var i -> Model.Var i
  | Bind.Node (c, slots) -> Model.Node (c, Array.fold_right (fun s acc -> Model.SCons (slot s, acc)) slots Model.SNil)

and slot = function
  | Bind.One t -> Model.One (tree t)
  | Bind.Many ts -> Model.Many (List.fold_right (fun t acc -> Model.TCons (tree t, acc)) ts Model.TNil)
  | Bind.Maybe None -> Model.Maybe Model.ONone
  | Bind.Maybe (Some t) -> Model.Maybe (Model.OSome (tree t))

let shape = function Bind.Sort s -> Model.Sort s | Bind.List s -> Model.List s | Bind.Option s -> Model.Option s

let schema (s : Bind.schema) : Model.schema =
  let field (f : Bind.field) = { Model.bind = f.bind; form = shape f.shape } in
  let ctor (c : Bind.ctor) = Array.to_list (Array.map field c.fields) in
  { Model.ctors = Array.to_list (Array.map (fun cs -> Array.to_list (Array.map ctor cs)) s.ctors);
    var_sort = s.var_sort;
    var_ctor = s.var_ctor }

let catch f =
  match f () with
  | x -> Some x
  | exception (Bind.Scope_error _ | Bind.Overflow _ | Bind.Malformed _ | Invalid_argument _) -> None

let huge : Bind.schema =
  let f bind shape = { Bind.label = "f"; bind; shape } in
  { Bind.sorts = [| "a"; "b" |];
    ctors =
      [| [| { Bind.name = "V"; fields = [||] };
            { Bind.name = "Deep"; fields = [| f (max_int - 3) (Bind.Sort 0); f 2 (Bind.List 1) |] };
            { Bind.name = "Wide"; fields = [| f 1 (Bind.Option 0); f (max_int / 2) (Bind.Sort 0) |] } |];
         [| { Bind.name = "B"; fields = [| f 3 (Bind.Sort 0) |] }; { Bind.name = "E"; fields = [||] } |] |];
    var_sort = 0;
    var_ctor = 0 }

let index () =
  match Random.int 10 with
  | 0 -> max_int - Random.int 4
  | 1 -> Random.bits ()
  | _ -> Random.int 9

let rec gen (s : Bind.schema) sort size =
  let ctors = s.ctors.(sort) in
  if size <= 0 || Random.int 4 = 0 then
    if sort = s.var_sort || Random.int 8 = 0 then Bind.Var (index ()) else Bind.Node (Random.int (Array.length ctors + 1), [||])
  else
    let c = Random.int (Array.length ctors + if Random.int 10 = 0 then 1 else 0) in
    let fields = if c < Array.length ctors then ctors.(c).fields else [||] in
    let arity = if Random.int 12 = 0 then Random.int 4 else Array.length fields in
    let any () = Random.int (Array.length s.sorts) in
    let slot j =
      let sh = if j < Array.length fields && Random.int 15 > 0 then fields.(j).shape else Bind.Sort (any ()) in
      let size = size / 2 in
      match sh, Random.int 20 with
      | _, 0 -> Bind.Many []
      | _, 1 -> Bind.Maybe None
      | Bind.Sort t, _ -> Bind.One (gen s t size)
      | Bind.List t, _ -> Bind.Many (List.init (Random.int 3) (fun _ -> gen s t size))
      | Bind.Option t, _ -> Bind.Maybe (if Random.bool () then Some (gen s t size) else None)
    in
    Bind.Node (c, Array.init arity slot)

let counts = Hashtbl.create 8

let tally name ok = Hashtbl.replace counts (name, ok) (1 + Option.value ~default:0 (Hashtbl.find_opt counts (name, ok)))

let failures = ref 0

let agree name (s : Bind.schema) t runtime model =
  let expected = Option.map tree (catch runtime) in
  tally name (expected <> None);
  if expected <> model then begin
    incr failures;
    Printf.printf "MISMATCH %s on %s\n" name (try Bind.to_string s 0 t with _ -> "<unprintable>")
  end

let run (s : Bind.schema) cases =
  let ms = schema s in
  for _ = 1 to cases do
    let sort = Random.int (Array.length s.sorts) in
    let t = gen s sort 6 in
    let mt = tree t in
    if not (Model.below m mt) then failwith "index above max_int";
    let depth = if Random.int 6 = 0 then max_int - Random.int 3 else Random.int 6 in
    let k = if Random.int 6 = 0 then max_int - Random.int 3 else Random.int 4 in
    let free = catch (fun () -> Bind.free s depth k sort t) in
    tally "free" (free <> None);
    if free <> Model.free ms m depth k sort mt then begin
      incr failures;
      print_endline "MISMATCH free"
    end;
    let by = if Random.int 5 = 0 then max_int - Random.int 3 else Random.int 4 in
    agree "shift" s t (fun () -> Bind.shift s sort by t) (Model.shift ms m sort by mt);
    agree "subst identity" s t (fun () -> Bind.subst s sort (Bind.identity depth) t) (Model.subst ms m sort (Model.identity depth) mt);
    let src = Random.int 6 and dst = Random.int 6 in
    let images = Array.init 8 (fun _ -> gen s s.var_sort 2) in
    let image i = images.(i mod 8) in
    agree "subst" s t
      (fun () -> Bind.subst s sort { Bind.src; dst; image } t)
      (Model.subst ms m sort { Model.src; dst; image = (fun i -> tree (image i)) } mt);
    agree "weaken" s t (fun () -> Bind.weaken s sort ~depth ~by t) (Model.weaken ms m sort depth by mt);
    let table = Array.init 8 (fun _ -> index ()) in
    let target i = table.(i mod 8) in
    agree "rename" s t
      (fun () -> Bind.rename s sort { Bind.rsrc = src; rdst = dst; target } t)
      (Model.rename ms m sort { Model.rsrc = src; rdst = dst; target } mt);
    let r = image 0 in
    agree "subst0" s t (fun () -> Bind.subst0 s sort ~depth t r) (Model.subst0 ms m sort depth mt (tree r))
  done

let () =
  Random.init 2026;
  run Term.schema 20000;
  run Block.schema 20000;
  run huge 20000;
  let names = [ "free"; "shift"; "subst identity"; "subst"; "weaken"; "rename"; "subst0" ] in
  List.iter
    (fun n ->
      let get ok = Option.value ~default:0 (Hashtbl.find_opt counts (n, ok)) in
      Printf.printf "%-15s %6d returned  %6d raised\n" n (get true) (get false))
    names;
  if !failures > 0 then begin
    Printf.printf "%d mismatches\n" !failures;
    exit 1
  end
