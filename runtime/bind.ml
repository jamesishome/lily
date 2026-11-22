type shape = Sort of int | List of int | Option of int

type field = { label : string; bind : int; shape : shape }

type ctor = { name : string; fields : field array }

type schema = { sorts : string array; ctors : ctor array array; var_sort : int; var_ctor : int }

type tree = Var of int | Node of int * slot array

and slot = One of tree | Many of tree list | Maybe of tree option

exception Scope_error of string

exception Overflow of string

exception Malformed of string

let scope_error fmt = Printf.ksprintf (fun s -> raise (Scope_error s)) fmt

let add a b = if b > max_int - a then raise (Overflow (Printf.sprintf "%d + %d exceeds max_int" a b)) else a + b

let nonnegative what n = if n < 0 then scope_error "%s %d is negative" what n

let var i =
  nonnegative "index" i;
  Var i

let fields schema sort c =
  let ctors = schema.ctors.(sort) in
  if c < 0 || c >= Array.length ctors || c = schema.var_ctor && sort = schema.var_sort then
    raise (Malformed (Printf.sprintf "tag %d is not a node of sort %s" c schema.sorts.(sort)));
  ctors.(c).fields

let rec map schema f k sort t =
  match t with
  | Var i -> f k i
  | Node (c, slots) ->
    let fs = fields schema sort c in
    Node (c, Array.mapi (fun j slot -> map_slot schema f (add k fs.(j).bind) fs.(j).shape slot) slots)

and map_slot schema f k shape slot =
  match shape, slot with
  | Sort s, One t -> One (map schema f k s t)
  | List s, Many ts -> Many (List.map (map schema f k s) ts)
  | Option s, Maybe o -> Maybe (Option.map (map schema f k s) o)
  | _ -> raise (Malformed "slot does not match its field shape")

let rec free schema depth k sort t =
  match t with
  | Var i -> if i < 0 || i - k >= depth then Some (i, k) else None
  | Node (c, slots) ->
    let fs = fields schema sort c in
    if Array.length slots <> Array.length fs then raise (Malformed "arity mismatch");
    let rec go j =
      if j = Array.length slots then None
      else
        match free_slot schema depth (add k fs.(j).bind) fs.(j).shape slots.(j) with
        | None -> go (j + 1)
        | found -> found
    in
    go 0

and free_slot schema depth k shape slot =
  match shape, slot with
  | Sort s, One t -> free schema depth k s t
  | List s, Many ts -> List.find_map (free schema depth k s) ts
  | Option s, Maybe o -> Option.bind o (free schema depth k s)
  | _ -> raise (Malformed "slot does not match its field shape")

let well_scoped schema sort ~depth t = depth >= 0 && free schema depth 0 sort t = None

let require schema sort what depth t =
  nonnegative (what ^ " depth") depth;
  match free schema depth 0 sort t with
  | None -> ()
  | Some (i, k) ->
    scope_error "%s: #%d under %d local binder%s is out of scope at depth %d" what i k (if k = 1 then "" else "s") depth

let shift schema sort by t =
  if by = 0 then t else map schema (fun k i -> Var (if i < k then i else add i by)) 0 sort t

let weaken schema sort ~depth ~by t =
  nonnegative "weakening" by;
  ignore (add depth by);
  require schema sort "weaken input" depth t;
  shift schema sort by t

type renaming = { rsrc : int; rdst : int; target : int -> int }

let renaming ~src ~dst map =
  nonnegative "source depth" src;
  nonnegative "target depth" dst;
  if Array.length map <> src then
    scope_error "renaming has %d entries but its source depth is %d" (Array.length map) src;
  Array.iteri
    (fun i j -> if j < 0 || j >= dst then scope_error "renaming sends #%d to #%d outside depth %d" i j dst)
    map;
  let map = Array.copy map in
  { rsrc = src; rdst = dst; target = Array.get map }

let rename schema sort r t =
  require schema sort "rename input" r.rsrc t;
  map schema (fun k i -> Var (if i < k then i else add (r.target (i - k)) k)) 0 sort t

type subst = { src : int; dst : int; image : int -> tree }

let substitution schema ~src ~dst images =
  nonnegative "source depth" src;
  nonnegative "target depth" dst;
  if Array.length images <> src then
    scope_error "substitution has %d images but its source depth is %d" (Array.length images) src;
  Array.iteri (fun i t -> require schema schema.var_sort (Printf.sprintf "image of #%d" i) dst t) images;
  let images = Array.copy images in
  { src; dst; image = Array.get images }

let identity depth =
  nonnegative "depth" depth;
  { src = depth; dst = depth; image = (fun i -> Var i) }

let apply schema s k i = if i < k then Var i else shift schema schema.var_sort k (s.image (i - k))

let subst schema sort s t =
  require schema sort "substitution input" s.src t;
  map schema (apply schema s) 0 sort t

let subst0 schema sort ~depth body r =
  nonnegative "depth" depth;
  let src = add depth 1 in
  require schema schema.var_sort "replacement" depth r;
  subst schema sort { src; dst = depth; image = (fun i -> if i = 0 then r else Var (i - 1)) } body

let rec print schema sort b t =
  match t with
  | Var i -> Printf.bprintf b "#%d" i
  | Node (c, slots) ->
    let ctor = schema.ctors.(sort).(c) in
    Buffer.add_string b ctor.name;
    if slots <> [||] then begin
      Buffer.add_string b " { ";
      Array.iteri
        (fun j slot ->
          if j > 0 then Buffer.add_string b "; ";
          Printf.bprintf b "%s = " ctor.fields.(j).label;
          print_slot schema ctor.fields.(j).shape b slot)
        slots;
      Buffer.add_string b " }"
    end

and print_slot schema shape b slot =
  match shape, slot with
  | Sort s, One t -> print schema s b t
  | List s, Many ts ->
    Buffer.add_char b '[';
    List.iteri
      (fun j t ->
        if j > 0 then Buffer.add_string b "; ";
        print schema s b t)
      ts;
    Buffer.add_char b ']'
  | Option _, Maybe None -> Buffer.add_string b "None"
  | Option s, Maybe (Some t) ->
    Buffer.add_string b "Some (";
    print schema s b t;
    Buffer.add_char b ')'
  | _ -> raise (Malformed "slot does not match its field shape")

let to_string schema sort t =
  let b = Buffer.create 64 in
  print schema sort b t;
  Buffer.contents b
