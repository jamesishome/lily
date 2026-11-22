open Check

let sort_name t s = t.sorts.(s).sort

let field_type t f =
  match f.shape with
  | One s -> sort_name t s
  | List s -> sort_name t s ^ " list"
  | Option s -> sort_name t s ^ " option"

let shape = function
  | One s -> Printf.sprintf "R.Sort %d" s
  | List s -> Printf.sprintf "R.List %d" s
  | Option s -> Printf.sprintf "R.Option %d" s

let slot f =
  match f.shape with
  | One _ -> "R.One " ^ f.label
  | List _ -> "R.Many " ^ f.label
  | Option _ -> "R.Maybe " ^ f.label

let record t fields =
  String.concat "; " (List.map (fun f -> Printf.sprintf "%s : %s" f.label (field_type t f)) fields)

let schema b t =
  let p fmt = Printf.bprintf b fmt in
  p "let schema : R.schema =\n";
  p "  { R.sorts = [| %s |];\n"
    (String.concat "; " (Array.to_list (Array.map (fun s -> Printf.sprintf "%S" s.sort) t.sorts)));
  p "    ctors =\n      [|\n";
  Array.iter
    (fun s ->
      p "        [|\n";
      List.iter
        (fun c ->
          let fs =
            List.map
              (fun f -> Printf.sprintf "{ R.label = %S; bind = %d; shape = %s }" f.label f.bind (shape f.shape))
              c.fields
          in
          match fs with
          | [] -> p "          { R.name = %S; fields = [||] };\n" c.name
          | [ f ] -> p "          { R.name = %S; fields = [| %s |] };\n" c.name f
          | fs ->
            p "          { R.name = %S;\n            fields =\n              [| %s |] };\n" c.name
              (String.concat ";\n                 " fs))
        s.ctors;
      p "        |];\n")
    t.sorts;
  p "      |];\n";
  p "    var_sort = %d;\n    var_ctor = %d }\n\n" t.var_sort t.var_ctor

let views b t =
  Array.iteri
    (fun i s ->
      Printf.bprintf b "  %s %s_view =\n" (if i = 0 then "type" else "and") s.sort;
      List.iter
        (fun c ->
          if c.index then Printf.bprintf b "    | %s of int\n" c.name
          else if c.fields = [] then Printf.bprintf b "    | %s\n" c.name
          else Printf.bprintf b "    | %s of { %s }\n" c.name (record t c.fields))
        s.ctors)
    t.sorts

let var_type t = sort_name t t.var_sort

let signature b t =
  let p fmt = Printf.bprintf b fmt in
  p "module type S = sig\n";
  Array.iter (fun s -> p "  type %s\n" s.sort) t.sorts;
  p "\n";
  views b t;
  p "\n  type renaming\n  type substitution\n\n";
  Array.iter
    (fun s ->
      List.iter
        (fun c ->
          if c.index then p "  val %s : int -> %s\n" c.builder s.sort
          else if c.fields = [] then p "  val %s : %s\n" c.builder s.sort
          else
            p "  val %s : %s -> %s\n" c.builder
              (String.concat " -> " (List.map (fun f -> f.label ^ ":" ^ field_type t f) c.fields))
              s.sort)
        s.ctors)
    t.sorts;
  p "  val renaming : src:int -> dst:int -> int array -> renaming\n";
  p "  val substitution : src:int -> dst:int -> %s array -> substitution\n" (var_type t);
  p "  val identity : int -> substitution\n";
  Array.iter
    (fun s ->
      p "\n  module %s : sig\n" (String.capitalize_ascii s.sort);
      p "    type t = %s\n" s.sort;
      p "    val view : t -> %s_view\n" s.sort;
      p "    val well_scoped : depth:int -> t -> bool\n";
      p "    val weaken : depth:int -> by:int -> t -> t\n";
      p "    val rename : renaming -> t -> t\n";
      p "    val subst : substitution -> t -> t\n";
      p "    val subst0 : depth:int -> t -> %s -> t\n" (var_type t);
      p "    val equal : t -> t -> bool\n";
      p "    val to_string : t -> string\n";
      p "  end\n")
    t.sorts;
  p "end\n\n"

let structure b t =
  let p fmt = Printf.bprintf b fmt in
  p "module M : S = struct\n";
  Array.iter (fun s -> p "  type %s = R.tree\n" s.sort) t.sorts;
  p "\n";
  views b t;
  p "\n  type renaming = R.renaming\n  type substitution = R.subst\n\n";
  Array.iter
    (fun s ->
      List.iter
        (fun c ->
          if c.index then p "  let %s = R.var\n" c.builder
          else if c.fields = [] then p "  let %s = R.Node (%d, [||])\n" c.builder c.tag
          else
            p "  let %s %s = R.Node (%d, [| %s |])\n" c.builder
              (String.concat " " (List.map (fun f -> "~" ^ f.label) c.fields))
              c.tag
              (String.concat "; " (List.map slot c.fields)))
        s.ctors)
    t.sorts;
  p "  let renaming ~src ~dst map = R.renaming ~src ~dst map\n";
  p "  let substitution ~src ~dst images = R.substitution schema ~src ~dst images\n";
  p "  let identity = R.identity\n";
  Array.iteri
    (fun i s ->
      p "\n  module %s = struct\n" (String.capitalize_ascii s.sort);
      p "    type t = %s\n\n" s.sort;
      p "    let view : t -> %s_view = function\n" s.sort;
      List.iter
        (fun c ->
          if c.index then p "      | R.Var i -> %s i\n" c.name
          else if c.fields = [] then p "      | R.Node (%d, [||]) -> %s\n" c.tag c.name
          else
            p "      | R.Node (%d, [| %s |]) -> %s { %s }\n" c.tag
              (String.concat "; " (List.map slot c.fields))
              c.name
              (String.concat "; " (List.map (fun f -> f.label) c.fields)))
        s.ctors;
      p "      | _ -> raise (R.Malformed %S)\n\n" s.sort;
      p "    let well_scoped ~depth t = R.well_scoped schema %d ~depth t\n" i;
      p "    let weaken ~depth ~by t = R.weaken schema %d ~depth ~by t\n" i;
      p "    let rename r t = R.rename schema %d r t\n" i;
      p "    let subst s t = R.subst schema %d s t\n" i;
      p "    let subst0 ~depth body r = R.subst0 schema %d ~depth body r\n" i;
      p "    let equal (a : t) (b : t) = a = b\n";
      p "    let to_string t = R.to_string schema %d t\n" i;
      p "  end\n")
    t.sorts;
  p "end\n\ninclude M\n"

let emit t =
  let b = Buffer.create 4096 in
  Buffer.add_string b "module R = Bind\n\n";
  schema b t;
  signature b t;
  structure b t;
  Buffer.contents b
