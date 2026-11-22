open Syntax

type shape = One of int | List of int | Option of int

type field = { label : string; bind : int; shape : shape }

type ctor = { name : string; builder : string; tag : int; fields : field list; index : bool }

type sort = { sort : string; ctors : ctor list }

type t = { sorts : sort array; var_sort : int; var_ctor : int }

let keywords =
  [ "and"; "as"; "assert"; "asr"; "begin"; "class"; "constraint"; "do"; "done"; "downto"; "effect"; "else";
    "end"; "exception"; "external"; "false"; "for"; "fun"; "function"; "functor"; "if"; "in"; "include";
    "inherit"; "initializer"; "land"; "lazy"; "let"; "lor"; "lsl"; "lsr"; "lxor"; "match"; "method"; "mod";
    "module"; "mutable"; "new"; "nonrec"; "object"; "of"; "open"; "or"; "private"; "rec"; "sig"; "struct";
    "then"; "to"; "true"; "try"; "type"; "val"; "virtual"; "when"; "while"; "with" ]

let reserved = [ "list"; "option"; "index"; "bind"; "int"; "bool"; "string"; "unit" ]

let where p = Printf.sprintf "%d:%d" p.line p.col

let snake name =
  let b = Buffer.create (String.length name + 4) in
  String.iteri
    (fun i c ->
      match c with
      | 'A' .. 'Z' ->
        (if i > 0 then match name.[i - 1] with 'a' .. 'z' | '0' .. '9' -> Buffer.add_char b '_' | _ -> ());
        Buffer.add_char b (Char.lowercase_ascii c)
      | c -> Buffer.add_char b c)
    name;
  let s = Buffer.contents b in
  if List.mem s keywords then s ^ "_" else s

let lower_ident what { it; at } =
  if it.[0] = '_' then error at "%s '%s' may not start with an underscore" what it;
  if List.mem it keywords then error at "%s '%s' is an OCaml keyword" what it

let distinct what items =
  let seen = Hashtbl.create 16 in
  List.iter
    (fun (name, at) ->
      match Hashtbl.find_opt seen name with
      | Some first when first.line = 0 -> error at "%s '%s' is reserved by the generated api" what name
      | Some first -> error at "%s '%s' collides with the one at %s" what name (where first)
      | None -> Hashtbl.add seen name at)
    items

let check (decls : decl list) =
  List.iter
    (fun (d : decl) ->
      lower_ident "sort name" d.name;
      if List.mem d.name.it reserved then error d.name.at "sort name '%s' is reserved" d.name.it)
    decls;
  distinct "duplicate sort" (List.map (fun (d : decl) -> d.name.it, d.name.at) decls);
  distinct "duplicate constructor"
    (List.concat_map (fun (d : decl) -> List.map (fun c -> c.cname.it, c.cname.at) d.ctors) decls);
  let index = Hashtbl.create 16 in
  List.iteri (fun i (d : decl) -> Hashtbl.replace index d.name.it i) decls;
  let variables =
    List.concat
      (List.mapi
         (fun s (d : decl) ->
           List.concat (List.mapi (fun c ctor -> if ctor.body = Index then [ s, c, ctor.cname ] else []) d.ctors))
         decls)
  in
  let var_sort, var_ctor =
    match variables with
    | [ (s, c, _) ] -> s, c
    | [] -> error (List.hd decls).name.at "schema has no variable constructor; mark exactly one with 'of index'"
    | (_, _, first) :: (_, _, second) :: _ ->
      error second.at "second variable constructor %s; %s at %s is already the variable constructor" second.it
        first.it (where first.at)
  in
  let resolve (b : base) =
    if b.sort.it = "index" then error b.sort.at "'index' is only valid as 'of index' on the variable constructor";
    match Hashtbl.find_opt index b.sort.it with
    | None -> error b.sort.at "unknown sort '%s'" b.sort.it
    | Some s -> ( match b.container with `One -> One s | `List -> List s | `Option -> Option s)
  in
  let field (f : Syntax.field) =
    lower_ident "field name" f.label;
    let bind =
      match f.bind with
      | None -> 0
      | Some { it = k; at } ->
        if k < 1 then error at "binder count %d is invalid; 'bind k in' needs k >= 1" k;
        k
    in
    { label = f.label.it; bind; shape = resolve f.base }
  in
  let sorts =
    List.map
      (fun (d : decl) ->
        let ctors =
          List.mapi
            (fun tag c ->
              let fields =
                match c.body with
                | Fields fs ->
                  distinct (Printf.sprintf "duplicate field in %s:" c.cname.it)
                    (List.map (fun (f : Syntax.field) -> f.label.it, f.label.at) fs);
                  List.map field fs
                | Index | Nullary -> []
              in
              { name = c.cname.it; builder = snake c.cname.it; tag; fields; index = c.body = Index })
            d.ctors
        in
        { sort = d.name.it; ctors })
      decls
  in
  let fixed = { file = "<generated>"; line = 0; col = 0 } in
  let values =
    List.map (fun n -> n, fixed) [ "renaming"; "substitution"; "identity"; "schema" ]
    @ List.concat_map (fun (d : decl) -> List.map (fun c -> snake c.cname.it, c.cname.at) d.ctors) decls
  in
  distinct "generated value" values;
  let types =
    List.map (fun n -> n, fixed) [ "renaming"; "substitution" ]
    @ List.concat_map (fun (d : decl) -> [ d.name.it, d.name.at; d.name.it ^ "_view", d.name.at ]) decls
  in
  distinct "generated type" types;
  let modules =
    List.map (fun n -> n, fixed) [ "R"; "S"; "M" ]
    @ List.map (fun (d : decl) -> String.capitalize_ascii d.name.it, d.name.at) decls
  in
  distinct "generated module" modules;
  { sorts = Array.of_list sorts; var_sort; var_ctor }
