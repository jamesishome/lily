type pos = { file : string; line : int; col : int }

type 'a located = { it : 'a; at : pos }

type base = { sort : string located; container : [ `One | `List | `Option ] }

type field = { label : string located; bind : int located option; base : base }

type body = Index | Fields of field list | Nullary

type ctor = { cname : string located; body : body }

type decl = { name : string located; ctors : ctor list }

exception Error of pos * string

let error at fmt = Printf.ksprintf (fun s -> raise (Error (at, s))) fmt

let describe { file; line; col } message = Printf.sprintf "%s:%d:%d: error: %s" file line col message
