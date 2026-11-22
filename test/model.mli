
type __ = Obj.t

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

val length : 'a1 list -> int

val add : int -> int -> int

val sub : int -> int -> int

module Nat :
 sig
 end

val nth_error : 'a1 list -> int -> 'a1 option

type shape =
| Sort of int
| List of int
| Option of int

type field = { bind : int; form : shape }

type schema = { ctors : field list list list; var_sort : int; var_ctor : int }

type tree =
| Var of int
| Node of int * slots
and slots =
| SNil
| SCons of slot * slots
and slot =
| One of tree
| Many of trees
| Maybe of opt
and trees =
| TNil
| TCons of tree * trees
and opt =
| ONone
| OSome of tree

val add0 : int -> int -> int -> int option

val slots_length : slots -> int

val fields : schema -> int -> int -> field list option

val map :
  schema -> int -> (int -> int -> tree option) -> int -> int -> tree -> tree
  option

val free :
  schema -> int -> int -> int -> int -> tree -> (int * int) option option

type well_scoped = __

val shift : schema -> int -> int -> int -> tree -> tree option

type subst_ = { src : int; dst : int; image : (int -> tree) }

val identity : int -> subst_

val apply : schema -> int -> subst_ -> int -> int -> tree option

val subst : schema -> int -> int -> subst_ -> tree -> tree option

val weaken : schema -> int -> int -> int -> int -> tree -> tree option

type renaming = { rsrc : int; rdst : int; target : (int -> int) }

val rename : schema -> int -> int -> renaming -> tree -> tree option

val subst0 : schema -> int -> int -> int -> tree -> tree -> tree option

val below : int -> tree -> bool

val below_slots : int -> slots -> bool

val below_slot : int -> slot -> bool

val below_trees : int -> trees -> bool

val below_opt : int -> opt -> bool
