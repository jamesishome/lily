
type __ = Obj.t

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some a -> Some (f a)
| None -> None

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val add : int -> int -> int **)

let rec add = (+)

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

module Nat =
 struct
 end

(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> None
              | x :: _ -> Some x)
    (fun n0 -> match l with
               | [] -> None
               | _ :: l' -> nth_error l' n0)
    n

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

(** val add0 : int -> int -> int -> int option **)

let add0 m a b =
  if (<) (sub m a) b then None else Some (add a b)

(** val slots_length : slots -> int **)

let rec slots_length = function
| SNil -> 0
| SCons (_, rest) -> Stdlib.Int.succ (slots_length rest)

(** val fields : schema -> int -> int -> field list option **)

let fields s sort c =
  match nth_error s.ctors sort with
  | Some cs ->
    if (&&) ((=) c s.var_ctor) ((=) sort s.var_sort)
    then None
    else nth_error cs c
  | None -> None

(** val map :
    schema -> int -> (int -> int -> tree option) -> int -> int -> tree ->
    tree option **)

let map s m f =
  let rec map0 k sort = function
  | Var i -> f k i
  | Node (c, ss) ->
    (match fields s sort c with
     | Some fs -> option_map (fun x -> Node (c, x)) (map_slots k fs ss)
     | None -> None)
  and map_slots k fs = function
  | SNil -> Some SNil
  | SCons (sl, rest) ->
    (match fs with
     | [] -> None
     | fd :: fs' ->
       (match add0 m k fd.bind with
        | Some k' ->
          (match map_slot k' fd.form sl with
           | Some x ->
             (match map_slots k fs' rest with
              | Some xs -> Some (SCons (x, xs))
              | None -> None)
           | None -> None)
        | None -> None))
  and map_slot k sh sl =
    match sh with
    | Sort s0 ->
      (match sl with
       | One t -> option_map (fun x -> One x) (map0 k s0 t)
       | _ -> None)
    | List s0 ->
      (match sl with
       | Many ts -> option_map (fun x -> Many x) (map_trees k s0 ts)
       | _ -> None)
    | Option s0 ->
      (match sl with
       | Maybe o -> option_map (fun x -> Maybe x) (map_opt k s0 o)
       | _ -> None)
  and map_trees k sort = function
  | TNil -> Some TNil
  | TCons (t, rest) ->
    (match map0 k sort t with
     | Some x ->
       (match map_trees k sort rest with
        | Some xs -> Some (TCons (x, xs))
        | None -> None)
     | None -> None)
  and map_opt k sort = function
  | ONone -> Some ONone
  | OSome t -> option_map (fun x -> OSome x) (map0 k sort t)
  in map0

(** val free :
    schema -> int -> int -> int -> int -> tree -> (int * int) option option **)

let free s m depth =
  let rec free0 k sort = function
  | Var i ->
    Some
      (if (&&) ((<=) k i) ((<=) depth (sub i k)) then Some (i, k) else None)
  | Node (c, ss) ->
    (match fields s sort c with
     | Some fs ->
       if (=) (slots_length ss) (length fs) then free_slots k fs ss else None
     | None -> None)
  and free_slots k fs = function
  | SNil -> Some None
  | SCons (sl, rest) ->
    (match fs with
     | [] -> Some None
     | fd :: fs' ->
       (match add0 m k fd.bind with
        | Some k' ->
          (match free_slot k' fd.form sl with
           | Some o ->
             (match o with
              | Some p -> Some (Some p)
              | None -> free_slots k fs' rest)
           | None -> None)
        | None -> None))
  and free_slot k sh sl =
    match sh with
    | Sort s0 -> (match sl with
                  | One t -> free0 k s0 t
                  | _ -> None)
    | List s0 -> (match sl with
                  | Many ts -> free_trees k s0 ts
                  | _ -> None)
    | Option s0 -> (match sl with
                    | Maybe o -> free_opt k s0 o
                    | _ -> None)
  and free_trees k sort = function
  | TNil -> Some None
  | TCons (t, rest) ->
    (match free0 k sort t with
     | Some o ->
       (match o with
        | Some p -> Some (Some p)
        | None -> free_trees k sort rest)
     | None -> None)
  and free_opt k sort = function
  | ONone -> Some None
  | OSome t -> free0 k sort t
  in free0

type well_scoped = __

(** val shift : schema -> int -> int -> int -> tree -> tree option **)

let shift s m sort n t =
  if (=) n 0
  then Some t
  else map s m (fun k i ->
         if (<) i k
         then Some (Var i)
         else option_map (fun x -> Var x) (add0 m i n)) 0 sort t

type subst_ = { src : int; dst : int; image : (int -> tree) }

(** val identity : int -> subst_ **)

let identity d =
  { src = d; dst = d; image = (fun x -> Var x) }

(** val apply : schema -> int -> subst_ -> int -> int -> tree option **)

let apply s m s0 k i =
  if (<) i k
  then Some (Var i)
  else shift s m s.var_sort k (s0.image (sub i k))

(** val subst : schema -> int -> int -> subst_ -> tree -> tree option **)

let subst s m sort s0 t =
  match free s m s0.src 0 sort t with
  | Some o ->
    (match o with
     | Some _ -> None
     | None -> map s m (apply s m s0) 0 sort t)
  | None -> None

(** val weaken : schema -> int -> int -> int -> int -> tree -> tree option **)

let weaken s m sort depth n t =
  match add0 m depth n with
  | Some _ ->
    (match free s m depth 0 sort t with
     | Some o -> (match o with
                  | Some _ -> None
                  | None -> shift s m sort n t)
     | None -> None)
  | None -> None

type renaming = { rsrc : int; rdst : int; target : (int -> int) }

(** val rename : schema -> int -> int -> renaming -> tree -> tree option **)

let rename s m sort r t =
  match free s m r.rsrc 0 sort t with
  | Some o ->
    (match o with
     | Some _ -> None
     | None ->
       map s m (fun k i ->
         if (<) i k
         then Some (Var i)
         else option_map (fun x -> Var x) (add0 m (r.target (sub i k)) k)) 0
         sort t)
  | None -> None

(** val subst0 :
    schema -> int -> int -> int -> tree -> tree -> tree option **)

let subst0 s m sort depth body r =
  match add0 m depth (Stdlib.Int.succ 0) with
  | Some n ->
    (match free s m depth 0 s.var_sort r with
     | Some o ->
       (match o with
        | Some _ -> None
        | None ->
          subst s m sort { src = n; dst = depth; image = (fun i ->
            if (=) i 0 then r else Var (sub i (Stdlib.Int.succ 0))) } body)
     | None -> None)
  | None -> None

(** val below : int -> tree -> bool **)

let rec below m = function
| Var i -> (<=) i m
| Node (_, ss) -> below_slots m ss

(** val below_slots : int -> slots -> bool **)

and below_slots m = function
| SNil -> true
| SCons (sl, rest) -> (&&) (below_slot m sl) (below_slots m rest)

(** val below_slot : int -> slot -> bool **)

and below_slot m = function
| One t -> below m t
| Many ts -> below_trees m ts
| Maybe o -> below_opt m o

(** val below_trees : int -> trees -> bool **)

and below_trees m = function
| TNil -> true
| TCons (t, rest) -> (&&) (below m t) (below_trees m rest)

(** val below_opt : int -> opt -> bool **)

and below_opt m = function
| ONone -> true
| OSome t -> below m t
