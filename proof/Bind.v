From Stdlib Require Import Lists.List Arith.Arith Bool.Bool micromega.Lia.
Import ListNotations.
Open Scope bool_scope.

Inductive shape := Sort (s : nat) | List (s : nat) | Option (s : nat).

Record field := { bind : nat; form : shape }.

Record schema := {
  ctors : list (list (list field));
  var_sort : nat;
  var_ctor : nat
}.

Inductive tree :=
| Var (i : nat)
| Node (c : nat) (ss : slots)
with slots :=
| SNil
| SCons (sl : slot) (rest : slots)
with slot :=
| One (t : tree)
| Many (ts : trees)
| Maybe (o : opt)
with trees :=
| TNil
| TCons (t : tree) (rest : trees)
with opt :=
| ONone
| OSome (t : tree).

Definition add (m a b : nat) : option nat :=
  if m - a <? b then None else Some (a + b).

Arguments add : simpl never.

Fixpoint slots_length ss :=
  match ss with SNil => 0 | SCons _ rest => S (slots_length rest) end.

Definition fields (S : schema) (sort c : nat) : option (list field) :=
  match nth_error (ctors S) sort with
  | None => None
  | Some cs =>
    if (c =? var_ctor S) && (sort =? var_sort S) then None
    else nth_error cs c
  end.

Section Map.
  Variable S : schema.
  Variable m : nat.
  Variable f : nat -> nat -> option tree.

  Fixpoint map (k sort : nat) (t : tree) : option tree :=
    match t with
    | Var i => f k i
    | Node c ss =>
      match fields S sort c with
      | None => None
      | Some fs => option_map (Node c) (map_slots k fs ss)
      end
    end
  with map_slots (k : nat) (fs : list field) (ss : slots) : option slots :=
    match ss, fs with
    | SNil, _ => Some SNil
    | SCons _ _, [] => None
    | SCons sl rest, fd :: fs' =>
      match add m k (bind fd) with
      | None => None
      | Some k' =>
        match map_slot k' (form fd) sl, map_slots k fs' rest with
        | Some x, Some xs => Some (SCons x xs)
        | _, _ => None
        end
      end
    end
  with map_slot (k : nat) (sh : shape) (sl : slot) : option slot :=
    match sh, sl with
    | Sort s, One t => option_map One (map k s t)
    | List s, Many ts => option_map Many (map_trees k s ts)
    | Option s, Maybe o => option_map Maybe (map_opt k s o)
    | _, _ => None
    end
  with map_trees (k sort : nat) (ts : trees) : option trees :=
    match ts with
    | TNil => Some TNil
    | TCons t rest =>
      match map k sort t, map_trees k sort rest with
      | Some x, Some xs => Some (TCons x xs)
      | _, _ => None
      end
    end
  with map_opt (k sort : nat) (o : opt) : option opt :=
    match o with
    | ONone => Some ONone
    | OSome t => option_map OSome (map k sort t)
    end.
End Map.

Section Free.
  Variable S : schema.
  Variable m : nat.
  Variable depth : nat.

  Fixpoint free (k sort : nat) (t : tree) : option (option (nat * nat)) :=
    match t with
    | Var i =>
      Some (if (k <=? i) && (depth <=? i - k) then Some (i, k) else None)
    | Node c ss =>
      match fields S sort c with
      | None => None
      | Some fs =>
        if slots_length ss =? length fs then free_slots k fs ss else None
      end
    end
  with free_slots (k : nat) (fs : list field) (ss : slots)
    : option (option (nat * nat)) :=
    match ss, fs with
    | SCons sl rest, fd :: fs' =>
      match add m k (bind fd) with
      | None => None
      | Some k' =>
        match free_slot k' (form fd) sl with
        | Some None => free_slots k fs' rest
        | found => found
        end
      end
    | _, _ => Some None
    end
  with free_slot (k : nat) (sh : shape) (sl : slot)
    : option (option (nat * nat)) :=
    match sh, sl with
    | Sort s, One t => free k s t
    | List s, Many ts => free_trees k s ts
    | Option s, Maybe o => free_opt k s o
    | _, _ => None
    end
  with free_trees (k sort : nat) (ts : trees)
    : option (option (nat * nat)) :=
    match ts with
    | TNil => Some None
    | TCons t rest =>
      match free k sort t with
      | Some None => free_trees k sort rest
      | found => found
      end
    end
  with free_opt (k sort : nat) (o : opt) : option (option (nat * nat)) :=
    match o with
    | ONone => Some None
    | OSome t => free k sort t
    end.
End Free.

Definition well_scoped S m sort depth t := free S m depth 0 sort t = Some None.

Definition shift S m sort n t :=
  if n =? 0 then Some t
  else
    map S m
      (fun k i => if i <? k then Some (Var i) else option_map Var (add m i n))
      0 sort t.

Record subst_ := { src : nat; dst : nat; image : nat -> tree }.

Definition identity d := {| src := d; dst := d; image := Var |}.

Definition apply S m s k i :=
  if i <? k then Some (Var i)
  else shift S m (var_sort S) k (image s (i - k)).

Definition subst S m sort s t :=
  match free S m (src s) 0 sort t with
  | Some None => map S m (apply S m s) 0 sort t
  | _ => None
  end.

Definition weaken S m sort depth n t :=
  match add m depth n with
  | None => None
  | Some _ =>
    match free S m depth 0 sort t with
    | Some None => shift S m sort n t
    | _ => None
    end
  end.

Record renaming := { rsrc : nat; rdst : nat; target : nat -> nat }.

Definition rename S m sort r t :=
  match free S m (rsrc r) 0 sort t with
  | Some None =>
    map S m
      (fun k i =>
         if i <? k then Some (Var i)
         else option_map Var (add m (target r (i - k)) k))
      0 sort t
  | _ => None
  end.

Definition subst0 S m sort depth body r :=
  match add m depth 1 with
  | None => None
  | Some n =>
    match free S m depth 0 (var_sort S) r with
    | Some None =>
      subst S m sort
        {| src := n; dst := depth;
           image := fun i => if i =? 0 then r else Var (i - 1) |} body
    | _ => None
    end
  end.

Fixpoint below m t :=
  match t with
  | Var i => i <=? m
  | Node _ ss => below_slots m ss
  end
with below_slots m ss :=
  match ss with
  | SNil => true
  | SCons sl rest => below_slot m sl && below_slots m rest
  end
with below_slot m sl :=
  match sl with
  | One t => below m t
  | Many ts => below_trees m ts
  | Maybe o => below_opt m o
  end
with below_trees m ts :=
  match ts with
  | TNil => true
  | TCons t rest => below m t && below_trees m rest
  end
with below_opt m o :=
  match o with
  | ONone => true
  | OSome t => below m t
  end.

Section Identity.
  Variable S : schema.
  Variable m : nat.
  Variable f : nat -> nat -> option tree.
  Hypothesis f_id : forall k i, i <= m -> f k i = Some (Var i).
  Variable d : nat.

  Fixpoint map_id k sort t {struct t} :
    below m t = true ->
    free S m d k sort t = Some None -> map S m f k sort t = Some t
  with map_slots_id k fs ss {struct ss} :
    below_slots m ss = true ->
    free_slots S m d k fs ss = Some None ->
    slots_length ss = length fs ->
    map_slots S m f k fs ss = Some ss
  with map_slot_id k sh sl {struct sl} :
    below_slot m sl = true ->
    free_slot S m d k sh sl = Some None -> map_slot S m f k sh sl = Some sl
  with map_trees_id k sort ts {struct ts} :
    below_trees m ts = true ->
    free_trees S m d k sort ts = Some None ->
    map_trees S m f k sort ts = Some ts
  with map_opt_id k sort o {struct o} :
    below_opt m o = true ->
    free_opt S m d k sort o = Some None -> map_opt S m f k sort o = Some o.
  Proof.
    - destruct t as [i | c ss]; simpl; intros B H.
      + apply f_id. now apply Nat.leb_le.
      + destruct (fields S sort c) as [fs |]; [| discriminate].
        destruct (slots_length ss =? length fs) eqn:E; [| discriminate].
        apply Nat.eqb_eq in E.
        rewrite (map_slots_id k fs ss B H E). reflexivity.
    - destruct ss as [| sl rest], fs as [| fd fs']; simpl;
        intros B H E; try reflexivity; try discriminate.
      apply andb_prop in B as [B1 B2].
      destruct (add m k (bind fd)) as [k' |]; [| discriminate].
      destruct (free_slot S m d k' (form fd) sl) as [[[] |] |]
        eqn:F; try discriminate.
      rewrite (map_slot_id _ _ _ B1 F).
      rewrite (map_slots_id k fs' rest B2 H ltac:(injection E; auto)).
      reflexivity.
    - destruct sh, sl as [t | ts | o]; simpl; intros B H; try discriminate.
      + rewrite (map_id _ _ _ B H). reflexivity.
      + rewrite (map_trees_id _ _ _ B H). reflexivity.
      + rewrite (map_opt_id _ _ _ B H). reflexivity.
    - destruct ts as [| t rest]; simpl; intros B H; [reflexivity |].
      apply andb_prop in B as [B1 B2].
      destruct (free S m d k sort t) as [[[] |] |] eqn:F; try discriminate.
      rewrite (map_id _ _ _ B1 F), (map_trees_id _ _ _ B2 H). reflexivity.
    - destruct o as [| t]; simpl; intros B H; [reflexivity |].
      rewrite (map_id _ _ _ B H). reflexivity.
  Qed.
End Identity.

Lemma add_ok m a b : a + b <= m -> add m a b = Some (a + b).
Proof.
  intro L. unfold add.
  destruct (m - a <? b) eqn:E; [apply Nat.ltb_lt in E; lia | reflexivity].
Qed.

Lemma apply_identity S m d k i :
  i <= m -> apply S m (identity d) k i = Some (Var i).
Proof.
  intro L. unfold apply, shift; simpl.
  destruct (i <? k) eqn:K; [reflexivity |].
  apply Nat.ltb_ge in K.
  destruct (k =? 0) eqn:Z.
  - apply Nat.eqb_eq in Z. subst. now rewrite Nat.sub_0_r.
  - simpl. rewrite add_ok by lia. simpl. do 2 f_equal. lia.
Qed.

Theorem subst_identity S m sort d t :
  below m t = true ->
  well_scoped S m sort d t ->
  subst S m sort (identity d) t = Some t.
Proof.
  unfold well_scoped, subst. simpl. intros B H. rewrite H.
  apply map_id with (d := d); auto.
  intros. now apply apply_identity.
Qed.
