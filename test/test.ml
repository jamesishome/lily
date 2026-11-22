let failures = ref 0

let check name ok =
  if not ok then begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end
  else Printf.printf "ok   %s\n" name

let raises name f =
  check name
    (match f () with
    | _ -> false
    | exception (Bind.Scope_error _ | Bind.Overflow _) -> true)

module T = struct
  open Term

  let apps = function [] -> assert false | f :: args -> List.fold_left (fun fn arg -> app ~fn ~arg) f args

  let v = var

  let body =
    let_ ~rhs:(v 0)
      ~body:
        (let_rec ~rhs:(apps [ v 0; v 2 ])
           ~body:
             (case ~scrutinee:(v 1)
                ~arms:[ pair_arm ~body:(apps (List.init 6 v)); default_arm ~body:(v 2) ]
                ~fallback:(Some (v 3))))

  let r = apps [ v 0; v 0 ]

  let expected y =
    let_ ~rhs:(apps [ v 0; v 0 ])
      ~body:
        (let_rec ~rhs:(apps [ v 0; apps [ v 2; v 2 ] ])
           ~body:
             (case ~scrutinee:(v 1)
                ~arms:[ pair_arm ~body:(apps [ v 0; v 1; v 2; v 3; apps [ v 4; v 4 ]; v y ]); default_arm ~body:(apps [ v 2; v 2 ]) ]
                ~fallback:(Some (v 2))))

  let run () =
    let result = Term.subst0 ~depth:1 body r in
    check "example subst0 gives the exact term" (Term.equal result (expected 4));
    check "example capture variant is still well scoped" (Term.well_scoped ~depth:1 (expected 3));
    check "example capture variant differs from the result" (not (Term.equal result (expected 3)));
    check "example result is well scoped at depth 1" (Term.well_scoped ~depth:1 result);
    check "example body is not well scoped at depth 1" (not (Term.well_scoped ~depth:1 body));
    check "identity substitution on term" (Term.equal (Term.subst (identity 2) body) body);
    let arm = pair_arm ~body:(apps [ v 0; v 1; v 2 ]) in
    check "identity substitution on arm" (Arm.equal (Arm.subst (identity 1) arm) arm);
    check "identity renaming" (Term.equal (Term.rename (renaming ~src:2 ~dst:2 [| 0; 1 |]) body) body);
    let swap = substitution ~src:2 ~dst:2 [| v 1; v 0 |] in
    check "simultaneous swap" (Term.equal (Term.subst swap (apps [ v 0; v 1 ])) (apps [ v 1; v 0 ]));
    let s = substitution ~src:2 ~dst:2 [| apps [ v 0; v 1 ]; v 0 |] in
    check "images are not substituted again"
      (Term.equal (Term.subst s (apps [ v 0; v 1 ])) (apps [ apps [ v 0; v 1 ]; v 0 ]));
    check "images are weakened under binders"
      (Term.equal (Term.subst s (lam ~body:(apps [ v 0; v 1; v 2 ]))) (lam ~body:(apps [ v 0; apps [ v 1; v 2 ]; v 1 ])));
    let empty = case ~scrutinee:(v 0) ~arms:[] ~fallback:None in
    check "empty containers survive subst0" (Term.equal (Term.subst0 ~depth:0 empty (lam ~body:(v 0))) (case ~scrutinee:(lam ~body:(v 0)) ~arms:[] ~fallback:None));
    check "empty containers well scoped" (Term.well_scoped ~depth:1 empty && not (Term.well_scoped ~depth:0 empty));
    check "weaken shifts only free indices"
      (Term.equal (Term.weaken ~depth:1 ~by:2 (lam ~body:(apps [ v 0; v 1 ]))) (lam ~body:(apps [ v 0; v 3 ])));
    check "rename crosses sorts and containers"
      (Term.equal
         (Term.rename (renaming ~src:2 ~dst:3 [| 2; 0 |]) (case ~scrutinee:(v 1) ~arms:[ pair_arm ~body:(v 3) ] ~fallback:(Some (v 0))))
         (case ~scrutinee:(v 0) ~arms:[ pair_arm ~body:(v 2) ] ~fallback:(Some (v 2))));
    check "subst0 cancels weaken" (Term.equal (Term.subst0 ~depth:2 (Term.weaken ~depth:2 ~by:1 body) r) body);
    check "two binders scope #1 in a closed arm" (Arm.well_scoped ~depth:0 (pair_arm ~body:(v 1)));
    check "two binders do not scope #2 in a closed arm" (not (Arm.well_scoped ~depth:0 (pair_arm ~body:(v 2))));
    raises "subst0 rejects a body outside depth + 1" (fun () -> Term.subst0 ~depth:0 body r);
    raises "subst0 rejects a replacement outside depth" (fun () -> Term.subst0 ~depth:0 (v 0) r);
    raises "subst0 rejects a negative depth" (fun () -> Term.subst0 ~depth:(-1) (v 0) r);
    raises "subst rejects a term outside its source" (fun () -> Term.subst (identity 1) body);
    raises "substitution rejects an image outside its target" (fun () -> substitution ~src:1 ~dst:1 [| v 1 |]);
    raises "substitution rejects a wrong domain" (fun () -> substitution ~src:2 ~dst:2 [| v 0 |]);
    raises "renaming rejects a target outside its range" (fun () -> renaming ~src:1 ~dst:1 [| 1 |]);
    raises "renaming rejects a wrong domain" (fun () -> renaming ~src:1 ~dst:3 [| 0; 1 |]);
    raises "rename rejects a term outside its source" (fun () -> Term.rename (renaming ~src:1 ~dst:1 [| 0 |]) body);
    raises "weaken rejects a term outside its depth" (fun () -> Term.weaken ~depth:1 ~by:1 body);
    raises "weaken rejects a negative amount" (fun () -> Term.weaken ~depth:2 ~by:(-1) body);
    raises "negative index" (fun () -> v (-1));
    raises "weaken reports depth overflow" (fun () -> Term.weaken ~depth:max_int ~by:1 (v 0));
    raises "subst0 reports depth overflow" (fun () -> Term.subst0 ~depth:max_int (v 0) (v 0));
    check "no index is free at a huge depth" (Term.well_scoped ~depth:max_int (v (max_int - 1)));
    check "max_int is out of scope at depth max_int" (not (Term.well_scoped ~depth:max_int (v max_int)))
end

module B = struct
  open Block

  let s = slot

  let run () =
    let l = loop ~body:[ local ~init:(s 2) ~scope:skip; seq ~first:skip ~rest:(local ~init:(s 3) ~scope:skip) ] in
    check "list binders scope every element" (Stmt.well_scoped ~depth:2 l && not (Stmt.well_scoped ~depth:1 l));
    let result = Stmt.subst0 ~depth:1 l (call ~callee:(s 0) ~args:[]) in
    check "subst0 through a list under two binders"
      (Stmt.equal result
         (loop ~body:[ local ~init:(call ~callee:(s 2) ~args:[]) ~scope:skip; seq ~first:skip ~rest:(local ~init:(s 2) ~scope:skip) ]));
    let g = guard ~test:None ~body:(local ~init:(s 0) ~scope:(loop ~body:[])) in
    check "variable sort can come second" (Expr.equal (Expr.subst (identity 1) g) g);
    check "nullary constructors view" (match Stmt.view skip with Skip -> true | _ -> false);
    check "empty list under binders" (Stmt.well_scoped ~depth:0 (loop ~body:[]))
end

let () =
  T.run ();
  B.run ();
  if !failures > 0 then begin
    Printf.printf "%d failures\n" !failures;
    exit 1
  end
