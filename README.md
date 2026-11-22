A toy ASDL for syntax with binders. It reads mutually recursive algebraic datatypes and emits OCaml modules with typed builders and capture-avoiding de Bruijn operations

---

The schema language is ASDL with OCaml syntax, plus `bind k in sort`. That annotation extends the context by `k` binders for that one field only. The last binder of a field gets index 0, and fields without an annotation stay in the enclosing context. One constructor per schema is marked `of index`, which fixes the variable sort, and every sort shares one de Bruijn namespace:

```
type term =
  | Var of index
  | Lam of { body: bind 1 in term }
  | App of { fn: term; arg: term }
  | Let of { rhs: term; body: bind 1 in term }
  | LetRec of { rhs: bind 1 in term; body: bind 1 in term }
  | Case of { scrutinee: term; arms: list(arm); fallback: option(term) }

and arm =
  | PairArm of { body: bind 2 in term }
  | DefaultArm of { body: term }
```

`lily compile` turns this into one OCaml module. The module has abstract `term` and `arm` types, a builder per constructor and a one-layer `view` you can pattern match on. Each sort also gets `well_scoped`, `weaken`, `rename`, `subst` and `subst0`, and every one of them takes its context depth explicitly. Index arithmetic lives in [`runtime/bind.ml`](runtime/bind.ml), a single traversal driven by the schema data that lily emits. A substitution applies all its images at once, so an image is never substituted again. Under `k` binders it leaves indices below `k` alone and weakens each inserted image by `k`

The sample comes from `examples/term.li`, and the consumer in `examples/subst.ml` calls `Term.subst0 ~depth:1` on one open term. That term uses `Let`, `LetRec` and `Case` with a pair arm and a fallback. The replacement is `(y y)`, so the inserted copy is easy to spot. Inside the pair arm there are four local binders, and `y` has to move from `#5` to `#4`. A cutoff that is off by one gives `#3` instead, which still passes `well_scoped` but points at the local `a`:


```sh
dune build
dune exec examples/subst.exe
```

A truncated run looks like this:

```
         q        p        f        a        x        y
before   #0       #1       #2       #3       #4       #5
subst0   #0       #1       #2       #3       (#4 #4)  #4       -> y
one-off  #0       #1       #2       #3       (#4 #4)  #3       -> a  captured
...
after Term.subst0 ~depth:1
  let (#0 #0) in                    let a = (y y) in
  letrec (#0 (#2 #2)) in            letrec f = (f (y y)) in
  case #1                           case a
  | pair (#0 #1 #2 #3 (#4 #4) #4)   | (p, q) -> (q p f a (y y) y)
  | _ (#2 #2)                       | _ -> (y y)
  else #2                           else y
```

Scope comes from the schema. If you change the pair arm to `bind 1 in term` in a copy and regenerate, the same probe stops accepting a closed arm whose body is `#1`:

```sh
mkdir -p /tmp/lily
sed 's/bind 2/bind 1/' examples/term.li > /tmp/lily/one.li
PATH=$PWD/_build/install/default/bin:$PATH sh examples/probe.sh examples/term.li /tmp/lily/one.li
```

```
  probe   PairArm { body = #1 } at depth 0 -> accepted
  ...
  probe   PairArm { body = #1 } at depth 0 -> rejected
      substitution input: #1 under 1 local binder is out of scope at depth 0
```

To run the tests from a clean checkout:

```sh
dune test
```

They build OCaml modules from both checked-in schemas and assert exact results for the example, identity substitutions and a simultaneous swap whose images must not be substituted again. They also cover empty containers, depths and maps that are out of scope or overflow, and 19 malformed schemas, each reported as `file:line:col`

---

### Stage 2

Rocq stays out of this build. The functions to model are `map`, `free`, `shift`, `apply`, `subst`, `subst0`, `rename` and the `renaming` and `substitution` constructors that check their inputs, all over `shape`, `field` and `tree` in `runtime/bind.ml`. Write `Σ ⊢ t : s @ d` when `well_scoped Σ s d t` holds and `σ : d ⇒ d'` when every image is scoped at `d'`. The statements to prove are:

- scope preservation: `Σ ⊢ t : s @ d → σ : d ⇒ d' → Σ ⊢ subst σ t : s @ d'`, and the same for `rename` and `weaken`
- identity: `Σ ⊢ t : s @ d → subst (identity d) t = t`
- composition: `subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t`
- `subst0` against `weaken`: `subst0 d (weaken d 1 t) r = t`
