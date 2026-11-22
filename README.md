A toy ASDL for syntax with binders that emits OCaml modules with capture-avoiding de Bruijn operations

---

The input language lets you specify mutually recursive variant types in OCaml-esque syntax where `bind k in` puts a field under `k` new binders and `of index` marks the variable constructor:

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

The generator then produces abstract types, typed builders and a one layer view + `well_scoped`, `weaken`, `rename`, `subst` and `subst0` for each sort. Each operation takes its context depth explicitly. The program substitutes `(y y)` for `x` in an open term. Inside the pair arm `y` sits under 4 local binders so it should move from `#5` to `#4`. A cutoff that is off by one would give `#3` instead and capture the local `a`:

```
         q        p        f        a        x        y
before   #0       #1       #2       #3       #4       #5
subst0   #0       #1       #2       #3       (#4 #4)  #4       -> y
one-off  #0       #1       #2       #3       (#4 #4)  #3       -> a
...
```
---

### TODO

- ~~Model `subst0`, `rename` + `weaken` in Rocq~~
- Prove that `subst σ` takes terms scoped at `d` to terms scoped at `d'` when every image of `σ` is scoped at `d'`
- Prove that `subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t`
