The example schemas compile, and output is deterministic

  $ lily compile ../../examples/term.li -o a.ml
  $ lily compile ../../examples/term.li -o b.ml
  $ cmp a.ml b.ml
  $ lily compile ../../examples/block.li | grep -c 'module Stmt\|module Expr'
  4

Narrowing the pair arm from two binders to one changes the scope of #1

  $ sed 's/bind 2 in term/bind 1 in term/' ../../examples/term.li > one.li
  $ diff ../../examples/term.li one.li
  10c10
  <   | PairArm of { body: bind 2 in term }
  ---
  >   | PairArm of { body: bind 1 in term }
  [1]
  $ sh ../../examples/probe.sh ../../examples/term.li one.li
  + lily compile ../../examples/term.li -o term.ml
  PairArm { body = #1 } at depth 0 -> accepted
  + lily compile one.li -o term.ml
  PairArm { body = #1 } at depth 0 -> rejected
    substitution input: #1 under 1 local binder is out of scope at depth 0

Malformed schemas report file, line and column

  $ bad() { printf "$2" > "$1.li"; lily compile "$1.li" -o out.ml; echo "exit $?"; }

  $ bad unknown 'type term =\n  | Var of index\n  | App of { fn: term; arg: trem }\n'
  unknown.li:3:29: error: unknown sort 'trem'
  exit 1
  $ bad dupsort 'type term = Var of index\nand term = Nil\n'
  dupsort.li:2:5: error: duplicate sort 'term' collides with the one at 1:6
  exit 1
  $ bad dupctor 'type term = Var of index | Nil\nand arm = Nil\n'
  dupctor.li:2:11: error: duplicate constructor 'Nil' collides with the one at 1:28
  exit 1
  $ bad dupfield 'type term = Var of index | App of { fn: term; fn: term }\n'
  dupfield.li:1:47: error: duplicate field in App: 'fn' collides with the one at 1:37
  exit 1
  $ bad novar 'type term = Nil | App of { fn: term; arg: term }\n'
  novar.li:1:6: error: schema has no variable constructor; mark exactly one with 'of index'
  exit 1
  $ bad twovar 'type term = Var of index | Ref of index\n'
  twovar.li:1:28: error: second variable constructor Ref; Var at 1:13 is already the variable constructor
  exit 1
  $ bad zero 'type term = Var of index | Lam of { body: bind 0 in term }\n'
  zero.li:1:48: error: binder count 0 is invalid; 'bind k in' needs k >= 1
  exit 1
  $ bad huge 'type term = Var of index | Lam of { body: bind 99999999999999999999 in term }\n'
  huge.li:1:48: error: binder count 99999999999999999999 is not a representable natural number
  exit 1
  $ bad index 'type term = Var of index | Box of { inner: index }\n'
  index.li:1:44: error: 'index' is only valid as 'of index' on the variable constructor
  exit 1
  $ bad keyword 'type term = Var of index | Lam of { val: term }\n'
  keyword.li:1:37: error: field name 'val' is an OCaml keyword
  exit 1
  $ bad sortkw 'type method = Var of index\n'
  sortkw.li:1:6: error: sort name 'method' is an OCaml keyword
  exit 1
  $ bad reserved 'type list = Var of index\n'
  reserved.li:1:6: error: sort name 'list' is reserved
  exit 1
  $ bad collide 'type term = Var of index | Let | Let_\n'
  collide.li:1:34: error: generated value 'let_' collides with the one at 1:28
  exit 1
  $ bad builtin 'type term = Var of index | Schema\n'
  builtin.li:1:28: error: generated value 'schema' is reserved by the generated api
  exit 1
  $ bad view 'type term = Var of index\nand term_view = Nil\n'
  view.li:2:5: error: generated type 'term_view' collides with the one at 1:6
  exit 1
  $ bad empty 'type term = Var of index | App of { }\n'
  empty.li:1:37: error: constructor App has an empty field list
  exit 1
  $ bad syntax 'type term = Var of index |\n'
  syntax.li:2:1: error: expected a constructor name but found end of file
  exit 1
  $ bad comment '(* open\ntype term = Var of index\n'
  comment.li:1:1: error: unterminated comment
  exit 1
  $ bad nothing ''
  nothing.li:1:1: error: schema declares no sorts
  exit 1

Bad command lines

  $ lily compile ../../examples/term.li -o bad-name.ml
  lily: bad-name.ml is not a valid OCaml module file name
  [1]
  $ lily compile missing.li -o out.ml
  lily: missing.li: No such file or directory
  [1]
  $ lily frobnicate
  usage: lily compile SCHEMA.li [-o OUTPUT.ml]
  [2]
