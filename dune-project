(lang dune 3.10)
(name lily)
(version 0.1.0)
(cram enable)
(generate_opam_files true)
(package
 (name lily)
 (synopsis "Schema compiler for syntax with binders")
 (depends (ocaml (>= 4.14)) dune))
