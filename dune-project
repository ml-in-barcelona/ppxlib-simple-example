(lang dune 3.21)

(generate_opam_files true)

(package
 (name ppx-simple-example)
 (synopsis "A short description of your project")
 (description "A longer description of your project")
 (depends
  (ocaml (>= 5.4.1))
  (ocaml-lsp-server (>= 1.25.0))
  (ppxlib (>= 0.37.0))
  (ocamlformat (>= 0.28.1))))
