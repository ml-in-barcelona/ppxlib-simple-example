(lang dune 3.12)

(generate_opam_files true)

(package
 (name ppx-simple-example)
 (synopsis "A short description of your project")
 (description "A longer description of your project")
 (depends
  (dune (>= 3.17.0))
  (ocaml-lsp-server (>= 1.20.1))
  (ppxlib (>= 0.27.0))
  (ocamlformat (>= 0.27.0))))
