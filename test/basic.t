Create a file input.ml with the following content
  $ cat > input.ml <<EOF
  > let () = print_endline [%yay]
  > EOF

Run the ppx and print the output
  $ ppx-simple-example.bin --impl input.ml
  let () = print_endline "r3p14ccd 70 r4nd0m 5tr1n9"
