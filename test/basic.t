Create a file input.ml with the following content
  $ cat > input.ml <<EOF
  > let () = print_endline [%yay]
  > EOF

Run the ppx and print the output
  $ ./standalone.exe --impl input.ml
  let () = print_endline "Hello future compiler engineer!"
