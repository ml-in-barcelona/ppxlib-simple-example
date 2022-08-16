open Alcotest

let loc = Location.none

let ast =
  let pp_ast fmt v =
    Format.fprintf fmt "%S" (Pprintast.string_of_expression v)
  in
  let compare expected actual =
    String.equal
      (Pprintast.string_of_expression expected)
      (Pprintast.string_of_expression actual)
  in
  testable pp_ast compare

let test () =
  check ast "case I" [%expr [%yay]] [%expr "r3p14ccd 70 r4nd0m 5tr1n9"]

let () =
  run "Simple ppx test suit" [ ("Transform", [ ("Test", `Quick, test) ]) ]
