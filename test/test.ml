open Alcotest
open Ppxlib
    
let loc = Location.none


module Ast = Ast
module Ast_helper = Ast_helper
module Ast_magic = Selected_ast.Ast.Config
module Asttypes = Asttypes
module Parse = Parse
module Parsetree = Parsetree
module Pprintast = Astlib.Pprintast
module Selected_ast = Selected_ast

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
  check ast "case I" [%expr "r3p14ccd 70 r4nd0m 5tr1n9"] [%expr [%yay]]

let () =
  run "Simple ppx test suit" [ ("Transform", [ ("Test", `Quick, test) ]) ]
