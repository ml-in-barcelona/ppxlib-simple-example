open Ppxlib
module Ast_builder = Ast_builder.Default

let expander ~loc ~path:_ = Ast_builder.estring ~loc "r3p14ccd 70 r4nd0m 5tr1n9"

let pattern =
  let open Ast_pattern in
  pstr nil

let extension =
  Context_free.Rule.extension
    (Extension.declare "yay" Expression pattern expander)

let () =
  Driver.register_transformation ~rules:[ extension ] "ppx-simple-example"
