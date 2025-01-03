open Ppxlib
module Ast_builder = Ast_builder.Default

let expander ~loc ~path:_ =
  Ast_builder.estring ~loc "Hello future compiler engineer!"

let pattern =
  let open Ast_pattern in
  pstr nil

let extension =
  Context_free.Rule.extension
    (Extension.declare "yay" Expression pattern expander)

let () =
  Driver.register_transformation ~rules:[ extension ] "ppx-simple-example"
