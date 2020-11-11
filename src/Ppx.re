open Ppxlib;

let expander = (~loc, ~path as _) =>
  Ast_builder.Default.estring(~loc, {|🎉|});

let extension =
  Context_free.Rule.extension(
    Extension.declare("yay", Expression, Ast_pattern.(pstr(nil)), expander),
  );

let () = Driver.register_transformation(~rules=[extension], "simple-ppx");
