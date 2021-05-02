open Ppxlib;

module Builder = Ast_builder.Default;
module Helper = Ast_helper;

let expander = (~loc, ~path as _) => {
  let innerFunName = Builder.pexp_ident(~loc, {txt: Lident("lola"), loc});

  let argument =
    Builder.pexp_apply(
      ~loc,
      innerFunName,
      [
        (Nolabel, Builder.pexp_constant(~loc, Helper.Const.string("value"))),
      ],
    );

  let funName = Builder.pexp_ident(~loc, {txt: Lident("style"), loc});
  let expr = Builder.pexp_apply(~loc, funName, [(Nolabel, argument)]);

  {
    ...expr,
    pexp_attributes: [
      Builder.attribute(~name={loc, txt: "bs"}, ~loc, ~payload=PStr([])),
    ],
  };
};

let extension =
  Context_free.Rule.extension(
    Extension.declare("yay", Expression, Ast_pattern.(pstr(nil)), expander),
  );

let () = Driver.register_transformation(~rules=[extension], "simple-ppx");
