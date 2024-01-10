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

type expression_desc =
  | Pexp_ident of longident_loc  
  | Pexp_constant of constant
  | Pexp_let of rec_flag * value_binding list * expression
  | Pexp_function of cases  
  | Pexp_fun of arg_label * expression option * pattern * expression
  | Pexp_apply of expression * (arg_label * expression) list
  | Pexp_match of expression * cases
  | Pexp_try of expression * cases
  | Pexp_tuple of expression list
  | Pexp_construct of longident_loc * expression option
  | Pexp_variant of label * expression option
  | Pexp_record of (longident_loc * expression) list * expression option
  | Pexp_field of expression * longident_loc  
  | Pexp_setfield of expression * longident_loc * expression
  | Pexp_array of expression list  
  | Pexp_ifthenelse of expression * expression * expression option
  | Pexp_sequence of expression * expression  
  | Pexp_while of expression * expression 
  | Pexp_for of pattern * expression * expression * direction_flag * expression
  | Pexp_constraint of expression * core_type  
  | Pexp_coerce of expression * core_type option * core_type
  | Pexp_send of expression * label loc  
  | Pexp_new of longident_loc  
  | Pexp_setinstvar of label loc * expression  
  | Pexp_override of (label loc * expression) list
  | Pexp_letmodule of string option loc * module_expr * expression
  | Pexp_letexception of extension_constructor * expression
  | Pexp_assert of expression
  | Pexp_lazy of expression  
  | Pexp_poly of expression * core_type option
  | Pexp_object of class_structure  
  | Pexp_newtype of string loc * expression  
  | Pexp_pack of module_expr
  | Pexp_open of open_declaration * expression
  | Pexp_letop of letop
  | Pexp_extension of extension 
  | Pexp_unreachable  
