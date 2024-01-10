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
  | Pexp_ident of longident_loc  (** Identifiers such as [x] and [M.x] *)
  | Pexp_constant of constant
      (** Expressions constant such as [1], ['a'], ["true"], [1.0], [1l], [1L],
          [1n] *)
  | Pexp_let of rec_flag * value_binding list * expression
      (** [Pexp_let(flag, \[(P1,E1) ; ... ; (Pn,En)\], E)] represents:
          - [let P1 = E1 and ... and Pn = EN in E] when [flag] is
            {{!Asttypes.rec_flag.Nonrecursive} [Nonrecursive]},
          - [let rec P1 = E1 and ... and Pn = EN in E] when [flag] is
            {{!Asttypes.rec_flag.Recursive} [Recursive]}. *)
  | Pexp_function of cases  (** [function P1 -> E1 | ... | Pn -> En] *)
  | Pexp_fun of arg_label * expression option * pattern * expression
      (** [Pexp_fun(lbl, exp0, P, E1)] represents:
          - [fun P -> E1] when [lbl] is {{!Asttypes.arg_label.Nolabel}
            [Nolabel]} and [exp0] is [None]
          - [fun ~l:P -> E1] when [lbl] is {{!Asttypes.arg_label.Labelled}
            [Labelled l]} and [exp0] is [None]
          - [fun ?l:P -> E1] when [lbl] is {{!Asttypes.arg_label.Optional}
            [Optional l]} and [exp0] is [None]
          - [fun ?l:(P = E0) -> E1] when [lbl] is
            {{!Asttypes.arg_label.Optional} [Optional l]} and [exp0] is
            [Some E0]
          Notes:
          - If [E0] is provided, only {{!Asttypes.arg_label.Optional}
            [Optional]} is allowed.
          - [fun P1 P2 .. Pn -> E1] is represented as nested
            {{!expression_desc.Pexp_fun} [Pexp_fun]}.
          - [let f P = E] is represented using {{!expression_desc.Pexp_fun}
            [Pexp_fun]}. *)
  | Pexp_apply of expression * (arg_label * expression) list
      (** [Pexp_apply(E0, \[(l1, E1) ; ... ; (ln, En)\])] represents
          [E0 ~l1:E1 ... ~ln:En]
          [li] can be {{!Asttypes.arg_label.Nolabel} [Nolabel]} (non labeled
          argument), {{!Asttypes.arg_label.Labelled} [Labelled]} (labelled
          arguments) or {{!Asttypes.arg_label.Optional} [Optional]} (optional
          argument).
          Invariant: [n > 0] *)
  | Pexp_match of expression * cases
      (** [match E0 with P1 -> E1 | ... | Pn -> En] *)
  | Pexp_try of expression * cases
      (** [try E0 with P1 -> E1 | ... | Pn -> En] *)
  | Pexp_tuple of expression list
      (** Expressions [(E1, ..., En)]
          Invariant: [n >= 2] *)
  | Pexp_construct of longident_loc * expression option
      (** [Pexp_construct(C, exp)] represents:
          - [C] when [exp] is [None],
          - [C E] when [exp] is [Some E],
          - [C (E1, ..., En)] when [exp] is [Some (Pexp_tuple\[E1;...;En\])] *)
  | Pexp_variant of label * expression option
      (** [Pexp_variant(`A, exp)] represents
          - [`A] when [exp] is [None]
          - [`A E] when [exp] is [Some E] *)
  | Pexp_record of (longident_loc * expression) list * expression option
      (** [Pexp_record(\[(l1,P1) ; ... ; (ln,Pn)\], exp0)] represents
          - [{ l1=P1; ...; ln=Pn }] when [exp0] is [None]
          - [{ E0 with l1=P1; ...; ln=Pn }] when [exp0] is [Some E0]
          Invariant: [n > 0] *)
  | Pexp_field of expression * longident_loc  (** [E.l] *)
  | Pexp_setfield of expression * longident_loc * expression
      (** [E1.l <- E2] *)
  | Pexp_array of expression list  (** [\[| E1; ...; En |\]] *)
  | Pexp_ifthenelse of expression * expression * expression option
      (** [if E1 then E2 else E3] *)
  | Pexp_sequence of expression * expression  (** [E1; E2] *)
  | Pexp_while of expression * expression  (** [while E1 do E2 done] *)
  | Pexp_for of pattern * expression * expression * direction_flag * expression
      (** [Pexp_for(i, E1, E2, direction, E3)] represents:
          - [for i = E1 to E2 do E3 done] when [direction] is
            {{!Asttypes.direction_flag.Upto} [Upto]}
          - [for i = E1 downto E2 do E3 done] when [direction] is
            {{!Asttypes.direction_flag.Downto} [Downto]} *)
  | Pexp_constraint of expression * core_type  (** [(E : T)] *)
  | Pexp_coerce of expression * core_type option * core_type
      (** [Pexp_coerce(E, from, T)] represents
          - [(E :> T)] when [from] is [None],
          - [(E : T0 :> T)] when [from] is [Some T0]. *)
  | Pexp_send of expression * label loc  (** [E # m] *)
  | Pexp_new of longident_loc  (** [new M.c] *)
  | Pexp_setinstvar of label loc * expression  (** [x <- 2] *)
  | Pexp_override of (label loc * expression) list
      (** [{< x1 = E1; ...; xn = En >}] *)
  | Pexp_letmodule of string option loc * module_expr * expression
      (** [let module M = ME in E] *)
  | Pexp_letexception of extension_constructor * expression
      (** [let exception C in E] *)
  | Pexp_assert of expression
      (** [assert E].
          Note: [assert false] is treated in a special way by the type-checker. *)
  | Pexp_lazy of expression  (** [lazy E] *)
  | Pexp_poly of expression * core_type option
      (** Used for method bodies.
          Can only be used as the expression under
          {{!class_field_kind.Cfk_concrete} [Cfk_concrete]} for methods (not
          values). *)
  | Pexp_object of class_structure  (** [object ... end] *)
  | Pexp_newtype of string loc * expression  (** [fun (type t) -> E] *)
  | Pexp_pack of module_expr
      (** [(module ME)].
          [(module ME : S)] is represented as
          [Pexp_constraint(Pexp_pack ME, Ptyp_package S)] *)
  | Pexp_open of open_declaration * expression
      (** - [M.(E)]
          - [let open M in E]
          - [let open! M in E] *)
  | Pexp_letop of letop
      (** - [let* P = E0 in E1]
          - [let* P0 = E00 and* P1 = E01 in E1] *)
  | Pexp_extension of extension  (** [\[%id\]] *)
  | Pexp_unreachable  (** [.] *)
