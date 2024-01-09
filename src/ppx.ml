open Ppxlib

(* let expander ~loc ~path:a b = *)
(*   (print_endline (Batteries.dump ("DEBUG:OLDRULE1",a,b))); *)
(*   { *)
(*   pexp_desc = Pexp_constant (Pconst_string ("foo", loc, None)); *)
(*   pexp_loc = loc; *)
(*   pexp_attributes = []; *)
(*   pexp_loc_stack = []; *)
(* } *)

(* let pattern = Ast_pattern.__ *)
(* let extension = *)
(*   Context_free.Rule.extension *)
(*     (Extension.declare "yay" Expression pattern expander) *)

(*: (Astlib.Ast_500.Parsetree.structure_item list) -> (Astlib.Ast_500.Parsetree.structure_item list)
*)

let printdesc2(x :structure_item_desc) :unit =
  (print_endline (Batteries.dump ("DEBUG21:", x)));
  ()

let printone (x : structure_item ) :unit =
  match x with
  |{
    pstr_desc; (*structure_item_desc*)
    _
  } ->
    (printdesc2 pstr_desc);
    ()
      

let printone2 x :unit =
  (print_endline (Batteries.dump ("DEBUG1:",x)));
  printone x

let proc2 x  : unit =
  printone2 x;
  ()

let printdesc2(x :structure_item_desc) :unit =
  (print_endline (Batteries.dump ("DEBUG21:", x)))


let print_value_binding_list2 (x : value_binding) : unit=
  match x with
  | {
    pvb_pat; (* : pattern; *)
    pvb_expr; (* : expression; *)
    pvb_attributes; (* : attributes; *)
    pvb_loc; (* : location; *)
  } ->
    (print_endline (Batteries.dump ("DEBUG21:", pvb_pat)))

let rec print_value_binding_list (x : value_binding list) : unit=
  match x with
  | [] -> ()
  | h :: t ->
    (print_value_binding_list2 h);
    (print_value_binding_list t);
    ()

  
let printdesc(x :structure_item_desc) :unit =
  (print_endline (Batteries.dump ("DEBUG21:", x)));
  match x with
  | Pstr_eval (expression,attributes) -> (print_endline (Batteries.dump ("Pstr_eval:", expression,attributes)))
  (*value binding*)
  | Pstr_value (rec_flag, value_binding_list) ->(print_endline (Batteries.dump ("Pstr_value:", rec_flag, value_binding_list)));
    print_value_binding_list(value_binding_list)
  | Pstr_primitive value_description ->(print_endline (Batteries.dump ("Pstr_primitive:", value_description)))
  | Pstr_type (rec_flag, type_declaration_list) ->(print_endline (Batteries.dump ("Pstr_type:", rec_flag, type_declaration_list)))
  | Pstr_typext  type_extension ->(print_endline (Batteries.dump ("Pstr_typext:", type_extension)))
  | Pstr_exception extension_constructor ->(print_endline (Batteries.dump ("Pstr_exception:", extension_constructor)))
  | Pstr_module  module_binding ->(print_endline (Batteries.dump ("Pstr_module:",module_binding)))
  | Pstr_recmodule  module_binding_list ->(print_endline (Batteries.dump ("Pstr_recmodule:", module_binding_list)))
  | Pstr_modtype module_type_declaration ->(print_endline (Batteries.dump ("Pstr_modtype:", module_type_declaration)))
  (*open model*)
  | Pstr_open open_description ->(print_endline (Batteries.dump ("Pstr_open", open_description)))
  | Pstr_class (class_declarations ) ->(print_endline (Batteries.dump ("Pstr_class:", class_declarations)))
  | Pstr_class_type (class_type_declarations) ->(print_endline (Batteries.dump ("Pstr_class_type:", class_type_declarations)))
  | Pstr_include  (include_declaration)->(print_endline (Batteries.dump ("Pstr_include:",include_declaration)))
  | Pstr_attribute (attribute)->(print_endline (Batteries.dump ("Pstr_attribute:", attribute)))
  | Pstr_extension ( extension , attributes)->(print_endline (Batteries.dump ("Pstr_extension:", extension , attributes)))

let foo = 1
  
let printone (x : structure_item ) :unit =
  match x with
  |{
    pstr_desc; (*structure_item_desc*)
    _
  } ->
    (*(print_endline (Batteries.dump ("DEBUG2a:", pstr_desc, pstr_loc )));*)
    (printdesc pstr_desc);
    ()
  (*   () *)
  (* | other -> *)
  (*   let f = (print_endline (Batteries.dump ("DEBUG4:",other))) in  *)
      

let printone2 x :unit =
  (print_endline (Batteries.dump ("DEBUG1:",x)));
  printone x
  
let proc1 x   =
  printone2 x;
  x

(* let rec map: unit = function *)
(*   | [] -> () *)
(*   | h :: t -> *)
(*     let u = (map t) in *)
(*     let i = (proc1 h) in *)
(*     let j = (print_endline (Batteries.dump ("DEBUG33:",i, u))) in  *)
(*     () *)
let debug proc lst : unit =
  let result = List.map proc lst in
  List.iter (fun i -> print_endline (Batteries.dump ("DEBUG33:", i))) result;
  ()
                
let transform x (*ast, bytecodes of the interface *) =
  (print_endline (Batteries.dump ("DEBUG3:",x)));
  (debug proc1 x);
  x
  
 let () = Driver.register_transformation ~impl:transform "simple-ppx" 
