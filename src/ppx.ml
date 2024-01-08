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

(*: (Astlib.Ast_500.Parsetree.structure_item list) -> (Astlib.Ast_500.Parsetree.structure_item list)*)
    
let proc1 x   =
  (print_endline (Batteries.dump ("DEBUG:OLDRULE1",x)));
  x

let rec map = function
  | [] -> []
  | h :: t -> proc1 h :: map t
                
let transform x =
  (print_endline (Batteries.dump ("DEBUG:OLDRULE1",x)));
  let foo = map x in 
  x
  
 let () = Driver.register_transformation ~impl:transform "simple-ppx" 
