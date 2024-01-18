type coq_unit =
| Coq_tt
  
let process_types_coq_unit__Coq_tt:string = "process_types_coq_unit__Coq_tt"
                                                               
let process_coq_unit__Coq_tt (x:coq_unit) :string =match x with 
| Coq_tt  -> (process_types_coq_unit__Coq_tt)

(* let process_bool__Coq_true x :string =match x with  *)
(* | Coq_true () -> (process_types_bool__Coq_true()) *)
(*  let process_bool__Coq_false x :string =match x with  *)
(* | Coq_false () -> (process_types_bool__Coq_false()) *)

(* let process_coprod__Coq_ii1 x :string =match x with  *)
(* | Coq_ii1 (var_name0) -> (process_types_coprod__Coq_ii1((process_var-name var-name0))) *)

(* let process_coprod__Coq_ii2 x :string =match x with  *)
(* | Coq_ii2 (var_name0) -> (process_types_coprod__Coq_ii2((process_var-name var-name0))) *)

(* let process_nat__O x :string =match x with o *)
(* | O () -> (process_types_nat__O()) *)
(*  let process_nat__S x :string =match x with  *)
(* | S (nat0) -> (process_types_nat__S((process_nat nat0))) *)

(* let process_paths__Coq_paths_refl x :string =match x with  *)
(* | Coq_paths_refl () -> (process_types_paths__Coq_paths_refl()) *)

(* let process_directive_argument_desc__Pdir_string x :string =match x with  *)
(* | Pdir_string (string0) -> (process_types_directive_argument_desc__Pdir_string((process_string string0))) *)

(* let process_directive_argument_desc__Pdir_int x :string =match x with  *)
(* | Pdir_int (string0,option1) -> (process_types_directive_argument_desc__Pdir_int((process_string string0),(process_option option1))) *)

(* let process_directive_argument_desc__Pdir_ident x :string =match x with  *)
(* | Pdir_ident (longident0) -> (process_types_directive_argument_desc__Pdir_ident((process_longident longident0))) *)

(* let process_directive_argument_desc__Pdir_bool x :string =match x with  *)
(* | Pdir_bool (bool0) -> (process_types_directive_argument_desc__Pdir_bool((process_bool bool0))) *)
(* | Ptop_def (structure0) -> (process_types_toplevel_phrase__Ptop_def((process_structure structure0))) *)

(* let process_toplevel_phrase__Ptop_dir x :string =match x with  *)
(* | Ptop_dir (toplevel_directive0) -> (process_types_toplevel_phrase__Ptop_dir((process_toplevel_directive toplevel_directive0))) *)
