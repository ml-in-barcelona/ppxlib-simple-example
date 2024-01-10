open Ppxlib

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
  (print_endline (Batteries.dump ("DEBUG33:", x)))

(* let print_value_binding_expr_desc (x : expression_desc) : unit = *)
(*   () *)
  
  
let print_value_binding_expr (x : expression) : unit=
  match x with
  | {
    pexp_desc (* : expression_desc *);
    pexp_loc (* : location  *);
    pexp_loc_stack (* : location_stack *);
    pexp_attributes (* : attributes *); (* [... \[@id1\] \[@id2\]] *)
  } ->
    (print_endline (Batteries.dump ("DEBUG66:desc", pexp_desc )));
    (print_endline (Batteries.dump ("DEBUG66:desc", pexp_attributes )));
  ()
  
let print_value_binding_list2 (x : value_binding) : unit=
  match x with
  | {
    pvb_pat; (* : pattern; *)
    pvb_expr; (* : expression; *)
    pvb_attributes; (* : attributes; *)
    pvb_loc; (* : location; *)
  } ->
    (print_endline (Batteries.dump ("DEBUG:value_binding.pat:", pvb_pat )));
    (print_endline (Batteries.dump ("DEBUG:value_binding.expr:", pvb_expr )));
    (*print_value_binding_expr pvb_expr*)
    (print_endline (Batteries.dump ("DEBUG:value_binding.atrr:", pvb_attributes )));
    (print_endline (Batteries.dump ("DEBUG:value_binding.loc:", pvb_loc )))

let rec print_value_binding_list (x : value_binding list) : unit=
  match x with
  | [] -> ()
  | h :: t ->
    (print_value_binding_list2 h);
    (print_value_binding_list t);
    ()

let rec process_id2(x:longident) =
  match x with
  | Lident string -> string
  | Ldot (longident, string) ->
    (process_id2 longident) ^ "." ^ string
  | Lapply (longident,longident2)
    -> (process_id2 longident)  ^ "."
       ^ (process_id2 longident2 )

let process_id(x:longident_loc) =
  match x with
  | {txt;_} ->(process_id2 txt)
(* (({txt2)) ->txt2 *)
    (* (print_endline (Batteries.dump ("DEBUG:process_id:",  txt2))); *)
    
  
let rec process_record_kind(x) =
  match x with
    {
     pld_name(* : string loc *);
     pld_mutable(* : mutable_flag *);
     pld_type(* : core_type *);
     pld_loc(* : Location.t *);
     pld_attributes(* : attributes *); 
   } ->
    (print_endline (Batteries.dump ("DEBUG:precord_kind:",  
                                    pld_name,
                                    "mutable",
                                    pld_mutable,
                                    "type",
                                    pld_type)))
and
process_core_type_desc x =
  match x with
  | Ptyp_constr (a,b) (* of Longident.t loc * core_type list *)
    ->
    let myid = (process_id a) in
    (process_core_type_list b);

    Printf.printf "DEBUG:Ptyp_constr1:%s" myid;
     (* "id" ^ a ^ " id2 " ^ myid  *)

    (print_endline (Batteries.dump (
         "DEBUG:Ptyp_constr:",
         "id",a,myid,
         "types",b )))

  | Ptyp_tuple a (* of core_type list *)
    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_tuple:" )))

  (*not in test*)
  | Ptyp_any  -> (print_endline (Batteries.dump ("DEBUG:Ptyp_any:")))
  | Ptyp_var name ->(print_endline (Batteries.dump ("DEBUG:Ptyp_var:"  , name)))
  | Ptyp_arrow (arg_label , core_type , core_type2) ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow10:" )))

  | Ptyp_object (a,b)(* of object_field list * closed_flag *)
    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow8:" )))
  | Ptyp_class (a,b) (* of Longident.t loc * core_type list *)
    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow7:" )))
  | Ptyp_alias (a,b) (* of core_type * string loc  *)
    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow6:" )))
  | Ptyp_variant (a,b,c) (* of row_field list * closed_flag * label list option *)
    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow5:" )))
  | Ptyp_poly (a,b) (* of string loc list * core_type *)
    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow4:" )))
  | Ptyp_package a(* of package_type  *)
    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow3:",a )))    
  (* | Ptyp_open (a,b) (\* of Longident.t loc * core_type *\)-> *)
  (*   (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow2",a,b ))) *)    
  | Ptyp_extension a (* of extension   *)    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_extension:",a )))
and
  process_record_kind_list(x) =
  match x with
  | [] -> ()
  | h :: t ->
    (process_record_kind h);
    (process_record_kind_list t);
    ()
and
process_core_type(x) =
  match x with 
    {
      ptyp_desc(* : core_type_desc *);
     ptyp_loc(* : Location.t *);
     ptyp_loc_stack(* : location_stack *);
     ptyp_attributes(* : attributes; *)
    }->
    (process_core_type_desc ptyp_desc);
    (*MOSTCOMMON*)
    (print_endline (Batteries.dump ("DEBUG:core_type.ptyp_desc:"  , ptyp_desc)))
and process_core_type_list(x:core_type list) =
  match x with
  | [] -> ()
  | h :: t ->
    process_core_type (h);
    process_core_type_list(t)



    

    
let print_constructor_arguments(x) =
  match x with
  | Pcstr_tuple a ->
    (process_core_type_list a);
    (print_endline (Batteries.dump ("DEBUG:Pcstr_tuple:"  , a)))
      
  | Pcstr_record a ->
    (print_endline (Batteries.dump ("DEBUG:Pcstr_record:"  , a)))

let rec process_pype_variant_constructor_declaration_list(x) =
  match x with
  | [] -> ()
  | h :: t ->
    (* (process_pype_variant_constructor_declaration_list h); *)
    match h with
    |{
      pcd_name(* : string loc *);
      pcd_vars(* : string loc list *);
      pcd_args(* : constructor_arguments *);
      pcd_res(* : core_type option *);
      pcd_loc(* : Location.t *);
      pcd_attributes(* : attributes *); 
    }->
      (* let name = match pcd_name with *)
      (*   | (str,_) -> str *)
      print_constructor_arguments(pcd_args);
      (print_endline (Batteries.dump (
           "DEBUG:constructor_declaration:",
               pcd_name,
               "vars",
               pcd_vars,
               "args",
               pcd_args,
               "res",
               pcd_res,
               "loc",
               pcd_loc,
               "attrs",
               pcd_attributes
             )));
      (process_pype_variant_constructor_declaration_list t);
      ()
  
let process_kind(x) =
  match x with
  (*and type_kind =*)
  | Ptype_abstract  -> (print_endline (Batteries.dump ("DEBUG:Ptype_abstract:")))
  | Ptype_variant a ->
    (process_pype_variant_constructor_declaration_list a);
    (print_endline (Batteries.dump ("DEBUG:Ptype_variant:",  a))) 
    (*of constructor_declaration list *)
    
   | Ptype_record a ->     
     process_record_kind_list(a)
   | Ptype_open -> (print_endline (Batteries.dump ("DEBUG:Ptype_abstract:")))

let print_type_decl(x) =
  match x with
    {
      ptype_name (* : string loc *);
      ptype_params (* : (core_type * (variance * injectivity)) list *);
      ptype_cstrs (*: (core_type * core_type * location) list*) ;   
      ptype_kind (*: type_kind*)  ; 
      ptype_private (*: private_flag*); 
      ptype_manifest (* : core_type option *);
      ptype_attributes (*: attributes*);
      ptype_loc (*: location*)
    } ->
    (print_endline (Batteries.dump ("DEBUG:type_decl:", ptype_name)));
    (print_endline (Batteries.dump ("DEBUG:parameters:", ptype_params)));
    (print_endline (Batteries.dump ("DEBUG:cstrs:", ptype_cstrs)));
    (print_endline (Batteries.dump ("DEBUG:kind:",ptype_kind)));
    (process_kind ptype_kind);
    (print_endline (Batteries.dump ("DEBUG:private:",  ptype_private,
                                    "DEBUG:manifest", ptype_manifest,
                                    "DEBUG:attr", ptype_attributes,
                                    "DEBUG:loc", ptype_loc
                                   )))
    
let rec process_type_decl_list(x) =
  match x with
  | [] -> ()
  | h :: t ->
    (print_type_decl h);
    (process_type_decl_list t);
    ()
    
let printdesc(x :structure_item_desc) :unit =
  (print_endline (Batteries.dump ("DEBUG:structure_item_desc:", x)));
  match x with
  | Pstr_eval (expression,attributes) -> (print_endline (Batteries.dump ("DEBUG:Pstr_eval:", expression,attributes)))
  (*value binding*)
  | Pstr_value (rec_flag, value_binding_list) ->(print_endline (Batteries.dump ("DEBUG:Pstr_value:", rec_flag, value_binding_list)));
    print_value_binding_list(value_binding_list)
  | Pstr_primitive value_description ->(print_endline (Batteries.dump ("DEBUG:Pstr_primitive:", value_description)))

  | Pstr_type (rec_flag, type_declaration_list) ->
    (*for expression_desc*)
    process_type_decl_list(type_declaration_list);
    (print_endline (Batteries.dump ("DEBUG:Pstr_type:", rec_flag, type_declaration_list)))


  | Pstr_typext  type_extension ->(print_endline (Batteries.dump ("DEBUG:Pstr_typext:", type_extension)))
  | Pstr_exception extension_constructor ->(print_endline (Batteries.dump ("DEBUG:Pstr_exception:", extension_constructor)))
  | Pstr_module  module_binding ->(print_endline (Batteries.dump ("DEBUG:Pstr_module:",module_binding)))
  | Pstr_recmodule  module_binding_list ->(print_endline (Batteries.dump ("DEBUG:Pstr_recmodule:", module_binding_list)))
  | Pstr_modtype module_type_declaration ->(print_endline (Batteries.dump ("DEBUG:Pstr_modtype:", module_type_declaration)))
  (*open model*)
  | Pstr_open open_description ->(print_endline (Batteries.dump ("DEBUG:Pstr_open", open_description)))
  | Pstr_class (class_declarations ) ->(print_endline (Batteries.dump ("DEBUG:Pstr_class:", class_declarations)))
  | Pstr_class_type (class_type_declarations) ->(print_endline (Batteries.dump ("DEBUG:Pstr_class_type:", class_type_declarations)))
  | Pstr_include  (include_declaration)->(print_endline (Batteries.dump ("DEBUG:Pstr_include:",include_declaration)))
  | Pstr_attribute (attribute)->(print_endline (Batteries.dump ("DEBUG:Pstr_attribute:", attribute)))
  | Pstr_extension ( extension , attributes)->(print_endline (Batteries.dump ("DEBUG:Pstr_extension:", extension , attributes)))

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
  (print_endline (Batteries.dump ("DEBUG:SECOND::",x)));
  printone x
  
let proc1 x   =
  printone2 x;
  x

let debug proc lst : unit =
  let result = List.map proc lst in
  List.iter (fun i -> print_endline (Batteries.dump ("DEBUG:TOPLEVEL:", i))) result;
  ()
                
let transform x (*ast, bytecodes of the interface *) =
  (print_endline (Batteries.dump ("DEBUG3:",x)));
  (debug proc1 x);
  x
  
 let () = Driver.register_transformation ~impl:transform "simple-ppx" 
