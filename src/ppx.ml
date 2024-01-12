open Ppxlib


type string_list = string list
type core_type_list = core_type list
(*: (Astlib.Ast_500.Parsetree.structure_item list) -> (Astlib.Ast_500.Parsetree.structure_item list)
*)

let printdesc2(x :structure_item_desc) :string =
  (print_endline (Batteries.dump ("DEBUG21:", x)));
  "descr"

let printone (x : structure_item ) :string =
  match x with
  |{
    pstr_desc; (*structure_item_desc*)
    _
  } ->
    (printdesc2 pstr_desc)
    
      

let printone2 x :string =
  (print_endline (Batteries.dump ("DEBUG1:",x)));
  printone x

let proc2 x  : string =
  (printone2 x)
  

let printdesc2(x :structure_item_desc) :string =
  (print_endline (Batteries.dump ("DEBUG33:", x)));
  "FIXME123"
  
let print_value_binding_expr (x : expression) : string=
  match x with
  | {
    pexp_desc (* : expression_desc *);
    pexp_loc (* : location  *);
    pexp_loc_stack (* : location_stack *);
    pexp_attributes (* : attributes *); (* [... \[@id1\] \[@id2\]] *)
  } ->
    (print_endline (Batteries.dump ("DEBUG66:desc", pexp_desc )));
    (print_endline (Batteries.dump ("DEBUG66:desc", pexp_attributes )));
  "TODO"
  
let print_value_binding_list2 (x : value_binding) : string =
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
    (print_endline (Batteries.dump ("DEBUG:value_binding.loc:", pvb_loc )));
    "yodo"

let rec print_value_binding_list (x : value_binding list) : string=
  match x with
  | [] -> "print_value_binding_list"
  | h :: t ->
    (print_value_binding_list2 h)
    ^ ";;" ^(print_value_binding_list t) ^ ";;"
     
let rec process_id1 a : string = 
  match a with
  | Lident string -> string 
  | Ldot (longident, string) ->
    (process_id1 (longident)) ^ "." ^ string 
  | Lapply (longident,longident2)
    -> (process_id1 (longident))  ^ "."
       ^ (process_id1 (longident2) ) 

let rec stringlister (x:string_list) : string =
  match x with
  | [] ->"stringlister"
  | h :: t -> h ^ stringlister(t)
and
  process_id2(x:longident *string_list):string =
  match x with
    (a,b) ->
    let sc = stringlister(b) in 
    match a with
    | Lident string -> string ^ sc
    | Ldot (longident, string) ->
      (process_id2 (longident,b)) ^ "." ^ string ^ sc
    | Lapply (longident,longident2)
      -> (process_id2 (longident, b))  ^ "."
         ^ (process_id2 (longident2,b) ) ^ sc
           
let process_id(x:longident_loc* string_list):string =
  match x with
  | (a,b) ->
    match a with
    | {txt;_} ->(process_id2 (txt,b))
(* (({txt2)) ->txt2 *)
    (* (print_endline (Batteries.dump ("DEBUG:process_id:",  txt2))); *)
  
let splitloc(x:longident_loc * string_list) : string=
  let (a, b) = x in
  match a with
    { txt; loc }  ->
    process_id2 (txt,  b)
      


let concatlist(a : string * string_list):string_list =
  let (str, string_list) = a in
  let newlist = str :: string_list  in
  newlist

let rec
  process_record_kind4 :label_declaration -> string_list -> string = fun x s -> ""
  and
  process_record_kind2(x :label_declaration)(s:string_list) = ""
  and
  process_record_kind3 x s = ""
  and
  process_record_kind((x,s):label_declaration *string_list):string =
  match x with
    {
     pld_name(* : string loc *);
     pld_mutable(* : mutable_flag *);
     pld_type(* : core_type *);
     pld_loc(* : Location.t *);
     pld_attributes(* : attributes *); 
   } ->
    let foo =process_core_type(pld_type, s) in
    (print_endline (Batteries.dump ("DEBUG:precord_kind:",  
                                    pld_name,
                                    "mutable",
                                    pld_mutable,
                                    "type",
                                    pld_type)));
    "process_record_kind:\"" ^ pld_name.txt ^ "\" body:" ^ foo
and
  process_core_type_desc (x : core_type_desc * string_list):string =
  match x with
    (ctd, s)->
    match ctd with
    | Ptyp_constr (a,b) (* of Longident.t loc * core_type list *)
      ->
      let {txt;loc} = a in
      let id1 = process_id1(txt) in
      (* let concat = (concatlist (id1, astring_list)) in *)
      (* let newy = [id1] @ astring_list in *)
      let newlist = (process_core_type_list (b, s)) in
      Printf.printf "DEBUG:Ptyp_constr1 '%s' %s" id1 newlist;
      (* "id" ^ a ^ " id2 " ^ myid  *)

      (print_endline (Batteries.dump (
         "DEBUG:Ptyp_constr:",
         "id",a,
         "types",b,
         "context",s,
         "id1", id1
       )));     
      "Ptyp_constr:\"" ^ id1 ^ "\"->" ^ newlist
    | Ptyp_tuple a (* of core_type list *)
      ->
      (print_endline (Batteries.dump ("DEBUG:Ptyp_tuple:", a )));
      "Ptyp_tuple" ^ process_core_type_list(a,  s )


    (*not in test*)
    | Ptyp_any  -> (print_endline (Batteries.dump ("DEBUG:Ptyp_any:"))); "any"
    | Ptyp_var name ->(print_endline (Batteries.dump ("DEBUG:Ptyp_var:"  , name))); "var-name"
  | Ptyp_arrow (arg_label , core_type , core_type2) ->
    (* process_core_type((core_type, string_list)); *)
    (* process_core_type(core_type2, string_list); *)
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow10:" ))); "arrow"

  | Ptyp_object (a,b)(* of object_field list * closed_flag *)
    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow8:" ))); "obj"
  | Ptyp_class (a,b) (* of Longident.t loc * core_type list *)
    ->
    let myid = (process_id (a,s)) in
    (* process_core_type_list(b, y :: myid); *)
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow7:" ))); "class"
  | Ptyp_alias (a,b) (* of core_type * string loc  *)
    ->
    (* process_core_type(a, y); *)
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow6:" ))); "alias"
  | Ptyp_variant (a,b,c) (* of row_field list * closed_flag * label list option *)
    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow5:" )));"variant"
  | Ptyp_poly (a,b) (* of string loc list * core_type *)
    ->
    (* process_core_type(b, y); *)
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow4:" ))); "poly"
  | Ptyp_package a(* of package_type  *)
    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow3:",a ))) ; "typ_package"
  (* | Ptyp_open (a,b) (\* of Longident.t loc * core_type *\)-> *)
  (*   (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow2",a,b ))) *)    
  | Ptyp_extension a (* of extension   *)    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_extension:",a ))); "extension"
and
  process_record_kind_list(a) : string =
  match a with
  (x, s)->
  match x with
  | [] -> "process_record_kind_list"
  | h :: t ->
    (process_record_kind (h ,  s)) ^ "/" ^ (process_record_kind_list (t, s))
    
and

  process_core_type(a: core_type * string_list):string=
  match a with
  | (x,s) ->
     match x with  
    {
      ptyp_desc(* : core_type_desc *);
      ptyp_loc(* : Location.t *);
      ptyp_loc_stack(* : location_stack *);
      ptyp_attributes(* : attributes; *)
    }->
    let td = (process_core_type_desc (ptyp_desc,s)) in
    (*MOSTCOMMON*)
    (print_endline (Batteries.dump ("DEBUG:core_type.ptyp_desc:" , a, td)));
    "ptyp_desc:" ^ td
and process_core_type_list(x: core_type_list * string_list):string =
  match x with
  | (a,b) ->
    match a with
    | [] -> "process_core_type_list:"
    | h :: t ->
      process_core_type (h, b) ^ "," ^ process_core_type_list(t,b)        


















let rec emit_id1 a : string = 
  match a with
  | Lident string -> string 
  | Ldot (longident, string) ->
    (emit_id1 (longident)) ^ "." ^ string 
  | Lapply (longident,longident2)
    -> (emit_id1 (longident))  ^ "."
       ^ (emit_id1 (longident2) ) 

let emit_core_type_desc (x : core_type_desc * string_list):string =
  match x with
    (ctd, s)->
    match ctd with
    | Ptyp_constr (a,b) (* of Longident.t loc * core_type list *)
      ->
      let {txt;loc} = a in
      let id1 = emit_id1(txt) in
      (* let concat = (concatlist (id1, astring_list)) in *)
      (* let newy = [id1] @ astring_list in *)
      (* let newlist = (process_core_type_list (b, s)) in *)
      id1 (* ^ "\"->" ^ newlist *)
    | Ptyp_tuple a (* of core_type list *)
      ->
      "Ptyp_tuple" ^ process_core_type_list(a,  s )


let  emit_core_type(a: core_type * string_list):string=
  match a with
  | (x,s) ->
     match x with  
    {
      ptyp_desc(* : core_type_desc *);
      ptyp_loc(* : Location.t *);
      ptyp_loc_stack(* : location_stack *);
      ptyp_attributes(* : attributes; *)
    }->
    let td = (emit_core_type_desc (ptyp_desc,s)) in
    td


let rec emit_core_type_list(x: core_type_list * string_list):string =
  match x with
  | (a,b) ->
    match a with
    | [] -> ""
    | h :: t ->
      let tt = emit_core_type_list(t,b)  in
      if tt != "" then
        emit_core_type (h, b) ^ "," ^ tt
      else
        emit_core_type (h, b)

let  imp_core_type((a,s,n): core_type * string_list*int):string=
  
  let name = emit_core_type(a,s) in
  "(process_" ^ name ^ " " ^ name ^ (string_of_int n) ^ ")"

let  decl_imp_core_type(a: core_type * string_list):string=
  let name = emit_core_type(a) in
  "let process_" ^ name ^ " ( a" ^ name ^ ":" ^ name ^ ")=()\n"

let rec decl_imp_core_type_list(x: core_type_list * string_list*int):string =
  match x with
  | (a,b,n) ->
    match a with
    | [] -> ""
    | h :: t ->
      let tt = decl_imp_core_type_list(t,b,n+1)  in
      if tt != "" then
        decl_imp_core_type (h, b) ^ " " ^ tt
      else
        decl_imp_core_type (h, b)

let rec imp_core_type_list(x: core_type_list * string_list*int):string =
  match x with
  | (a,b,n) ->
    match a with
    | [] -> ""
    | h :: t ->
      let tt = imp_core_type_list(t,b,n+1)  in
      if tt != "" then
        imp_core_type (h, b,n)  ^ "," ^ tt
      else
        imp_core_type (h, b,n ) 

let emit_constructor_arguments(name,x,s):string =
  match x with
  | Pcstr_tuple a ->
    "| " ^ name ^ " ("^ (emit_core_type_list (a,s))  ^ ") -> " ^ "(process_types (" ^ imp_core_type_list (a,s,0) ^"))"
    
let decl_emit_constructor_arguments(name,x,s):string =
  match x with
  | Pcstr_tuple a ->
    decl_imp_core_type_list (a,s,0) 

let print_constructor_arguments(a) =
  match a with
  | (x,s) ->
    match x with
    | Pcstr_tuple a ->       
      (print_endline (Batteries.dump ("DEBUG:Pcstr_tuple:"  , a)));
      "Pcstr_tuple:" ^ (process_core_type_list (a,s))
       
    | Pcstr_record a ->
      (print_endline (Batteries.dump ("DEBUG:Pcstr_record:"  , a)));
      "FIXME:Pcstr_record"

let rec process_pype_variant_constructor_declaration_list(a:constructor_declaration list*string_list):string =
  match a with
  | (x,s)->
    match x with
    | [] -> "VARIANT:" 
    | h :: t ->
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
        let newtext = (emit_constructor_arguments(pcd_name.txt, pcd_args, s)) in
        let newtext2 = (decl_emit_constructor_arguments(pcd_name.txt, pcd_args, s)) in
        (print_endline ("DEBUG2A:" ^ newtext2));
        (print_endline ("DEBUG2B:" ^ newtext));

        let ret =              "constructor:\""^ pcd_name.txt ^ "\""
                               ^ "{" ^
                               print_constructor_arguments(pcd_args,s)
                               ^ "}" ^ "\t|" ^
                               process_pype_variant_constructor_declaration_list(t,s)
        in
        Printf.printf "DEBUG:constructor_declaration_new: %s\n" ret;
        ret
        
  
let process_kind(a) :string=
  match a with
  | (x,s)->
    match x with
    (*and type_kind =*)
    | Ptype_abstract  -> (print_endline (Batteries.dump ("DEBUG:Ptype_abstract:")));
      "DEBUG:Ptype_abstract"
    | Ptype_variant a ->      
      (print_endline (Batteries.dump ("DEBUG:Ptype_variant:",  a)));
      "type variant:" ^ (process_pype_variant_constructor_declaration_list (a,s))      
    (*of constructor_declaration list *)     
    | Ptype_record a ->     
      process_record_kind_list(a,s)
    | Ptype_open -> (print_endline (Batteries.dump ("DEBUG:Ptype_abstract:"))); "Ptype_abstract"

let print_type_decl(a) =
  match a with
  |(x,s) ->
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
      
      (print_endline (Batteries.dump ("DEBUG:private:",  ptype_private,
                                      "DEBUG:manifest", ptype_manifest,
                                      "DEBUG:attr", ptype_attributes,
                                      "DEBUG:loc", ptype_loc
                                     )));
      "print_type_decl:\"" ^  ptype_name.txt ^ "\" = " ^ (process_kind (ptype_kind,s))
      
type     type_declaration_list = type_declaration list
    
let rec process_type_decl_list(a:type_declaration_list*string_list):string =
  match a with
  |(x,s)->
    match x with
    | [] -> "process_type_decl_list"
    | h :: t ->
      (print_type_decl (h,s))
      ^ "[" ^
      (process_type_decl_list (t,s))
      ^ "]"
      
    
let printdesc(a :structure_item_desc*string_list) :string =
  match a with
  |(x,s)->
    (print_endline (Batteries.dump ("DEBUG:structure_item_desc:", x)));
    match x with
    | Pstr_eval (expression,attributes) ->
      (print_endline (Batteries.dump ("DEBUG:Pstr_eval:", expression,attributes)));
      "Pstr_eval"
    (*value binding*)
    | Pstr_value (rec_flag, value_binding_list) ->
      (print_endline (Batteries.dump ("DEBUG:Pstr_value:", rec_flag, value_binding_list)));
      "Pstr_value:"      ^ print_value_binding_list(value_binding_list)
    | Pstr_primitive value_description ->(print_endline (Batteries.dump ("DEBUG:Pstr_primitive:", value_description))) ; "primitive"
                                         
    | Pstr_type (rec_flag, type_declaration_list) ->
      (*for expression_desc*)
      
      (print_endline (Batteries.dump ("DEBUG:Pstr_type:", rec_flag, type_declaration_list)));
      "Pstr_type:"^
      process_type_decl_list((type_declaration_list,s))
    | Pstr_typext  type_extension ->(print_endline (Batteries.dump ("DEBUG:Pstr_typext:", type_extension))); "typeext"
    | Pstr_exception extension_constructor ->(print_endline (Batteries.dump ("DEBUG:Pstr_exception:", extension_constructor))); "exception"
    | Pstr_module  module_binding ->(print_endline (Batteries.dump ("DEBUG:Pstr_module:",module_binding))); "binding"
    | Pstr_recmodule  module_binding_list ->(print_endline (Batteries.dump ("DEBUG:Pstr_recmodule:", module_binding_list))) ; "recmodule"
    | Pstr_modtype module_type_declaration ->(print_endline (Batteries.dump ("DEBUG:Pstr_modtype:", module_type_declaration))); "modtype"
    (*open model*)
    | Pstr_open open_description ->(print_endline (Batteries.dump ("DEBUG:Pstr_open", open_description))); "open"
    | Pstr_class (class_declarations ) ->(print_endline (Batteries.dump ("DEBUG:Pstr_class:", class_declarations))); "class"
    | Pstr_class_type (class_type_declarations) ->(print_endline (Batteries.dump ("DEBUG:Pstr_class_type:", class_type_declarations))) ; "class_Type"
    | Pstr_include  (include_declaration)->(print_endline (Batteries.dump ("DEBUG:Pstr_include:",include_declaration))); "include"
    | Pstr_attribute (attribute)->(print_endline (Batteries.dump ("DEBUG:Pstr_attribute:", attribute))); "attribte"
    | Pstr_extension ( extension , attributes)->(print_endline (Batteries.dump ("DEBUG:Pstr_extension:", extension , attributes))) ; "extension"

                              
let process_types (x) = ()

let process_arg_label ( aarg_label:arg_label)=()
let process_cases ( acases:cases)=()
let process_class_structure ( aclass_structure:class_structure)=()
let process_constant ( aconstant:constant)=()
let process_expression ( aexpression:expression)=()
let process_extension ( aextension:extension)=()
let process_extension_constructor ( aextension_constructor:extension_constructor)=()
let process_label ( alabel:label)=()
let process_letop ( aletop:letop)=()
let process_list ( alist)=()
let process_loc ( aloc)=()
let process_option ( aloc)=()
let process_longident_loc ( alongident_loc:longident_loc)=()
let process_module_expr ( amodule_expr:module_expr)=()
let process_open_declaration ( aopen_declaration:open_declaration)=()
let process_pattern ( apattern:pattern)=()
let process_rec_flag ( arec_flag:rec_flag)=()
                                           

let foo(x) =
  match x with    
  | Pexp_ident longident_loc -> (process_types ((process_longident_loc longident_loc)))
  | Pexp_constant constant -> (process_types ((process_constant constant)))
  | Pexp_let (rec_flag,alist,expression) -> (process_types ((process_rec_flag rec_flag),(process_list alist),(process_expression expression)))
  | Pexp_function cases -> (process_types ((process_cases cases)))
  | Pexp_fun (arg_label,option,pattern,expression) -> (process_types ((process_arg_label arg_label),(process_option option),(process_pattern pattern),(process_expression expression)))
  | Pexp_apply (expression, list) -> (process_types ((process_expression expression),(process_list list)))
  | Pexp_match (expression, cases) -> (process_types ((process_expression expression),(process_cases cases)))
  | Pexp_try (expression, cases) -> (process_types ((process_expression expression),(process_cases cases)))
  | Pexp_tuple list -> (process_types ((process_list list)))
  | Pexp_construct (longident_loc, option) -> (process_types ((process_longident_loc longident_loc),(process_option option)))
| Pexp_variant (label,option) -> (process_types ((process_label label),(process_option option)))
| Pexp_record (list, option) -> (process_types ((process_list list),(process_option option)))
| Pexp_field (expression ,longident_loc) -> (process_types ((process_expression expression),(process_longident_loc longident_loc)))
| Pexp_setfield (expression, longident_loc, expression1) -> (process_types ((process_expression expression),(process_longident_loc longident_loc),(process_expression expression)))
| Pexp_array list -> (process_types ((process_list list)))
| Pexp_ifthenelse (expression, expression2, option) -> (process_types ((process_expression expression),(process_expression expression),(process_option option)))

let foo = 1
  
let printone (x : structure_item) :string =
  
  match x with
  |{
    pstr_desc; (*structure_item_desc*)
    _
  } ->
    (print_endline ("TOP structure_item_desc"     ^ "|" ^ (printdesc (pstr_desc,[]))));
    "fixme"
    
(*   () *)
(* | other -> *)
(*   let f = (print_endline (Batteries.dump ("DEBUG4:",other))) in  *)
      

let printone2 x :string =
  (print_endline (Batteries.dump ("DEBUG:SECOND::",x)));
  printone x
  
let proc1 x :string  =
  printone2 x
 

let debug proc lst : string =
  let result = List.map proc lst in
  List.iter (fun i -> print_endline (Batteries.dump ("DEBUG:TOPLEVEL:", i))) result;
    "TODO"
                
let transform x (*ast, bytecodes of the interface *) =
  (print_endline (Batteries.dump ("DEBUG3:",x)));
  let foo = (debug proc1 x) in
  x
  
 let () = Driver.register_transformation ~impl:transform "simple-ppx" 
