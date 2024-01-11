open Ppxlib


type string_list = string list
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


let foo(x:longident):string = "skip"

let rec process_id1(a) : string = 
  match a with
  | Lident string -> string 
  | Ldot (longident, string) ->
    (process_id1 (longident)) ^ "." ^ string 
  | Lapply (longident,longident2)
    -> (process_id1 (longident))  ^ "."
       ^ (process_id1 (longident2) ) 

let rec stringlister(x:string_list) : string =
  match x with
  | [] ->""
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

let foo1 (x:longident_loc) = "flab"
  
let splitloc(x:longident_loc * string_list) : string=
  let (a, b) = x in
  let at =  foo1(a) in
    match a with
      { txt; loc }  ->
     process_id2 (txt,  b)
  

let checkstringlist(a: string_list) ="lfkjsd"

let concatlist(a : string * string_list):string_list =
  let (str, string_list) = a in
  let newlist = str :: string_list  in
  newlist

let rec process_record_kind(a:label_declaration *string_list) =
  match a with
  (x,s)->
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
                                pld_type)))
and
  process_core_type_desc (x : core_type_desc * string_list) =
  match x with
    (ctd, astring_list)->
    match ctd with
    | Ptyp_constr (a,b) (* of Longident.t loc * core_type list *)
      ->
      let {txt;loc} = a in
      let ff = (checkstringlist astring_list)  in
      let concat = (concatlist (process_id1(txt), astring_list)) in
      let myid = (process_id (a, concat)) in
      let newy = [myid] @ astring_list in
      (process_core_type_list (b, newy));

      Printf.printf "DEBUG:Ptyp_constr1 Constructor '%s' " myid;
      (* "id" ^ a ^ " id2 " ^ myid  *)

      (print_endline (Batteries.dump (
         "DEBUG:Ptyp_constr:",
         "id",a,myid,
         "types",b,
         "context",astring_list)))

    | Ptyp_tuple a (* of core_type list *)
      ->
      (print_endline (Batteries.dump ("DEBUG:Ptyp_tuple:" )))


    (*not in test*)
    | Ptyp_any  -> (print_endline (Batteries.dump ("DEBUG:Ptyp_any:")))
    | Ptyp_var name ->(print_endline (Batteries.dump ("DEBUG:Ptyp_var:"  , name)))
  | Ptyp_arrow (arg_label , core_type , core_type2) ->
    (* process_core_type((core_type, string_list)); *)
    (* process_core_type(core_type2, string_list); *)
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow10:" )))

  | Ptyp_object (a,b)(* of object_field list * closed_flag *)
    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow8:" )))
  | Ptyp_class (a,b) (* of Longident.t loc * core_type list *)
    ->
    let myid = (process_id (a,astring_list)) in
    (* process_core_type_list(b, y :: myid); *)
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow7:" )))
  | Ptyp_alias (a,b) (* of core_type * string loc  *)
    ->
    (* process_core_type(a, y); *)
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow6:" )))
  | Ptyp_variant (a,b,c) (* of row_field list * closed_flag * label list option *)
    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow5:" )))
  | Ptyp_poly (a,b) (* of string loc list * core_type *)
    ->
    (* process_core_type(b, y); *)
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow4:" )))
  | Ptyp_package a(* of package_type  *)
    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow3:",a )))    
  (* | Ptyp_open (a,b) (\* of Longident.t loc * core_type *\)-> *)
  (*   (print_endline (Batteries.dump ("DEBUG:Ptyp_arrow2",a,b ))) *)    
  | Ptyp_extension a (* of extension   *)    ->
    (print_endline (Batteries.dump ("DEBUG:Ptyp_extension:",a )))
and
  process_record_kind_list(a) =
  match a with
  (x,s)->
  match x with
  | [] -> ()
  | h :: t ->
    (process_record_kind (h ,s));
    (process_record_kind_list (t, s));
    ()
and

  process_core_type(a: core_type * string_list)=
  match a with
  | (x,s) ->
     match x with  
    {
      ptyp_desc(* : core_type_desc *);
      ptyp_loc(* : Location.t *);
      ptyp_loc_stack(* : location_stack *);
      ptyp_attributes(* : attributes; *)
    }->
    (process_core_type_desc (ptyp_desc,s));
    (*MOSTCOMMON*)
    (print_endline (Batteries.dump ("DEBUG:core_type.ptyp_desc:" , a)))
and process_core_type_list(x ) =
  (*: core_type_list * string_list*)
  match x with
  | (a,b) ->
    match a with
    | [] -> ()
    | h :: t ->
       process_core_type (h, b); 
      process_core_type_list(t,b)        
    
let print_constructor_arguments(a) =
  match a with
  | (x,s) ->
    match x with
    | Pcstr_tuple a ->
       (process_core_type_list (a,s)); 
       (print_endline (Batteries.dump ("DEBUG:Pcstr_tuple:"  , a)))
       
    | Pcstr_record a ->
      (print_endline (Batteries.dump ("DEBUG:Pcstr_record:"  , a)))

let rec process_pype_variant_constructor_declaration_list(a:constructor_declaration list*string_list) =
  match a with
  | (x,s)->
    match x with
    | [] -> ()
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
        print_constructor_arguments(pcd_args,s);
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
        (process_pype_variant_constructor_declaration_list (t,s));
      ()
  
let process_kind(a) =
  match a with
  | (x,s)->
    match x with
    (*and type_kind =*)
    | Ptype_abstract  -> (print_endline (Batteries.dump ("DEBUG:Ptype_abstract:")))
    | Ptype_variant a ->
      (process_pype_variant_constructor_declaration_list (a,s));
      (print_endline (Batteries.dump ("DEBUG:Ptype_variant:",  a))) 
    (*of constructor_declaration list *)
      
    | Ptype_record a ->     
      process_record_kind_list(a,s)
    | Ptype_open -> (print_endline (Batteries.dump ("DEBUG:Ptype_abstract:")))

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
      (process_kind (ptype_kind,s));
      (print_endline (Batteries.dump ("DEBUG:private:",  ptype_private,
                                      "DEBUG:manifest", ptype_manifest,
                                      "DEBUG:attr", ptype_attributes,
                                      "DEBUG:loc", ptype_loc
                                     )))
type     type_declaration_list = type_declaration list
    
let rec process_type_decl_list(a:type_declaration_list*string_list) =
  match a with
  |(x,s)->
    match x with
    | [] -> ()
    | h :: t ->
      (print_type_decl (h,s));
      (process_type_decl_list (t,s));
      ()
    
let printdesc(a :structure_item_desc*string_list) :unit =
  match a with
  |(x,s)->
    (print_endline (Batteries.dump ("DEBUG:structure_item_desc:", x)));
    match x with
    | Pstr_eval (expression,attributes) -> (print_endline (Batteries.dump ("DEBUG:Pstr_eval:", expression,attributes)))
    (*value binding*)
    | Pstr_value (rec_flag, value_binding_list) ->(print_endline (Batteries.dump ("DEBUG:Pstr_value:", rec_flag, value_binding_list)));
      print_value_binding_list(value_binding_list)
    | Pstr_primitive value_description ->(print_endline (Batteries.dump ("DEBUG:Pstr_primitive:", value_description)))
                                         
    | Pstr_type (rec_flag, type_declaration_list) ->
      (*for expression_desc*)
      process_type_decl_list((type_declaration_list,s));
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
  
let printone (x : structure_item) :unit =
  
  match x with
  |{
    pstr_desc; (*structure_item_desc*)
    _
  } ->
    (*(print_endline (Batteries.dump ("DEBUG2a:", pstr_desc, pstr_loc )));*)
    (printdesc (pstr_desc,[]));
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
