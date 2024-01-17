open Ppxlib
open Ppxlibextras
let ppddump x = () (*stub to hide batteries dump*)


let process_apply (a,c) :string = "apply:" ^ a ^ "|" ^ c
let process_coerce a = "FIXME122"
let process_constraint (a,b) = "process_constraint" ^ a ^ "|" ^b
let process_construct (a,b) = "process_construct" ^a^ "|" ^b
let process_field (a,b) = "process_field" ^ a ^ "|" ^b
let process_for a = "FIXME126"
let process_fun (a,b,c,d) = "process_fun:" ^ a ^ "|" ^b ^ "|" ^c ^ "|" ^d
let process_ifthenelse (a,b,c) = "process_ifthenelse" ^ a ^ b ^c 
let process_let (a,b,c) = "let" ^ a ^ "|" ^ b ^ "|" ^ c
let process_letexception (a,b) = "process_letexception" ^ a ^ "|" ^ b
let process_letmodule a = "FIXME131"
let process_match (a,b) = "process_match" ^ a ^ "|" ^ b
let process_newtype a = "FIXME1334"
let process_open a = "FIXME1337"
let process_poly a = "FIXME1338"
let process_record a = "FIXME1339"
let process_send a = "FIXME1340"
let process_sequence  (a,b) = "process_sequences" ^ a ^ "|" ^ b
let process_setfield a = "FIXME1352"
let process_setinstvar a = "FIXME1362"
let process_try a = "FIXME1343"
let process_variant a = "FIXME1355"
let process_while  a = "FIXME1378"
                                                                           
let process_types (x):string = "TOP1" ^ x
let process_array (x):string = "ARRAY" ^ x
let process_extension1 (x):string = "EXT" ^ x
let process_function (x):string = "FUNCTION" ^ x
let process_ident (x):string = "IDENT" ^ x
let process_lazy (x):string = "LAZY" ^ x
let process_letop1 (x):string = "LETOP" ^ x
let process_new (x):string = "NEW" ^ x

let process_object (x):string = "OBJECT" ^ x



let process_override (x):string = "OVERRIDE" ^ x
let process_pack (x):string = "PACK" ^ x     let process_tuple (x):string = "TUPLE" ^ x                                                               
                                
let process_constant1 (x):string = "CONSTANT" ^ x
let process_assert (x):string = "ASSERT" ^ x
let process_option ( a):string = "process_option_TODO" ^ a
                                                                


let process_direction_flag ( alist0):string =  "FIXME4"
let process_arg_label ( a:arg_label):string=
  "process_arg_label" ^
  match a with
  | Nolabel -> "NoLabel"
  | Labelled a  -> "label:"^a
  | Optional a -> "label_optional:"^a


let process_class_structure ( aclass_structure0:class_structure):string=  "FIXME7"
let process_constant ( a:constant):string=
  "process_constant" ^
  match a with
  | Pconst_integer (a,b) -> "int" ^a
  | Pconst_char char  -> "char" ^ String.make 1 char
  | Pconst_string (string,location,stringoption) -> "Pconst_string(\"" ^ string ^ "\")"
  | Pconst_float (string , char_option) -> "float" ^ string


let process_extension ( aextension0:extension):string= "FIXME9"
let process_extension_constructor ( aextension_constructor0:extension_constructor):string= "FIXME10"
let process_label ( alabel0:label):string="process_label" ^ alabel0
let process_letop ( aletop0:letop):string="FIXME12"
let rec process_list ( a ):string=
  "process_list" ^  
  match a with
  | [] -> "process_list"
  | a :: t -> a ^ "," ^ (process_list t)

let process_loc ( aloc0):string="FIXME14"

let rec process_id1 a : string = 
  match a with
  | Lident string -> string 
  | Ldot (longident, string) ->
    (process_id1 (longident)) ^ "." ^ string 
  | Lapply (longident,longident2)
    -> (process_id1 (longident))  ^ "."
       ^ (process_id1 (longident2) ) 

let process_longident_loc ( a :longident_loc):string="ident:" ^ (process_id1 a.txt)
let process_module_expr ( amodule_expr0:module_expr):string="FIXME16"
let process_open_declaration ( aopen_declaration0:open_declaration):string="FIXME17"
let process_rec_flag ( x:rec_flag):string="process_rec_flag" ^
                                          match x with 
                                          | Nonrecursive -> "plain"
                                          | Recursive -> "rec"








let rec
  process_list1 ( a: (arg_label * expression) list):string=
  "process_list1" ^
  match a with
  | [] -> "process_list1"
  | (l,e) :: t -> (process_arg_label l) ^ "|" ^ (process_expression e) ^ "|" ^ (process_list1 t)
and process_expression_option ( a: expression option ):string = "process_expression_option_TODO" ^
  match a with
  | Some x -> (process_expression x)
  | None -> "nope"
and process_string_loc_expression_list x = "process_string_loc_expression_list"
and process_expression_list ( a ):string=
  "process_list" ^  
  match a with
  | [] -> "process_expression_list"
  | a :: t -> (process_expression a) ^ "|" ^ (process_expression_list t)
and process_value_binding x =
  "process_value_binding:" ^
  process_pattern(x.pvb_pat) ^ "|" ^
  process_expression(x.pvb_expr)

and  process_case (a:case) =
  "case:" ^ 
  process_pattern a.pc_lhs ^ "|" ^
  process_expression_option a.pc_guard ^ "|" ^
  process_expression a.pc_rhs
    
and process_cases ( a:cases):string=
  "process_cases" ^  
  match a with
  | [] -> "process_cases"
  | a :: t -> (process_case a) ^ "|" ^ (process_cases t)

and process_value_binding_list x = "value_binding_list" ^
    match x with
    | [] -> "process_expression_list"
    | a :: t -> (process_value_binding a) ^ "|" ^ (process_value_binding_list t)  
and  print_value_binding_expr (x : expression) : string=
  match x with
  | {
    pexp_desc (* : expression_desc *);
    pexp_loc (* : location  *);
    pexp_loc_stack (* : location_stack *);
    pexp_attributes (* : attributes *); (* [... \[@id1\] \[@id2\]] *)
  } ->
    (* (ppddump ("DEBUG66:desc", pexp_desc ))); *)
    (* (ppddump ("DEBUG66:desc", pexp_attributes ))); *)
  "print_value_binding_expr:" ^ "|" ^ (process_expression_desc pexp_desc)
and process_expression_desc ( x:expression_desc):string=
  match x with
  | Pexp_apply (expressionA0,listA1) -> (process_apply ((process_expression expressionA0),(process_list1 listA1)))
  | Pexp_array (listA0) -> (process_array ((process_expression_list listA0)))
  | Pexp_assert (expressionA0) -> (process_assert ((process_expression expressionA0)))
  | Pexp_coerce (expressionA0,optionA1,core_typeA2) -> (process_coerce ((process_expression expressionA0),(process_core_type_option optionA1),(process_core_type core_typeA2)))
  | Pexp_constant (constantA0) -> (process_constant1 ((process_constant constantA0)))
  | Pexp_constraint (expressionA0,core_typeA1) -> (process_constraint ((process_expression expressionA0),(process_core_type core_typeA1)))
  | Pexp_construct (longident_locA0,optionA1) -> (process_construct ((process_longident_loc longident_locA0),(process_expression_option optionA1)))
  | Pexp_extension (extensionA0) -> (process_extension1 ((process_extension extensionA0)))
  | Pexp_field (expressionA0,longident_locA1) -> (process_field ((process_expression expressionA0),(process_longident_loc longident_locA1)))
  | Pexp_for (patternA0,expressionA1,expressionA2,direction_flagA3,expressionA4) -> (process_for ((process_pattern patternA0),(process_expression expressionA1),(process_expression expressionA2),(process_direction_flag direction_flagA3),(process_expression expressionA4)))
  | Pexp_fun (arg_labelA0,optionA1,patternA2,expressionA3) -> (process_fun ((process_arg_label arg_labelA0),(process_expression_option optionA1),(process_pattern patternA2),(process_expression expressionA3)))
  | Pexp_function (casesA0) -> (process_function ((process_cases casesA0)))
  | Pexp_ident (longident_locA0) -> (process_ident ((process_longident_loc longident_locA0)))
  | Pexp_ifthenelse (expressionA0,expressionA1,optionA2) -> (process_ifthenelse ((process_expression expressionA0),(process_expression expressionA1),(process_expression_option optionA2)))
  | Pexp_lazy (expressionA0) -> (process_lazy ((process_expression expressionA0)))
  | Pexp_letexception (extension_constructorA0,expressionA1) -> (process_letexception ((process_extension_constructor extension_constructorA0),(process_expression expressionA1)))
  | Pexp_letmodule (locA0,module_exprA1,expressionA2) -> (process_letmodule ((process_loc locA0),(process_module_expr module_exprA1),(process_expression expressionA2)))
  | Pexp_letop (letopA0) -> (process_letop1 ((process_letop letopA0)))
  | Pexp_let (rec_flagA0,listA1,expressionA2) -> (process_let ((process_rec_flag rec_flagA0),(process_value_binding_list listA1),(process_expression expressionA2)))
  | Pexp_match (expressionA0,casesA1) -> (process_match ((process_expression expressionA0),(process_cases casesA1)))
  | Pexp_new (longident_locA0) -> (process_new ((process_longident_loc longident_locA0)))
  | Pexp_newtype (locA0,expressionA1) -> (process_newtype ((process_loc locA0),(process_expression expressionA1)))
  | Pexp_object (class_structureA0) -> (process_object ((process_class_structure class_structureA0)))
  | Pexp_open (open_declarationA0,expressionA1) -> (process_open ((process_open_declaration open_declarationA0),(process_expression expressionA1)))
  | Pexp_override (listA0) -> (process_override ((process_string_loc_expression_list listA0)))
  | Pexp_pack (module_exprA0) -> (process_pack ((process_module_expr module_exprA0)))
  | Pexp_poly (expressionA0,optionA1) -> (process_poly ((process_expression expressionA0),(process_core_type_option optionA1)))
  | Pexp_record (listA0,optionA1) -> (process_record ((process_long_ident_expression_list listA0),(process_expression_option optionA1)))
  | Pexp_send (expressionA0,locA1) -> (process_send ((process_expression expressionA0),(process_loc locA1)))
  | Pexp_sequence (expressionA0,expressionA1) -> (process_sequence ((process_expression expressionA0),(process_expression expressionA1)))
  | Pexp_setfield (expressionA0,longident_locA1,expressionA2) -> (process_setfield ((process_expression expressionA0),(process_longident_loc longident_locA1),(process_expression expressionA2)))
  | Pexp_setinstvar (locA0,expressionA1) -> (process_setinstvar ((process_loc locA0),(process_expression expressionA1)))
  | Pexp_try (expressionA0,casesA1) -> (process_try ((process_expression expressionA0),(process_cases casesA1)))
  | Pexp_tuple (listA0) -> (process_tuple ((process_expression_list listA0)))
  | Pexp_unreachable -> "Unreachable"
  | Pexp_variant (labelA0,optionA1) ->
    (process_variant ((process_label labelA0),
                      (process_expression_option optionA1)))
  | Pexp_while (expressionA0,expressionA1) -> (process_while ((process_expression expressionA0),(process_expression expressionA1)))
and process_pattern_desc x = 
    match x with
    |Ppat_any -> "patterna1"
    |Ppat_var (name) -> "pattern_Ppat_var:" ^ name.txt
    |Ppat_alias (pattern ,loc_string) -> "patterna3"
    |Ppat_constant constant  -> "patterna4"
    |Ppat_interval (constant ,constant2)  -> "patterna5"
    |Ppat_tuple pattern_list   -> "patterna6"
    |Ppat_construct (a, b)  -> "patterna7"
    |Ppat_variant (pattern, labeloptional ) -> "patterna8"
    |Ppat_record (list_longident_locpattern, closed_flag) -> "patterna9"
    |Ppat_array (pattern_) -> "patterna10 "
    |Ppat_or (pattern, pattern2)  -> "patterna12"
    |Ppat_constraint (pattern , core_type) -> "Ppat_constraint:" ^ process_pattern pattern ^ "|" ^ process_core_type core_type
    |Ppat_type longident_loc  -> "patterna14"
    |Ppat_lazy pattern  -> "patterna15"
    |Ppat_unpack (loc_option_string) -> "patterna16"
    |Ppat_exception pattern  -> "patterna17"
    |Ppat_extension extension  -> "patterna19"
    |Ppat_open (longident_loc, pattern) -> "patterna30"
and process_long_ident_expression_list x = "process_long_ident_expression_list"
and process_pattern ( apattern0:pattern):string= "PATTERN" ^ (process_pattern_desc apattern0.ppat_desc)
and process_expression ( x:expression):string= "EXPR:" ^process_expression_desc(x.pexp_desc)
and process_record_kind4 :label_declaration -> string_list -> string = fun x s -> ""
and  process_record_kind2(x :label_declaration)(s:string_list) = ""
and    process_record_kind3 x s = ""
and process_core_type ( x ):string = (my_process_core_type x)
and process_core_type_option ( a: core_type option ):string = "processcore_type_option_TODO" ^
  match a with
  | Some x -> (process_core_type x)
  | None -> "nope"
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
    let pct = (my_process_core_type pld_type) in
    (ppddump ("DEBUG:precord_kind:",  
                                    pld_name,
                                    "mutable",
                                    pld_mutable,
                                    "type",
              pld_type));
    (*
       this is a field in a record
    *)
    "process_record_kind:\"" ^ pld_name.txt ^ "|" ^ "\" body:" ^ pct
and
  my_process_core_type_desc (x : core_type_desc * string_list):string =
  match x with
    (ctd, s)->
    match ctd with
    | Ptyp_constr (a,b) (* of Longident.t loc * core_type list *)
      ->
      let {txt;loc} = a in
      let id1 = process_id1(txt) in
      (* let concat = (concatlist (id1, astring_list)) in *)
      (* let newy = [id1] @ astring_list in *)
      let newlist = (my_process_core_type_list (b, s)) in
      Printf.printf "DEBUG:Ptyp_constr1 '%s' %s" id1 newlist;
      (* "id" ^ a ^ " id2 " ^ myid  *)
      (ppddump (
         "DEBUG:Ptyp_constr:",
         "id",a,
         "types",b,
         "context",s,
         "id1", id1
       ));     
      "Ptyp_constr:\"" ^ id1 ^ "|" ^ "\"->" ^ newlist
    | Ptyp_tuple a (* of core_type list *)
      ->
      (ppddump ("DEBUG:Ptyp_tuple:", a ));
      "Ptyp_tuple" ^ my_process_core_type_list(a,  s )
    (*not in test*)
    | Ptyp_any  -> (ppddump ("DEBUG:Ptyp_any:")); "any"
    | Ptyp_var name ->(ppddump ("DEBUG:Ptyp_var:"  , name)); "var-name"
  | Ptyp_arrow (arg_label , core_type , core_type2) ->
    (* my_process_core_type((core_type, string_list)); *)
    (* my_process_core_type(core_type2, string_list); *)
    (ppddump ("DEBUG:Ptyp_arrow10:" )); "arrow"
  | Ptyp_object (a,b)(* of object_field list * closed_flag *)
    ->
    (ppddump ("DEBUG:Ptyp_arrow8:" )); "obj"
  | Ptyp_class (a,b) (* of Longident.t loc * core_type list *)
    ->
    let myid = (process_id1 a.txt) in
    (* my_process_core_type_list(b, y :: myid); *)
    (ppddump ("DEBUG:Ptyp_arrow7:" )); "class"
  | Ptyp_alias (a,b) (* of core_type * string loc  *)
    ->
    (* my_process_core_type(a, y); *)
    (ppddump ("DEBUG:Ptyp_arrow6:" )); "alias"
  | Ptyp_variant (a,b,c) (* of row_field list * closed_flag * label list option *)
    ->
    (ppddump ("DEBUG:Ptyp_arrow5:" ));"variant"
  | Ptyp_poly (a,b) (* of string loc list * core_type *)
    ->
    (* my_process_core_type(b, y); *)
    (ppddump ("DEBUG:Ptyp_arrow4:" )); "poly"
  | Ptyp_package a(* of package_type  *)
    ->
    (ppddump ("DEBUG:Ptyp_arrow3:",a )) ; "typ_package"
  (* | Ptyp_open (a,b) (\* of Longident.t loc * core_type *\)-> *)
  (*   (ppddump ("DEBUG:Ptyp_arrow2",a,b )) *)    
  | Ptyp_extension a (* of extension   *)    ->
    (ppddump ("DEBUG:Ptyp_extension:",a )); "extension"
and
  process_record_kind_list(p,x,s) : string =
  match x with
  | [] -> "process_record_kind_list"
  | h :: t ->
    (process_record_kind (h ,  s)) ^ "/" ^ (process_record_kind_list (p, t, s))    
and
  my_process_core_type(x: core_type ):string=
  match x with  
    {
      ptyp_desc(* : core_type_desc *);
      ptyp_loc(* : Location.t *);
      ptyp_loc_stack(* : location_stack *);
      ptyp_attributes(* : attributes; *)
    }->
    let td = (my_process_core_type_desc (ptyp_desc, [])) in
    "ptyp_desc:" ^ td
and my_process_core_type_list(x: core_type_list * string_list):string =
  match x with
  | (a,b) ->
    match a with
    | [] -> "my_process_core_type_list:"
    | h :: t ->
      my_process_core_type  h ^ "," ^ my_process_core_type_list(t,b)        

          
let print_value_binding_list2 (x : value_binding) : string =
  match x with
  | {
    pvb_pat; (* : pattern; *)
    pvb_expr; (* : expression; *)
    pvb_attributes; (* : attributes; *)
    pvb_loc; (* : location; *)
  } ->
    (ppddump ("DEBUG:value_binding.pat:", pvb_pat ));
    (ppddump ("DEBUG:value_binding.expr:", pvb_expr ));
    (*print_value_binding_expr pvb_expr*)
    (ppddump ("DEBUG:value_binding.atrr:", pvb_attributes ));
    (ppddump ("DEBUG:value_binding.loc:", pvb_loc ));
    "pattern:" ^ (process_pattern pvb_pat) ^ "|" ^ " expr: " ^ (process_expression pvb_expr)

let rec print_value_binding_list (x : value_binding list) : string=
  match x with
  | [] -> "print_value_binding_list"
  | h :: t ->
    (print_value_binding_list2 h)
    ^ ";;" ^(print_value_binding_list t) ^ ";;"
     

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
    (* (ppddump ("DEBUG:process_id:",  txt2)); *)
  
let splitloc(x:longident_loc * string_list) : string=
  let (a, b) = x in
  match a with
    { txt; loc }  ->
    process_id2 (txt,  b)
let concatlist(a : string * string_list):string_list =
  let (str, string_list) = a in
  let newlist = str :: string_list  in
  newlist



















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
      (* let newlist = (my_process_core_type_list (b, s)) in *)
      id1 (* ^ "\"->" ^ newlist *)
    | Ptyp_tuple a (* of core_type list *)
      ->
      "Ptyp_tuple" ^ my_process_core_type_list(a,  s )

    (*not in test*)
    | Ptyp_any  -> (ppddump ("DEBUG:Ptyp_any:")); "any"
    | Ptyp_var name ->(ppddump ("DEBUG:Ptyp_var:"  , name)); "var-name"
  | Ptyp_arrow (arg_label , core_type , core_type2) ->
    (* my_process_core_type((core_type, string_list)); *)
    (* my_process_core_type(core_type2, string_list); *)
    (ppddump ("DEBUG:Ptyp_arrow10:" )); "arrow"

  | Ptyp_object (a,b)(* of object_field list * closed_flag *)
    ->
    (ppddump ("DEBUG:Ptyp_arrow8:" )); "obj"
  | Ptyp_class (a,b) (* of Longident.t loc * core_type list *)
    ->
    let myid = (process_id1 a.txt ) in
    (* my_process_core_type_list(b, y :: myid); *)
    (ppddump ("DEBUG:Ptyp_arrow7:" )); "class"
  | Ptyp_alias (a,b) (* of core_type * string loc  *)
    ->
    (* my_process_core_type(a, y); *)
    (ppddump ("DEBUG:Ptyp_arrow6:" )); "alias"
  | Ptyp_variant (a,b,c) (* of row_field list * closed_flag * label list option *)
    ->
    (ppddump ("DEBUG:Ptyp_arrow5:" ));"variant"
  | Ptyp_poly (a,b) (* of string loc list * core_type *)
    ->
    (* my_process_core_type(b, y); *)
    (ppddump ("DEBUG:Ptyp_arrow4:" )); "poly"
  | Ptyp_package a(* of package_type  *)
    ->
    (ppddump ("DEBUG:Ptyp_arrow3:",a )) ; "typ_package"
  (* | Ptyp_open (a,b) (\* of Longident.t loc * core_type *\)-> *)
  (*   (ppddump ("DEBUG:Ptyp_arrow2",a,b )) *)    
  | Ptyp_extension a (* of extension   *)    ->
    (ppddump ("DEBUG:Ptyp_extension:",a )); "extension"


let  emit_core_type(a: core_type * string_list*int):string=
  match a with
  | (x,s,n) ->
     match x with  
    {
      ptyp_desc(* : core_type_desc *);
      ptyp_loc(* : Location.t *);
      ptyp_loc_stack(* : location_stack *);
      ptyp_attributes(* : attributes; *)
    }->
    let td = (emit_core_type_desc (ptyp_desc,s)) in
    td ^ (string_of_int n)

let  emit_core_type2(a: core_type * string_list*int):string=
  match a with
  | (x,s,n) ->
    match x with  
      {
        ptyp_desc(* : core_type_desc *);
        ptyp_loc(* : Location.t *);
        ptyp_loc_stack(* : location_stack *);
        ptyp_attributes(* : attributes; *)
      }->
      let td = (emit_core_type_desc (ptyp_desc,s)) in
      td 
                

let rec emit_core_type_list(x: core_type_list * string_list*int):string =
  match x with
  | (a,b,n) ->
    match a with
    | [] -> ""
    | h :: t ->
      let tt = emit_core_type_list(t,b,n+1)  in
      let h1 = emit_core_type (h,b,n) in
      if tt != "" then 
        h1 ^ "," ^ tt
      else 
        h1

let  imp_core_type((a,s,n): core_type * string_list*int):string=

  let name1 = emit_core_type2(a,s,n) in
  let name = emit_core_type(a,s,n) in
  "(process_" ^ name1 ^ " " ^ name  ^ ")"
(* ^"B" ^(string_of_int n) *)


(* calls the function from the constructor*)
let rec imp_core_type_list(x: core_type_list * string_list*int):string =
  match x with
  | (a,b,n) ->
    match a with
    | [] -> ""
    | h :: t ->
      let tt = imp_core_type_list(t,b,n+1)  in
      let one = imp_core_type (h, b,n ) in
      if tt != "" then 
        one ^ "," ^ tt
      else 
        one 

let emit_constructor_arguments(a1:(string*string*constructor_arguments*string_list)):string =  let (parent,name,x,s) = a1 in  match x with  | Pcstr_tuple a ->
    "| " ^ name ^ " ("^ (emit_core_type_list (a,s,0))  ^ ") -> " ^ "("
    ^ "process_types_" ^ parent ^ "__"^ name^  "(" ^ imp_core_type_list (a,s,0) ^"))"
  | other  -> "other"

let  decl_imp_core_type(a: string*string *core_type * string_list*int):string=
  let (parent, parent2, atype, s, n) = a in
  let name = emit_core_type(atype, s, n) in
  let h1 = emit_core_type2(atype, s, n) in
  (print_endline ("DEBUG2A:" ^ "let process_" ^ h1 ^ " x : " ^ h1 ^ "= x"));  
  "a" ^ name  
(* ":" ^ name1  *)
(* ")" *)
(* :string=\""^parent  ^ "__" ^ parent2  ^ "_" ^ name1  ^"\" ^ \"a" ^ name ^ "\"\n" *)


let ff =1
let rec decl_imp_core_type_list(parent,name,a,b,n) = 
  match a with
  | [] -> ""
  | h :: t ->
    let h1 = decl_imp_core_type (parent,name, h, b,n) in
    let tt = decl_imp_core_type_list(parent,name,t,b,n+1)  in
    if tt != "" then 
      h1 ^ "," ^ tt 
    else 
      h1
        
let f=1        
let rec decl_imp_core_type_list2((parent,name,a,b,n): string*string*core_type_list * string_list*int):string = 
  match a with
  | [] -> ""
  | h :: t ->
    let h1 = emit_core_type2(h, b, n) in
    let tt = decl_imp_core_type_list2(parent,name,t,b,n+1)  in
    if tt != "" then 
      h1 ^ "*" ^ tt 
    else 
      h1

(*sep with hats ^ string concat *)
let rec decl_imp_core_type_list_hats((parent,name,a,b,n): string*string*core_type_list * string_list*int):string = 
  match a with
  | [] -> ""
  | h :: t ->
    let h1 = decl_imp_core_type (parent,name, h, b,n) in
    let quoted = "\"" ^ h1 ^ "\"" in
    let tt = decl_imp_core_type_list_hats(parent,name,t,b,n+1)  in
    if tt != "" then 
      quoted ^ "^" ^ tt 
    else 
      quoted
        
let decl_emit_constructor_arguments(parent,name,x,s):string =
  match x with
  | Pcstr_tuple a ->
    "let "^ "process_types_" ^ parent ^ "__" ^ name
    ^ "(("    ^  decl_imp_core_type_list (parent,name,a,s,0) ^   "):"
    ^ "("    ^  decl_imp_core_type_list2 (parent,name,a,s,0) ^  ")):string"
    ^ " = \"process_types_" ^ parent ^ "__" ^ name ^ "\"^" ^
    (decl_imp_core_type_list_hats (parent,name,a,s,0) )
  | other  -> "other"

let process_label_declaration  x =
  "Label_decl:" ^  x.pld_name.txt ^ process_core_type x.pld_type
    
let rec process_label_declaration_list x = 
  match x with
  | [] -> "label_declaration_list:" 
  | h :: t ->
    process_label_declaration h ^
    "|"^ (process_label_declaration_list t)

let print_constructor_arguments(a) =
  match a with
  | (x,s) ->
    match x with
    | Pcstr_tuple a ->       
      (ppddump ("DEBUG:Pcstr_tuple:"  , a));
      "Pcstr_tuple:" ^ (my_process_core_type_list (a,s))
       
    | Pcstr_record a ->
      (ppddump ("DEBUG:Pcstr_record:"  , a));
      "Pcstr_record" ^
      (process_label_declaration_list a)

        
let rec process_type_variant_constructor_declaration_list(a:string*constructor_declaration list*string_list):string =
  match a with
  | (p,x,s)->
    match x with
    | [] -> "VARIANT(" ^ p ^ "):"
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
        (print_endline (
            "DEBUG2C: let process_"
            ^ p ^ "__" ^ pcd_name.txt
            ^ " x :string ="
            ^ "match x with "));
        (* let name = match pcd_name with *)
        (*   | (str,_) -> str *)
        (* (ppddump ( *)
        (*      "DEBUG:constructor_declaration:", *)
        (*      pcd_name, *)
        (*      "vars", *)
        (*      pcd_vars, *)
        (*      "args", *)
        (*      pcd_args, *)
        (*      "res", *)
        (*      pcd_res, *)
        (*      "loc", *)
        (*      pcd_loc, *)
        (*      "attrs", *)
        (*      pcd_attributes *)
        (*    )); *)
        let newtext = (emit_constructor_arguments(p,pcd_name.txt, pcd_args, s)) in
        let newtext2 = (decl_emit_constructor_arguments(p,pcd_name.txt, pcd_args, s)) in
        (print_endline ("DEBUG2B:" ^ newtext2));
        (print_endline ("DEBUG2C:" ^ newtext)); 
        let ret =              "constructor:\""^ pcd_name.txt ^ "\""
                               ^ "{" ^
                               print_constructor_arguments(pcd_args,s)
                               ^ "}" ^ "\t|" ^
                               process_type_variant_constructor_declaration_list(p,t,s)
        in
        Printf.printf "DEBUG:constructor_declaration_new: %s\n" ret;
        ret
        
let bar =1
  
let process_kind(a) :string=
  match a with
  | (p,x,s)->
    match x with
    (*and type_kind =*)
    | Ptype_abstract  -> (ppddump ("DEBUG:Ptype_abstract:"));
      "DEBUG:Ptype_abstract"
    | Ptype_variant a ->      
      (* (ppddump ("DEBUG:Ptype_variant:",  a)); *)
      "type variant:" ^ (process_type_variant_constructor_declaration_list (p,a,s))      
    (*of constructor_declaration list *)     
    | Ptype_record a ->     
      process_record_kind_list(p,a,s)
    | Ptype_open -> (ppddump ("DEBUG:Ptype_abstract:")); "Ptype_abstract"

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
      (* (ppddump ("DEBUG:type_decl:", ptype_name)); *)
      (* (ppddump ("DEBUG:parameters:", ptype_params)); *)
      (* (ppddump ("DEBUG:cstrs:", ptype_cstrs)); *)
      (* (ppddump ("DEBUG:kind:",ptype_kind)); *)
      
      (* (ppddump ("DEBUG:private:",  ptype_private, *)
      (*                                 "DEBUG:manifest", ptype_manifest, *)
      (*                                 "DEBUG:attr", ptype_attributes, *)
      (*                                 "DEBUG:loc", ptype_loc *)
      (*                                )); *)
      "print_type_decl:\"" ^  ptype_name.txt ^ "\" = " ^ (process_kind (ptype_name.txt,ptype_kind,s))
      
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

(*
   start of generator for record types
      first step to generate record vistior :
   1. function with type
   1.1. single argument x
   2. match x with pattern
   3. action on variablee to print them.

   and type_kind = Parsetree.type_kind =
  | Ptype_record of label_declaration list  (** Invariant: non-empty list *)

           | Ptype_record a ->
            let a = self#list self#label_declaration ctx a in
            ( Ptype_record (Stdlib.fst a),
              self#constr ctx "Ptype_record" [ Stdlib.snd a ] )
*)
let fffff=1

(*the decl list
  list,
  string context,
  separarator
*)


let printdesc(a :structure_item_desc*string_list) :string =
  "printdesc" ^
  match a with
  |(x,s)->
    (* (ppddump ("DEBUG:structure_item_desc:", x)); *)
    match x with
    | Pstr_value (rec_flag, value_binding_list) ->
      (* (ppddump ("DEBUG:Pstr_value:", rec_flag, value_binding_list)); *)
      "Pstr_value:"      ^ print_value_binding_list(value_binding_list)
    | Pstr_type (rec_flag, type_declaration_list) ->      
      (print_endline ("\nHELP:\n"^(Emitthecode.emit_type_decl_list (type_declaration_list,s," "))^"\n"));
      "Pstr_type:"^
      process_type_decl_list((type_declaration_list,s))
    | Pstr_module  module_binding ->
      (* (ppddump ("DEBUG:Pstr_module:",module_binding)); *) "module_binding"
    (*open model*)
    | Pstr_open open_description ->(ppddump ("DEBUG:Pstr_open", open_description)); "module_open"
    | Pstr_eval (expression,attributes) ->
      (ppddump ("DEBUG:Pstr_eval:", expression,attributes));
      "Pstr_eval"
    (*value binding*)
    | Pstr_primitive value_description ->(ppddump ("DEBUG:Pstr_primitive:", value_description)) ; "primitive"
    | Pstr_typext  type_extension ->(ppddump ("DEBUG:Pstr_typext:", type_extension)); "typeext"
    | Pstr_exception extension_constructor ->(ppddump ("DEBUG:Pstr_exception:", extension_constructor)); "exception"
    | Pstr_recmodule  module_binding_list ->(ppddump ("DEBUG:Pstr_recmodule:", module_binding_list)) ; "recmodule"
    | Pstr_modtype module_type_declaration ->(ppddump ("DEBUG:Pstr_modtype:", module_type_declaration)); "modtype"
    | Pstr_class (class_declarations ) ->(ppddump ("DEBUG:Pstr_class:", class_declarations)); "class"
    | Pstr_class_type (class_type_declarations) ->(ppddump ("DEBUG:Pstr_class_type:", class_type_declarations)) ; "class_Type"
    | Pstr_include  (include_declaration)->(ppddump ("DEBUG:Pstr_include:",include_declaration)); "include"
    | Pstr_attribute (attribute)->(ppddump ("DEBUG:Pstr_attribute:", attribute)); "_attribute"
    | Pstr_extension ( extension , attributes)->(ppddump ("DEBUG:Pstr_extension:", extension , attributes)) ; "extension"

let process_string x = x
let foo = 1
  
let printone (x : structure_item) :string =
  match x with
  |{
    pstr_desc; (*structure_item_desc*)
    _
  } ->
    "TOPstructure_item_desc:" ^ (printdesc (pstr_desc,[]))

let printone2 x :string =
  (ppddump ("DEBUG:SECOND::",x));
  printone x
  
let proc1 x :string  =
  printone2 x
 
let debug proc lst : string =
  let result = List.map proc lst in
  List.iter (fun i -> print_endline i) result;
    "TODO"
                
let transform x (*ast, bytecodes of the interface *) =
  (ppddump ("DEBUG3:",x));
  (print_endline ("DEBUG2AA:" ^ "open Ppxlib")); 
  let foo = (debug proc1 x) in
  x

let process_bool x = "bool"
                                                          
let () = Driver.register_transformation ~impl:transform "simple-ppx" 
