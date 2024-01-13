open Ppxlib
let process_types_structure_item_desc__Pstr_eval x = "process_types_structure_item_desc__Pstr_eval"
let process_rec_flag x = x
  let process_type_extension x =x 
let process_value_description x = x
let process_module_binding x = x
let process_open_declaration x =x 
let process_module_type_declaration x = x
let process_include_declaration x =x 
let process_attributes  x = x
let process_list x = x
let process_type_exception   x = x
  
let process_attribute x = x
let process_expression x = x
let process_structure x = x
let process_longident_loc x = x
let process_functor_parameter x =x
let process_types_module_expr_desc__Pmod_ident   x = "process_types_module_expr_desc__Pmod_ident"
let process_bool x = x
let process_module_type x = x
let process_extension (x,y) = x
let process_longident x = x
let process_string x = x
let process_option x = x
let process_module_expr x = x


(*generated code below*)
let process_types_directive_argument_desc__Pdir_bool ( abool0:bool):string="directive_argument_desc__Pdir_bool_bool" ^ "abool0"
let process_types_directive_argument_desc__Pdir_ident ( alongident0:longident):string="directive_argument_desc__Pdir_ident_longident" ^ "alongident0"
let process_types_directive_argument_desc__Pdir_int (a,b):string="directive_argument_desc__Pdir_int_string" ^ "astring0"
let process_types_directive_argument_desc__Pdir_string ( astring0:string):string="directive_argument_desc__Pdir_string_string" ^ "astring0"
let process_types_module_expr_desc__Pmod_apply ( amodule_expr0,amodule_expr1):string="module_expr_desc__Pmod_apply_module_expr" ^ "amodule_expr0"
let process_types_module_expr_desc__Pmod_constraint ( a,b):string="module_expr_desc__Pmod_constraint_module_expr" ^ "amodule_expr0"
let process_types_module_expr_desc__Pmod_extension ( aextension0):string="module_expr_desc__Pmod_extension_extension" ^ "aextension0"
let process_types_module_expr_desc__Pmod_functor ( a,b):string="module_expr_desc__Pmod_functor_functor_parameter" ^ "afunctor_parameter0"
let process_types_module_expr_desc__Pmod_structure ( astructure0:structure):string="module_expr_desc__Pmod_structure_structure" ^ "astructure0"
let process_types_module_expr_desc__Pmod_unpack ( aexpression0:expression):string="module_expr_desc__Pmod_unpack_expression" ^ "aexpression0"
let process_types_structure_item_desc__Pstr_attribute ( aattribute0:attribute):string="structure_item_desc__Pstr_attribute_attribute" ^ "aattribute0"
let process_types_structure_item_desc__Pstr_class ( alist0):string="structure_item_desc__Pstr_class_list" ^ "alist0"
let process_types_structure_item_desc__Pstr_class_type ( alist0):string="structure_item_desc__Pstr_class_type_list" ^ "alist0"
let process_types_structure_item_desc__Pstr_exception ( atype_exception0:type_exception):string="structure_item_desc__Pstr_exception_type_exception" ^ "atype_exception0"
let process_types_structure_item_desc__Pstr_extension ( a,b):string="structure_item_desc__Pstr_extension_extension" ^ "aextension0"
let process_types_structure_item_desc__Pstr_include ( ainclude_declaration0:include_declaration):string="structure_item_desc__Pstr_include_include_declaration" ^ "ainclude_declaration0"
let process_types_structure_item_desc__Pstr_modtype ( amodule_type_declaration0:module_type_declaration):string="structure_item_desc__Pstr_modtype_module_type_declaration" ^ "amodule_type_declaration0"
let process_types_structure_item_desc__Pstr_module ( amodule_binding0:module_binding):string="structure_item_desc__Pstr_module_module_binding" ^ "amodule_binding0"
let process_types_structure_item_desc__Pstr_open ( aopen_declaration0:open_declaration):string="structure_item_desc__Pstr_open_open_declaration" ^ "aopen_declaration0"
let process_types_structure_item_desc__Pstr_primitive ( avalue_description0:value_description):string="structure_item_desc__Pstr_primitive_value_description" ^ "avalue_description0"
let process_types_structure_item_desc__Pstr_recmodule ( alist0):string="structure_item_desc__Pstr_recmodule_list" ^ "alist0"
let process_types_structure_item_desc__Pstr_type (a,b):string="structure_item_desc__Pstr_type_rec_flag" ^ "arec_flag0"
let process_types_structure_item_desc__Pstr_typext ( atype_extension0:type_extension):string="structure_item_desc__Pstr_typext_type_extension" ^ "atype_extension0"
let process_types_structure_item_desc__Pstr_value (a,b):string="structure_item_desc__Pstr_value_rec_flag" ^ "arec_flag0"
let process_types_toplevel_phrase__Ptop_dir ( atoplevel_directive0:toplevel_directive):string="toplevel_phrase__Ptop_dir_toplevel_directive" ^ "atoplevel_directive0"
let process_types_with_constraint__Pwith_modsubst ( alongident_loc0:longident_loc):string="with_constraint__Pwith_modsubst_longident_loc" ^ "alongident_loc0"
let process_types_with_constraint__Pwith_modtype ( a,b):string="with_constraint__Pwith_modtype_longident_loc" ^ "alongident_loc0"
let process_types_with_constraint__Pwith_modtypesubst ( a,b):string="with_constraint__Pwith_modtypesubst_longident_loc" ^ "alongident_loc0"
let process_types_with_constraint__Pwith_module ( a,b):string="with_constraint__Pwith_module_longident_loc" ^ "alongident_loc0"
let process_types_with_constraint__Pwith_typesubst ( a,b):string="with_constraint__Pwith_typesubst_longident_loc" ^ "alongident_loc0"


let  process_types_directive_argument_desc x =
  match x with 
  | Pdir_bool (bool0) -> (process_types_directive_argument_desc__Pdir_bool((process_bool bool0)))
  | Pdir_ident (longident0) -> (process_types_directive_argument_desc__Pdir_ident((process_longident longident0)))
  | Pdir_int (string0,option1) -> (process_types_directive_argument_desc__Pdir_int((process_string string0),(process_option option1)))
  | Pdir_string (string0) -> (process_types_directive_argument_desc__Pdir_string((process_string string0)))

let process_types_module_expr_desc x = match x with 
  | Pmod_apply (module_expr0,module_expr1) -> (process_types_module_expr_desc__Pmod_apply((process_module_expr module_expr0),(process_module_expr module_expr1)))
  | Pmod_constraint (module_expr0,module_type1) -> (process_types_module_expr_desc__Pmod_constraint((process_module_expr module_expr0),(process_module_type module_type1)))
  | Pmod_extension (extension0) -> (process_types_module_expr_desc__Pmod_extension((process_extension extension0)))
  | Pmod_functor (functor_parameter0,module_expr1) -> (process_types_module_expr_desc__Pmod_functor((process_functor_parameter functor_parameter0),(process_module_expr module_expr1)))
  | Pmod_ident (longident_loc0) -> (process_types_module_expr_desc__Pmod_ident((process_longident_loc longident_loc0)))
  | Pmod_structure (structure0) -> (process_types_module_expr_desc__Pmod_structure((process_structure structure0)))
  | Pmod_unpack (expression0) -> (process_types_module_expr_desc__Pmod_unpack((process_expression expression0)))

let process_types_structure_item_desc x = match x with 
  | Pstr_attribute (attribute0) -> (process_types_structure_item_desc__Pstr_attribute((process_attribute attribute0)))
  | Pstr_class (list0) -> (process_types_structure_item_desc__Pstr_class((process_list list0)))
  | Pstr_class_type (list0) -> (process_types_structure_item_desc__Pstr_class_type((process_list list0)))
  | Pstr_eval (expression0,attributes1) -> (process_types_structure_item_desc__Pstr_eval((process_expression expression0),(process_attributes attributes1)))
  | Pstr_exception (type_exception0) -> (process_types_structure_item_desc__Pstr_exception((process_type_exception type_exception0)))
  | Pstr_extension (extension0,attributes1) -> (process_types_structure_item_desc__Pstr_extension((process_extension extension0),(process_attributes attributes1)))
  | Pstr_include (include_declaration0) -> (process_types_structure_item_desc__Pstr_include((process_include_declaration include_declaration0)))
  | Pstr_modtype (module_type_declaration0) -> (process_types_structure_item_desc__Pstr_modtype((process_module_type_declaration module_type_declaration0)))
  | Pstr_module (module_binding0) -> (process_types_structure_item_desc__Pstr_module((process_module_binding module_binding0)))
| Pstr_open (open_declaration0) -> (process_types_structure_item_desc__Pstr_open((process_open_declaration open_declaration0)))
| Pstr_primitive (value_description0) -> (process_types_structure_item_desc__Pstr_primitive((process_value_description value_description0)))
| Pstr_recmodule (list0) -> (process_types_structure_item_desc__Pstr_recmodule((process_list list0)))
| Pstr_type (rec_flag0,list1) -> (process_types_structure_item_desc__Pstr_type((process_rec_flag rec_flag0),(process_list list1)))
| Pstr_typext (type_extension0) -> (process_types_structure_item_desc__Pstr_typext((process_type_extension type_extension0)))
| Pstr_value (rec_flag0,list1) -> (process_types_structure_item_desc__Pstr_value((process_rec_flag rec_flag0),(process_list list1)))

let process_types_toplevel_phrase__Ptop_def x = "process_types_toplevel_phrase__Ptop_def"
let     process_toplevel_directive x = x

let process_types_toplevel_phrase x = match x with 
  | Ptop_def (structure0) -> (process_types_toplevel_phrase__Ptop_def((process_structure structure0)))
  | Ptop_dir (toplevel_directive0) -> (process_types_toplevel_phrase__Ptop_dir((process_toplevel_directive toplevel_directive0)))


let process_types_with_constraint__Pwith_modsubst x = "process_types_with_constraint__Pwith_modsubst"

let process_open_declaration x = x
  let process_type_declaration x =x 
let process_types_with_constraint__Pwith_type ( a,b):string="with_constraint__Pwith_type_longident_loc" ^ "alongident_loc0"
                                                                                      
let process_types_with_constraint x = match x with 
  | Pwith_modsubst (longident_loc0,longident_loc1) -> (process_types_with_constraint__Pwith_modsubst((process_longident_loc longident_loc0),(process_longident_loc longident_loc1)))
  | Pwith_modtype (longident_loc0,module_type1) -> (process_types_with_constraint__Pwith_modtype((process_longident_loc longident_loc0),(process_module_type module_type1)))
  | Pwith_modtypesubst (longident_loc0,module_type1) -> (process_types_with_constraint__Pwith_modtypesubst((process_longident_loc longident_loc0),(process_module_type module_type1)))
  | Pwith_module (longident_loc0,longident_loc1) -> (process_types_with_constraint__Pwith_module((process_longident_loc longident_loc0),(process_longident_loc longident_loc1)))
  | Pwith_type (longident_loc0,type_declaration1) -> (process_types_with_constraint__Pwith_type((process_longident_loc longident_loc0),(process_type_declaration type_declaration1))) 
  | Pwith_typesubst (longident_loc0,type_declaration1) -> (process_types_with_constraint__Pwith_typesubst((process_longident_loc longident_loc0),(process_type_declaration type_declaration1))) 
