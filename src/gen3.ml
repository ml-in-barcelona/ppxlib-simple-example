open Ppxlib
let process_attributes x : attributes= x
let process_attribute x : attribute= x
let process_bool x : bool= x
let process_expression x : expression= x
let process_extension x : extension= x
let process_functor_parameter x : functor_parameter= x
let process_include_declaration x : include_declaration= x
let process_list x = x
let process_longident_loc x : longident_loc= x
let process_longident x : longident= x
let process_module_binding x : module_binding= x
let process_module_expr x : module_expr= x
let process_module_type_declaration x : module_type_declaration= x
let process_module_type x : module_type= x
let process_open_declaration x : open_declaration= x
let process_option x = x
let process_rec_flag x : rec_flag= x
let process_string x : string= x
let process_structure x : structure= x
let process_toplevel_directive x : toplevel_directive= x
let process_type_declaration x : type_declaration= x
let process_type_exception x : type_exception= x
let process_type_extension x : type_extension= x
let process_value_description x : value_description= x
let process_types_directive_argument_desc__Pdir_bool((abool0):(bool)):string = "process_types_directive_argument_desc__Pdir_bool"^"abool0"
let process_types_directive_argument_desc__Pdir_ident((alongident0):(longident)):string = "process_types_directive_argument_desc__Pdir_ident"^"alongident0"
let process_types_directive_argument_desc__Pdir_int((astring0,aoption1)):string = "process_types_directive_argument_desc__Pdir_int"^"astring0"^"aoption1"
let process_types_directive_argument_desc__Pdir_string((astring0):(string)):string = "process_types_directive_argument_desc__Pdir_string"^"astring0"
let process_types_module_expr_desc__Pmod_apply((amodule_expr0,amodule_expr1):(module_expr*module_expr)):string = "process_types_module_expr_desc__Pmod_apply"^"amodule_expr0"^"amodule_expr1"
let process_types_module_expr_desc__Pmod_constraint((amodule_expr0,amodule_type1):(module_expr*module_type)):string = "process_types_module_expr_desc__Pmod_constraint"^"amodule_expr0"^"amodule_type1"
let process_types_module_expr_desc__Pmod_extension((aextension0):(extension)):string = "process_types_module_expr_desc__Pmod_extension"^"aextension0"
let process_types_module_expr_desc__Pmod_functor((afunctor_parameter0,amodule_expr1):(functor_parameter*module_expr)):string = "process_types_module_expr_desc__Pmod_functor"^"afunctor_parameter0"^"amodule_expr1"
let process_types_module_expr_desc__Pmod_ident((alongident_loc0):(longident_loc)):string = "process_types_module_expr_desc__Pmod_ident"^"alongident_loc0"
let process_types_module_expr_desc__Pmod_structure((astructure0):(structure)):string = "process_types_module_expr_desc__Pmod_structure"^"astructure0"
let process_types_module_expr_desc__Pmod_unpack((aexpression0):(expression)):string = "process_types_module_expr_desc__Pmod_unpack"^"aexpression0"
let process_types_structure_item_desc__Pstr_attribute((aattribute0):(attribute)):string = "process_types_structure_item_desc__Pstr_attribute"^"aattribute0"
let process_types_structure_item_desc__Pstr_class((alist0)):string = "process_types_structure_item_desc__Pstr_class"^"alist0"
let process_types_structure_item_desc__Pstr_class_type((alist0)):string = "process_types_structure_item_desc__Pstr_class_type"^"alist0"
let process_types_structure_item_desc__Pstr_eval((aexpression0,aattributes1):(expression*attributes)):string = "process_types_structure_item_desc__Pstr_eval"^"aexpression0"^"aattributes1"
let process_types_structure_item_desc__Pstr_exception((atype_exception0):(type_exception)):string = "process_types_structure_item_desc__Pstr_exception"^"atype_exception0"
let process_types_structure_item_desc__Pstr_extension((aextension0,aattributes1):(extension*attributes)):string = "process_types_structure_item_desc__Pstr_extension"^"aextension0"^"aattributes1"
let process_types_structure_item_desc__Pstr_include((ainclude_declaration0):(include_declaration)):string = "process_types_structure_item_desc__Pstr_include"^"ainclude_declaration0"
let process_types_structure_item_desc__Pstr_modtype((amodule_type_declaration0):(module_type_declaration)):string = "process_types_structure_item_desc__Pstr_modtype"^"amodule_type_declaration0"
let process_types_structure_item_desc__Pstr_module((amodule_binding0):(module_binding)):string = "process_types_structure_item_desc__Pstr_module"^"amodule_binding0"
let process_types_structure_item_desc__Pstr_open((aopen_declaration0):(open_declaration)):string = "process_types_structure_item_desc__Pstr_open"^"aopen_declaration0"
let process_types_structure_item_desc__Pstr_primitive((avalue_description0):(value_description)):string = "process_types_structure_item_desc__Pstr_primitive"^"avalue_description0"
let process_types_structure_item_desc__Pstr_recmodule((alist0)):string = "process_types_structure_item_desc__Pstr_recmodule"^"alist0"
let process_types_structure_item_desc__Pstr_type((arec_flag0,alist1)):string = "process_types_structure_item_desc__Pstr_type"^"arec_flag0"^"alist1"
let process_types_structure_item_desc__Pstr_typext((atype_extension0):(type_extension)):string = "process_types_structure_item_desc__Pstr_typext"^"atype_extension0"
let process_types_structure_item_desc__Pstr_value((arec_flag0,alist1)):string = "process_types_structure_item_desc__Pstr_value"^"arec_flag0"^"alist1"
let process_types_toplevel_phrase__Ptop_def((astructure0):(structure)):string = "process_types_toplevel_phrase__Ptop_def"^"astructure0"
let process_types_toplevel_phrase__Ptop_dir((atoplevel_directive0):(toplevel_directive)):string = "process_types_toplevel_phrase__Ptop_dir"^"atoplevel_directive0"
let process_types_with_constraint__Pwith_modtype((alongident_loc0,amodule_type1):(longident_loc*module_type)):string = "process_types_with_constraint__Pwith_modtype"^"alongident_loc0"^"amodule_type1"
let process_types_with_constraint__Pwith_modtypesubst((alongident_loc0,amodule_type1):(longident_loc*module_type)):string = "process_types_with_constraint__Pwith_modtypesubst"^"alongident_loc0"^"amodule_type1"
let process_types_with_constraint__Pwith_module((alongident_loc0,alongident_loc1):(longident_loc*longident_loc)):string = "process_types_with_constraint__Pwith_module"^"alongident_loc0"^"alongident_loc1"
let process_types_with_constraint__Pwith_type((alongident_loc0,atype_declaration1):(longident_loc*type_declaration)):string = "process_types_with_constraint__Pwith_type"^"alongident_loc0"^"atype_declaration1"
 let process_directive_argument_desc__Pdir_string x :string =match x with 
| Pdir_string (string0) -> (process_types_directive_argument_desc__Pdir_string((process_string string0)))
 let process_directive_argument_desc__Pdir_int x :string =match x with 
| Pdir_int (string0,option1) -> (process_types_directive_argument_desc__Pdir_int((process_string string0),(process_option option1)))
 let process_directive_argument_desc__Pdir_ident x :string =match x with 
| Pdir_ident (longident0) -> (process_types_directive_argument_desc__Pdir_ident((process_longident longident0)))
 let process_directive_argument_desc__Pdir_bool x :string =match x with 
| Pdir_bool (bool0) -> (process_types_directive_argument_desc__Pdir_bool((process_bool bool0)))

let process_toplevel_phrase__Ptop_dir x :string =match x with
  | Ptop_def (structure0) -> (process_types_toplevel_phrase__Ptop_def((process_structure structure0))) 
| Ptop_dir (toplevel_directive0) -> (process_types_toplevel_phrase__Ptop_dir((process_toplevel_directive toplevel_directive0)))

let process_structure_item_desc__Pstr_value x :string =match x with
  | Pstr_eval (expression0,attributes1) -> (process_types_structure_item_desc__Pstr_eval((process_expression expression0),(process_attributes attributes1)))
| Pstr_value (rec_flag0,list1) -> (process_types_structure_item_desc__Pstr_value((process_rec_flag rec_flag0),(process_list list1)))
 let process_structure_item_desc__Pstr_primitive x :string =match x with 
| Pstr_primitive (value_description0) -> (process_types_structure_item_desc__Pstr_primitive((process_value_description value_description0)))
 let process_structure_item_desc__Pstr_type x :string =match x with 
| Pstr_type (rec_flag0,list1) -> (process_types_structure_item_desc__Pstr_type((process_rec_flag rec_flag0),(process_list list1)))
 let process_structure_item_desc__Pstr_typext x :string =match x with 
| Pstr_typext (type_extension0) -> (process_types_structure_item_desc__Pstr_typext((process_type_extension type_extension0)))
 let process_structure_item_desc__Pstr_exception x :string =match x with 
| Pstr_exception (type_exception0) -> (process_types_structure_item_desc__Pstr_exception((process_type_exception type_exception0)))
 let process_structure_item_desc__Pstr_module x :string =match x with 
| Pstr_module (module_binding0) -> (process_types_structure_item_desc__Pstr_module((process_module_binding module_binding0)))
 let process_structure_item_desc__Pstr_recmodule x :string =match x with 
| Pstr_recmodule (list0) -> (process_types_structure_item_desc__Pstr_recmodule((process_list list0)))
 let process_structure_item_desc__Pstr_modtype x :string =match x with 
| Pstr_modtype (module_type_declaration0) -> (process_types_structure_item_desc__Pstr_modtype((process_module_type_declaration module_type_declaration0)))
 let process_structure_item_desc__Pstr_open x :string =match x with 
| Pstr_open (open_declaration0) -> (process_types_structure_item_desc__Pstr_open((process_open_declaration open_declaration0)))
 let process_structure_item_desc__Pstr_class x :string =match x with 
| Pstr_class (list0) -> (process_types_structure_item_desc__Pstr_class((process_list list0)))
 let process_structure_item_desc__Pstr_class_type x :string =match x with 
| Pstr_class_type (list0) -> (process_types_structure_item_desc__Pstr_class_type((process_list list0)))
 let process_structure_item_desc__Pstr_include x :string =match x with 
| Pstr_include (include_declaration0) -> (process_types_structure_item_desc__Pstr_include((process_include_declaration include_declaration0)))
 let process_structure_item_desc__Pstr_attribute x :string =match x with 
| Pstr_attribute (attribute0) -> (process_types_structure_item_desc__Pstr_attribute((process_attribute attribute0)))
 let process_structure_item_desc__Pstr_extension x :string =match x with 
| Pstr_extension (extension0,attributes1) -> (process_types_structure_item_desc__Pstr_extension((process_extension extension0),(process_attributes attributes1)))

let process_module_expr_desc__Pmod_structure x :string =match x with
  | Pmod_ident (longident_loc0) -> (process_types_module_expr_desc__Pmod_ident((process_longident_loc longident_loc0)))
| Pmod_structure (structure0) -> (process_types_module_expr_desc__Pmod_structure((process_structure structure0)))
 let process_module_expr_desc__Pmod_functor x :string =match x with 
| Pmod_functor (functor_parameter0,module_expr1) -> (process_types_module_expr_desc__Pmod_functor((process_functor_parameter functor_parameter0),(process_module_expr module_expr1)))
 let process_module_expr_desc__Pmod_apply x :string =match x with 
| Pmod_apply (module_expr0,module_expr1) -> (process_types_module_expr_desc__Pmod_apply((process_module_expr module_expr0),(process_module_expr module_expr1)))
 let process_module_expr_desc__Pmod_constraint x :string =match x with 
| Pmod_constraint (module_expr0,module_type1) -> (process_types_module_expr_desc__Pmod_constraint((process_module_expr module_expr0),(process_module_type module_type1)))
 let process_module_expr_desc__Pmod_unpack x :string =match x with 
| Pmod_unpack (expression0) -> (process_types_module_expr_desc__Pmod_unpack((process_expression expression0)))
 let process_module_expr_desc__Pmod_extension x :string =match x with 
| Pmod_extension (extension0) -> (process_types_module_expr_desc__Pmod_extension((process_extension extension0)))

let process_with_constraint__Pwith_module x :string =match x with
  | Pwith_type (longident_loc0,type_declaration1) -> (process_types_with_constraint__Pwith_type((process_longident_loc longident_loc0),(process_type_declaration type_declaration1)))
| Pwith_module (longident_loc0,longident_loc1) -> (process_types_with_constraint__Pwith_module((process_longident_loc longident_loc0),(process_longident_loc longident_loc1)))
 let process_with_constraint__Pwith_modtype x :string =match x with 
| Pwith_modtype (longident_loc0,module_type1) -> (process_types_with_constraint__Pwith_modtype((process_longident_loc longident_loc0),(process_module_type module_type1)))
 let process_with_constraint__Pwith_modtypesubst x :string =match x with 
| Pwith_modtypesubst (longident_loc0,module_type1) -> (process_types_with_constraint__Pwith_modtypesubst((process_longident_loc longident_loc0),(process_module_type module_type1)))
