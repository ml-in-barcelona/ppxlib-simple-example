open Ppxlib
open Ppxlibextras
let rec emit_type_decl_list((x,s,t1):(type_declaration_list*string_list*string)):string=
  match x with
  | [] -> ""
  | h :: t ->
    (emit_type_decl (h,s))
    ^ t1 ^
    (emit_type_decl_list (t,s,t1))
and  emit_id1 a : string = 
  match a with
  | Lident string -> string 
  | Ldot (longident, string) ->
    (emit_id1 (longident)) ^ "." ^ string 
  | Lapply (longident,longident2)
    -> (emit_id1 (longident))  ^ "."
       ^ (emit_id1 (longident2) ) 

and emit_core_type_desc (x : core_type_desc * string_list):string =
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
      "Ptyp_tuple" ^ emit_core_type_list(a,  s )
    | other -> "FIXME"
        
and emit_type_decl ((x,s)) =
  "emit_type_decl"^
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
    "\nDEBUG2Erec: let process_type_decl_" ^  ptype_name.txt ^ " (x:" ^ ptype_name.txt
    ^ "):string = match x with {"
    ^ (emit_type_decl_kind (ptype_name.txt,ptype_kind,s,";"))
    ^ "} ->"
    ^ (emit_type_decl_kind_process (ptype_name.txt,ptype_kind,s,"^"))
and  emit_core_type(a: core_type * string_list):string=
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
    td (* ^ (string_of_int n) *)

and emit_core_type_list(x: core_type_list * string_list):string =
  match x with
  | (a,b) ->
    match a with
    | [] -> ""
    | h :: t ->
      let tt = emit_core_type_list(t,b)  in
      let h1 = emit_core_type (h,b) in
      if tt != "" then 
        h1 ^ "," ^ tt
      else 
        h1
and  emit_constructor_arguments(a1:(string*string*constructor_arguments*string_list)):string =  let (parent,name,x,s) = a1 in  match x with  | Pcstr_tuple a ->
    "| " ^ name ^ " ("^ (emit_core_type_list (a,s))  ^ ") -> " ^ "("
    ^ "process_types_" ^ parent ^ "__"^ name^  "(" ^ "imp_core_type_list (a,s,0)" ^"))"
  | other  -> "other"

and emit_type_variant_constructor_declaration_list(a:string*constructor_declaration list*string_list):string =
  match a with
  | (p,x,s)->
    match x with
    | [] -> "VARIANT2(" ^ p ^ "):"
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
            "DEBUG2EC: let process_"
            ^ p ^ "__" ^ pcd_name.txt
            ^ " x :string ="
            ^ "match x with "));
        let newtext = (emit_constructor_arguments(p,pcd_name.txt, pcd_args, s)) in
        let newtext2 = "(decl_emit_constructor_arguments(p,pcd_name.txt, pcd_args, s))" in
        (print_endline ("DEBUG2EB:" ^ newtext2));
        (print_endline ("DEBUG2EC:" ^ newtext)); 
        let ret =              "constructor:\""^ pcd_name.txt ^ "\""
                               ^ "{" ^
                               emit_constructor_arguments(p,pcd_name.txt,pcd_args,s)
                               ^ "}" ^ "\t|" ^
                               "process_type_variant_constructor_declaration_list(p,t,s)"
        in
        Printf.printf "DEBUG2E:constructor_declaration_new: %s\n" ret;
        ret
and emit_type_decl_kind((p,x,s,ss)) :string=
  "emit_type_decl_kind" ^
  match x with
  | Ptype_record a ->     
    emit_record_kind_field_list(p,a,s,ss)
  | Ptype_abstract -> "ABSTRACT"
  | Ptype_variant a -> (*  of constructor_declaration list *)
    "VARIANT2" ^ (emit_type_variant_constructor_declaration_list (p,a,s))                                          
  | Ptype_open  -> "OPEN"
and  emit_record_kind_field_list(p,x,s,ss) : string =
    match x with
  | [] -> ""
  | h :: t ->
    let one = (emit_record_kind_field (h, s)) in
    let tail1 = (emit_record_kind_field_list (p, t, s, ss)) in
    if tail1 != "" then
      one ^ ss ^ tail1
    else
      one                                            
and  emit_record_kind_field((x,s):label_declaration *string_list):string =
  match x with
    {
     pld_name(* : string loc *);
     pld_mutable(* : mutable_flag *);
     pld_type(* : core_type *);
     pld_loc(* : Location.t *);
     pld_attributes(* : attributes *); 
   } ->
    let pct = (emit_core_type (pld_type,s)) in
    pld_name.txt  ^ "(* " ^ pct ^ "*)"


and emit_type_decl_kind_process((p,x,s,ss)) :string=
  match x with
  | Ptype_record a ->     
    emit_record_kind_field_list_process(p,a,s,ss)
  | other -> "SKIP"
and  emit_record_kind_field_list_process(p,x,s,ss) : string =
    match x with
  | [] -> ""
  | h :: t ->
    let one = (emit_record_kind_field_process (h, s)) in
    let tail1 = (emit_record_kind_field_list_process (p, t, s, ss)) in
    if tail1 != "" then
      one ^ ss ^ tail1
    else
      one                                            
and  emit_record_kind_field_process((x,s):label_declaration *string_list):string =
  match x with
    {
     pld_name(* : string loc *);
     pld_mutable(* : mutable_flag *);
     pld_type(* : core_type *);
     pld_loc(* : Location.t *);
     pld_attributes(* : attributes *); 
   } ->
    let pct = (emit_core_type (pld_type,s)) in
    "(process_type_decl_" ^ pct ^ " " ^  pld_name.txt ^ ")"

and emit_core_type2(a: core_type * string_list*int):string=
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

and decl_emit_type_decl_kind_process((p,x,s,ss)) :string=
  match x with
  | Ptype_record a ->     
    decl_emit_record_kind_field_list_process(p,a,s,ss)
  | other -> "SKIP"
and  decl_emit_record_kind_field_list_process(p,x,s,ss) : string =
    match x with
  | [] -> ""
  | h :: t ->
    let one = (emit_record_kind_field_process (h, s)) in
    let tail1 = (emit_record_kind_field_list_process (p, t, s, ss)) in
    if tail1 != "" then
      one ^ ss ^ tail1
    else
      one                                            
and  decl_emit_record_kind_field_process((x,s):label_declaration *string_list):string =
  match x with
    {
     pld_name(* : string loc *);
     pld_mutable(* : mutable_flag *);
     pld_type(* : core_type *);
     pld_loc(* : Location.t *);
     pld_attributes(* : attributes *); 
   } ->
    let pct = (emit_core_type2 (pld_type,s,0)) in
    "(process_type_decl_" ^ pct ^ " " ^  pld_name.txt ^ ")"
