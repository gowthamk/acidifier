val uncurry_arrow :                                                                       
	Types.type_desc -> Types.type_desc list * Types.type_desc                               
val to_tye : Types.type_desc -> Types.type_expr                                           
val extract_lambda : Typedtree.case -> Ident.t list * Typedtree.expression                
val curry : Types.type_desc list -> Types.type_desc -> Types.type_desc                    
val mk_tvar_name : string option -> int -> string                                         
val unify_tyes :
	Types.type_expr -> Types.type_expr -> (string * Types.type_expr) list
