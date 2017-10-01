open Utils
open Types
open Typedtree
open Speclang

let rec uncurry_arrow = function 
  (Tarrow (_,typ_expr1,typ_expr2,_)) ->
    let (ty1,ty2) = (typ_expr1.desc, typ_expr2.desc) in 
      begin
        match ty2 with 
            Tarrow _ -> (fun (x,y) -> (ty1::x,y)) (uncurry_arrow ty2)
          | _ -> ([ty1],ty2)
      end
| Tlink typ_expr -> uncurry_arrow @@ typ_expr.desc
| _ -> failwith "uncurry_arrow called on non-arrow type"

let to_tye tyd = let open Types in
  {desc=tyd; level=0; id=0}

let rec extract_lambda ({c_lhs; c_rhs}) : (Ident.t list * expression)= 
  let open Asttypes in
  match (c_lhs.pat_desc, c_rhs.exp_desc) with
    | (Tpat_var (id,loc), Texp_function (_,[case],_)) -> 
        let (args,body) = extract_lambda case in
          (id::args,body)
    | (Tpat_var (id,loc), _) -> ([id], c_rhs)
    | (Tpat_alias (_,id,_), Texp_function (_,[case],_) ) -> 
        let (args,body) = extract_lambda case in
          (id::args,body)
    | (Tpat_alias (_,id,loc), _) -> ([id], c_rhs)
    | _ -> failwith "Unimpl. Specverify.extract_lambda"

let curry arg_tyds (res_tyd : Types.type_desc) =  
  let open Types in let open Asttypes in
  let f tyd = {desc=tyd; level=0; id=0} in
    List.fold_right (fun arg_tyd arr -> 
                       Tarrow (Nolabel, f arg_tyd, f arr, Cunknown))
      arg_tyds res_tyd 

let mk_tvar_name name_op id = match name_op with
  | Some a -> a^(string_of_int id)
  | None -> "tvar("^(string_of_int id)^")"

let rec unify_tyes binds tye1 tye2 = 
  let open Types in
  let (tyd1,tyd2) = (tye1.desc, tye2.desc) in
  let doIt_list = List.fold_left2 unify_tyes binds in
  let fail () = 
    let strf =Format.str_formatter  in
    begin
      Format.fprintf strf "Following types cannot be unified:\n";
      Printtyp.raw_type_expr strf tye1;
      Format.fprintf strf "\n";
      Printtyp.raw_type_expr strf tye2;
      Printf.printf "%s\n" @@ Format.flush_str_formatter ();
      failwith "Unification failure"
    end in
  let assrt b = if b then () else failwith "not unifiable" in
    match (tyd1,tyd2) with
      (* 
       * One of tye1 and tye2 is a concrete type, but we don't
       * know which one.
       *)
      | (Tvar aop, _) | (Tunivar aop, _) 
      | (_, Tvar aop) | (_, Tunivar aop) -> 
          let a = mk_tvar_name aop tye1.id in
            if List.mem_assoc a binds then binds 
            else (a,tye2)::binds
      | (Ttuple [tye1],_) -> unify_tyes binds tye1 tye2
      | (Tarrow (_,tye11,tye12,_), Tarrow (_,tye21,tye22,_)) ->
          unify_tyes (unify_tyes binds tye11 tye21) tye12 tye22
      | (Ttuple tyes1, Ttuple tyes2) -> 
          let _ = assrt (List.length tyes1 = List.length tyes2) in
            doIt_list tyes1 tyes2
      | (Tconstr (path1,tyes1,_), Tconstr (path2,tyes2,_)) ->
          let _ = assrt (Path.same path1 path2) in
            doIt_list tyes1 tyes2
      | (Tlink tye1,_) -> unify_tyes binds tye1 tye2
      | (_, Tlink tye2) -> unify_tyes binds tye1 tye2
      | (Tarrow _,_) | (_, Tarrow _) | (Ttuple _,_) | (_,Ttuple _)
      | (Tconstr _,_) | (_,Tconstr _) -> fail ()
      | _ -> failwith "unify_tyes: Unimpl."

let unify_tyes tye1 tye2 = 
  let tyebinds = unify_tyes [] tye1 tye2 in
  (*let strf = Format.str_formatter in
  let print_bind (a,tye) = 
    begin
      Format.fprintf strf "%s :-> " a;
      Printtyp.type_expr strf tye;
      Printf.printf "%s\n" @@ Format.flush_str_formatter ()
    end in
  let _ = List.iter print_bind tyebinds in*)
    tyebinds
