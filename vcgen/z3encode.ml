open Utils
open Speclang
open Specelab
open Z3
open Z3.SMT
open Z3.Sort
open Z3.Expr
open Z3.Solver
open Z3.Symbol
open Z3.Datatype
open Z3.FuncDecl
open Z3.Boolean
open Z3.Arithmetic 
open Z3.Arithmetic.Integer
open Z3.Quantifier
module Solver = Z3.Solver
module Model = Z3.Model
module Symbol = Z3.Symbol
module Int = Z3.Arithmetic.Integer
module Bool = Z3.Boolean
module Quantifier = Z3.Quantifier
module Expr = Z3.Expr
module Constructor = Z3.Datatype.Constructor
module P = Speclang.Predicate

let mk_new_ctx () = 
  let cfg = [("model", "true"); ("proof", "false")] in
    mk_context cfg

let ctx = ref @@ mk_new_ctx ()
let solver = ref @@ mk_solver !ctx None 
let (cmap : (string,Expr.expr) Hashtbl.t) = Hashtbl.create 211
let (tmap : (Type.t,Sort.sort) Hashtbl.t) = Hashtbl.create 47
let (fmap : (string,FuncDecl.func_decl) Hashtbl.t) = Hashtbl.create 47

let fresh_bv_name = gen_name "bv" 
let fresh_bv () = Ident.create @@  fresh_bv_name ()

let reset () = 
  begin
    ctx := mk_new_ctx ();
    solver := mk_solver !ctx None;
    Hashtbl.clear cmap;
    Hashtbl.clear tmap;
    Hashtbl.clear fmap;
  end

let sort_of_typ typ = try Hashtbl.find tmap typ 
                      with Not_found ->
                        (printf "%s not found in tmap" 
                           (Type.to_string typ); raise Not_found)
let fun_of_str str = try Hashtbl.find fmap str
                      with Not_found ->
                        (printf "%s not found in fmap" str;
                         raise Not_found)
let const_of_name n = try Hashtbl.find cmap n 
                      with Not_found -> (printf "%s not found in cmap" n; 
                                         raise Not_found)
let const_of_id id = const_of_name @@ Ident.name id
(*
 * Z3 API for the current ctx
 *)
let sym s = Symbol.mk_string !ctx s
let mk_app f args = mk_app !ctx f args
let mk_int_sort () = Int.mk_sort !ctx
let mk_bool_sort () = Bool.mk_sort !ctx
let mk_numeral_i i = Int.mk_numeral_i !ctx i
let mk_uninterpreted_s s = mk_uninterpreted_s !ctx s
let mk_const_s str sort = Expr.mk_const_s !ctx str sort
let mk_constructor_s a b c d e = mk_constructor_s !ctx a b c d e
let mk_sort_s a b = mk_sort_s !ctx a b
let mk_func_decl_s name arg_sorts res_sort = 
  mk_func_decl_s !ctx name arg_sorts res_sort
let mk_and conjs = mk_and !ctx conjs
let mk_or conjs = mk_or !ctx conjs
let mk_eq e1 e2 = mk_eq !ctx e1 e2
let mk_gt e1 e2 = mk_gt !ctx e1 e2
let mk_lt e1 e2 = mk_lt !ctx e1 e2
let mk_ge e1 e2 = mk_ge !ctx e1 e2
let mk_le e1 e2 = mk_le !ctx e1 e2
let mk_not e = mk_not !ctx e
let mk_true () = mk_true !ctx
let mk_false () = mk_false !ctx
let mk_ite e1 e2 e3 = mk_ite !ctx e1 e2 e3
let mk_distinct es = mk_distinct !ctx es
let mk_add es = mk_add !ctx es
let mk_sub es = mk_sub !ctx es
let mk_mul es = mk_mul !ctx es
let _assert e = Solver.add !solver [e]
let _assert_all e = Solver.add !solver e
let check_sat () = Solver.check !solver []

let (@=>) e1 e2 = mk_implies !ctx e1 e2
let (@<=>) e1 e2 = mk_iff !ctx e1 e2
let (@&) e1 e2 = mk_and [e1; e2]
let (@|) e1 e2 = mk_or [e1; e2]
let (@=) e1 e2 = mk_eq e1 e2
let (@<) e1 e2 = mk_lt e1 e2
let (@>) e1 e2 = mk_gt e1 e2
let (@>=) e1 e2 = mk_ge e1 e2
let (@<=) e1 e2 = mk_le e1 e2
let (@!=) e1 e2 = mk_not (e1 @= e2)
let (!@) e = mk_not e

let forall sorts f = 
  let n = List.length sorts in
  let names = List.tabulate n 
                (fun i -> sym @@ "a"^(string_of_int i)) in
  let vars = List.tabulate n 
               (fun i -> mk_bound !ctx (n-i-1) 
                           (List.nth sorts i)) in
  let body = f vars in
    mk_forall !ctx sorts names body None [] [] None None

let exists sorts f = 
  let n = List.length sorts in
  let names = List.tabulate n 
                (fun i -> sym @@ "a"^(string_of_int i)) in
  let vars = List.tabulate n 
               (fun i -> mk_bound !ctx (n-i-1) 
                           (List.nth sorts i)) in
  let body = f vars in
    mk_exists !ctx sorts names body None [] [] None None

let declare_enum_type (ty:Type.t) (consts: Ident.t list) =
  let mk_cstr e = 
    let name = Ident.name e in 
      mk_constructor_s name (sym @@ "is"^name) [] [] [] in
  let cstrs = List.map mk_cstr consts in
  let s_ty = mk_sort_s (Type.to_string ty) cstrs in
  let s_consts = List.map (fun f -> mk_app f []) @@
                      Datatype.get_constructors s_ty in
  begin
    Hashtbl.add tmap ty s_ty;
    List.iter (fun (c,s_c) -> 
                 Hashtbl.add cmap (Ident.name c) s_c)
      (List.zip consts s_consts);
    printf "%s added\n" (Type.to_string ty);
  end

let declare_variant_type (ty:Type.t) (consts: Cons.t list) =
  let mk_cstr (Cons.T {name; recognizer}) = 
      mk_constructor_s name (sym recognizer) [] [] [] in
  let cstrs = List.map mk_cstr consts in
  let s_ty = mk_sort_s (Type.to_string ty) cstrs in
  let s_consts = List.map (fun f -> mk_app f []) @@
                      Datatype.get_constructors s_ty in
  begin
    Hashtbl.add tmap ty s_ty;
    List.iter (fun (Cons.T {name},s_c) -> 
                 Hashtbl.add cmap name s_c)
      (List.zip consts s_consts);
    printf "%s added\n" (Type.to_string ty);
  end

let declare_extendible_type (ty:Type.t) (consts: Ident.t list) =
  let sort = mk_uninterpreted_s (Type.to_string ty) in
  let s_consts = List.map (fun c -> 
                         mk_const_s (Ident.name c) sort) consts in
  let distinct_asn = mk_distinct s_consts in
    begin
      Hashtbl.add tmap ty sort;
      List.iter (fun (c,s_c) -> 
                   Hashtbl.add cmap (Ident.name c) s_c)
        (List.zip consts s_consts);
      _assert distinct_asn;
      printf "%s added\n" (Type.to_string ty);
    end

let declare_types (ke) =
  begin
    Hashtbl.add tmap Type.Int (mk_int_sort ());
    Hashtbl.add tmap Type.Bool (mk_bool_sort ());
    Hashtbl.add tmap Type.String (mk_uninterpreted_s "Str");
    KE.iter (fun tyid kind -> 
               let tyname () = Type._of @@ Ident.name tyid in
                 match kind with
                   | Kind.Variant consts -> 
                       declare_variant_type (tyname ()) consts
                   | Kind.Enum consts -> 
                       declare_enum_type (tyname ()) consts
                   | Kind.Extendible consts ->
                       declare_extendible_type (tyname ()) !consts
                   | Kind.Uninterpreted ->
                       Hashtbl.add tmap (tyname ()) 
                         (mk_uninterpreted_s @@ Ident.name tyid);
                   | _ -> ()) ke;
  end

let declare_vars te = 
  let declare_fun name typ = 
    let (arg_typs,res_typ) = match typ with
      | Type.Arrow(Type.Tuple t1s,t2) -> (t1s,t2)
      | Type.Arrow (t1,t2) -> ([t1],t2)
      | _ -> failwith "Z3E.declare_vars: Impossible" in
    let (arg_sorts,res_sort) = (List.map sort_of_typ arg_typs, 
                                sort_of_typ res_typ) in
    let func_decl = mk_func_decl_s name arg_sorts res_sort in
    let _ = printf "%s being added\n" name in
      Hashtbl.add fmap name func_decl in
  let declare_const name typ = 
    let sort = sort_of_typ typ in
    let const_decl = mk_const_s name sort in
      Hashtbl.add cmap name const_decl in
    TE.iter (fun id typ -> let name = Ident.name id in 
               match typ with
                 | Type.Arrow _ -> declare_fun name typ
                 | Type.Unit -> ()
                 | _ -> declare_const name typ) te

(*
 * Encoding
 *)
let rec doIt_expr e = 
  let open Speclang.Expr in 
  let f = doIt_expr in 
    match e with 
      | Var id -> const_of_id id
      | App (id,svs) when (Ident.name id = "+") -> mk_add (List.map f svs)
      | App (id,svs) when (Ident.name id = "-") -> mk_sub (List.map f svs)
      | App (id,svs) when (Ident.name id = "*") -> mk_mul (List.map f svs)
      | App (id,[v1;v2]) when (Ident.name id = "=") -> (f v1) @= (f v2)
      | App (id,[v1;v2]) when (Ident.name id = "<") -> (f v1) @< (f v2)
      | App (id,[v1;v2]) when (Ident.name id = "<=") -> (f v1) @<= (f v2)
      | App (id,[v1;v2]) when (Ident.name id = ">") -> (f v1) @> (f v2)
      | App (id,[v1;v2]) when (Ident.name id = ">=") -> (f v1) @>= (f v2)
      | App (id,svs) -> mk_app (fun_of_str @@ Ident.name id)
                          (List.map f svs) 
      | ConstInt i -> mk_numeral_i i
      | ConstBool true -> mk_true ()
      | ConstBool false -> mk_false ()
      | ConstString s -> failwith "VCE.doIt_expr: ConstString Unimpl."

let rec doIt_pred p = 
  let f = doIt_pred in 
  let g = doIt_expr in
    match p with 
      | P.BoolExpr e -> doIt_expr e
      | P.Eq (v1,v2) -> (g v1) @= (g v2)
      | P.LE (v1,v2) -> (g v1) @<= (g v2)
      | P.GE (v1,v2) -> (g v1) @>= (g v2)
      | P.Not v -> mk_not @@ f v
      | P.And vs -> mk_and @@ List.map f vs
      | P.Or vs -> mk_or @@ List.map f vs
      | P.ITE (v1,v2,v3) -> mk_ite (f v1) (f v2) (f v3)
      | P.If (t1,t2) -> (doIt_pred t1) @=> (doIt_pred t2)
      | P.Iff (t1,t2) -> (doIt_pred t1) @<=> (doIt_pred t2)
      | P.Forall (tys,f) -> expr_of_quantifier @@
          forall (List.map sort_of_typ tys)
            (fun es -> 
               let bvs = List.map (fun e -> fresh_bv ()) es in
               let _ = List.iter2
                         (fun bv e -> Hashtbl.add cmap (Ident.name bv) e) 
                         bvs es in
               let p = doIt_pred @@ f bvs in
               let _ = List.iter 
                         (fun bv -> Hashtbl.remove cmap (Ident.name bv)) bvs in
                 p)
      | P.Exists (tys,f) -> expr_of_quantifier @@
          exists (List.map sort_of_typ tys)
            (fun es -> 
               let bvs = List.map (fun e -> fresh_bv ()) es in
               let _ = List.iter2
                         (fun bv e -> Hashtbl.add cmap (Ident.name bv) e) 
                         bvs es in
               let p = doIt_pred @@ f bvs in
               let _ = List.iter 
                         (fun bv -> Hashtbl.remove cmap (Ident.name bv)) bvs in
                 p)

let declare_pred name p =
  let s_pred = mk_const_s name (sort_of_typ Type.Bool) in
  let e_pred = doIt_pred p in
    begin
      Hashtbl.add cmap name s_pred;
      _assert @@ s_pred @<=> e_pred 
    end

let assert_const name = 
  let s_pred = Hashtbl.find cmap name in
  _assert s_pred

let assert_prog phi = match phi with
  | P.And phis -> 
      _assert_all @@ List.map doIt_pred phis
  | _ -> _assert @@ doIt_pred phi

let assert_neg_const name = 
  let s_pred = Hashtbl.find cmap name in
  _assert (mk_not s_pred)

let setup (ke,te,phi) =
  begin
    declare_types ke;
    declare_vars te;
    assert_prog phi;
    Printf.printf "*****  CONTEXT ******\n";
    print_string @@ Solver.to_string !solver;
    print_string "(check-sat)\n";
    print_string "(get-model)\n";
    Printf.printf "\n*********************\n";
    flush_all ();
  end

let doIt (ke,te,phi) vcs = 
  if not (Log.open_ "z3.log") then
    failwith "Log couldn't be opened."
  else
    let _ = setup (ke,te,phi) in
    (*let res = discharge (List.hd vcs) in
    let _ =match res with 
        | SATISFIABLE -> printf "SAT\n"
        | UNSATISFIABLE -> 
            printf "%s verified!\n" 
              (Ident.name @@ fst @@ List.hd vcs)
        | UNKNOWN -> printf "UNKNOWN\n" in*)
    begin
      Printf.printf "Disposing...\n";
      reset ();
      Gc.full_major ();
      true
    end
