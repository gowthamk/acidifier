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

type 'a spec_expr = 'a Speclang.Expr.t
type z3_expr = Z3.Expr.expr
type z3_sort = Z3.Sort.sort
type z3_func = func_decl
type z3_pred = (z3_expr list -> z3_expr)
type z3_set = (z3_expr list -> z3_expr -> z3_expr)
type z3_rel = z3_expr*z3_expr -> z3_expr

let unexpected () = failwith "Unexpected!" 
let dprintf = function 
  | true -> printf
  | false -> (Printf.ifprintf stdout)
(* Debug print flags *)
let _dbv = ref false;;
let _ddecls = ref false;;

let mk_new_ctx () = 
  let cfg = [("model", "true"); ("proof", "false")] in
    mk_context cfg

let ctx = ref @@ mk_new_ctx ()
let solver = ref @@ mk_solver !ctx None 
let (cmap : (string, z3_expr) Hashtbl.t) = Hashtbl.create 211
let (tmap : (some_type,z3_sort) Hashtbl.t) = Hashtbl.create 47
let (fmap : (string,FuncDecl.func_decl) Hashtbl.t) = Hashtbl.create 47

let (fresh_bv_name, bv_reset) = gen_name "bv" 
let fresh_bv () = Ident.create @@  fresh_bv_name ()

let (fresh_sv_name, _) = gen_name "S" 
let fresh_sv () = Ident.create @@  fresh_sv_name ()

let (fresh_rel_name, _) = gen_name "bR" 
let fresh_rel () = Ident.create @@  fresh_rel_name ()

let (fresh_const_name, _) = gen_name "c" 
let fresh_const () = Ident.create @@  fresh_const_name ()

let (fresh_st_name, st_reset) = gen_name "st" 
let fresh_st () = Ident.create @@  fresh_st_name ()

let reset () = 
  begin
    ctx := mk_new_ctx ();
    solver := mk_solver !ctx None;
    Hashtbl.clear cmap;
    Hashtbl.clear tmap;
    Hashtbl.clear fmap;
  end

let sort_of_typ typ = try Hashtbl.find tmap (SomeType typ) 
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
let mk_app f (args:z3_expr list) = mk_app !ctx f args
let mk_int_sort () = Int.mk_sort !ctx
let mk_bool_sort () = Bool.mk_sort !ctx
let mk_numeral_i i = Int.mk_numeral_i !ctx i
let mk_true () = mk_true !ctx
let mk_false () = mk_false !ctx
let mk_uninterpreted_s s = mk_uninterpreted_s !ctx s
let mk_const_s str sort = Expr.mk_const_s !ctx str sort
let mk_constructor_s a b c d e = mk_constructor_s !ctx a b c d e
let mk_sort_s a b = mk_sort_s !ctx a b
let mk_func_decl_s name arg_sorts res_sort = 
  mk_func_decl_s !ctx name arg_sorts res_sort
let mk_and conjs = 
  let non_trivial expr = not (is_true expr) in
  let conjs = List.filter non_trivial conjs |>
              fun nt_conjs ->
                List.fold_right 
                  (fun conj conjs' -> 
                    if (Boolean.is_and conj)
                    then (Expr.get_args conj)@conjs'
                    else conj::conjs') nt_conjs [] in
    match conjs with 
      | [] -> mk_true () | [c] -> c 
      | _ -> mk_and !ctx conjs
let mk_or disjs = match disjs with 
  | [] -> mk_false () | [c] -> c 
  | _ -> mk_or !ctx disjs
let mk_eq e1 e2 = mk_eq !ctx e1 e2
let mk_gt e1 e2 = mk_gt !ctx e1 e2
let mk_lt e1 e2 = mk_lt !ctx e1 e2
let mk_ge e1 e2 = mk_ge !ctx e1 e2
let mk_le e1 e2 = mk_le !ctx e1 e2
let mk_not e = mk_not !ctx e
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

let mk_forall consts body = 
    mk_forall_const !ctx consts body None [] [] None None

let mk_exists consts body = 
    mk_exists_const !ctx consts body None [] [] None None

(*
 * Easy way to create bound vars
 *)
type  bv_t = {id:Ident.t; const:z3_expr; name:string; }
let new_bv ?sort () = 
  let rec_sort () = sort_of_typ @@ Type.Rec in
  let s = match sort with | Some s -> s
                          | None -> rec_sort () in
  let bv_name = fresh_bv_name () in
  let bv_id = Ident.create bv_name in
  let bv_const = mk_const_s bv_name s in
    {name=bv_name; id=bv_id; const=bv_const}

let sort_check params psorts = 
  let psorts1 = List.map Expr.get_sort params in
    if List.length psorts1 = List.length psorts &&
       List.for_all2 Sort.equal psorts1 psorts 
    then ()
    else failwith "sort_check: Unexpected"

let mk_new_set name psorts : z3_set = 
  let rec_sort = sort_of_typ @@ Type.Rec in
  let bool_sort = sort_of_typ @@ Type.Bool in
  let arg_sorts = psorts@[rec_sort] in
  let s_decl = mk_func_decl_s name arg_sorts bool_sort in
    fun params x -> (sort_check params psorts; 
                     mk_app s_decl (params@[x]))

let mk_new_pred name psorts : z3_pred = 
  let bool_sort = sort_of_typ @@ Type.Bool in
  let p_decl = mk_func_decl_s name psorts bool_sort in
    fun params -> (sort_check params psorts;
                   mk_app p_decl params)

let mk_new_rel () : z3_rel = 
  let rel_name = fresh_rel_name () in
  let rec_sort = sort_of_typ @@ Type.Rec in
  let bool_sort = sort_of_typ @@ Type.Bool in
  let rel = mk_func_decl_s rel_name 
           [rec_sort; rec_sort] bool_sort in
  fun (x,y) ->  mk_app rel [x;y] 

let mk_set_eq fvs (s1:z3_set) (s2:z3_set) : z3_expr = 
  let rec_sort = sort_of_typ @@ Type.Rec in
  let bv = mk_const_s (fresh_bv_name ()) rec_sort in
  let body = (s1 fvs bv) @<=> (s2 fvs bv) in
    expr_of_quantifier @@ mk_forall [bv] body

let declare_enum_type (SomeType ty) (consts: Ident.t list) =
  let tyname = Type.to_string ty in
  let s = mk_uninterpreted_s tyname in
  let consts = List.map (Ident.name) consts in
  let tags = List.map (fun c -> 
                         mk_const_s c s) consts in
  let {const=a} = new_bv ~sort:s () in
  let s_univ_cstr = expr_of_quantifier @@ 
        mk_forall [a] @@ 
          mk_or (List.map (fun tag -> a @= tag) tags) in
  begin
    Hashtbl.add tmap (SomeType ty) s;
    List.iter2 (Hashtbl.add cmap) consts tags;
    _assert s_univ_cstr;
    dprintf !_ddecls "%s added\n" tyname;
    bv_reset ();
  end

let declare_variant_type (SomeType ty) (consts: Cons.t list) =
  let mk_cstr (Cons.T {name; recognizer}) = 
      mk_constructor_s name (sym recognizer) [] [] [] in
  let cstrs = List.map mk_cstr consts in
  let s_ty = mk_sort_s (Type.to_string ty) cstrs in
  let s_consts = List.map (fun f -> mk_app f []) @@
                      Datatype.get_constructors s_ty in
  begin
    Hashtbl.add tmap (SomeType ty) s_ty;
    List.iter (fun (Cons.T {name},s_c) -> 
                 Hashtbl.add cmap name s_c)
      (List.zip consts s_consts);
    dprintf !_ddecls "%s added\n" (Type.to_string ty);
  end

let declare_extendible_type (SomeType ty) (consts: Ident.t list) =
  let sort = mk_uninterpreted_s (Type.to_string ty) in
  let s_consts = List.map (fun c -> 
                         mk_const_s (Ident.name c) sort) consts in
  let distinct_asn = mk_distinct s_consts in
    begin
      Hashtbl.add tmap (SomeType ty) sort;
      List.iter (fun (c,s_c) -> 
                   Hashtbl.add cmap (Ident.name c) s_c)
        (List.zip consts s_consts);
      _assert distinct_asn;
      dprintf !_ddecls "%s added\n" (Type.to_string ty);
    end

let declare_types (ke) =
  begin
    Hashtbl.add tmap (SomeType Type.Int) (mk_int_sort ());
    Hashtbl.add tmap (SomeType Type.Bool) (mk_bool_sort ());
    Hashtbl.add tmap (SomeType Type.String) 
                              (mk_uninterpreted_s "Str");
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

let declare_const name typ = 
  let _ = printf "%s being added\n" name in
  let sort = sort_of_typ typ in
  let const_decl = mk_const_s name sort in
    Hashtbl.add cmap name const_decl

let declare_vars te = 
  let declare_fun: type a. string -> a Type.t -> unit = 
    fun name typ ->
      let f = sort_of_typ in
      let (arg_sorts,res_sort) = match typ with
        | Type.Arrow(Type.Pair (t11,t12),t2) -> 
              ([f t11; f t12], f t2)
        | Type.Arrow(Type.Triple (t11,t12,t13),t2) -> 
              ([f t11; f t12; f t13],f t2)
        | Type.Arrow (t1,t2) -> ([f t1], f t2)
        | _ -> failwith "Z3E.declare_vars: Impossible" in
      let func_decl = mk_func_decl_s name arg_sorts res_sort in
      let _ = dprintf !_ddecls "%s being added\n" name in
        Hashtbl.add fmap name func_decl in
    TE.iter (fun id (SomeType typ) -> let name = Ident.name id in 
               match typ with
                 | Type.Arrow _ -> declare_fun name typ
                 | Type.Unit -> ()
                 | _ -> declare_const name typ) te

(*
 * Encoding
 *)
let rec doIt_expr: type a. a spec_expr -> z3_expr = fun e -> 
  let open Ident in 
  let f (SomeExpr e) = doIt_expr e in 
    match e with 
    | Var (id,_) -> const_of_id id
    | App2 (id,svs,_) when (name id = "+") -> mk_add (List.map f svs)
    | App2 (id,svs,_) when (name id = "-") -> mk_sub (List.map f svs)
    | App2 (id,svs,_) when (name id = "*") -> mk_mul (List.map f svs)
    | App2 (id,[v1;v2],_) when (name id = "=") -> (f v1) @= (f v2)
    | App2 (id,[v1;v2],_) when (name id = "<") -> (f v1) @< (f v2)
    | App2 (id,[v1;v2],_) when (name id = "<=") -> (f v1) @<= (f v2)
    | App2 (id,[v1;v2],_) when (name id = ">") -> (f v1) @> (f v2)
    | App2 (id,[v1;v2],_) when (name id = ">=") -> (f v1) @>= (f v2)
    | App2 (id,svs,_) -> mk_app (fun_of_str @@ name id)
                        (List.map f svs) 
    | App (id,svs,_) -> mk_app (fun_of_str @@ name id)
                        (List.map doIt_expr svs)
    | Const(Type.Int,i) -> mk_numeral_i i
    | Const(Type.Bool,true) -> mk_true ()
    | Const(Type.Bool,false) -> mk_false ()
    | Const(Type.String,s) -> failwith "Z3E.doIt_expr: String Unimpl."
    | _ -> failwith "doIt_expr: Unexpected"

let rec doIt_st_expr: state spec_expr
            -> (z3_pred * z3_set)  = function
  | Var (st,Type.St) -> 
    let st_sort = sort_of_typ @@ Type.St in
    let st_const = mk_const_s (Ident.name st) st_sort in
    let in_func = fun_of_str @@ Ident.name L.is_in in
    let set = fun params x -> mk_app in_func [st_const; x] in
    let pred = fun params -> mk_true () in
      (pred, set)
  | _ -> failwith "doIt_st_expr: Unexpected!"

let rec doIt_set_expr: z3_expr list -> set spec_expr
              -> (z3_pred * z3_set) = 
  fun fvs e -> 
    let _ =  dprintf !_dbv "~~ %s\n" @@ Speclang.Expr.to_string e in
    let psorts = List.map Expr.get_sort fvs in
    let rec_sort = sort_of_typ @@ Type.Rec in
    let ret f = 
      let pred = (fun params -> mk_true ()) in
      let set = (fun params x -> f x) in
        (pred, set) in
    let doIt f = 
      let s_name = fresh_sv_name () in
      let phi_name = "phi_"^s_name in
      let s = mk_new_set s_name psorts in
      let phi_s = mk_new_pred phi_name psorts in
      (* returns a predicate that defines s *)
      let phi_def = f s in
      let asn = expr_of_quantifier @@ 
                  mk_forall fvs @@ (phi_s fvs) @<=> phi_def in
      let _ = _assert asn in
        (phi_s, s) in
    match e with
    | Var (st,Type.St) -> doIt_st_expr e
    | App (id,args,Type.Set) -> 
      let z3_id = fun_of_str @@ Ident.name id in
      let z3_args = List.map doIt_expr args in
        ret @@ fun x -> mk_app z3_id @@ z3_args@[x]
    | App2 (id,args,Type.Set) -> 
      let z3_id = fun_of_str @@ Ident.name id in
      let z3_args = List.map (fun (SomeExpr e) -> 
                                doIt_expr e) args in
        ret @@ fun x -> mk_app z3_id @@ z3_args@[x]
    | SConst recs -> 
      let r_consts = List.map doIt_expr recs in
      let set = fun x -> mk_or @@  
                      List.map (mk_eq x) r_consts in
        ret @@ set
    | SLit f -> doIt @@ fun s ->
      let bv = new_bv () in
      let _ = Hashtbl.add cmap bv.name bv.const in
      let _ =  dprintf !_dbv "SLit: added %s\n" bv.name in
      let fvs' = fvs@[bv.const] in
      let s_body = doIt_pred fvs' @@ f bv.id in
      let _ = Hashtbl.remove cmap bv.name in
      let _ =  dprintf !_dbv "SLit: removed %s\n" bv.name in
      let phi = expr_of_quantifier @@ 
                    mk_forall [bv.const] @@ 
                      (s fvs bv.const) @<=> s_body in
        phi
    | SExists (ty, f) -> doIt @@ fun s ->
      (* Note: Skolemizing is not safe because stability VCs
       * invoke same definitions twice *)
      let ex_bv = new_bv ~sort:(sort_of_typ ty) () in
      let _ = Hashtbl.add cmap ex_bv.name ex_bv.const in
      let _ =  dprintf !_dbv "SExists: added %s\n" ex_bv.name in
      let (pred,set_expr) = f ex_bv.id in
      let fvs' = fvs@[ex_bv.const] in
      let  cstr_s2 = doIt_pred fvs' pred in 
      let (phi_s2, s2) = doIt_set_expr fvs' set_expr in
      let _ = Hashtbl.remove cmap ex_bv.name in
      let _ =  dprintf !_dbv "SExists: removed %s\n" ex_bv.name in
      let fa_bv = new_bv () in
      let s_def = expr_of_quantifier @@ mk_forall [fa_bv.const] @@ 
                    (s fvs fa_bv.const) @<=> (s2 fvs' fa_bv.const) in
      let phi = expr_of_quantifier @@ 
                  mk_exists [ex_bv.const] @@ mk_and [cstr_s2; 
                                                     phi_s2 fvs'; 
                                                     s_def] in
        phi
    | SBind (e1, f) -> doIt @@ fun s ->
      let (phi_s1,s1) = doIt_set_expr fvs e1 in
      let bv = new_bv () in
      let _ = Hashtbl.add cmap bv.name bv.const in
      let _ =  dprintf !_dbv "SBind: added %s\n" bv.name in
      let e2 = f bv.id in
      let (phi_s2,s2) = doIt_set_expr (fvs@[bv.const]) e2 in
      let _ = Hashtbl.remove cmap bv.name in
      let _ =  dprintf !_dbv "SBind: removed %s\n" bv.name in
      (*
       * Set s2 is defined for each bv∈s1
       *)
      let phi_s2_cond = expr_of_quantifier @@ 
            mk_forall [bv.const] @@ 
              (s1 fvs bv.const) @=> (phi_s2 (fvs@[bv.const])) in
      let ({const=a},{const=b}) = (new_bv(), new_bv()) in
      (* s = s1»=(λx.s2) ⇔ P1 ∧ P2, where... *)
      let bind_eq1 = 
        (* P1: ∀a.∀b. a∈s1 ∧ b∈s2(a) ⇒ b∈s *)
        let ante = mk_and [s1 fvs a; 
                           s2 (fvs@[a]) b] in
        let eq1 = ante @=> s fvs b in
          expr_of_quantifier @@ mk_forall [a;b] eq1 in
      let bind_eq2 =  
        (* P2: ∀b. b∈s ⇒ ∃a. a∈s1 ∧ b∈s2(a) *)
        let conseq = expr_of_quantifier @@ 
              mk_exists [a] @@ mk_and [s1 fvs a;
                                       s2 (fvs@[a]) b] in
        let eq2 = (s fvs b) @=> conseq in
          expr_of_quantifier @@ mk_forall [b] eq2 in
      let phi = mk_and [phi_s1 fvs; 
                        phi_s2_cond; 
                        bind_eq1;
                        bind_eq2] in
        phi
    | SITE (p,e1,e2) -> doIt @@ fun s ->
      let varphi = doIt_pred fvs p in
      let (phi_s1,s1) = doIt_set_expr fvs e1 in
      let (phi_s2,s2) = doIt_set_expr fvs e2 in
      let s_eq_s1 = mk_set_eq fvs s s1 in
      let s_eq_s2 = mk_set_eq fvs s s2 in
      (* s1 is defined, and s=s1 on true branch *)
      let t_case = mk_and [phi_s1 fvs; s_eq_s1] in
      (* s2 is defined, and s=s2 on false branch *)
      let f_case = mk_and [phi_s2 fvs; s_eq_s2] in
      let phi = mk_ite varphi t_case f_case  in
        phi
    | SU (e1,e2) -> doIt @@ fun s ->
      let (phi_s1,s1) = doIt_set_expr fvs e1 in
      let (phi_s2,s2) = doIt_set_expr fvs e2 in
      (* Both s1 and s2 are defined, and s=s1 U s2*)
      let s1_u_s2 = fun params x -> mk_or [s1 params x; 
                                           s2 params x] in
      let s_eq_s1_u_s2 = mk_set_eq fvs s s1_u_s2 in
      let phi = mk_and [phi_s1 fvs; 
                        phi_s2 fvs; 
                        s_eq_s1_u_s2] in
        phi
    | _ -> failwith @@ "doIt_set_expr: Unexpected "
                       ^(Speclang.Expr.to_string e)


and doIt_pred (fvs: z3_expr list) (p:pred): z3_expr = 
  let _ =  dprintf !_dbv "-- %s\n" @@ P.to_string p in
  let fsorts = List.map Expr.get_sort fvs in
  let f p = doIt_pred fvs p in 
  let g e = doIt_expr e in
  let g_set = doIt_set_expr fvs in
  let g_st = doIt_st_expr in
  let sorts_of_typ: type a. a Type.t -> z3_sort list = function
    | Type.Pair (t1,t2) -> [sort_of_typ t1; 
                            sort_of_typ t2]
    | Type.Triple (t1,t2,t3) -> [sort_of_typ t1; 
                                 sort_of_typ t2;
                                 sort_of_typ t3] 
    | typ -> [sort_of_typ typ] in
  let type_of = Speclang.Expr.type_of in
  let (@==) s1 s2 = mk_set_eq fvs s1 s2 in
  let join_with: (z3_set -> z3_set -> z3_expr) -> 
                 (z3_pred * z3_set) -> 
                 (z3_pred * z3_set) -> z3_expr =
      fun f (phi_s1,s1) (phi_s2,s2) -> 
        mk_and [phi_s1 fvs; phi_s2 fvs; f s1 s2] in
  let one x = x in
  let st_sort = sort_of_typ @@ Type.St in
    match p with 
      | Expr e -> one @@ g e
      | Eq (v1,v2) -> (match type_of v1, type_of v2 with 
        | (Type.Set, Type.Set) ->  
              join_with (@==) (g_set v1) (g_set v2)
        | (Type.St, Type.Set) -> 
              join_with (@==) (g_st v1) (g_set v2)
        | (Type.Set, Type.St) -> 
              join_with (@==) (g_set v1) (g_st v2)
        | _ -> one @@ (g v1) @= (g v2))
      | LE (v1,v2) -> one @@ (g v1) @<= (g v2)
      | GE (v1,v2) -> one @@ (g v1) @>= (g v2)
      | Not v -> one @@ mk_not @@ f v
      | And vs -> one @@ mk_and (List.map f vs)
      | Or vs -> one @@ mk_or (List.map f vs)
      | ITE (v1,v2,v3) -> one @@ mk_ite (f v1) (f v2) (f v3)
      | If (t1,t2) -> one @@ (f t1) @=> (f t2)
      | Iff (t1,t2) -> one @@ (f t1) @<=> (f t2)
      | Forall (ty,body_fn) -> one @@ expr_of_quantifier @@
          let sorts = sorts_of_typ ty in
          let (bv_names,bv_ids,bv_consts) = List.split3 @@
            List.map (fun sort -> 
                        let bv_name = if sort = st_sort 
                                      then fresh_st_name () 
                                      else fresh_bv_name () in
                        let bv_id = Ident.create bv_name in
                        let bv_const = mk_const_s bv_name sort in
                          (bv_name,bv_id,bv_const)) sorts in
          let _ = List.iter2 (Hashtbl.add cmap) bv_names bv_consts in
          let body = doIt_pred (fvs@bv_consts) @@ body_fn bv_ids in
          let _ = List.iter (Hashtbl.remove cmap) bv_names in
            mk_forall bv_consts body
      | Exists (ty,body_fn) -> one @@ expr_of_quantifier @@
          let sorts = sorts_of_typ ty in
          let (bv_names,bv_ids,bv_consts) = List.split3 @@
            List.map (fun sort -> 
                        let bv_name = fresh_bv_name () in
                        let bv_id = Ident.create bv_name in
                        let bv_const = mk_const_s bv_name sort in
                          (bv_name,bv_id,bv_const)) sorts in
          let _ = List.iter2 (Hashtbl.add cmap) bv_names bv_consts in
          let body = doIt_pred (fvs@bv_consts) @@ body_fn bv_ids in
          let _ = List.iter (Hashtbl.remove cmap) bv_names in
            mk_exists bv_consts body
      | SIn (e1,e2) -> 
          let v1 = g e1 in
          let (phi_s2, s2) = match type_of e2 with
            | Type.Set -> g_set e2
            | Type.St -> g_st e2 in
            mk_and [phi_s2 fvs; s2 fvs v1]

let assert_phi phi = match phi with
  | P.And phis -> 
      _assert_all (*@@ List.concat *)
          @@ List.map (fun phi -> 
                        let ps = doIt_pred [] phi in 
                          (bv_reset(); st_reset(); ps)) phis
  | _ -> _assert @@ doIt_pred [] phi

let discharge psi = 
  let out_chan = open_out "VC.z3" in
    begin
      assert_phi @@ Not psi;
      output_string out_chan @@ Solver.to_string !solver;
      output_string out_chan "(check-sat)\n";
      output_string out_chan "(get-model)\n";
      printf "Context printed in VC.z3\n";
      flush_all ();
      check_sat ()
    end
(*
let assert_neg_const name = 
  let s_pred = Hashtbl.find cmap name in
  _assert (mk_not s_pred)
*)
let setup (ke,te,phi) =
  begin
    declare_types ke;
    declare_vars te;
    assert_phi phi;
  end

type res = SAT | UNSAT | UNKNOWN
let check_validity (ke,te,phi) psi =
  if not (Log.open_ "z3.log") then
    failwith "Log couldn't be opened."
  else
    let _ = setup (ke,te,phi) in
    let res = discharge psi in
    let _ = match res with 
        | SATISFIABLE -> printf "SAT\n"
        | UNSATISFIABLE -> printf "UNSAT\n"
        | UNKNOWN -> printf "UNKNOWN\n" in
      begin
        Printf.printf "Disposing...\n";
        reset ();
        Gc.full_major ();
        failwith "Unimpl.";
        UNSAT
      end
