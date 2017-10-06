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

let (fresh_const_name, _) = gen_name "c" 
let fresh_const () = Ident.create @@  fresh_const_name ()

let (fresh_st_name, _) = gen_name "st" 
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
let mk_and conjs = match conjs with 
  | [] -> mk_true () | [c] -> c 
  | _ -> mk_and !ctx conjs
let mk_or conjs = mk_or !ctx conjs
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

let mk_new_set () = 
  let sv_name = fresh_sv_name () in
  let rec_sort = sort_of_typ @@ Type.Rec in
  let bool_sort = sort_of_typ @@ Type.Bool in
  let s_decl = mk_func_decl_s sv_name [rec_sort] bool_sort in
    s_decl

let mk_set_eq f1 f2 = expr_of_quantifier @@
  let rec_sort = sort_of_typ @@ Type.Rec in
  let bv_name = fresh_bv_name () in
  let bv_id = Ident.create bv_name in
  let bv_const = mk_const_s bv_name rec_sort in
  let _ = Hashtbl.add cmap bv_name bv_const in
  let body = (mk_app f1 [bv_const]) @<=> (mk_app f2 [bv_const]) in
  let _ = Hashtbl.remove cmap bv_name in
    mk_forall [bv_const] body

let declare_enum_type (SomeType ty) (consts: Ident.t list) =
  let mk_cstr e = 
    let name = Ident.name e in 
      mk_constructor_s name (sym @@ "is"^name) [] [] [] in
  let cstrs = List.map mk_cstr consts in
  let s_ty = mk_sort_s (Type.to_string ty) cstrs in
  let s_consts = List.map (fun f -> mk_app f []) @@
                      Datatype.get_constructors s_ty in
  begin
    Hashtbl.add tmap (SomeType ty) s_ty;
    List.iter (fun (c,s_c) -> 
                 Hashtbl.add cmap (Ident.name c) s_c)
      (List.zip consts s_consts);
    dprintf !_ddecls "%s added\n" (Type.to_string ty);
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
            -> (z3_expr list * z3_func) = function
  | Var (st,Type.St) -> 
    let s = mk_new_set () in
    let rec_sort = sort_of_typ @@ Type.Rec in
    let st_sort = sort_of_typ @@ Type.St in
    let bv_name = fresh_bv_name () in
    let bv_id = Ident.create bv_name in
    let bv_const = mk_const_s bv_name rec_sort in
    let st_const = mk_const_s (Ident.name st) st_sort in
    let in_func = fun_of_str @@ Ident.name L.is_in in
    let body = (mk_app s [bv_const]) 
               @<=> (mk_app in_func [st_const; bv_const]) in
    let cstr = expr_of_quantifier 
                @@ mk_forall [bv_const] body in
      ([cstr], s)
  | _ -> failwith "doIt_st_expr: Unexpected!"

let rec doIt_set_expr: set spec_expr 
              -> (z3_expr list * z3_func) = fun e -> 
  let rec_sort = sort_of_typ @@ Type.Rec in
  let _ =  dprintf !_dbv "~~ %s\n" @@ Speclang.Expr.to_string e in
  let bv () = 
    let bv_name = fresh_bv_name () in
    let bv_id = Ident.create bv_name in
    let bv_const = mk_const_s bv_name rec_sort in
      (bv_name, bv_id, bv_const) in
    match e with
    | Var (st,Type.St) -> doIt_st_expr e
    | SConst recs -> 
      let s = mk_new_set () in
      let (bv_name, bv_id, bv_const) = bv () in
      let r_consts = List.map doIt_expr recs in
      let disjs = List.map (mk_eq bv_const) r_consts in
      let body = (mk_app s [bv_const]) @<=> (mk_or disjs) in
      let cstr = expr_of_quantifier 
                  @@ mk_forall [bv_const] body in
        ([cstr], s)
    | SLit f ->
      let s = mk_new_set () in
      let (bv_name, bv_id, bv_const) = bv () in
      let _ = Hashtbl.add cmap bv_name bv_const in
      let _ =  dprintf !_dbv "SLit: added %s\n" bv_name in
      let phis = doIt_pred @@ f bv_id in
      let body = (mk_app s [bv_const]) @<=> mk_and phis in
      let _ = Hashtbl.remove cmap bv_name in
      let _ =  dprintf !_dbv "SLit: removed %s\n" bv_name in
      let cstr = expr_of_quantifier 
                  @@ mk_forall [bv_const] body in
        ([cstr], s)
    | SExists (ty, f) ->
      let c_name = match ty with 
                    | Type.St -> fresh_st_name () 
                    | _ -> fresh_const_name () in
      let _ =  dprintf !_dbv "SExists: new skolem const: %s" c_name in
      let _ = declare_const c_name ty in
      let (pred,set_expr) = f @@ Ident.create c_name in
      let cstrs_1 = doIt_pred pred in 
      let (cstrs_2, s) = doIt_set_expr set_expr in
        (cstrs_1 @ cstrs_2, s)
    | SBind (e1, f) -> 
      let s = mk_new_set () in
      let (e1_cstrs,s1) = doIt_set_expr e1 in
      let (a_name, a_id, a_const) = bv () in
      let (b_name, b_id, b_const) = bv () in
      let _ = Hashtbl.add cmap a_name a_const in
      let _ = Hashtbl.add cmap b_name b_const in
      let _ =  dprintf !_dbv "SBind: added %s\n" a_name in
      let _ =  dprintf !_dbv "SBind: added %s\n" b_name in
      let (phi, s2) = doIt_set_expr @@ f a_id in
      let _ = flush_all () in
      (* s = s1»=f ⇔ P1 ∧ P2, where... *)
      let bind_cstr1 =  
        (*P1: ∀b. b∈s ⇒ ∃a. a∈s1 ∧ s2=f(a) ∧ b∈s2 *)
        let ex_body = mk_and @@ List.concat @@
                        [[mk_app s1 [a_const]]; 
                         phi; [mk_app s2 [b_const]]] in
        let fa_body = (mk_app s [b_const]) 
                      @=> expr_of_quantifier
                          @@ mk_exists [a_const] ex_body in
          expr_of_quantifier 
                  @@ mk_forall [b_const] fa_body in
      let bind_cstr2 = 
        (*P1: ∀a.∀b. a∈s1 ∧ s2=f(a) ∧ b∈s2 ⇒ b∈s *)
        let ante = mk_and @@ List.concat @@
                      [[mk_app s1 [a_const]];
                       phi; [mk_app s2 [b_const]]] in
        let fa_body = ante @=> mk_app s [b_const] in
          expr_of_quantifier 
                @@ mk_forall [a_const; b_const] fa_body in
      let _ = Hashtbl.remove cmap a_name in
      let _ = Hashtbl.remove cmap b_name in
      let _ =  dprintf !_dbv "SBind: removed %s\n" a_name in
      let _ =  dprintf !_dbv "SBind: removed %s\n" b_name in
      let cstrs = e1_cstrs @ [bind_cstr1; bind_cstr2] in
        (cstrs, s)
    | SITE (p,e1,e2) -> 
      let s = mk_new_set () in
      let (e1_cstrs,s1) = doIt_set_expr e1 in
      let (e2_cstrs,s2) = doIt_set_expr e2 in
      let (bv_name, bv_id, bv_const) = bv () in
      let varphi = mk_and @@ doIt_pred p in
      let t_case = varphi @=> mk_app s1 [bv_const] in
      let f_case = (!@ varphi) @=> mk_app s2 [bv_const] in
      let body = mk_app s [bv_const] 
                 @<=> mk_and [t_case; f_case] in
      let cstr = expr_of_quantifier 
                  @@ mk_forall [bv_const] body in
        (e1_cstrs @ e2_cstrs @ [cstr], s)
    | SU (e1,e2) ->
      let s = mk_new_set () in
      let (e1_cstrs,s1) = doIt_set_expr e1 in
      let (e2_cstrs,s2) = doIt_set_expr e2 in
      let (bv_name, bv_id, bv_const) = bv () in
      let in_s1_or_s2 = mk_or [mk_app s1 [bv_const]; 
                               mk_app s2 [bv_const]] in
      let body = mk_app s [bv_const] @<=> in_s1_or_s2 in
      let cstr = expr_of_quantifier 
                  @@ mk_forall [bv_const] body in
        (e1_cstrs @ e2_cstrs @ [cstr], s)
    | _ -> failwith @@ "doIt_set_expr: Unexpected "
                       ^(Speclang.Expr.to_string e)


and doIt_pred (p:pred) : z3_expr list = 
  let _ =  dprintf !_dbv "-- %s\n" @@ P.to_string p in
  let f = doIt_pred in 
  let and_f p = mk_and @@ doIt_pred p in
  let g: type a. a spec_expr -> z3_expr = function
    | e -> doIt_expr e in
  let g_set = doIt_set_expr in
  let g_st = doIt_st_expr in
  let sorts_of_typ: type a. a Type.t -> z3_sort list = function
    | Type.Pair (t1,t2) -> [sort_of_typ t1; 
                            sort_of_typ t2]
    | Type.Triple (t1,t2,t3) -> [sort_of_typ t1; 
                                 sort_of_typ t2;
                                 sort_of_typ t3] 
    | typ -> [sort_of_typ typ] in
  let type_of = Speclang.Expr.type_of in
  let (@==) s1 s2 = mk_set_eq s1 s2 in
  let join_with: type a b c. (a -> b -> c) 
                  -> (c list*a) -> (c list*b) -> c list = 
      fun f (l1,a) (l2,b) -> l1 @ l2 @ [f a b] in
  let one x = [x] in
    match p with 
      | Expr e -> [g e]
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
      | Not v -> one @@ mk_not @@ and_f v
      | And vs -> List.concat @@ List.map f vs
      | Or vs -> one @@ mk_or @@ List.concat @@ List.map f vs
      | ITE (v1,v2,v3) -> one @@ mk_ite (and_f v1) 
                                  (and_f v2) (and_f v3)
      | If (t1,t2) -> one @@ (and_f t1) @=> (and_f t2)
      | Iff (t1,t2) -> one @@ (and_f t1) @<=> (and_f t2)
      | Forall (ty,body_fn) -> one @@ expr_of_quantifier @@
          let sorts = sorts_of_typ ty in
          let (bv_names,bv_ids,bv_consts) = List.split3 @@
            List.map (fun sort -> 
                        let bv_name = fresh_bv_name () in
                        let bv_id = Ident.create bv_name in
                        let bv_const = mk_const_s bv_name sort in
                          (bv_name,bv_id,bv_const)) sorts in
          let _ = List.iter2 (Hashtbl.add cmap) bv_names bv_consts in
          let body = and_f @@ body_fn bv_ids in
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
          let body = and_f @@ body_fn bv_ids in
          let _ = List.iter (Hashtbl.remove cmap) bv_names in
            mk_exists bv_consts body
      | SIn (e1,e2) -> 
          let v1 = g e1 in
          let (cstrs, s2) = match type_of e2 with
            | Type.Set -> g_set e2
            | Type.St -> g_st e2 in
            cstrs @ [mk_app s2 [v1]]
(*
let assert_const name = 
  let s_pred = Hashtbl.find cmap name in
  _assert s_pred
*)
let assert_phi phi = match phi with
  | P.And phis -> 
      _assert_all @@ List.concat 
          @@ List.map (fun phi -> 
                          let ps = doIt_pred phi in 
                          let print p = printf "%s\n" 
                                          @@ Z3.Expr.to_string p in
                          let _ = List.iter print ps in
                            (bv_reset(); ps)) phis
  | _ -> _assert_all @@ doIt_pred phi
(*
let assert_neg_const name = 
  let s_pred = Hashtbl.find cmap name in
  _assert (mk_not s_pred)
*)
let setup (ke,te,phi) =
  let out_chan = open_out "VC.z3" in
    begin
      declare_types ke;
      declare_vars te;
      assert_phi phi;
      Printf.printf "*****  CONTEXT ******\n";
      output_string out_chan @@ Solver.to_string !solver;
      output_string out_chan "(check-sat)\n";
      output_string out_chan "(get-model)\n";
      Printf.printf "\n*********************\n";
      flush_all ();
    end

type res = SAT | UNSAT | UNKNOWN
let check_validity (ke,te,phi) psi =
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
        UNSAT
      end
