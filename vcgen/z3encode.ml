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
type z3_pred = z3_expr
(*
 * A type for bound variables.
 *)
type  bv_t = {id:Ident.t; const:z3_expr; name:string; }
type z3_set = (bv_t -> z3_expr)

let unexpected () = failwith "Unexpected!" 
let dprintf = function 
  | true -> printf
  | false -> (Printf.ifprintf stdout)
(* Debug print flags *)
let _dbv = ref false;;
let _ddecls = ref false;;

(*
 * z3 -smt2 smt.auto-config=false smt.mbqi=true
 * smt.macro-finder=true smt.random-seed=5
 * smt.pull_nested_quantifiers=true
 *)
let mk_new_ctx () = 
  let _ = Random.init 23 in
  let seed =  Random.int 100 in
  let cfg = [("auto-config","false")] in
    mk_context cfg

let mk_new_solver ctx = 
  let solver = mk_solver ctx None in
  let param_vals = [("mbqi",`Bool true); 
                    ("macro-finder",`Bool true); 
                    ("random-seed",`Int 5); 
                    ("pull_nested_quantifiers", `Bool true)] in
  let params = Params.mk_params ctx in
    begin
      List.iter (fun (name, value) -> 
                  let sym = Symbol.mk_string ctx name in
                    match value with
                    | `Bool b -> Params.add_bool params sym b
                    | `Int i -> Params.add_int params sym i) 
                param_vals;
      Solver.set_parameters solver params;
      solver
    end;;

(*
 * Z3 state
 *)
let ctx = ref @@ mk_new_ctx ()
let solver = ref @@ mk_new_solver !ctx
let (cmap : (string, z3_expr) Hashtbl.t) = Hashtbl.create 211
let (tmap : (some_type,z3_sort) Hashtbl.t) = Hashtbl.create 47
let (fmap : (string,FuncDecl.func_decl) Hashtbl.t) = Hashtbl.create 47
(*
 * Fresh name generators. Maintain an internal state.
 *)
let (fresh_bv_name, bv_reset) = gen_name "bv" 
let fresh_bv () = Ident.create @@  fresh_bv_name ()

let (fresh_sv_name, sv_reset) = gen_name "S" 
let fresh_sv () = Ident.create @@  fresh_sv_name ()

let (fresh_const_name, const_reset) = gen_name "c" 
let fresh_const () = Ident.create @@  fresh_const_name ()

let (fresh_vc_name,_) = gen_name "VC" 

let reset_state () = 
  begin
    ctx := mk_new_ctx ();
    solver := mk_new_solver !ctx;
    bv_reset ();
    sv_reset ();
    const_reset ();
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

let mk_new_pset name psorts : z3_expr list -> z3_set = 
  let rec_sort = sort_of_typ @@ Type.Rec in
  let bool_sort = sort_of_typ @@ Type.Bool in
  let arg_sorts = psorts@[rec_sort] in
  let s_decl = mk_func_decl_s name arg_sorts bool_sort in
    fun params x -> (sort_check params psorts; 
                     mk_app s_decl (params@[x.const]))

let mk_set_eq (s1:z3_set) (s2:z3_set) : z3_expr = 
  let bv = new_bv () in
  let a = s1 bv in
  let b = s2 bv in
  let body = a @<=> b in
  let expr = expr_of_quantifier @@ mk_forall [bv.const] body in
    expr

let declare_enum_type (SomeType ty) (consts: Ident.t list) =
  let tyname = Type.to_string ty in
  let s = mk_uninterpreted_s tyname in
  let consts = List.map (Ident.name) consts in
  let tags = List.map (fun c -> 
                         mk_const_s c s) consts in
  let {const=a} = new_bv ~sort:s () in
  let s_max_cstr = expr_of_quantifier @@ 
        mk_forall [a] @@ 
          mk_or (List.map (fun tag -> a @= tag) tags) in
  let s_min_cstr = mk_and @@ 
        List.map (fun (x,x') -> x @!= x') @@ 
          List.distinct_pairs tags in
  let s_univ_cstr = mk_and [s_min_cstr; s_max_cstr] in
  begin
    Hashtbl.replace tmap (SomeType ty) s;
    List.iter2 (Hashtbl.replace cmap) consts tags;
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
    Hashtbl.replace tmap (SomeType ty) s_ty;
    List.iter (fun (Cons.T {name},s_c) -> 
                 Hashtbl.replace cmap name s_c)
      (List.zip consts s_consts);
    dprintf !_ddecls "%s added\n" (Type.to_string ty);
  end

let declare_extendible_type (SomeType ty) (consts: Ident.t list) =
  let sort = mk_uninterpreted_s (Type.to_string ty) in
  let s_consts = List.map (fun c -> 
                         mk_const_s (Ident.name c) sort) consts in
  let distinct_asn = mk_distinct s_consts in
    begin
      Hashtbl.replace tmap (SomeType ty) sort;
      List.iter (fun (c,s_c) -> 
                   Hashtbl.replace cmap (Ident.name c) s_c)
        (List.zip consts s_consts);
      _assert distinct_asn;
      dprintf !_ddecls "%s added\n" (Type.to_string ty);
    end

let declare_types (ke) =
  begin
    Hashtbl.replace tmap (SomeType Type.Int) (mk_int_sort ());
    Hashtbl.replace tmap (SomeType Type.Bool) (mk_bool_sort ());
    Hashtbl.replace tmap (SomeType Type.String) 
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
                       Hashtbl.replace tmap (tyname ()) 
                         (mk_uninterpreted_s @@ Ident.name tyid);
                   | _ -> ()) ke;
  end

let declare_const name typ = 
  let sort = sort_of_typ typ in
  let const_decl = mk_const_s name sort in
    Hashtbl.replace cmap name const_decl

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
        Hashtbl.replace fmap name func_decl in
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

let rec doIt_st_expr: state spec_expr -> z3_set  = function
  | Var (st,Type.St) -> 
    let st_sort = sort_of_typ @@ Type.St in
    let st_const = mk_const_s (Ident.name st) st_sort in
    let in_func = fun_of_str @@ Ident.name L.is_in in
      fun bv -> mk_app in_func [st_const; bv.const]
  | _ -> failwith "doIt_st_expr: Unexpected!"

let rec doIt_set_expr: ?fvs:z3_expr list option -> set spec_expr 
							-> (z3_pred * z3_set) = fun ?fvs:(fvs=None) e -> 
  (*let _ =  dprintf !_dbv "~~ %s\n" @@ Speclang.Expr.to_string e in*)
  let ret f = (mk_true (), f) in
  let rec_sort = sort_of_typ @@ Type.Rec in
    match e with
    | Var (st,Type.St) -> ret @@ doIt_st_expr e
    | App (id,args,Type.Set) -> ret @@ fun bv ->
      let z3_id = fun_of_str @@ Ident.name id in
      let z3_args = List.map doIt_expr args in
        mk_app z3_id @@ z3_args@[bv.const]
    | App2 (id,args,Type.Set) -> ret @@ fun bv ->
      let z3_id = fun_of_str @@ Ident.name id in
      let z3_args = List.map (fun (SomeExpr e) -> 
                                doIt_expr e) args in
        mk_app z3_id @@ z3_args@[bv.const]
    | SConst recs -> ret @@ fun bv ->
      let consts = List.map doIt_expr recs in
        mk_or @@  List.map (mk_eq bv.const) consts
    | SLit f -> ret @@ fun bv ->
      let _ = Hashtbl.replace cmap bv.name bv.const in
      let _ = dprintf !_dbv "SLit: added %s :-> %s\n" bv.name 
                (Expr.to_string @@ const_of_name bv.name)in
      let s_body = doIt_pred ~fvs:fvs @@ f bv.id in
      let _ = Hashtbl.remove cmap bv.name in
      let _ = dprintf !_dbv "SLit: removed %s\n" bv.name in
        s_body
    | SExists (ty, f) -> 
      let ex_bv = new_bv ~sort:(sort_of_typ ty) () in
      let _ = Hashtbl.replace cmap ex_bv.name ex_bv.const in
      let _ =  dprintf !_dbv "SExists: added %s\n" ex_bv.name in
      let (pred,set_expr) = f ex_bv.id in
      let phi = doIt_pred ~fvs:fvs pred in 
      let (_,s) = doIt_set_expr ~fvs:fvs set_expr in
      let _ = Hashtbl.remove cmap ex_bv.name in
      let _ =  dprintf !_dbv "SExists: removed %s\n" ex_bv.name in
        ret @@ fun bv -> expr_of_quantifier @@ 
          mk_exists [ex_bv.const] @@ mk_and [phi; s bv]
    | SBind (e1, f) -> (match fvs with
      | None ->  ret @@ fun bv ->
        let (_,s1) = doIt_set_expr ~fvs:fvs e1 in
        let ex_bv = new_bv () in
        let _ = Hashtbl.replace cmap ex_bv.name ex_bv.const in
        let _ =  dprintf !_dbv "SBind: added %s :-> %s\n" 
                  ex_bv.name 
                  (Expr.to_string @@ const_of_name ex_bv.name) in
        let e2 = f ex_bv.id in
        let (_,s2) = doIt_set_expr ~fvs:fvs e2 in
        let pred = expr_of_quantifier @@
                      mk_exists [ex_bv.const] @@ 
                        mk_and [s1 ex_bv; s2 bv] in
        let _ = Hashtbl.remove cmap ex_bv.name in
        let _ =  dprintf !_dbv "SBind: removed %s\n" ex_bv.name in
          pred
      | Some fvs -> 
        let s_name = fresh_sv_name () in
        let psorts = List.map Expr.get_sort fvs in
        let s = mk_new_pset s_name psorts in
        let (p1,s1) = doIt_set_expr ~fvs:(Some fvs) e1 in
        let (a,b) = (new_bv(), new_bv()) in
        let _ = Hashtbl.add cmap a.name a.const in
        let _ = dprintf !_dbv "SBind: added %s\n" a.name in
        let e2 = f a.id in
        let (p2,s2) = doIt_set_expr ~fvs:(Some fvs) e2 in
        (* s = s1»=(λx.s2) ⇔ P1 ∧ P2, where... *)
        let bind_eq1 = 
          (* P1: ∀a.a∈s1 ⇒ ∃b. b∈s2(a) ∧ b∈s *)
          let ante = s1 a in
          let conseq = expr_of_quantifier @@ mk_exists [b.const] 
                        @@ mk_and [s2 b; s fvs b] in
          let eq1 = ante @=> conseq in
            expr_of_quantifier @@ mk_forall [a.const] eq1 in
        let bind_eq2 =  
          (* P2: ∀b. b∈s ⇒ ∃a. a∈s1 ∧ b∈s2(a) *)
          let ante = s fvs b in
          let conseq = expr_of_quantifier @@ 
                mk_exists [a.const] @@ mk_and [s1 a; s2 b] in
          let eq2 = ante @=> conseq in
            expr_of_quantifier @@ mk_forall [b.const] eq2 in
        let _ = Hashtbl.remove cmap a.name in
        let _ =  dprintf !_dbv "SBind: removed %s\n" a.name in
          (mk_and [p1; p2; bind_eq1; bind_eq2],
           fun bv -> s fvs bv)
        (*let phi = mk_and [bind_eq1; bind_eq2] in
        let asn = expr_of_quantifier @@ mk_forall fvs phi in
        let _ = _assert asn in
           s fvs bv*)  )
    | SITE (p,e1,SConst []) -> 
      let varphi = doIt_pred ~fvs:fvs p in
      let (p1,s1) = doIt_set_expr ~fvs:fvs e1 in
        (p1, fun bv -> mk_and [varphi; s1 bv])
    | SITE (p,SConst [],e2) -> 
      let varphi = doIt_pred ~fvs:fvs p in
      let (p2,s2) = doIt_set_expr ~fvs:fvs e2 in
        (p2, fun bv -> mk_and [mk_not varphi; s2 bv])
    | SITE (p,e1,e2) -> 
      let varphi = doIt_pred ~fvs:fvs p in
      let (p1,s1) = doIt_set_expr ~fvs:fvs e1 in
      let (p2,s2) = doIt_set_expr ~fvs:fvs e2 in
        (mk_and [p1;p2], fun bv -> mk_ite varphi (s1 bv) (s2 bv))
    | SU (e1,e2) -> 
      let (p1,s1) = doIt_set_expr ~fvs:fvs e1 in
      let (p2,s2) = doIt_set_expr ~fvs:fvs e2 in
        (mk_and [p1;p2], fun bv -> mk_or [s1 bv; s2 bv])
    | _ -> failwith @@ "doIt_set_expr: Unexpected "
                       ^(Speclang.Expr.to_string e)


and doIt_pred: ?fvs:z3_expr list option -> pred -> z3_expr = 
  fun ?fvs:(fvs=None) p ->
  (*let _ =  dprintf !_dbv "-- %s\n" @@ P.to_string p in*)
  let f p = doIt_pred ~fvs:fvs p in 
  let g e = doIt_expr e in
  let g_set (e:set spec_expr) = snd @@ doIt_set_expr e in
  let h_set = doIt_set_expr ~fvs:(match fvs with 
                                    | None -> Some [] 
                                    | _ -> fvs) in
  let g_st = doIt_st_expr in
  let sorts_of_typ: type a. a Type.t -> z3_sort list = 
    function
      | Type.Pair (t1,t2) -> [sort_of_typ t1; 
                              sort_of_typ t2]
      | Type.Triple (t1,t2,t3) -> [sort_of_typ t1; 
                                   sort_of_typ t2;
                                   sort_of_typ t3] 
      | typ -> [sort_of_typ typ] in
  let type_of = Speclang.Expr.type_of in
  let (@==) s1 s2 = mk_set_eq s1 s2 in
  let join_with f (p1,s1) (p2,s2) = mk_and [p1; p2; f s1 s2] in
  let (@+) l1op l2 = match l1op with
    | Some l1 -> Some (l1 @ l2)
    | None -> Some l2 in
  let st_sort = sort_of_typ @@ Type.St in
    match p with 
      | Expr e -> g e
      | Eq (v1,v2) -> (match type_of v1, type_of v2 with 
        | (Type.Set, Type.Set) ->  
              (g_set v1) @== (g_set v2)
        | (Type.St, Type.Set) -> 
            let s1 = g_st v1 in
            let (p2,s2) = h_set v2 in
              mk_and [p2; s1 @== s2] 
        | (Type.Set, Type.St) -> 
            let (p1,s1) = h_set v1 in
            let s2 = g_st v2 in
              mk_and [p1; s1 @== s2] 
        | (Type.St, Type.St) -> 
              (g_st v1) @== (g_st v2)
        | _ ->  (g v1) @= (g v2))
      | LE (v1,v2) -> (g v1) @<= (g v2)
      | GE (v1,v2) -> (g v1) @>= (g v2)
      | Not v -> mk_not @@ f v
      | And vs -> mk_and (List.map f vs)
      | Or vs -> mk_or (List.map f vs)
      | ITE (v1,v2,v3) -> mk_ite (f v1) (f v2) (f v3)
      | If (t1,t2) -> (f t1) @=> (f t2)
      | Iff (t1,t2) -> (f t1) @<=> (f t2)
      | Forall (ty,body_fn) -> expr_of_quantifier @@
          let sorts = sorts_of_typ ty in
          let (bv_names,bv_ids,bv_consts) = List.split3 @@
            List.map (fun sort -> 
                       let bv_name = fresh_bv_name () in
                       let bv_id = Ident.create bv_name in
                       let bv_const = mk_const_s bv_name sort in
                         (bv_name,bv_id,bv_const)) sorts in
          let _ = List.iter2 (Hashtbl.replace cmap) 
                    bv_names bv_consts in
          let body = doIt_pred ~fvs:(fvs@+bv_consts) @@ 
                        body_fn bv_ids in
          let _ = List.iter (Hashtbl.remove cmap) bv_names in
            mk_forall bv_consts body
      | Exists (ty,body_fn) -> expr_of_quantifier @@
          let sorts = sorts_of_typ ty in
          let (bv_names,bv_ids,bv_consts) = List.split3 @@
            List.map (fun sort -> 
                       let bv_name = fresh_bv_name () in
                       let bv_id = Ident.create bv_name in
                       let bv_const = mk_const_s bv_name sort in
                         (bv_name,bv_id,bv_const)) sorts in
          let _ = List.iter2 (Hashtbl.replace cmap) 
                      bv_names bv_consts in
          let body = doIt_pred ~fvs:(fvs@+bv_consts) @@ 
                      body_fn bv_ids in
          let _ = List.iter (Hashtbl.remove cmap) bv_names in
            mk_exists bv_consts body
      | SIn (Var (v_id,_) as e1,e2) -> 
          let v_const = g e1 in
          let s2 = match type_of e2 with
            | Type.Set -> g_set e2
            | Type.St -> g_st e2 in
            s2 {id=v_id; const=v_const; name=Ident.name v_id}
      | _ -> failwith "doIt_set_expr: Unimpl."

let assert_phi phi = match phi with
  | P.And phis -> 
      _assert_all (*@@ List.concat *)
          @@ List.map (fun phi -> 
                        let ps = doIt_pred phi in 
                        (bv_reset(); ps)) phis
  | _ -> _assert @@ doIt_pred phi

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

module Z3decode = struct

  let (tmodel : (some_type, z3_expr list) Hashtbl.t) = Hashtbl.create 47
  let (cmodel : (string, z3_expr) Hashtbl.t) = Hashtbl.create 47
  let (fmodel : (string, z3_expr list list) Hashtbl.t) = Hashtbl.create 47

  let univ_of_typ typ = try Hashtbl.find tmodel (SomeType typ) 
                        with Not_found ->
                          (printf "%s not found in tmodel" 
                             (Type.to_string typ); raise Not_found)
  let doIt_sorts ke model = 
  begin
    Hashtbl.replace tmodel (SomeType Type.Bool) [mk_true ();
                                             mk_false ()];
    KE.iter (fun tyid kind -> 
      let SomeType typ = Type._of @@ Ident.name tyid in
      let sort = sort_of_typ typ in
      let univ = Model.sort_universe model sort in 
        Hashtbl.replace tmodel (SomeType typ) univ) ke;
  end

  let doIt_funs te model = 
    TE.iter (fun fnid (SomeType (Type.Arrow (arg_typ,res_typ))) -> 
      let arg_univs = match arg_typ with
        | Type.Pair (t1,t2) -> [univ_of_typ t1; univ_of_typ t2]
        | Type.Triple (t1,t2,t3) -> [univ_of_typ t1; 
                                     univ_of_typ t2; 
                                     univ_of_typ t3]
        | t -> [univ_of_typ t] in
      let args_univ = List.cart_prod arg_univs in
      let fdecl = fun_of_str @@ Ident.name fnid in
      let fapps = List.map (mk_app fdecl) args_univ in
      let eval expr = from_just @@ 
                          Model.eval model expr true in
      let fres = List.map (fun fapp -> Z3enums.int_of_lbool @@ 
                            get_bool_value @@ eval fapp) fapps in
      begin
        printf "-------- Model for %s -----\n" (Ident.name fnid);
        List.iter2 (fun fapp res -> 
          let str1 = Expr.to_string fapp in
          let str2 = string_of_int res in
          printf "%s = %s\n" str1 str2) fapps fres;
      end) te

  let doIt (ke,te) model = 
    begin
      doIt_sorts ke model;
      printf "---------- Sort Universes --------\n";
      Hashtbl.iter (fun (SomeType ty) vals -> 
        let strs = List.map Expr.to_string vals in
        let univ_str = String.concat "," strs in
        let ty_str = Type.to_string ty in
          printf "%s :-> {%s}\n" ty_str univ_str) tmodel;
        (* doIt_funs te model;*)
    end
    
end

(* 
 * We assume phi is a quantified formula of form ∀x*.ψ1⇒ψ2, 
 * where ψ1 and ψ2 are drawn from Prop^0+SL. Since we are
 * interested in validity, we check satisfiability of ∃x*.ψ1∧¬ψ.
 * In the interest of human-readibile VCs, we Skolemize ∃x*, and
 * break ψ1∧¬ψ2 into two assertions.
 *)
type res = Z3.Solver.status = 
  | UNSATISFIABLE | UNKNOWN | SATISFIABLE 
let check_validity (ke,te,phi) psi debug =
  let _ = if not (Log.open_ "z3.log") then
          failwith "Log couldn't be opened." in
  let vc_name = fresh_vc_name () in
  let out_chan = open_out @@ vc_name^".z3" in
  let some t = SomeType t in
  let skolems = [(Ident.create "stl", some Type.St); 
                 (Ident.create "stgP", some Type.St); 
                 (Ident.create "stgQ", some Type.St)] in
  let te' = List.fold_left (fun te (id,t) -> 
                              TE.add id t te) te skolems in
  let impl = let open Type in match psi with 
    | P.Forall (Triple(St,St,St),f) -> f @@ List.map fst skolems
    | _ -> failwith "check_validity: Unimpl." in
  let phi' = let open P in match impl with 
    | If (p1,p2) -> (*if debug then Not p2 
                    else*) ?&& [phi; p1; Not p2]
    | _ -> failwith "check_validity: Unimpl." in
  let res = 
    begin
      setup (ke,te',phi');
      output_string out_chan @@ Solver.to_string !solver;
      output_string out_chan "(check-sat)\n";
      output_string out_chan "(get-model)\n";
      printf "Context printed in %s.z3\n" vc_name;
      flush_all ();
      check_sat ()
    end in
  let _ = match res with 
    | SATISFIABLE -> (printf "SAT\n";
        (*Z3decode.doIt (ke,te) 
            (from_just @@ Solver.get_model !solver)*))
    | UNSATISFIABLE -> printf "UNSAT\n"
    | UNKNOWN -> printf "UNKNOWN\n" in
    begin
      Printf.printf "Disposing...\n";
      reset_state ();
      Gc.full_major ();
      (* failwith "Unimpl.";*)
      res
    end
