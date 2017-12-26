open Utils
open Types
open Typedtree

let dprintf = function 
  | true -> printf
  | false -> (Printf.ifprintf stdout)
(* Debug print flags *)
let _dsubst = ref false;;

(* Types of the spec language *)
type id
type some
type set
type table
type date
type record
type state = set (* current both are the same *)

module Type = struct

  type _ t = 
    | Any: _ t 
    | Int: int t 
    | Bool: bool t 
    | String: string t 
    | Unit: unit t 
    | Id: id t 
    | Rec: record t
    | St: state t 
    | Set: set t 
    | Table: table t 
    | Date: date t
    | Arrow: 'a t* 'b t -> ('a -> 'b) t
    | List: 'a t -> 'a list t
    | Pair: 'a t * 'b t -> ('a * 'b) t
    | Triple: 'a t * 'b t * 'c t -> ('a * 'b * 'c) t
    | Option: 'a t -> 'a option t

  type some_type = SomeType: 'a t -> some_type

  let rec to_string: type a. a t -> string  = function 
    | Any -> "any" | Int -> "Int" | Bool -> "Bool" 
    | Id -> "Id" | String -> "Str" | Unit -> "Unit" 
    | Table -> "Table" | Date -> "Date"
    | Rec -> "Rec" | St -> "St" | Set -> "Set"
    | Arrow (t1,t2) -> (to_string t1)^" -> "^(to_string t2)
    | List t -> (to_string t)^" list"
    | Pair (t1,t2) -> "("^(to_string t1)^","^(to_string t2)^")"
    | Triple (t1,t2,t3) -> "("^(to_string t1)^","^(to_string t2)
                           ^","^(to_string t2)^")"
    | Option t -> (to_string t)^" option"

  let _of: string -> some_type  = function
    |"Id" -> SomeType Id | "Rec" -> SomeType Rec 
    | "St" -> SomeType St | "Set" -> SomeType Set 
    | "Str" -> SomeType String | "Unit" -> SomeType Unit
    | "Table" -> SomeType Table 
    | str -> failwith @@ "Type._of: Unexpected "^str^"\n"

  let assert_equal: type a b. a t -> b t -> unit = 
    fun t1 t2 -> () (* Unimpl. *)

end

type some_type = Type.some_type = SomeType: 'a Type.t -> some_type

module Cons = 
struct
  type t = T: {name: string; 
               recognizer: string; 
               args: (string * 'a Type.t) list} -> t
  let nop = T {name = "NOP";
               recognizer = "isNOP"; 
               args = []}
  let name (T {name}) = name
end

module Fun = 
struct
  type t = T of {name: Ident.t; 
                 rec_flag: bool;
                 args_t: (Ident.t * type_desc) list; 
                 res_t: type_desc;
                 body: expression}

  let name (T {name}) = name

  let anonymous loc = 
    let (file,ln,ch) = Location.get_pos_info loc in
    let name = "anon@"^file^"::"^(string_of_int ln)^"::"
        ^(string_of_int ch) in
      Ident.create name

  let make ~name ~rec_flag ~args_t ~res_t ~body = 
    T {name=name; rec_flag=rec_flag; args_t=args_t; 
       res_t=res_t; body=body}
end

module Kind = 
struct
 type t = Uninterpreted 
        | Variant of Cons.t list (* Cons.t includes a recognizer *)
        | Enum of Ident.t list
        | Extendible of Ident.t list ref
        | Alias: 'a Type.t -> t

  let to_string = function Uninterpreted -> "Uninterpreted type"
    | Variant cons_list -> 
        let cons_names = List.map 
                           (fun (Cons.T {name}) -> name) cons_list in
          "Variant ["^(String.concat "," cons_names)^"]"
    | Enum ids -> 
        let id_names = List.map
                         (fun id -> Ident.name id) ids in
          "Enum ["^(String.concat "," id_names)^"]"
    | Extendible ids -> 
        let id_names = List.map
                         (fun id -> Ident.name id) !ids in
          "Extendible ["^(String.concat "," id_names)^"]"
    | Alias typ -> "Alias of "^(Type.to_string typ)
end

module L = 
struct
  (*
   * General constants
   *)
  let plus = Ident.create "+"
  let minus = Ident.create "-"
  let ge = Ident.create ">="
  let gt = Ident.create ">"
  let le = Ident.create "<="
  let lt = Ident.create "<"
  let eq = Ident.create "="
  let nott = Ident.create "~"
  let andd = Ident.create "&&"
  let orr = Ident.create "||"
  (*
   * Constants of the spec language
   *)
  let id = Ident.create "id"
  let del = Ident.create "del"
  let txn = Ident.create "txn"
  let table = Ident.create "table"
  let is_in = Ident.create "in"
  let dom_eq = Ident.create "dom_eq"
  let empty_st = Ident.create "empty"
  let flush = Ident.create "flush"
  (* Field Accessors. Eg: s_id, c_name etc *)
  let (accessors: (string * Ident.t) list ref) = ref []
  let set_accessors (acc_idents:Ident.t list) : unit = 
    accessors := List.map (fun a -> (Ident.name a, a)) acc_idents
  let get_accessor = function
    | "id" -> id | "del" -> del | "txn" -> txn (* spl. accessors *)
    | str -> List.assoc str !accessors
  let get_accessors () = snd @@ List.split !accessors
  (* Invariants and Relations *)
  let _I = Ident.create "I"
  let _II = Ident.create "II"
  let _IIr = Ident.create "IIr"
  let _IIc = Ident.create "IIc"
  let _R = Ident.create "R"
  let _Rl = Ident.create "Rl"
  let _Rc = Ident.create "Rc"
  let _F = Ident.create "F"
  let _Fc = Ident.create "Fctxt"
end

type _ expr = 
            | Var: Ident.t * 'a Type.t -> 'a expr
            | App:  Ident.t * 'a expr list * 'b Type.t -> 'b expr
            | App2:  Ident.t * some_expr list * 'b Type.t -> 'b expr
            | Const: 'a Type.t * 'a -> 'a expr
            | SConst: record expr list ->  set expr
            | SLit: (Ident.t -> pred) -> set expr
            | SExists: 'a Type.t * (Ident.t -> pred * set expr) 
                          -> set expr (* exists(x,φ,s) *)
            | SBind: set expr * (Ident.t -> set expr) 
                          -> set expr (* s1 »= λx.s2 *)
            | SITE: pred * set expr * set expr 
                          -> set expr (* if φ then s1 else s2 *)
            | SU: set expr * set expr -> set expr (* s1 ∪ s2 *)

and some_expr = SomeExpr: 'a expr -> some_expr

and pred = 
          | Expr: bool expr -> pred
          | Eq: 'a expr * 'a expr -> pred
          | GE: int expr * int expr -> pred
          | LE: int expr * int expr -> pred
          | Not: pred -> pred
          | And: pred list -> pred
          | Or: pred list -> pred
          | ITE: pred * pred * pred -> pred
          | If: pred * pred -> pred
          | Iff: pred * pred -> pred
          | Forall: 'a Type.t * (Ident.t list -> pred) -> pred
          | Exists: 'a Type.t * (Ident.t list -> pred) -> pred
          | SIn of record expr * set expr

let (fresh_bv,bv_reset) = gen_name "bv"
let (fresh_stl,_) = gen_name "δ"
let (fresh_stg,_) = gen_name "Δ"

let rec expr_to_string: type a. a expr -> string = fun e -> 
  let to_string = expr_to_string in
  match e with
  | Var (id,ty) -> Ident.name id
  | App (id,svs,res_ty) -> (Ident.name id)^"("
      ^(String.concat "," @@ List.map to_string svs)^")"
  | App2 (id,some_exps,res_ty) -> (Ident.name id)^"("
      ^(String.concat "," @@ List.map 
          (fun (SomeExpr e) -> to_string e) some_exps)^")"
  | Const (Type.Int, i) -> string_of_int i
  | Const (Type.Bool, b) -> string_of_bool b
  | Const (Type.String,s) -> s
  | Const _ -> failwith "expr_to_string: Unimpl."
  | SConst recs -> "{"^(String.concat "," @@ 
                       List.map to_string recs)^"}"
  | SLit f -> 
    let bv = Ident.create @@ fresh_bv () in
      "{ "^(Ident.name bv)^":"^(Type.to_string Type.Rec)^" | "
        ^(pred_to_string @@ f bv)^" }"
  | SExists (ty,f) -> 
    let bv = Ident.create @@ fresh_bv () in
    let (phi,s) = f bv in 
      "∃("^(Ident.name bv)^":"^(Type.to_string ty)^" | "
        ^(pred_to_string phi)^"). "^(to_string s)
  | SBind (s1,f2) ->
    let s1str = to_string s1 in
    let tystr = "Rec" in
    let bv = Ident.create @@ fresh_bv () in
    let bvstr = Ident.name bv in
    let s2str = to_string @@ f2 bv in
      "("^s1str^") >>= (fun "^bvstr^":"^tystr^" -> "^s2str^")"
  | SITE (phi,s1,s2) -> (pred_to_string phi)^"? "^(to_string s1)
                       ^": "^(to_string s2)
  | SU (s1,s2) -> (to_string s1)^" U "^(to_string s2)

and pred_to_string x = 
  let f = pred_to_string in
  let g x = "("^(f x)^")" in
  let h = expr_to_string in
    match x with
    | Expr e -> h e
    | Eq (e1,e2) -> (h e1)^" = "^(h e2)
    | GE (e1,e2) -> (h e1)^" ≥ "^(h e2)
    | LE (e1,e2) -> (h e1)^" ≤ "^(h e2)
    | Not sv -> "~("^(f sv)^")"
    | And svs -> "("^(String.concat " && " @@ List.map f svs)^")"
    | Or svs -> "("^(String.concat " || " @@ List.map f svs)^")"
    | If (v1,v2) -> (f v1)^" => "^(f v2)
    | Iff (v1,v2) -> (f v1)^" <=> "^(f v2)
    | ITE (grd,sv1,sv2) -> (g grd)^"?"^(g sv1)^":"^(g sv2)
    | Forall (Type.Pair (ty1,ty2),phi) -> 
        let (bv1,bv2) = (Ident.create @@ fresh_bv (), 
                         Ident.create @@ fresh_bv ()) in
        let bvs = [Ident.name bv1; Ident.name bv2] in
        let tys = [Type.to_string ty1; Type.to_string ty2] in
        let bvtys = List.map (fun (bv,ty) -> bv^":"^ty) 
                      @@ List.zip bvs tys in
        "∀("^(String.concat "," bvtys)^"). " ^(f @@ phi[bv1;bv2])
    | Forall (Type.Triple (ty1,ty2,ty3),phi) -> 
        let (bv1,bv2,bv3) = (Ident.create @@ fresh_bv (), 
                             Ident.create @@ fresh_bv (), 
                             Ident.create @@ fresh_bv ()) in
        let bvs = [Ident.name bv1; Ident.name bv2; Ident.name bv3] in
        let tys = [Type.to_string ty1; Type.to_string ty2; 
                   Type.to_string ty3] in
        let bvtys = List.map (fun (bv,ty) -> bv^":"^ty) 
                      @@ List.zip bvs tys in
        "∀("^(String.concat "," bvtys)^"). " ^(f @@ phi[bv1;bv2;bv3])
    | Forall (ty,phi) -> 
        let bv = Ident.create @@ fresh_bv () in
        "∀("^(Ident.name bv)^":"^(Type.to_string ty)^"). " 
            ^(f @@ phi [bv])
    | Exists (Type.Pair (ty1,ty2),phi) -> 
        let (bv1,bv2) = (Ident.create @@ fresh_bv (), 
                         Ident.create @@ fresh_bv ()) in
        let bvs = [Ident.name bv1; Ident.name bv2] in
        let tys = [Type.to_string ty1; Type.to_string ty2] in
        let bvtys = List.map (fun (bv,ty) -> bv^":"^ty) 
                      @@ List.zip bvs tys in
        "∃("^(String.concat "," bvtys)^"). " ^(f @@ phi[bv1;bv2])
    | Exists (Type.Triple (ty1,ty2,ty3),phi) -> 
        let (bv1,bv2,bv3) = (Ident.create @@ fresh_bv (), 
                             Ident.create @@ fresh_bv (), 
                             Ident.create @@ fresh_bv ()) in
        let bvs = [Ident.name bv1; Ident.name bv2; Ident.name bv3] in
        let tys = [Type.to_string ty1; Type.to_string ty2; 
                   Type.to_string ty3] in
        let bvtys = List.map (fun (bv,ty) -> bv^":"^ty) 
                      @@ List.zip bvs tys in
        "∃("^(String.concat "," bvtys)^"). " ^(f @@ phi[bv1;bv2;bv3])
    | Exists (ty,phi) -> 
        let bv = Ident.create @@ fresh_bv () in
        "∃("^(Ident.name bv)^":"^(Type.to_string ty)^"). " 
            ^(f @@ phi [bv])
    | SIn (e1,s2) -> (h e1)^" ∈ "^(h s2)

let rec type_cast: type a b. a expr -> b Type.t -> b expr = 
  fun e ty' -> match e,ty' with
    | SConst _, Type.Set -> e
    | SLit _, Type.Set -> e
    | SExists (_,_), Type.Set -> e
    | SBind (_,_), Type.Set -> e
    | SITE (_,_,_), Type.Set -> e 
    | SU (_,_), Type.Set -> e
    | Var (v,ty), _ -> (Type.assert_equal ty ty'; Var (v,ty'))
    | App (f,args,ty), _ -> (Type.assert_equal ty ty'; 
                             App (f,args,ty')) 
    | App2 (f,sargs,ty), _ -> (Type.assert_equal ty ty'; 
                               App2 (f,sargs,ty')) 
    | Const (Type.Int, c), Type.Int -> e
    | Const (Type.Bool, c), Type.Bool -> e
    | Const (Type.String, c), Type.String -> e
    | _, _ -> failwith "Speclang.type_cast: Error!"

let rec expr_subst: type a b.  a expr * Ident.t -> b expr -> b expr = 
  fun (e',x) e ->  
    let g = pred_subst (e',x) in
    let _ = (dprintf !_dsubst) "[%s/%s] %s\n" (expr_to_string e') 
              (Ident.name x) (expr_to_string e) in
      match e with
      | Var (v,ty) -> if Ident.equal v x 
                      then type_cast e' ty else e
      | App (v,exps,res_ty) -> 
        let exps' = List.map (fun exp -> 
                                expr_subst (e',x) exp) exps in
        let (e'': b expr) = match (e', Ident.equal v x) with 
          | (Var (v',_), true) -> App (v', exps', res_ty) 
          | _ -> App (v, exps', res_ty) in
          e''
      | App2 (v,some_exps,res_ty) -> 
        let some_exps' = List.map (fun (SomeExpr exp) -> 
                      SomeExpr (expr_subst (e',x) exp)) some_exps in
        let (e'': b expr) = match (e', Ident.equal v x) with 
          | (Var (v',_), true) -> App2 (v', some_exps', res_ty) 
          | _ -> App2 (v, some_exps', res_ty) in
          e''
      | SConst exps -> 
          SConst (List.map (fun exp -> 
                              expr_subst (e',x) exp) exps)
      | SLit phi -> SLit (fun v -> g (phi v))
      | SBind (s,bind_f) -> 
          SBind (expr_subst (e',x) s, 
                 fun v -> expr_subst (e',x) @@ bind_f v)
      | SExists (ty,body_f) -> 
          SExists(ty, fun v -> 
                        let (p,s) = body_f v in 
                          (g p, expr_subst (e',x) s))
      | SITE (p,s1,s2) -> SITE (g p, expr_subst (e',x) s1, 
                                     expr_subst (e',x) s2)
      | SU (s1,s2) -> SU (expr_subst (e',x) s1, 
                          expr_subst (e',x) s2)
      | _ -> e

and pred_subst: type a. a expr * Ident.t -> pred -> pred = 
  fun (e,x) p -> 
    let f = pred_subst (e,x) in 
    let _ = dprintf !_dsubst "[%s/%s] %s\n" (expr_to_string e) 
              (Ident.name x) (pred_to_string p) in
      match p with
      | Expr exp -> Expr (expr_subst (e,x) exp)
      | And ps -> And (List.map f ps)
      | Or ps -> Or (List.map f ps)
      | Not p -> Not (f p)
      | Eq (e1,e2) -> Eq (expr_subst (e,x) e1, expr_subst (e,x) e2)
      | GE (e1,e2) -> GE (expr_subst (e,x) e1, expr_subst (e,x) e2)
      | LE (e1,e2) -> LE (expr_subst (e,x) e1, expr_subst (e,x) e2)
      | ITE (p1,p2,p3) -> ITE (f p1, f p2, f p3)
      | If (p1,p2) -> If (f p1, f p2)
      | Iff (p1,p2) -> Iff (f p1, f p2)
      | Exists (tys,phi) -> Exists (tys, fun v -> f (phi v))
      | Forall (tys,phi) -> Forall (tys, fun v -> f (phi v))
      | SIn (e1,s2) -> SIn (expr_subst (e,x) e1, expr_subst (e,x) s2)

module Expr = 
struct
  type 'b t = 'b expr = 
           | Var: Ident.t * 'b Type.t -> 'b t
           | App:  Ident.t * 'a expr list * 'b Type.t -> 'b t
           | App2:  Ident.t * some_expr list * 'b Type.t -> 'b t
           | Const: 'b Type.t * 'b -> 'b t
           | SConst: record expr list ->  set t
           | SLit: (Ident.t -> pred) -> set t
           | SExists: 'a Type.t * (Ident.t -> pred * set expr) 
                         -> set t (* exists(x,φ,s) *)
           | SBind: set t * (Ident.t -> set t) 
                         -> set t (* s1 »= λx.s2 *)
           | SITE: pred * set expr * set expr 
                         -> set t (* if φ then s1 else s2 *)
           | SU: set expr * set expr -> set t (* s1 ∪ s2 *)

  let to_string = expr_to_string

  let subst = expr_subst

  (* Without the type annotation, the type inferred for 
   * this function is:
   *    set expr -> set Type.t 
   * Why couldn't ocamlc infer the most general type?
   * *)
  let type_of: type a. a expr -> a Type.t = function
    | Var (_,ty) -> ty
    | App (_,_,ty) -> ty
    | App2 (_,_,ty) -> ty
    | Const (ty,_) -> ty
    | SConst _ -> Type.Set
    | SLit _ -> Type.Set
    | SExists _ -> Type.Set
    | SBind _ -> Type.Set
    | SITE _ -> Type.Set
    | SU _ -> Type.Set

  let type_cast = type_cast

  (* let (??) x = Expr.Var x *)
  (*let (???) x = SVar x*)
  let (!!) c = Const(Type.Int,c)
  let (!!!) recs = SConst recs
  let (@>>=) s f = SBind (s,fun x -> f @@ Var(x,Type.Rec))
  let (@<+>) s1 s2 = match s1,s2 with
    | SConst [], _ -> s2
    | _, SConst [] -> s1
    | _,_ -> SU (s1,s2)
  (* The only set literals are those of records. *)
  let _SConst rs = SConst rs
  let _SLit f = SLit (fun x -> f @@ Var(x,Type.Rec))
  let _SExists ty f = SExists (ty, fun x -> f @@ Var (x,ty))
  let _SBind s f = SBind (s, fun x -> f @@ Var(x,Type.Rec))
  let _SITE a b c = SITE(a,b,c)
  let table_name s = Var (Ident.create s, Type.Table)
  let record (x) = Var (x,Type.Rec) 
  let var (x,ty) = Var (x,ty)
  let state_var x = Var (x,Type.St)
  let (@+) x y = App2 (L.plus, [SomeExpr x; SomeExpr y], Type.Int)
  let (@-) x y = App2 (L.minus, [SomeExpr x; SomeExpr y], Type.Int)
                   
end


module Predicate = 
struct
  (* Reexporting the pred variant type as Predicate.t *)
  type t = pred = 
         | Expr: bool expr-> t
         | Eq: 'a expr * 'a expr-> t
         | GE: int expr * int expr-> t
         | LE: int expr * int expr-> t
         | Not: pred-> t
         | And: pred list-> t
         | Or: pred list-> t
         | ITE: pred * pred * pred-> t
         | If: pred * pred-> t
         | Iff: pred * pred-> t
         | Forall: 'a Type.t * (Ident.t list -> pred)-> t
         | Exists: 'a Type.t * (Ident.t list -> pred)-> t
         | SIn of record expr * set expr

  let to_string = pred_to_string

  let print_all = List.iter (fun p -> 
    begin
      printf "%s\n" @@ to_string p;
      bv_reset ();
    end)

  let subst = pred_subst

  let conj p1 p2 = match (p1,p2) with
    | (And xs, And ys) -> And (xs@ys)
    | (And xs,_) -> And (xs@[p2])
    | (_,And ys) -> And (p1::ys)
    | _ -> And [p1;p2]
  let disj p1 p2 = match (p1,p2) with
    | (Or xs, Or ys) -> Or (xs@ys)
    | (Or xs,_) -> Or (xs@[p2])
    | (_,Or ys) -> Or (p1::ys)
    | _ -> Or [p1;p2]
  let truee = Expr (Const(Type.Bool,true))
  let falsee = Expr (Const(Type.Bool,false))
  let (@:) r s = SIn (r,s)(*r∈s*)
  let (?&&) xs = And (List.concat @@ 
    List.map (function | And ys -> ys
                       | y -> [y]) xs)
  let (?||) xs = Or xs
  let (@&&) x y = conj x y
  let (@||) x y = disj x y
  let (@==) x y = Eq (x,y)
  let (@!=) x y = Not (Eq (x,y))
  let (@>=) x y = GE (x,y)
  let (@=>) x y = If (x,y)
  let (@<=>) x y = Iff (x,y)
(*
  let empty_st x = Expr (Expr.App (L.empty_st,[x]))
  let flush (stl,stg,st) = Expr (Expr.App (L.flush, [stl;stg;st]))
  let dom_eq (st1,st2) = Expr (Expr.App (L.dom_eq,[st1;st2]))
*)
  let b_app (bf,args) = Expr(Expr.App (bf,args,Type.Bool))
  let table (x) = Expr.App (L.table, [x], Type.Table) 
  let id (x) = Expr.App (L.id,[x], Type.Id)
  let del (x) = Expr (Expr.App (L.del, [x], Type.Bool))
(*
  let txn (x) = Expr.App (L.txn,[x])
  let empty_st x = Expr (Expr.App (L.empty_st,[x]))
*)
  let is_in_dom (i,st) = 
    Exists (Type.Rec, fun [r] -> ?&& [Var(r,Type.Rec) @: st;
                                      id(Var(r,Type.Rec)) @== i])
  let is_not_in_dom (i,st) = 
    Forall (Type.Rec, fun [r] -> (Var(r,Type.Rec) @: st) @=>
                                      id(Var(r,Type.Rec)) @!= i)
  let _I (st) = b_app(L._I,[st])
  let _R (st,st') = b_app(L._R,[st;st'])
  let _Rl (stl,stg,stg') = b_app(L._Rl,[stl;stg;stg'])
  let _Rc (stl,stg,stg') = b_app(L._Rc,[stl;stg;stg'])
  let _IIr (stl,stg,stg') = b_app(L._IIr,[stl;stg;stg'])
  let _IIc (stl,stg,stg') = b_app(L._IIc,[stl;stg;stg'])
  let _F: state expr -> set expr =
    fun (stg) -> App (L._F,[stg],Type.Set)
  let _Fc: state expr -> set expr =
    fun (stg) -> App (L._Fc,[stg],Type.Set)

  let _Forall_St1 f = 
    Forall (Type.St, 
            fun l -> match l with 
              | [st] -> f @@ Var(st,Type.St)
              | _ -> failwith "_Forall_St1: Unexpected")
  let _Forall_St2 f = 
    Forall (Type.Pair (Type.St, Type.St), 
            fun l -> match l with 
              | [stg;stg'] -> f(Var(stg,Type.St),
                                Var(stg',Type.St))
              | _ -> failwith "_Forall_St2: Unexpected")
  let _Forall_St3 f = 
    Forall (Type.Triple (Type.St, Type.St, Type.St), 
            fun l -> match l with 
              | [stl;stg;stg'] -> f(Var(stl,Type.St),
                                    Var(stg,Type.St),
                                    Var(stg',Type.St))
              | _ -> failwith "_Forall_St3: Unexpected")
(*
  let _Forall_St4 f = 
    Forall ([Type.St; Type.St; Type.St; Type.St], 
            fun l -> match l with 
              | [st0;st1;st2;st3] -> f(st0,st1,st2,st3) 
              | _ -> failwith "_Forall_St4: Unexpected")
*)
  let _Forall_Rec1 (f: record expr -> pred) = 
    Forall (Type.Rec, 
            fun l -> match l with 
              | [r] -> f @@ Expr.Var(r,Type.Rec)
              | _ -> failwith "_Forall_Rec1: Unexpected")
  let _Forall_Rec2 (f: record expr * record expr -> pred) = 
    Forall (Type.Pair (Type.Rec, Type.Rec), 
            fun l -> match l with 
              | [r1;r2] -> f (Expr.Var(r1,Type.Rec),
                              Expr.Var(r2,Type.Rec))
              | _ -> failwith "_Forall_Rec2: Unexpected")
  let _Forall_St1_Rec1 f = 
    Forall (Type.Pair (Type.St, Type.Rec), 
            function [st;r] -> f (Var (st,Type.St), 
                                  Var(r,Type.Rec))
              | _ -> failwith "_Forall_St1_Rec1: Unexpected")

  let _Forall_St1_Rec2 f = 
    Forall (Type.Triple (Type.St, Type.Rec, Type.Rec), 
            function [st;r1;r2] -> f (Var (st,Type.St), 
                                      Var (r1,Type.Rec), 
                                      Var (r2,Type.Rec))
              | _ -> failwith "_Forall_St1_Rec2: Unexpected")
(*
  let _Forall_St3_Rec1 f = 
    Forall ([Type.St; Type.St; Type.St; Type.Rec], 
            fun l -> match l with 
              | [stl;stg;stg';r] -> f(stl,stg,stg',r) 
              | _ -> failwith "_Forall_St3_Rec1: Unexpected")
*)
  let _Exists_Id1 f = 
    Exists (Type.Id, 
            function [i] -> f (Expr.Var(i,Type.Id))
                   | _ -> failwith "_Exists_Id1: Unexpected")
  let _Exists_St1 f = 
    Exists (Type.St, 
            function [st] -> f (Expr.Var(st,Type.St))
                   | _ -> failwith "_Exists_St1: Unexpected")

  let _Exists_Rec1 f = 
    Exists (Type.Rec, 
            function [r] -> f (Expr.Var(r,Type.Rec))
                   | _ -> failwith "_Exists_Rec1: Unexpected")

  let _Exists2: type a b. (a Type.t * b Type.t) -> 
                          (a expr * b expr -> pred) -> pred = 
    fun (a,b) f -> 
      Exists(Type.Pair (a,b), 
             function [x;y] -> f (Expr.Var (x,a), Expr.Var (y,b)) 
                    | _ -> failwith "_Exists2: Unexpected")

end

module Isolation = 
struct
  type t = RC | RR | SI | SER 

  open Predicate

  (*
   * Common isolation guarantees.
   *)
  (* No isolation *)
  let _II0 _ = truee 
  (* No write-write conflicts: 
       ∀(r′ ∈ δ)(r ∈ ∆). r.id = r′.id ⇒ r ∈ ∆′ *)
  let _IIww (stl,stg,stg') = _Forall_Rec2 @@
    fun (r,r') -> ?&& [r' @: stl; 
                       r @: stg;
                       id(r) @== id(r')]
                  @=> (r @: stg')
  (* Snapshot isolation: ∆′ =∆ *)
  let _IIss (stl,stg,stg') = stg' @== stg

  (*
   * Machine/store-specific basic isolation common to all levels.
   *)
  let _IIm  = _IIww

  let spec_of = 
    let ret (spec_r,spec_c) = 
          ?&& [(_Forall_St3 @@ fun (stl,stg,stg') -> 
                  _IIr(stl,stg,stg') 
                         @<=> ?&& [_IIm(stl,stg,stg'); 
                                   spec_r(stl,stg,stg')]); 
               (_Forall_St3 @@ fun (stl,stg,stg') -> 
                  _IIc(stl,stg,stg') 
                         @<=> ?&& [_IIm(stl,stg,stg'); 
                                   spec_c(stl,stg,stg')])] in
      function
      | RC -> ret (_II0, _II0)
      | RR -> ret (_IIss, _II0) 
      | SI -> ret (_IIss, _IIww)
      | SER -> ret (_IIss, _IIss)
end

module StateTransformer = struct
  type t = (state expr -> set expr)

  let to_string _F = 
    let (stl,stg) = (fresh_stl(), fresh_stg ()) in
    let s = _F (Var (Ident.create stg, Type.Set)) in
      "λ("^stg^"). "^(Expr.to_string s)

  let empty = fun _ -> Expr._SConst []
  let (@<+>) _F1 _F2 = let open Expr in 
    fun stg -> _F1(stg) @<+> _F2(stg)
end
