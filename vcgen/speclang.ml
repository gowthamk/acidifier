open Utils
open Types
open Typedtree

module Type = 
struct
  (* Types of the spec language *)
  type t = Any | Int | Bool | String | Unit 
    | Id | Rec | St | Set | Table | Date
    | Arrow of t*t | List of t | Tuple of t list
    | Option of t

  let rec to_string = function Any -> "any"
    | Int -> "Int" | Bool -> "Bool" | Id -> "Id"
    | String -> "String" | Unit -> "Unit" 
    | Table -> "Table" | Date -> "Date"
    | Rec -> "Rec" | St -> "St" | Set -> "Set"
    | Arrow (t1,t2) -> (to_string t1)^" -> "^(to_string t2)
    | List t -> (to_string t)^" list"
    | Tuple ts -> "("^(String.concat "," @@ List.map to_string ts)^")"
    | Option t -> (to_string t)^" option"

  let _of str = match str with
    |"Id" -> Id | "Rec" -> Rec | "St" -> St
    | "Set" -> Set | "Str" -> String | "Unit" -> Unit
    | "Table" -> Table | _ -> failwith "Type._of: Unexpected"

  let id = Id
  let table = Table
  let record = Rec
  let st = St
  let set = Set
end

module Cons = 
struct
  type t = T of {name: string; 
                 recognizer: string; 
                 args: (string * Type.t) list}
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
        | Alias of Type.t

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
  (* Invariants and Relations *)
  let _II = Ident.create "II"
  let _IIr = Ident.create "IIr"
  let _IIc = Ident.create "IIc"
  let _R = Ident.create "R"
  let _Rl = Ident.create "Rl"
  let _Rc = Ident.create "Rc"
end

module Expr = 
struct
  type t =
    | Var of Ident.t
    | App of Ident.t * t list
    | ConstInt of int
    | ConstBool of bool
    | ConstString of string

  let rec to_string x = match x with
    | Var id -> Ident.name id
    | App (id,svs) -> (Ident.name id)^"("
        ^(String.concat "," @@ List.map to_string svs)^")"
    | ConstInt i -> string_of_int i
    | ConstBool b -> string_of_bool b
    | ConstString s -> s
end

module BasePredicate = 
struct
  (* Will be extended later to include set predicates *)
  type t = ..
  type t += 
    | BoolExpr of Expr.t 
    | Eq of Expr.t * Expr.t
    | GE of Expr.t * Expr.t
    | LE of Expr.t * Expr.t
    | Not of t
    | And of t list
    | Or of t list
    | ITE of t * t * t
    | If of t * t 
    | Iff of t * t 
    | Forall of Type.t list * (Ident.t list -> t)
    | Exists of Type.t list * (Ident.t list -> t)

  let (fresh_bv,_) = gen_name "bv"

  let rec to_string x =
    let f = to_string in
    let g x = "("^(f x)^")" in
    let h = Expr.to_string in
      match x with
        | BoolExpr e -> Expr.to_string e
        | Eq (e1,e2) -> (h e1)^" = "^(h e2)
        | GE (e1,e2) -> (h e1)^" ≥ "^(h e2)
        | LE (e1,e2) -> (h e1)^" ≤ "^(h e2)
        | Not sv -> "~("^(f sv)^")"
        | And svs -> "("^(String.concat " &&\n\t" @@ List.map f svs)^")"
        | Or svs -> "("^(String.concat " || " @@ List.map f svs)^")"
        | If (v1,v2) -> (to_string v1)^" => "^(to_string v2)
        | Iff (v1,v2) -> (to_string v1)^" <=> "^(to_string v2)
        | ITE (grd,sv1,sv2) -> (g grd)^"?"^(g sv1)^":"^(g sv2)
        | Forall (tys,f) -> 
            let bvtys = List.map 
                          (fun ty -> (Ident.create @@ fresh_bv (),ty)) tys in
            let bvty_to_string (bv,ty) = 
                          (Ident.name bv)^":" ^(Type.to_string ty) in
            "∀("^(String.concat "," @@ List.map bvty_to_string bvtys)^"). "
              ^(to_string @@ f @@ List.map fst bvtys)
        | Exists (tys,f) -> 
            (*let fresh_bv = gen_name "bv" in*)
            let bvtys = List.map 
                          (fun ty -> (Ident.create @@ fresh_bv (),ty)) tys in
            let bvty_to_string (bv,ty) = 
                          (Ident.name bv)^":" ^(Type.to_string ty) in
            "∃("^(String.concat "," @@ List.map bvty_to_string bvtys)^"). "
              ^(to_string @@ f @@ List.map fst bvtys)
        | _ -> failwith "Predicate.to_string: Unimpl"

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
  let truee = BoolExpr (Expr.ConstBool true)
  let falsee = BoolExpr (Expr.ConstBool false)
  let (@:) r s = BoolExpr (Expr.App (L.is_in,[r;s]))(*r∈s*)
  let (?&&) xs = And xs
  let (?||) xs = Or xs
  let (@&&) x y = conj x y
  let (@||) x y = disj x y
  let (@==) x y = Eq (x,y)
  let (@!=) x y = Not (Eq (x,y))
  let (@>=) x y = GE (x,y)
  let (@=>) x y = If (x,y)
  let (@<=>) x y = Iff (x,y)
  let (??) x = Expr.Var x
  let (!!) c = Expr.ConstInt c
  let empty_st x = BoolExpr (Expr.App (L.empty_st,[x]))
  let flush (stl,stg,st) = BoolExpr (Expr.App (L.flush, [stl;stg;st]))
  let dom_eq (st1,st2) = BoolExpr (Expr.App (L.dom_eq,[st1;st2]))
  let b_app (bf,args) = BoolExpr(Expr.App (bf,args))
  let table (x) = Expr.App (L.table, [x]) 
  let id (x) = Expr.App (L.id,[x])
  let del (x) = BoolExpr (Expr.App (L.del,[x]))
  let txn (x) = Expr.App (L.txn,[x])
  let is_in_dom (i,st) = 
    Exists ([Type.Rec], fun [r] -> ?&& [??r @: st;
                                        id(??r) @== i])
  let is_not_in_dom (i,st) = Not (is_in_dom (i,st))
  let _R (st,st') = b_app(L._R,[st;st'])
  let _Rl (stl,stg,stg') = b_app(L._Rl,[stl;stg;stg'])
  let _Rc (stl,stg,stg') = b_app(L._Rc,[stl;stg;stg'])
  let _IIr (stl,stg,stg') = b_app(L._IIr,[stl;stg;stg'])
  let _IIc (stl,stg,stg') = b_app(L._IIc,[stl;stg;stg'])

  let _Forall_St1 f = 
    Forall ([Type.St], 
            fun l -> match l with 
              | [stl] -> f stl
              | _ -> failwith "_Forall_St1: Unexpected")
  let _Forall_St2 f = 
    Forall ([Type.St; Type.St], 
            fun l -> match l with 
              | [stl;stg] -> f(stl,stg) 
              | _ -> failwith "_Forall_St2: Unexpected")
  let _Forall_St3 f = 
    Forall ([Type.St; Type.St; Type.St], 
            fun l -> match l with 
              | [stl;stg;stg'] -> f(stl,stg,stg')
              | _ -> failwith "_Forall_St3: Unexpected")
  let _Forall_St4 f = 
    Forall ([Type.St; Type.St; Type.St; Type.St], 
            fun l -> match l with 
              | [st0;st1;st2;st3] -> f(st0,st1,st2,st3) 
              | _ -> failwith "_Forall_St4: Unexpected")
  let _Forall_Rec1 f = 
    Forall ([Type.Rec], 
            fun l -> match l with 
              | [r] -> f r 
              | _ -> failwith "_Forall_Rec1: Unexpected")
  let _Forall_Rec2 f = 
    Forall ([Type.Rec; Type.Rec], 
            fun l -> match l with 
              | [r1;r2] -> f (r1,r2) 
              | _ -> failwith "_Forall_Rec2: Unexpected")
  let _Forall_St1_Rec1 f = 
    Forall ([Type.St; Type.Rec], 
            function [st;r] -> f (st,r)
              | _ -> failwith "_Forall_St1_Rec1: Unexpected")
  let _Forall_St3_Rec1 f = 
    Forall ([Type.St; Type.St; Type.St; Type.Rec], 
            fun l -> match l with 
              | [stl;stg;stg';r] -> f(stl,stg,stg',r) 
              | _ -> failwith "_Forall_St3_Rec1: Unexpected")
  let _Exists_Id1 f = 
    Exists ([Type.Id], 
            function [i] -> f i
                   | _ -> failwith "_Exists_Id1: Unexpected")
end

module Set = 
struct
  module P = BasePredicate

  type t = Const of Expr.t list (* {1,2}, .. *)
         | Var of Ident.t (* x, δ, Δ, ... *)
         | Lit of (Ident.t -> P.t) (* {x | φ} *)
         | Exists of (Ident.t -> P.t * t) (* exists(x,φ,s) *)
         | Bind of t * (Ident.t -> t) (* s1 »= λx.s2 *)
         | ITE of P.t * t * t (* if φ then s1 else s2 *)
         | U of t*t (* s1 ∪ s2 *)

  let (fresh_bv,_) = gen_name "sv"

  let rec to_string t = let ty = Type.Rec in match t with
    | Var x -> Ident.name x
    | Lit f -> 
      let bv = Ident.create @@ fresh_bv () in
        "{ "^(Ident.name bv)^":"^(Type.to_string ty)^" | "
          ^(P.to_string @@ f bv)^" }"
    | Exists f -> 
      let bv = Ident.create @@ fresh_bv () in
      let (phi,s) = f bv in 
        "∃("^(Ident.name bv)^":"^(Type.to_string ty)^" | "
          ^(P.to_string phi)^"). "^(to_string s)
    | Bind (s1,f2) ->
      let s1str = to_string s1 in
      let tystr = Type.to_string ty in
      let bv = Ident.create @@ fresh_bv () in
      let bvstr = Ident.name bv in
      let s2str = to_string @@ f2 bv in
        "("^s1str^") >>= (fun "^bvstr^":"^tystr^" -> "^s2str^")"
    | ITE (phi,s1,s2) -> (P.to_string phi)^"? "^(to_string s1)
                         ^": "^(to_string s2)
    | U (s1,s2) -> (to_string s1)^" U "^(to_string s2)

  let (???) x = Var x
  let (!!!) l = Const l
  let (@>>=) s f = Bind (s,f)
  let (@<+>) s1 s2 = U (s1,s2)
end

module Predicate = struct
  module S = Set
  include BasePredicate

  type t += SetEq of S.t * S.t

  let to_string = function
    | SetEq (s1,s2) -> (S.to_string s1)^" = "^(S.to_string s2)
    | s -> (*BasePredicate.*)to_string s

  let (@===) s1 s2 = SetEq (s1,s2)
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
    fun (r,r') -> ?&& [??r' @: stl; 
                       ??r @: stg;
                       id(??r) @== id(??r')]
                  @=> (??r @: stg')
  (* Snapshot isolation: ∆′ =∆ *)
  let _IIss (stl,stg,stg') = stg' @== stg

  (*
   * Machine/store-specific basic isolation common to all levels.
   *)
  let _IIm  = _IIww

  let spec_of = 
    let ret (spec_r,spec_c) = 
          ?&& [(_Forall_St3 @@ fun (stl,stg,stg') -> 
                  _IIr(??stl,??stg,??stg') 
                         @<=> ?&& [_IIm(??stl,??stg,??stg'); 
                                   spec_r(??stl,??stg,??stg')]); 
               (_Forall_St3 @@ fun (stl,stg,stg') -> 
                  _IIc(??stl,??stg,??stg') 
                         @<=> ?&& [_IIm(??stl,??stg,??stg'); 
                                   spec_c(??stl,??stg,??stg')])] in
      function
      | RC -> ret (_II0, _II0)
      | RR -> ret (_IIss, _II0) 
      | SI -> ret (_IIss, _IIww)
      | SER -> ret (_IIss, _IIss)
end

module Misc =
struct

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

end
