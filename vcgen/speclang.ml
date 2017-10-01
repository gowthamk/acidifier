open Utils
open Types
open Typedtree

let dprintf = function 
  | true -> printf
  | false -> (Printf.ifprintf stdout)
(* Debug print flags *)
let _dsubst = ref false;;

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
  let _I = Ident.create "I"
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

  let rec subst (e',x) e = 
    let f = subst (e',x) in 
    let _ = (dprintf !_dsubst) "[%s/%s] %s\n" (to_string e') 
              (Ident.name x) (to_string e) in
      match e with
      | Var v -> if Ident.equal v x then e' else e
      | App (v,exps) -> (match (e', Ident.equal v x) with 
                          | (Var v', true) -> App (v', List.map f exps)
                          | _ -> App (v, List.map f exps))
      | _ -> e
end

type pred = 
          | BoolExpr of Expr.t 
          | Eq of Expr.t * Expr.t
          | GE of Expr.t * Expr.t
          | LE of Expr.t * Expr.t
          | Not of pred
          | And of pred list
          | Or of pred list
          | ITE of pred * pred * pred
          | If of pred * pred 
          | Iff of pred * pred 
          | Forall of Type.t list * (Ident.t list -> pred)
          | Exists of Type.t list * (Ident.t list -> pred)
          | SEq of set * set
          | SIn of Expr.t * set
and set = SConst of Expr.t list (* {1,2}, .. *)
        | SVar of Ident.t (* x, δ, Δ, ... *)
        | SLit of (Ident.t -> pred) (* {x | φ} *)
        | SExists of Type.t * (Ident.t -> pred * set) (* exists(x,φ,s) *)
        | SBind of set * (Ident.t -> set) (* s1 »= λx.s2 *)
        | SITE of pred * set * set (* if φ then s1 else s2 *)
        | SU of set*set (* s1 ∪ s2 *)

let (fresh_bv,_) = gen_name "bv"
let (fresh_stl,_) = gen_name "δ"
let (fresh_stg,_) = gen_name "Δ"

let rec pred_to_string x = 
  let f = pred_to_string in
  let g x = "("^(f x)^")" in
  let h = Expr.to_string in
    match x with
    | BoolExpr e -> Expr.to_string e
    | Eq (e1,e2) -> (h e1)^" = "^(h e2)
    | GE (e1,e2) -> (h e1)^" ≥ "^(h e2)
    | LE (e1,e2) -> (h e1)^" ≤ "^(h e2)
    | Not sv -> "~("^(f sv)^")"
    | And svs -> "("^(String.concat " && " @@ List.map f svs)^")"
    | Or svs -> "("^(String.concat " || " @@ List.map f svs)^")"
    | If (v1,v2) -> (f v1)^" => "^(f v2)
    | Iff (v1,v2) -> (f v1)^" <=> "^(f v2)
    | ITE (grd,sv1,sv2) -> (g grd)^"?"^(g sv1)^":"^(g sv2)
    | Forall (tys,b) -> 
        let bvtys = List.map 
                      (fun ty -> (Ident.create @@ fresh_bv (),ty)) tys in
        let bvty_to_string (bv,ty) = 
                      (Ident.name bv)^":" ^(Type.to_string ty) in
        "∀("^(String.concat "," @@ List.map bvty_to_string bvtys)^"). "
          ^(f @@ b @@ List.map fst bvtys)
    | Exists (tys,b) -> 
        let bvtys = List.map 
                      (fun ty -> (Ident.create @@ fresh_bv (),ty)) tys in
        let bvty_to_string (bv,ty) = 
                      (Ident.name bv)^":" ^(Type.to_string ty) in
        "∃("^(String.concat "," @@ List.map bvty_to_string bvtys)^"). "
          ^(f @@ b @@ List.map fst bvtys)
    | SEq (s1,s2) -> (set_to_string s1)^" = "^(set_to_string s2)
    | SIn (e1,s2) -> (Expr.to_string e1)^" ∈ "^(set_to_string s2)

and set_to_string t = 
  let ty = Type.Rec in 
  let to_string = set_to_string in
    match t with
    | SConst l -> "{"^(String.concat "," @@ 
                       List.map Expr.to_string l)^"}"
    | SVar x -> Ident.name x
    | SLit f -> 
      let bv = Ident.create @@ fresh_bv () in
        "{ "^(Ident.name bv)^":"^(Type.to_string ty)^" | "
          ^(pred_to_string @@ f bv)^" }"
    | SExists (ty,f) -> 
      let bv = Ident.create @@ fresh_bv () in
      let (phi,s) = f bv in 
        "∃("^(Ident.name bv)^":"^(Type.to_string ty)^" | "
          ^(pred_to_string phi)^"). "^(to_string s)
    | SBind (s1,f2) ->
      let s1str = to_string s1 in
      let tystr = Type.to_string ty in
      let bv = Ident.create @@ fresh_bv () in
      let bvstr = Ident.name bv in
      let s2str = to_string @@ f2 bv in
        "("^s1str^") >>= (fun "^bvstr^":"^tystr^" -> "^s2str^")"
    | SITE (phi,s1,s2) -> (pred_to_string phi)^"? "^(to_string s1)
                         ^": "^(to_string s2)
    | SU (s1,s2) -> (to_string s1)^" U "^(to_string s2)

let rec pred_subst (e,x) p = 
  let f = pred_subst (e,x) in 
  let _ = dprintf !_dsubst "[%s/%s] %s\n" (Expr.to_string e) 
            (Ident.name x) (pred_to_string p) in
    match p with
    | BoolExpr exp -> BoolExpr (Expr.subst (e,x) exp)
    | And ps -> And (List.map f ps)
    | Or ps -> Or (List.map f ps)
    | Not p -> Not (f p)
    | Eq (e1,e2) -> Eq (Expr.subst (e,x) e1, Expr.subst (e,x) e2)
    | GE (e1,e2) -> GE (Expr.subst (e,x) e1, Expr.subst (e,x) e2)
    | LE (e1,e2) -> LE (Expr.subst (e,x) e1, Expr.subst (e,x) e2)
    | ITE (p1,p2,p3) -> ITE (f p1, f p2, f p3)
    | If (p1,p2) -> If (f p1, f p2)
    | Iff (p1,p2) -> Iff (f p1, f p2)
    | SEq (s1,s2) -> SEq (set_subst (e,x) s1, set_subst (e,x) s2)
    | SIn (e1,s2) -> SIn (Expr.subst (e,x) e1, set_subst (e,x) s2)
    | Exists (tys,g) -> Exists (tys, fun v -> f (g v))
    | Forall (tys,g) -> Forall (tys, fun v -> f (g v))

and set_subst (e,x) s = 
  let subst = set_subst in 
  let _ = dprintf !_dsubst "[%s/%s] %s\n" (Expr.to_string e) 
            (Ident.name x) (set_to_string s) in
    match s with
      | SConst exps -> SConst (List.map (Expr.subst (e,x)) exps)
      (* Set variable may be let-bound, which we substitute with 
       * a new variable *)
      | SVar v -> (match e with | Expr.Var v' -> SVar v' 
                                | _ -> SVar v)
      | SLit f -> SLit (fun v -> pred_subst (e,x) (f v))
      | SBind (s,f) -> 
        let s' = subst (e,x) s in
          SBind (s', fun v -> subst (e,x) @@ f v)
      | SExists (ty,f) -> 
        SExists(ty, fun v -> let (p,s) = f v in 
                      (pred_subst (e,x) p, subst (e,x) s))
      | SITE (p,s1,s2) -> 
        let p' = pred_subst (e,x) p in
        let s1' = subst (e,x) s1 in 
        let s2' = subst (e,x) s2 in 
          SITE (p', s1', s2')
      | SU (s1,s2) -> SU (subst (e,x) s1, subst (e,x) s2)

module Predicate = 
struct
  (* Reexporting the pred variant type as Predicate.t *)
  type t = pred = 
                | BoolExpr of Expr.t 
                | Eq of Expr.t * Expr.t
                | GE of Expr.t * Expr.t
                | LE of Expr.t * Expr.t
                | Not of pred
                | And of pred list
                | Or of pred list
                | ITE of pred * pred * pred
                | If of pred * pred 
                | Iff of pred * pred 
                | Forall of Type.t list * (Ident.t list -> pred)
                | Exists of Type.t list * (Ident.t list -> pred)
                | SEq of set * set
                 (* SIn is needed because (@:) only relates
                  * expressions. *)
                | SIn of Expr.t * set

  let to_string = pred_to_string

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
  let truee = BoolExpr (Expr.ConstBool true)
  let falsee = BoolExpr (Expr.ConstBool false)
  let (@:) r s = BoolExpr (Expr.App (L.is_in,[r;s]))(*r∈s*)
  let (?&&) xs = And xs
  let (?||) xs = Or xs
  let (@&&) x y = conj x y
  let (@||) x y = disj x y
  let (@==) x y = Eq (x,y)
  let (@===) s1 s2 = SEq (s1,s2)
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
  let _I (st) = b_app(L._I,[st])
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
  let _Exists_Rec1 f = 
    Exists ([Type.Rec], 
            function [r] -> f r
                   | _ -> failwith "_Exists_Rec1: Unexpected")
  let _Exists_St1 f = 
    Exists ([Type.St], 
            function [st] -> f st
                   | _ -> failwith "_Exists_St1: Unexpected")
end

module Set = 
struct
  (* Reexporting the set variant type as Set.t *)
  type t = set = SConst of Expr.t list (* {1,2}, .. *)
               | SVar of Ident.t (* x, δ, Δ, ... *)
               | SLit of (Ident.t -> pred) (* {x | φ} *)
               | SExists of Type.t * (Ident.t -> pred * set) (* exists(x,φ,s) *)
               | SBind of set * (Ident.t -> set) (* s1 »= λx.s2 *)
               | SITE of pred * set * set (* if φ then s1 else s2 *)
               | SU of set*set (* s1 ∪ s2 *)

  let to_string = set_to_string
  let subst = set_subst
  let (???) x = SVar x
  let (!!!) l = SConst l
  let (@>>=) s f = SBind (s,f)
  let (@<+>) s1 s2 = SU (s1,s2)
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

module StateTransformer = struct
  type t = (Set.t * Set.t -> Set.t)

  let to_string _F = 
    let (stl,stg) = (fresh_stl(), fresh_stg ()) in
    let s = _F (SVar (Ident.create stl), 
                SVar (Ident.create stg)) in
      "λ("^stl^","^stg^"). "^(Set.to_string s)
end

