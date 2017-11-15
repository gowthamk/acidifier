open App
open Speclang

module KE = Light_env.Make(struct include Kind end)
module TE = Light_env.Make(struct 
                            type t = some_type
                            let to_string = function
                              | SomeType t -> Type.to_string t
                           end)
module P = Predicate
module K = Kind
module T = Type

let (<<) f g x = f(g x)

let some t = SomeType t

let mk_nullary_cons name : Cons.t = 
  let recognizer = "is"^name in
    Cons.T {name=name; recognizer=recognizer; args=[]}

let ty1  = Type.Arrow (Type.St, Type.Bool)
let ty2  = Type.Arrow (Type.Pair (Type.St, Type.St), Type.Bool)
let ty3 = Type.Arrow (Type.Triple (Type.St, Type.St, Type.St), Type.Bool)

let bootstrap_pe (Spec.T spec) = 
  let _Gs = List.map (fun (Spec.Txn tspec) -> 
                        tspec.guarantee) spec.txns in
  let open P in
  (* R = U_{i}(G_i) *)
  let _R_def = _Forall_St2 @@ function (stg,stg') -> 
        _R(stg,stg') @<=> (?|| (List.map (fun _G -> 
                                  b_app(_G,[stg;stg'])) _Gs)) in
  (* Rl(δ,Δ,Δ') <=> R(Δ,Δ') /\ IIr(δ,Δ,Δ') *)
  let _Rl_def = _Forall_St3 @@ function (stl,stg,stg') -> 
      _Rl(stl,stg,stg') @<=> (?&& [_R(stg,stg'); 
                                   _IIr(stl,stg,stg')]) in
  (* Rc(δ,Δ,Δ') <=> R(Δ,Δ') /\ IIc(δ,Δ,Δ') *)
  let _Rc_def = _Forall_St3 @@ function (stl,stg,stg') -> 
      _Rc(stl,stg,stg') @<=> (?&& [_R(stg,stg'); 
                                    _IIc(stl,stg,stg')]) in
  (* Id Axiom *)
  let id_axiom = _Forall_St1_Rec2 @@ function (st,r1,r2) ->
      (?&& [r1 @: st; r2 @: st]) @=> (?|| [r1 @== r2; 
                                           id(r1) @!= id(r2)]) in
  (* Extensional equality of records *)
  let rec_ext_eq = _Forall_Rec2 @@ function (r1,r2) ->
      let accessors = L.get_accessors () in
      let attr r1 acc = App (acc,[r1],Type.Any) in
      let basic_eq = [id(r1) @== id(r2); 
                      table(r1) @== table(r2)] in
      let r1_attrs = List.map (attr r1) accessors in
      let r2_attrs = List.map (attr r2) accessors in
      let attrs_eq = List.map2 (fun a1 a2 -> a1 @== a2) 
                          r1_attrs r2_attrs in
      let all_eq = basic_eq @ attrs_eq in
        (?&& all_eq) @=> (r1 @== r2) in
  (* flush_def *)
  (* ∀(r:Rec). r∈(δ»Δ) ⇔ (¬(r.id∈dom(δ)) ∧ r∈Δ) ∨ (r∈δ ∧ ¬r.del) *)
  (*let flush_def = 
    _Forall_St3 @@ fun (stl,stg,st) -> 
      _Forall_Rec1 @@ fun r -> 
        (r @: st) @<=> ?|| [is_not_in_dom(id(r),stl) 
                                  @&& (r @: stg);
                              (r @: stl) @&& Not (del(r))] in*)
  (* flush theorems *)
  (* dom_eq def *)
  (* empty_st def *)
  (* Extensional equality of states: an optimization *)
    ?&& ([_R_def; 
          _Rl_def; 
          _Rc_def; 
          id_axiom;
          rec_ext_eq;
          (*flush_def*)] 
         @ (* Guarantees and Invariants *)spec.asserts)


let bootstrap (App.T {schemas; txns}) = 
  let kinds = let open Kind in let open Type in 
    [
      (to_string Id, Uninterpreted);
      (to_string Rec, Uninterpreted);
      (to_string St, Uninterpreted);
      (*(to_string Rec, Enum (List.map Ident.create ["rec0"; "rec1"]));
      (to_string St, Enum (List.map Ident.create ["st0"; "st1"; "st2"]));*)
      (to_string String, Uninterpreted);
      (* Table :-> Variant{Stock, Order, Customer, ...} *)
      let table_names = List.map Tableschema.name schemas in
      (*let all_cons = List.map mk_nullary_cons table_names in *)
      let all_tags = List.map Ident.create table_names in 
        (to_string Table, Enum all_tags)
    ] in
  (* Record field accessors *)
  (* eg: TE[s_id :-> Type.record -> Type.Id],
   *     TE[c_name :-> Type.record -> Type.String]*)
  let cols = List.concat @@ List.map Tableschema.cols schemas in
  let accessors = List.map 
                    (fun (col_name,SomeType col_typ) -> 
                       (Ident.create col_name,
                        some @@ Type.Arrow (Type.Rec,col_typ))) 
                    cols in
  let _ = L.set_accessors @@ List.map fst accessors in
  (* Get spec and add G's and I to TE *)
  let Spec.T spec = Spec.spec () in 
  let _Gs = List.map (fun (Spec.Txn tspec) -> 
                        tspec.guarantee) spec.txns in
  let types = let open Type in
    [
      (L.empty_st, some @@ Arrow (Type.St,Type.Bool));
      (L.table, some @@ Arrow (Type.Rec,Type.Table));
      (L.is_in, some @@ Arrow (Type.Pair (Type.St, Type.Rec),
                            Type.Bool));
      (L.flush, some ty3);
      (*  _IIr/IIc/Rl/Rc/I :-> ty3; R/G :-> ty2; I :-> ty1 *)
      (L._IIr, some ty3);
      (L._IIc, some ty3);
      (L._Rl, some ty3);
      (L._Rc, some ty3);
      (L._R, some ty2);
      (L._I, some ty1);
      (L._F, some @@ Arrow (Pair (St,Rec), Bool));
      (L._Fc, some @@ Arrow (Pair (St,Rec), Bool));
      (* special hidden fields *)
      (L.id, some @@ Arrow (Type.Rec, Type.Id));
      (L.del, some @@ Arrow (Type.Rec, Type.Bool));
    ]
    @ (* Record field accessors *) accessors
    @ (* Guarantees *) (List.map (fun _G -> 
                                    (_G, some ty2)) _Gs) in
  (* bootstrap KE *)
  let ke = List.fold_left 
            (fun ke (ty_str,k) -> 
              KE.add (Ident.create ty_str) k ke) 
            KE.empty kinds in
  (* bootstrap TE *)
  let te = List.fold_left 
            (fun te (id,ty) -> TE.add id ty te) 
            TE.empty types in
  (* bootstrap Phi *)
  let phi = bootstrap_pe (Spec.T spec) in
    (ke,te,phi)

let doIt app = 
  let (ke,te,phi) = bootstrap app in
    (ke,te,phi)
