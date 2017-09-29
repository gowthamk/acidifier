open App
open Speclang

module KE = Light_env.Make(struct include Kind end)
module TE = Light_env.Make(struct include Type end)
module P = Predicate
module K = Kind
module T = Type

let (<<) f g x = f(g x)

let mk_nullary_cons name : Cons.t = 
  let recognizer = "is"^name in
    Cons.T {name=name; recognizer=recognizer; args=[]}

let ty1  = Type.Arrow (Type.St, Type.Bool)
let ty2  = Type.Arrow (Type.Tuple [Type.St; Type.St], Type.Bool)
let ty3 = Type.Arrow (Type.Tuple [Type.St; Type.St; Type.St], Type.Bool)

let bootstrap_pe (Spec.T spec) = 
  let _Gs = List.map (fun (Spec.Txn tspec) -> 
                        tspec.guarantee) spec.txns in
  let _I = spec.invariant in
  let open P in
  (* R = U_{i}(G_i) *)
  let _R_def = _Forall_St2 @@
      function (stg,stg') -> _R(??stg,??stg') @<=> 
        (?|| (List.map (fun _G -> b_app(_G,[??stg;??stg'])) _Gs)) in
  (* Rl(δ,Δ,Δ') <=> R(Δ,Δ') /\ IIr(δ,Δ,Δ') *)
  let _Rl_def = _Forall_St3 @@ function (stl,stg,stg') -> 
      _Rl(??stl,??stg,??stg') @<=> (?&& [_R(??stg,??stg'); 
                                         _IIr(??stl,??stg,??stg')]) in
  (* Rc(δ,Δ,Δ') <=> R(Δ,Δ') /\ IIc(δ,Δ,Δ') *)
  let _Rc_def = _Forall_St3 @@ function (stl,stg,stg') -> 
      _Rc(??stl,??stg,??stg') @<=> (?&& [_R(??stg,??stg'); 
                                         _IIc(??stl,??stg,??stg')]) in
  (* flush_def *)
  (* ∀(r:Rec). r∈(δ»Δ) ⇔ (¬(r.id∈dom(δ)) ∧ r∈Δ) ∨ (r∈δ ∧ ¬r.del) *)
  let flush_def = _Forall_St3_Rec1 @@ fun (stl,stg,st,r) ->
      (??r @: ??st) @<=> ?|| [is_not_in_dom(id(??r),??stl) 
                                  @&& (??r @: ??stg);
                              (??r @: ??stl) @&& Not (del(??r))] in
  (* flush theorems *)
  (* dom_eq def *)
  (* empty_st def *)
  (* Extensional equality of states: an optimization *)
    ?&& ([_R_def; 
          _Rl_def; 
          _Rc_def; 
          flush_def] 
         @ (* Guarantees and Invariants *)spec.asserts)


let bootstrap (App.T {schemas; txns}) = 
  let kinds = 
    [
      (Type.Id, K.Uninterpreted);
      (Type.Rec, K.Uninterpreted);
      (Type.St, K.Uninterpreted);
      (Type.String, K.Uninterpreted);
      (* Table :-> Variant{Stock, Order, Customer, ...} *)
      let table_names = List.map Tableschema.name schemas in
      let all_cons = List.map mk_nullary_cons table_names in 
        (Type.Table, Kind.Variant all_cons)
    ] in
  (* Record field accessors *)
  (* eg: TE[s_id :-> Type.record -> Type.Id],
   *     TE[c_name :-> Type.record -> Type.String]*)
  let cols = List.concat @@ List.map Tableschema.cols schemas in
  let accessors = List.map 
                    (fun (col_name,col_typ) -> 
                       (Ident.create col_name,
                        Type.Arrow (Type.record,col_typ))) cols in
  let _ = L.set_accessors @@ List.map fst accessors in
  (* Get spec and add G's and I to TE *)
  let Spec.T spec = Spec.spec () in 
  let _Gs = List.map (fun (Spec.Txn tspec) -> 
                        tspec.guarantee) spec.txns in
  let _I = spec.invariant in
  let types = 
    [
      (L.empty_st, Type.Arrow (Type.St,Type.Bool));
      (L.table, Type.Arrow (Type.Rec,Type.Table));
      (L.is_in, Type.Arrow (Type.Tuple [Type.St; Type.Rec],
                            Type.Bool));
      (L.flush, ty3);
      (*  _IIr/IIc/Rl/Rc :-> ty3; R/G :-> ty2; I :-> ty1 *)
      (L._IIr, ty3);
      (L._IIc,ty3);
      (L._Rl,ty3);
      (L._Rc,ty3);
      (L._R, ty2);
      (_I,ty1)
    ]
    @ (* Record field accessors *) accessors
    @ (* Guarantees *) (List.map (fun _G -> (_G,ty2)) _Gs) in
  (* bootstrap KE *)
  let ke = List.fold_left 
            (fun ke (ty,k) -> 
              KE.add (Ident.create @@ Type.to_string ty) k ke) 
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
