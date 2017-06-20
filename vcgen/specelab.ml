open App
open Speclang

module KE = Light_env.Make(struct include Kind end)
module TE = Light_env.Make(struct include Type end)
module P = Predicate

let (<<) f g x = f(g x)

let mk_nullary_cons name : Cons.t = 
  let recognizer = "is"^name in
    Cons.T {name=name; recognizer=recognizer; args=[]}


let bootstrap_pe (Spec.T spec) = 
  let _Gs = List.map (fun (Spec.Txn tspec) -> 
                        tspec.guarantee) spec.txns in
  let _I = spec.invariant in
  let open P in
  (* R = U_{i}(G_i) *)
  let _R_def = Forall ([Type.St; Type.St],
      function [stg;stg'] -> b_app(L._R,[??stg;??stg']) @<=> 
        (?|| (List.map (fun _G -> b_app(_G,[??stg;??stg'])) _Gs))) in
  (* Rl(st,stg,stg') <=> R(stg,stg') /\ IIr(stl,stg,stg') *)
  let _Rl_def = Forall ([Type.St; Type.St; Type.St],
      function [stl;stg;stg'] -> b_app(L._Rl,[??stl;??stg;??stg']) @<=> 
        (?&& [b_app(L._R,[??stg;??stg']); 
              b_app(L._IIr,[??stl;??stg;??stg'])])) in
  (* Rc(st,stg,stg') <=> R(stg,stg') /\ IIc(stl,stg,stg') *)
  let _Rc_def = Forall ([Type.St; Type.St; Type.St],
      function [stl;stg;stg'] -> b_app(L._Rc,[??stl;??stg;??stg']) @<=> 
        (?&& [b_app(L._R,[??stg;??stg']); 
              b_app(L._IIc,[??stl;??stg;??stg'])])) in
    ?&& ([_R_def; _Rl_def; _Rc_def] @ spec.asserts)

let bootstrap (App.T {schemas; txns}) = 
  (* 1. Id typedef to KE *)
  let add_Id = KE.add (Ident.create "Id") Kind.Uninterpreted in
  (* 2. Rec typedef to KE *)
  let add_Rec = KE.add (Ident.create "Rec") Kind.Uninterpreted in
  (* 3. Loc typedef to KE *)
  let add_Loc = KE.add (Ident.create "Loc") Kind.Uninterpreted in
  (* 4. St typedef to KE *)
  let add_St = KE.add (Ident.create "St") Kind.Uninterpreted in
  (* 5. Set typedef to KE *)
  let add_Set = KE.add (Ident.create "Set") Kind.Uninterpreted in
  (* 6. Str typedef to KE *)
  let add_Str = KE.add (Ident.create "Str") Kind.Uninterpreted in
  (* 7. TE[value :-> St*Loc -> Rec] *)
  let add_value = TE.add (Ident.create "value") @@
                   Type.Arrow (Type.Tuple[Type.st; Type.loc], 
                               Type.record) in
  (* 8. TE[remove :-> Set*Set*Loc -> Bool]*) 
  let add_remove = TE.add L.remove @@
                     Type.Arrow (Type.Tuple[Type.set; Type.set; Type.loc], 
                                 Type.Bool) in
  (* 9. TE[add :-> Set*Set*Loc -> Bool]*)
  let add_add = TE.add L.add @@
                  Type.Arrow (Type.Tuple[Type.set; Type.set; Type.loc], 
                              Type.Bool) in
  (* TE[empty :-> Set] *)
  let add_empty = TE.add L.empty Type.set in
  (* 10. eg: KE[table :-> Variant{Stock, Order, Customer, ...}] *)
  let table_names = List.map Tableschema.name schemas in
  let add_Table = 
    let all_cons = List.map (mk_nullary_cons) table_names in
      KE.add (Ident.create "Table") (Kind.Variant all_cons) in
  (* 11. TE[table :-> Type.record -> Type.table] *)
  let add_table te = 
    let typ = Type.Arrow (Type.record,Type.table) in
      TE.add (L.table) typ te in
  (* 12. TE[dom :-> Type.St -> Type.Set]*)
  let add_dom te = 
    let typ = Type.Arrow (Type.St, Type.Set) in
      TE.add (L.dom) typ te in
  (* 12. Record field accessors to TE *)
  (* eg: TE[s_id :-> Type.record -> Type.Id],
   *     TE[c_name :-> Type.record -> Type.String]*)
  let cols = List.concat @@ List.map Tableschema.cols schemas in
  let accessors = List.map 
                    (fun (col_name,col_typ) -> 
                       (Ident.create col_name,
                        Type.Arrow (Type.record,col_typ))) cols in
  let _ = L.set_accessors @@ List.map fst accessors in
  let add_field_accessors (te:TE.t) : TE.t = 
      List.fold_left (fun te (acc_name,acc_typ) -> 
                    TE.add acc_name acc_typ te) te accessors in 
  (* Get spec and add G's and I to TE *)
  let Spec.T spec = Spec.spec () in 
  let _Gs = List.map (fun (Spec.Txn tspec) -> 
                        tspec.guarantee) spec.txns in
  let _I = spec.invariant in
  (* 13. TE[_IIr/IIc/Rl/Rc :-> Type.St*Type.St*Type.St -> Type.Bool] *)
  (*     TE[G :-> (St*St) -> Bool]; TE[I :-> St -> Bool]*)
  let add_Rs_Gs_IIs_and_I te = 
    let ty1  = Type.Arrow (Type.St, Type.Bool) in
    let ty2  = Type.Arrow (Type.Tuple [Type.St; Type.St], Type.Bool) in
    let ty3 = Type.Arrow (Type.Tuple [Type.St; Type.St; Type.St], Type.Bool) in
      begin
        TE.add L._R ty2 @@ TE.add L._Rc ty3 @@ TE.add L._Rl ty3 @@ 
        TE.add L._IIc ty3 @@ TE.add L._IIr ty3 @@ TE.add _I ty1 @@
        List.fold_left (fun te _G -> TE.add _G ty2 te) te _Gs
      end in
  (* bootstrap KE *)
  let ke = List.fold_left (fun ke f -> f ke) KE.empty
      [add_Id; add_Rec; add_Loc; add_St; add_Set; add_Str; add_Table] in
  (* bootstrap TE *)
  let te = List.fold_left (fun te f -> f te) TE.empty
      [add_value; add_remove; add_add; add_empty; add_table; add_dom; 
       add_field_accessors; add_Rs_Gs_IIs_and_I] in
  (* bootstrap Phi *)
  let phi = bootstrap_pe (Spec.T spec) in
    (ke,te,phi)

let doIt app = 
  let (ke,te,phi) = bootstrap app in
    (ke,te,phi)
