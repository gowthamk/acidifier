open App
open Speclang

module KE = Light_env.Make(struct include Kind end)
module TE = Light_env.Make(struct include Type end)

let (<<) f g x = f(g x)

let mk_nullary_cons name : Cons.t = 
  let recognizer = "is"^name in
    Cons.T {name=name; recognizer=recognizer; args=[]}

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
  let add_remove = TE.add (Ident.create "remove") @@
                     Type.Arrow (Type.Tuple[Type.set; Type.set; Type.loc], 
                                 Type.Bool) in
  (* 9. TE[add :-> Set*Set*Loc -> Bool]*)
  let add_add = TE.add (Ident.create "add") @@
                  Type.Arrow (Type.Tuple[Type.set; Type.set; Type.loc], 
                              Type.Bool) in
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
  let add_field_accessors (te:TE.t) : TE.t = 
    let cols = List.concat @@ List.map Tableschema.cols schemas in
    let accessors = List.map 
                      (fun (col_name,col_typ) -> 
                         (Ident.create col_name,
                          Type.Arrow (Type.record,col_typ))) cols in
    let _ = L.set_accessors @@ List.map fst accessors in
      List.fold_left (fun te (acc_name,acc_typ) -> 
                    TE.add acc_name acc_typ te) te accessors in 
  (* bootstrap KE *)
  let ke = List.fold_left (fun ke f -> f ke) KE.empty
      [add_Id; add_Rec; add_Loc; add_St; add_Set; add_Str; add_Table] in
  (* bootstrap TE *)
  let te = List.fold_left (fun te f -> f te) TE.empty
      [add_value; add_remove; add_add; add_table; add_dom; 
       add_field_accessors] in
    (ke,te)

let doIt app = 
  let (ke,te) = bootstrap app in
    (ke,te)
