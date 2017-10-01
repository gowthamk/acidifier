open Utils
open Types
open Typedtree
open Speclang
open Specelab
module P = Predicate
module S = Set
module E = Expr
module F = StateTransformer
module Z3E = Z3encode
open P
open S

module VE = Light_env.Make(struct 
                             include Speclang.Expr 
                           end)

type env = {txn: Ident.t; 
            mutable ke: KE.t; 
            mutable te: TE.t; 
            mutable phi: P.t}

let printf = Printf.printf
let sprintf = Printf.sprintf
let ppf = Format.std_formatter
let not_found msg = (Printf.printf "%s\n" msg; raise Not_found)
let map_snd_opts = List.map (function (_,Some x) -> x
                               | _ -> failwith "Unexpected")
let pervasives = [("Pervasives.&&", L.andd); 
                  ("Pervasives.||", L.orr); 
                  ("Pervasives.not", L.nott); 
                  ("Pervasives.+", L.plus); 
                  ("Pervasives.-", L.minus);
                  ("Pervasives.=", L.eq);
                  ("Pervasives.>", L.gt);
                  ("Pervasives.>=", L.ge);
                  ("Pervasives.<", L.lt);
                  ("Pervasives.<=", L.le);]

let print_env env = 
  begin
    printf "----- Kind Env ----\n";
    KE.print env.ke;
    printf "----- Type Env ----\n";
    TE.print env.te;
    printf "----- Context ----\n";
    printf "%s\n" @@ P.to_string env.phi;
  end

 let rec type_of_tye ke (tye : type_expr) = 
  let open Path in
  let ppf = Format.std_formatter in
  let strf = Format.str_formatter in
  (*let _ = Printtyp.type_expr strf tye in
  let _ = printf "of_tye(%s)\n" @@ 
            Format.flush_str_formatter () in*)
  let f = type_of_tye ke in 
    match tye.desc with
    | Tvar aop -> 
      let a_name = Astutils.mk_tvar_name aop tye.id in
      (*let _ = printf "type_of_tye(%s)\n" a_name in*)
      let msg = sprintf "Kind of %s not found" a_name in
      let knd = try KE.find_name a_name ke 
                with Not_found -> not_found msg in
        (match knd with | Kind.Alias typ -> typ
          | _ -> failwith "type_of_tye: Unexpected")
    | Tarrow (_,te1,te2,_) -> Type.Arrow (f te1, f te2)
    | Ttuple tes -> Type.Tuple (List.map f tes)
    | Tconstr (Pdot (Pident id,"t",_),[te],_) 
      when (Ident.name id = "List") -> Type.List (f te)
    | Tconstr (Pident id,[te],_) 
      when (Ident.name id = "list") -> Type.List (f te)
    | Tconstr (Pident id,[te],_) 
      when (Ident.name id = "option") -> Type.Option (f te)
    | Tconstr (Pident id,[],_) 
      when (Ident.name id = "string") -> Type.String
    | Tconstr (Pident id,[],_) 
      when (Ident.name id = "int") -> Type.Int
    | Tconstr (Pident id,[],_) 
      when (Ident.name id = "bool") -> Type.Bool
    | Tconstr (Pident id,[],_) 
      when (Ident.name id = "unit") -> Type.Unit
    | Tconstr (Pident id,[],_) 
      when (Ident.name id = "id") -> Type.Id
    | Tlink te -> f te
    | Tconstr (Pdot (Pident id,s,_),[],_)  ->
        let _ = Printf.printf "Unknown Tconstr %s.%s\n" 
                  (Ident.name id) s in
        let _ = Printtyp.type_expr ppf tye  in
          failwith "Unimpl."
    | _ -> 
        let _ = Printf.printf "Unknown type\n" in
        let _ = Printtyp.type_expr ppf tye in
          failwith "Unimpl."

let type_of_tyd ke tyd = let open Types in
  type_of_tye ke {desc=tyd; level=0; id=0}

let _assert env phi = 
  env.phi <- env.phi @&& phi


let stability_asn _R (_stableQ,_Q) = 
  BoolExpr(??_stableQ) 
      @<=> Forall ([Type.St; Type.St; Type.St], fun [stl;stg;stg'] -> 
                      ?&& [b_app(_Q,[??stl;??stg]);
                           b_app(_R,[??stl;??stg;??stg'])]
                  @=> b_app(_Q,[??stl;??stg']))

let read_stability_asn = stability_asn L._Rl
let commit_stability_asn = stability_asn L._Rc

let rec expr_to_native (ve:VE.t) (exp:Typedtree.expression) : Expr.t = 
  let open Expr in 
  match exp.exp_desc with
    (* id *)
    | Texp_ident (path,_,_) -> 
        let names = Path.all_names path in
        let name = String.concat "." names in
          begin
            try ??(List.assoc name pervasives)
            with Not_found -> 
              try VE.find_name name ve
              with Not_found -> 
                ??(Ident.create name)
          end
    (* constant *)
    | Texp_constant const ->
        let open Asttypes in 
          (match const with 
             | Const_int i -> (ConstInt i)
             | Const_string (s, None) -> (ConstString s)
             | Const_string (s, Some s') -> (ConstString (s^s'))
             | _ -> failwith "Texp_constant Unimpl.")
    (* native fn application *)
    | Texp_apply (e1, largs) ->
        let pf = match expr_to_native ve e1 with 
          | Var id -> id | _ -> failwith "expr_to_native: Unexpected" in 
        let e2s = map_snd_opts largs in
        let pargs = List.map (expr_to_native ve) e2s in
          App (pf,pargs)
    (* record field access *)
    | Texp_field (e1,_,ld) -> 
        let pe1 = expr_to_native ve e1 in 
        (* ld must be one of the known accessors *)
        let accessor_id = L.get_accessor ld.lbl_name in
          App (accessor_id,[pe1])
    | Texp_setfield ({exp_desc=Texp_ident (path,x,y)} as e1,loc,ld,e2) -> 
        (* We let x' denote x in the new state. *)
        let new_id = Ident.create @@ (Path.last path)^"'" in
        let id_exp = {e1 with exp_desc=Texp_ident(Path.Pident new_id,x,y)} in
        let e1' = {e1 with exp_desc=Texp_field(id_exp,loc,ld)} in
        let ne1 = expr_to_native ve e1' in
        let ne2 = expr_to_native ve e2 in
          App (L.eq, [ne1;ne2])
    (* e1;e2 *)
    | Texp_sequence (e1,e2) ->
        let ne1 = expr_to_native ve e1 in
        let ne2 = expr_to_native ve e2 in
          (match ne2 with 
            | App (op,ne2s) when op = L.andd -> App (L.andd, ne1::ne2s)
            | _ -> App (L.andd,[ne1;ne2]))
    | _ -> failwith "expr_to_native: Unimpl."

let rec native_to_pred native_exp = 
  let open Ident in 
  let open Expr in 
  let open Predicate in 
  let f = native_to_pred in
    match native_exp with
      | App ({name},nes) when (name = Ident.name L.andd) -> And(List.map f nes)
      | App ({name},nes) when (name = Ident.name L.orr) -> Or (List.map f nes)
      | App ({name},[ne]) when (name = Ident.name L.nott) -> Not (f ne)
      | App ({name},[ne1;ne2]) when (name = Ident.name L.eq) -> Eq (ne1,ne2)
      | App ({name},[ne1;ne2]) when (name = Ident.name L.le) -> LE (ne1,ne2)
      | App ({name},[ne1;ne2]) when (name = Ident.name L.ge) -> GE (ne1,ne2)
      | _ -> BoolExpr native_exp 

let expr_to_pred ve exp = native_to_pred @@ expr_to_native ve exp

let stabilize env (_F:F.t)= 
  let _ = printf "--- to stabilize: %s\n" @@ F.to_string _F in
    _F

(* Returns a stable F.t *)
let rec doIt_letexp env (x,tye) (e1:expression) (e2:expression) : F.t = 
  let _assert = _assert env in
    match e1.exp_desc with 
    (* SQL.select1 *)
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"select1",_),_,_)},
                  [(Asttypes.Nolabel,Some e11); 
                   (Asttypes.Nolabel,Some e12)]) when (Ident.name id = "SQL") -> 
        begin
          match (e11.exp_desc,e12.exp_desc) with
          | (Texp_construct (_,{cstr_name="::"},
                             [{exp_desc=Texp_construct (_,table_cons,[])}; 
                              {exp_desc=Texp_construct (_,{cstr_name="[]"},[])}]), 
             Texp_function (arg_label,[case],_)) -> 
              let _ = printf "SQL.select1\n" in
              (* Predicate describing the record read. *)
              let phi stg r = 
                (* Δ satisfies I *)
                let inv_pred = _I()
                (* r belongs to Δ *)
                let belongs_pred = SIn (r,stg) in
                (* r meets the search criterion... *)
                let ([arg_id],body) = Astutils.extract_lambda case in
                let ve = VE.add arg_id r VE.empty in 
                let select_pred = expr_to_pred ve body in 
                (* ... and r belongs to table t *)
                let t = Ident.create @@ String.lowercase_ascii @@ 
                          table_cons.cstr_name in
                let table_pred = table(r) @== ??t in
                  ?&& [belongs_pred; table_pred; select_pred] in
              (* Analyze e2 assuming  x: { ν:Rec | ∃Δ. Φ(Δ,v)} *)
              let te' = TE.add x Type.Rec env.te in
              let phi' = P.conj env.phi 
                            (_Exists_St1 @@ fun stg -> phi ???stg ??x) in
              let _F2 = doIt_exp {env with te=te'; phi=phi'} e2 in
              (* λ(δ.Δ). exists(x', phi(x'), [x'/x] F2(δ,Δ))*)
              let _F(stl,stg) = 
                SExists (Type.Rec, fun x' -> 
                                    (phi stg ??x', S.subst (??x',x) 
                                                 @@ _F2(stl,stg))) in
              let stable_F = stabilize env _F in
                stable_F
          | (Texp_construct (_,{cstr_name="::"},args), _) ->
              failwith "doIt_valbind: SQL join Unimpl.\n"
          | _ -> failwith "doIt_valbind: SQL.select1 impossible case"
        end
    | _ -> failwith "doIt_letexp: Unimpl.\n"

(* Returns a stable F.t *)
and doIt_exp env (exp:Typedtree.expression) = 
  let _assert = _assert env in
    match exp.exp_desc with
    (* let x = e1 in e2 *)
    | Texp_let (ast_rec, [{vb_pat={pat_desc=Tpat_var (x,_); 
                                   pat_type=tye};
                           vb_expr=e1}], e2) -> 
        doIt_letexp env (x,tye) e1 e2
    | Texp_let (ast_rec, [{vb_pat={pat_desc=Tpat_any};
                           vb_expr=e1}], e2) -> 
        let _F1 = doIt_exp env e1 in
        let _F2 = doIt_exp env e2 in
        let _F(stl,stg) = _F1(stl,stg) @<+> _F2(stl,stg) in
          _F
    | Texp_ifthenelse (grd_e,e1,Some e2) -> 
        let phi = expr_to_pred VE.empty grd_e in
        let _F1 = doIt_exp env e1 in
        let _F2 = doIt_exp env e2 in
        let _F(stl,stg) = SITE(phi, _F1(stl,stg), _F2(stl,stg)) in
          _F
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"update",_),_,_)},
                  [(_,Some e1); (_,Some e2); (_,Some e3)]) 
        when (Ident.name id = "SQL") -> 
        begin
          match (e1.exp_desc, e2.exp_desc, e3.exp_desc) with
          | (Texp_construct (_,table_cons,[]), (* Table being updated *)
             Texp_function (_,[s_case],_), (* SET function g *)
             Texp_function (_,[w_case],_)) (* WHERE function f *) -> 
              let _ = printf "SQL.update table_name g f\n" in
              (* t is the table being updated *)
              let t = Ident.create @@ String.lowercase_ascii @@ 
                        table_cons.cstr_name in
              (* Predicate describing the record updated. *)
              let phi r = 
                (* r meets the search criterion... *)
                let ([y],e2) = Astutils.extract_lambda w_case in
                let where_pred = expr_to_pred 
                                (VE.add y r VE.empty) e2 in 
                (* ... and r belongs to table t *)
                let table_pred = table(r) @== ??t in
                  ?&& [table_pred; where_pred] in
              (* Predicate describing the updataion *)
              let (<~) r' r = 
                (*  r' is updated version of r... *)
                let ([x],e1) = Astutils.extract_lambda s_case in
                let x' = Ident.create @@ (Ident.name x)^"'" in
                let upd_pred = expr_to_pred (VE.add x' r' @@ 
                                             VE.add x r VE.empty) e1 in 
                (* ... but r and r' both belongs to the same table *)
                let table_pred = table(r') @== table(r) in
                  ?&& [table_pred; upd_pred] in
              let bind_f r = SITE(phi(??r), 
                                  SLit (fun r' -> ??r' <~ ??r),
                                  SConst [??r]) in
              let _F(stl,stg) = SBind (stg,bind_f) in
              let stable_F = stabilize env _F in
                stable_F (* compile and see *)
          | _ -> failwith "doIt_exp: SQL.update impossible case"
        end
    (* e1;e2 *)(* same as let _ = e1 in e2 *)
    | Texp_sequence (e1,e2) ->
        let _F1 = doIt_exp env e1 in
        let _F2 = doIt_exp env e2 in
        let _F(stl,stg) = _F1(stl,stg) @<+> _F2(stl,stg) in
          _F
    (* () *)
    | Texp_construct (_,{cstr_name="()"}, []) -> fun _ -> SConst []
    (* unsupported *)
    | _ ->
        let _ = Printtyped.expression 0 (Format.std_formatter) exp in 
          failwith "doIt_exp: Unimpl."

let doIt_txn env (Fun.T txn_fn) (Spec.Txn txn) =
  let _ = printf "-------------------------------------\n" in
  let _ = printf "   Analyzing %s ...\n" txn.name in
  let _ = printf "-------------------------------------\n" in
  (*let init_phi = env.phi in*)
  let iso_spec = Isolation.spec_of txn.iso in
  (* Phi <- Phi /\ iso_spec *)
  let _ = env.phi <- env.phi @&& iso_spec in
  let _G = txn.guarantee in
  (* Start analyzing the txn function *)
  (* TE[arg_i :-> arg_i_T]*) 
  let _ = env.te <- List.fold_left 
                      (fun te (arg_id,arg_tyd) -> 
                         TE.add arg_id (type_of_tyd env.ke arg_tyd) te) 
                      env.te txn_fn.args_t in
  (* (Θ,Γ,Φ) |- txn_fn.body ⇒ F *)
  let _F = doIt_exp env txn_fn.body in
(*
  let _assert = _assert env in
  (* Q must be stable w.r.t Rc *)
  let _stableQ = Ident.create @@ "cstable"^(Ident.name _Q) in
  let _ = env.te <- TE.add _stableQ Type.Bool env.te in
  let _ = _assert @@ commit_stability_asn(_stableQ,_Q) in
  let _ = env.vcs <- _stableQ::env.vcs in
  (* ∀(σl,σg). Q(σl,σg) => G(σl>>σg,σg) *)
  (* ∀(σ,σ'). I(σ) ∧ G(σ,σ') => I(σ') *)
  let _soundG = Ident.create @@ "sound"^(Ident.name _G) in
  let _ = env.te <- TE.add _soundG Type.Bool env.te in
  let fa_asn1 = _Forall_St3 @@ fun (stl,stg,st) ->
    ?&&[b_app(_Q,[??stl;??stg]); flush(??stl,??stg,??st)] 
          @=> b_app(_G,[??st; ??stg]) in
  let fa_asn2 = _Forall_St2 @@ fun (stg,stg') ->
        (b_app(_I,[??stg]) @&& b_app(_G,[??stg;??stg'])) 
              @=> b_app(_I,[??stg']) in
  let _ = _assert @@ 
          BoolExpr(??_soundG) @<=> ?&& [fa_asn1; fa_asn2] in
  let _ = env.vcs <- _soundG::env.vcs in
  let _ = print_env env in
  let _ = Z3E.doIt (env.ke,env.te,env.phi) env.vcs in
 *)
    ()

let doIt (ke,te,phi) (App.T app) (Spec.T spec) = 
  let spec_of_txn (Fun.T {name}) = 
    List.find (fun (Spec.Txn txn_spec) -> 
                 txn_spec.name = Ident.name name) spec.txns in
  (* Fixme :remove this *)
  let txns = [List.hd @@ List.rev app.txns] in
  let _ = List.iter (fun txn -> 
                       let env = {txn=Fun.name txn; ke=ke; 
                                  te=te; phi=phi} in
                         doIt_txn env txn (spec_of_txn txn)) txns in
    failwith "Unimpl."

