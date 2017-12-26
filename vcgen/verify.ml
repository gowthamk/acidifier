open Utils
open Types
open Typedtree
open Speclang
open Specelab
module P = Predicate
module E = Expr
module F = StateTransformer
module Z3E = Z3encode
open P
let _F (s1,s2) = failwith "Use P._F to refer to L._F application"
open E


module VE = Light_env.Make(struct 
                             type t = some_expr
                             let to_string = function
                               | SomeExpr e -> E.to_string e
                               | _ -> failwith "VE.S.to_string: impossible!"
                           end)

type env = {txn: Ident.t; 
            mutable ke: KE.t; 
            mutable te: TE.t;
            mutable ve: VE.t;
            mutable phi: P.t;
            mutable _Fc: F.t}

let some t = SomeType t 
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

let (fresh_stg_name, stg_reset) = gen_name "stg" 
let fresh_stg () = Ident.create @@ fresh_stg_name ()

 let rec type_of_tye ke (tye : type_expr) : some_type= 
  let open Path in
  let ppf = Format.std_formatter in
  let strf = Format.str_formatter in
  (* Higher-rank polymorphism is needed to realize this:
  let f: type b. type_expr -> (type a. a Type.t -> b Type.t) 
        -> b Type.t =
      fun tye g -> let SomeType t = type_of_tye ke tye 
                     in g t in *)
  let f = type_of_tye ke in 
  let open Type in 
  let is_table_name str = 
    try
      match KE.find_name (Type.to_string Table) ke with
      | Kind.Variant cons -> List.exists (fun c -> 
                                Cons.name c = str) cons
      | Kind.Enum tags -> List.exists (fun t -> 
                                Ident.name t = str) tags
      | _ -> false
    with Not_found -> false in
    match tye.desc with
    | Tvar aop -> 
        let a_name = Astutils.mk_tvar_name aop tye.id in
        let msg = sprintf "Kind of %s not found" a_name in
        let knd = try KE.find_name a_name ke 
                  with Not_found -> not_found msg in
          (match knd with | Kind.Alias typ -> SomeType typ
            | _ -> failwith "type_of_tye: Unexpected")
    | Tarrow (_,te1,te2,_) -> 
        let (SomeType t1, SomeType t2) = (f te1, f te2) in
          SomeType (Arrow (t1, t2))
    | Ttuple [te1;te2] -> 
        let (SomeType t1, SomeType t2) = (f te1, f te2) in
          SomeType (Pair (t1,t2))
    | Ttuple [te1;te2;te3] -> 
        let (SomeType t1, SomeType t2, SomeType t3) = 
            (f te1, f te2, f te3) in
          SomeType (Triple (t1,t2,t3))
    | Tconstr (Pdot (Pident id,"t",_),[te],_) 
      when (Ident.name id = "List") -> 
        let SomeType t = f te in SomeType (List t)
    | Tconstr (Pident id,[te],_) 
      when (Ident.name id = "list") -> 
        let SomeType t = f te in SomeType (List t)
    | Tconstr (Pident id,[te],_) 
      when (Ident.name id = "option") -> 
        let SomeType t = f te in SomeType (Option t)
    | Tconstr (Pident id,[],_) 
      when (Ident.name id = "string") -> SomeType (String)
    | Tconstr (Pident id,[],_) 
      when (Ident.name id = "int") -> SomeType (Int)
    | Tconstr (Pident id,[],_) 
      when (Ident.name id = "bool") -> SomeType (Bool)
    | Tconstr (Pident id,[],_) 
      when (Ident.name id = "unit") -> SomeType (Unit)
    | Tconstr (Pident id,[],_) 
      when (Ident.name id = "id") -> SomeType (Id)
    | Tlink te -> f te
    | Tconstr (Pident id,[],_) 
      when (is_table_name @@ Ident.name id) -> SomeType (Rec)
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


(*
let stability_asn _R (_stableQ,_Q) = 
  Expr(_stableQ) 
      @<=> _Forall_St3 @@ fun (stl,stg,stg') ->
                      ?&& [b_app(_Q,[??stl;??stg]);
                           b_app(_R,[??stl;??stg;??stg'])]
                  @=> b_app(_Q,[??stl;??stg'])

let read_stability_asn = stability_asn L._Rl
let commit_stability_asn = stability_asn L._Rc
*)

let rec expr_to_native env (exp:Typedtree.expression)
    : some_expr = 
  let open Expr in 
  match exp.exp_desc with
    (* id *)
    | Texp_ident (path,_,_) -> 
        let names = Path.all_names path in
        let name = String.concat "." names in
          begin
            try VE.find_name name env.ve
            with Not_found -> 
              try let SomeType t = TE.find_name name env.te in
                  SomeExpr (var (Ident.create name, t))
              with Not_found ->
                failwith @@ "Unknown identifier: "^name
          end
    (* constant *)
    | Texp_constant const ->
        let open Asttypes in 
          (match const with 
             | Const_int i -> SomeExpr (Const(Type.Int,i))
             | Const_string (s, None) -> 
                  SomeExpr (Const(Type.String,s))
             | Const_string (s, Some s') -> 
                  SomeExpr (Const(Type.String,s^s'))
             | _ -> failwith "Texp_constant Unimpl.")
    (* native fn application *)
    | Texp_apply ({exp_desc=Texp_ident (path,_,_)}, largs) ->
        let names = Path.all_names path in
        let name = String.concat "." names in
        let op_id = List.assoc name pervasives in
        let e2s = map_snd_opts largs in
        let nes = List.map (expr_to_native env) e2s in
        let SomeType ty = type_of_tye env.ke exp.exp_type in
          SomeExpr (App2 (op_id,nes,ty))
    (* record field access *)
    | Texp_field (e1,_,ld) -> 
        let SomeExpr pe1 = expr_to_native env e1 in 
        (* ld must be one of the known accessors *)
        let accessor_id = L.get_accessor ld.lbl_name in
        let SomeType ty = type_of_tye env.ke exp.exp_type in
          SomeExpr (App (accessor_id,[pe1],ty))
    | Texp_setfield ({exp_desc=Texp_ident (path,x,y)} as e1, 
                     loc,ld, e2) -> 
        (* We let x' denote x in the new state. *)
        let new_id = Ident.create @@ (Path.last path)^"'" in
        let id_exp = {e1 with exp_desc = 
                                Texp_ident(Path.Pident new_id,x,y)} in
        let e1' = {e1 with exp_desc=Texp_field(id_exp,loc,ld)} in
        let SomeExpr (App (_,_,t1) as ne1) = expr_to_native env e1' in
        let SomeExpr ne2 = expr_to_native env e2 in
          SomeExpr (App (L.eq, [ne1; Expr.type_cast ne2 t1],
                         Type.Bool))
    (* a sequence of setfields *)
    | Texp_sequence (e1,e2) ->
        let SomeExpr ne1 = expr_to_native env e1 in
        let SomeExpr ne2 = expr_to_native env e2 in
          (match ne1, ne2 with 
            | App (_,_,Type.Bool), App (op,ne2s,Type.Bool) 
              when op = L.andd -> 
                let ne2s' = List.map (fun e -> Expr.type_cast e
                                         Type.Bool) ne2s in
                SomeExpr (App (L.andd, ne1::ne2s', Type.Bool))
            | App (_,_,Type.Bool), App (_,_,Type.Bool) -> 
                SomeExpr (App (L.andd, [ne1; ne2], Type.Bool))
            | _ -> failwith "expr_to_native: Unexpected")
    | _ -> failwith "expr_to_native: Unimpl."

let rec native_to_pred: bool expr -> pred = fun native_exp ->
  let open Ident in 
  let open Expr in 
  let open Predicate in 
  let f e = native_to_pred @@ type_cast e Type.Bool in
  let to_int e = type_cast e Type.Int in
    match native_exp with
      | App ({name},nes,_) when (name = Ident.name L.andd) -> 
          And (List.map f nes)
      | App ({name},nes,_) when (name = Ident.name L.orr) -> 
          Or (List.map f nes)
      | App ({name},[ne],_) when (name = Ident.name L.nott) -> 
          Not (f ne)
      | App ({name},[ne1;ne2],_) when (name = Ident.name L.eq) -> 
          Eq (ne1,ne2)
      | App ({name},[ne1;ne2],_) when (name = Ident.name L.le) -> 
          LE (to_int ne1, to_int ne2)
      | App ({name},[ne1;ne2],_) when (name = Ident.name L.ge) -> 
          GE (to_int ne1, to_int ne2)
      | _ -> Expr native_exp

let expr_to_pred env exp = 
  let SomeExpr ne = expr_to_native env exp in
    native_to_pred @@ Expr.type_cast ne Type.Bool

let stabilize env rc (_F:F.t)= 
  let _ = printf "--- to stabilize: %s\n" @@ F.to_string _F in
  let _Fc = env._Fc in
  let (d,_R) = match rc with 
    | `Read -> (false,_Rl)
    | `Commit -> (true,_Rc) in
  let psi = _Forall_St3 @@ fun (stl,stg,stg') -> 
    let ante = ?&& [_I(stg); _I(stg'); (*I(Δ) ∧ I(Δ')*)
                    stl @== _Fc(stg); 
                    _R(stl,stg,stg')] in 
    let conseq = _F(stg) @== _F(stg') in 
      ante @=> conseq in
  let res = Z3E.check_validity (env.ke, env.te, env.phi) psi d in
  let _stable_F = match res with 
    | UNSATISFIABLE -> _F 
    | _ -> (* Ignore Δ in favor of a Skolem Δ'*)
      let stg' = fresh_stg () in
      let _ = env.te <- TE.add stg' (some Type.St) env.te in
      let _ = env.phi <- ?&& [env.phi; _I(state_var stg')] in 
        fun _ -> _F(state_var stg') in
    _stable_F

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
              let phi r = 
                (* r meets the search criterion... *)
                let ([arg_id],body) = Astutils.extract_lambda case in
                let env' = {env with ve = VE.add arg_id 
                                         (SomeExpr r) VE.empty} in 
                let where_pred = expr_to_pred env' body in 
                (* ... and r belongs to table t *)
                let t = Expr.table_name @@ String.lowercase_ascii @@ 
                          table_cons.cstr_name in
                let table_pred = table(r) @== t in
                  ?&& [table_pred; where_pred] in
              let bind_f r = SITE(phi(r), 
                                  SConst [r],
                                  SConst []) in
              (* _F1(Δ) is the (stable) result of SELECT on Δ *)
              let _F1 = stabilize env `Read @@ 
                          fun stg -> _SBind stg bind_f in
              (* Let-bound x: Rec becomes global. Conservative w.r.t
               * stability; sound nonetheless. *)
              let _ = env.te <- TE.add x (some Type.Rec) env.te in
              (* _Fc for e2 is same for e since δ hasn't been updated *)
              let _F2 = doIt_exp env e2 in
              (* _F = λ(Δ).IF (x ∈ F1(Δ)) THEN F2(Δ) ELSE ∅ *)
              let _F(stg) = SITE (record(x) @: _F1(stg),
                                  _F2(stg), 
                                  _SConst []) in
                _F
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
        let open F in
        let _F1 = doIt_exp env e1 in
        let _Fc' = env._Fc @<+> _F1 in
        let _F2 = doIt_exp {env with _Fc = _Fc'} e2 in
          _F1 @<+> _F2
    | Texp_ifthenelse (grd_e,e1,Some e2) -> 
        let phi = expr_to_pred env grd_e in
        let _F1 = doIt_exp env e1 in
        let _F2 = doIt_exp env e2 in
        let _F(stg) = SITE(phi, _F1(stg), _F2(stg)) in
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
              let t = table_name @@ String.lowercase_ascii @@ 
                        table_cons.cstr_name in
              (* Predicate describing the record updated. *)
              let phi r = 
                (* r meets the search criterion... *)
                let ([y],e2) = Astutils.extract_lambda w_case in
                let env' = {env with ve=VE.add y 
                                         (SomeExpr r) env.ve} in
                let where_pred = expr_to_pred env' e2 in 
                (* ... and r belongs to table t *)
                let table_pred = table(r) @== t in
                  ?&& [table_pred; where_pred] in
              (* Predicate describing the updataion *)
              let (<~) r' r = 
                (*  r' is updated version of r... *)
                let ([x],e1) = Astutils.extract_lambda s_case in
                let x' = Ident.create @@ (Ident.name x)^"'" in
                let env' = {env with ve = VE.add x' (SomeExpr r') @@ 
                                      VE.add x (SomeExpr r) env.ve} in
                let upd_pred = expr_to_pred env' e1 in 
                (* ... but r and r' both belongs to the same table *)
                let table_pred = table(r') @== table(r) in
                  ?&& [table_pred; upd_pred] in
              let bind_f r = SITE(phi(r), 
                                  _SLit (fun r' -> r' <~ r),
                                  SConst []) in
              let _F(stg) = _SBind stg bind_f in
              (* _F must be checked stable under δ=_Fc'(Δ) *)
              let _Fc' = let open F in env._Fc @<+> _F in
              let stable_F = stabilize {env with _Fc = _Fc'} 
                              `Read _F in
                stable_F 
          | _ -> failwith "doIt_exp: SQL.update impossible case"
        end
    (* e1;e2 *)(* same as let _ = e1 in e2 *)
    | Texp_sequence (e1,e2) ->
        let open F in
        let _F1 = doIt_exp env e1 in
        let _Fc' = env._Fc @<+> _F1 in
        let _F2 = doIt_exp {env with _Fc = _Fc'} e2 in
          _F1 @<+> _F2
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
  (* δ = F(Δ) when committing *)
  let _ = stabilize {env with _Fc = _F} `Commit _F in
  let _ = printf "Hello\n" in
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
                                  te=te; phi=phi; ve=VE.empty;
                                  _Fc=F.empty} in
                         doIt_txn env txn (spec_of_txn txn)) txns in
    failwith "Unimpl."

