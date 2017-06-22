open Utils
open Types
open Typedtree
open Speclang
open Specelab
module P = Predicate
module Z3E = Z3encode
open P

module VE = Light_env.Make(struct 
                             include Speclang.Expr 
                           end)

let (fresh_Q_name, _) = gen_name "Q"
let (fresh_U_name, _) = gen_name "U"

type env = {txn: Ident.t; 
            mutable ke: KE.t; 
            mutable te: TE.t; 
            mutable phi: P.t; 
            mutable vcs: Ident.t list;}

let printf = Printf.printf
let sprintf = Printf.sprintf
let ppf = Format.std_formatter
let not_found msg = (Printf.printf "%s\n" msg; raise Not_found)
let map_snd_opts = List.map (function (_,Some x) -> x
                               | _ -> failwith "Unexpected")
let ty2 = Type.Arrow (Type.Tuple [Type.St; Type.St], Type.Bool)
let ty3 = Type.Arrow (Type.Tuple [Type.St; Type.St;Type.St], Type.Bool)

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
    printf "------- VCs ------\n";
    printf "[%s]\n" @@ String.concat ", " 
      @@ List.map Ident.name env.vcs
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
      let a_name = Misc.mk_tvar_name aop tye.id in
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

let doIt_valbind env (lhs_id,lhs_tye,rhs_exp) _P = 
  (*let ty = type_of_tye env.ke lhs_tye in
  let _ = env.te <- TE.add lhs_id ty env.te in
  let _ = print_env env in*)
  let _ = printf "doIt_valbind" in
  let _assert = _assert env in
    match rhs_exp.exp_desc with 
    (* SQL.select1 *)
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"select1",_),_,_)},
                  [(Asttypes.Nolabel,Some e1); 
                   (Asttypes.Nolabel,Some e2)]) when (Ident.name id = "SQL") -> 
        begin
          match (e1.exp_desc,e2.exp_desc) with
          | (Texp_construct (_,{cstr_name="::"},
                             [{exp_desc=Texp_construct (_,table_cons,[])}; 
                              {exp_desc=Texp_construct (_,{cstr_name="[]"},[])}]), 
             Texp_function (arg_label,[case],_)) -> 
              let _ = printf "SQL.select1 table_name fun\n" in
              (* TE[lhs_id :-> Type.Rec] *)
              let _ = env.te <- TE.add lhs_id Type.Rec env.te in
              let table_name = Ident.create @@ String.lowercase_ascii @@ 
                               table_cons.cstr_name in
              (* table(lhs_id) = table_name *)
              let _ = _assert (table(??lhs_id) @== ??table_name) in
              (* lhs_id meets the search criterion (i.e., f(lhs_id)=true)*)
              let ([arg_id],body) = Misc.extract_lambda case in
              let ve = VE.add arg_id ??lhs_id VE.empty in 
              let select_pred = expr_to_pred ve body in 
              (* Q(σl,σg) <=> P(σl,σg) /\ f(lhs_id) /\
               *              ∃(l:Loc). l∈dom(σl>>σg) /\ value(σl>>σg,l) = lhs_id*)
              (* Caution: the last conjunct may need weakening for
               * it to be stable. *)
              let _Q = Ident.create @@ fresh_Q_name () in
              let _ = env.te <- TE.add _Q ty2 env.te in 
              let ex_asn st= Exists ([Type.Loc], function [l] -> 
                               ?&& [??l @: dom(st); 
                                    value(st,??l) @== ??lhs_id]) in
              let asn (stl,stg) = 
                b_app(_Q,[??stl;??stg]) @<=> ?&& [b_app(_P,[??stl;??stg]); 
                                                  select_pred;
                                                  ex_asn (??stl @>> ??stg)] in
              let _ = _assert @@ _Forall_St2 asn in
              (* stability of _Q *)
              let _stableQ = Ident.create @@ "rstable"^(Ident.name _Q) in
              let _ = env.te <- TE.add _stableQ Type.Bool env.te in
              let _ = _assert @@ read_stability_asn(_stableQ,_Q) in
              let _ = env.vcs <- _stableQ::env.vcs in
                _Q
          | (Texp_construct (_,{cstr_name="::"},args), _) ->
              failwith "doIt_valbind: SQL join Unimpl.\n"
          | _ -> failwith "doIt_valbind: SQL.select1 impossible case"
        end
    | _ -> failwith "doIt_valbind: Unimpl.\n"

let rec doIt_exp env (exp:Typedtree.expression) _P = 
  let _assert = _assert env in
    match exp.exp_desc with
    (* let id = e1 in e2 *)
    | Texp_let (ast_rec, [{vb_pat={pat_desc=Tpat_var (lhs_id,_); 
                                   pat_type=lhs_tye};
                           vb_expr=e1}], e2) -> 
        let _Q = doIt_valbind env (lhs_id,lhs_tye,e1) _P in
          doIt_exp env e2 _Q
    | Texp_let (ast_rec, [{vb_pat={pat_desc=Tpat_any};
                           vb_expr=e1}], e2) -> 
        let _Q = doIt_exp env e1 _P in
          doIt_exp env e2 _Q
    | Texp_ifthenelse (grd_e,e1,Some e2) -> 
        let grd_p = expr_to_pred VE.empty grd_e in 
        let (_P1,_P2) = (Ident.create @@ fresh_Q_name (), 
                         Ident.create @@ fresh_Q_name ()) in
        let _ = env.te <- TE.add _P2 ty2 (TE.add _P1 ty2 env.te) in
            (* P1 = P /\ grd_p *)
        let _ = _assert @@ _Forall_St2 @@ fun (stl,stg) -> 
            b_app(_P1,[??stl;??stg]) @<=> ?&& [b_app(_P,[??stl;??stg]); grd_p] in
            (* P2 = P /\ ~grd_p *)
        let _ = _assert @@ _Forall_St2 @@ fun (stl,stg) -> 
            b_app(_P2,[??stl;??stg]) @<=> ?&& [b_app(_P,[??stl;??stg]); 
                                               P.Not grd_p] in
        let _Q1 = doIt_exp env e1 _P1 in
        let _Q2 = doIt_exp env e2 _P2 in 
        (* Q = Q1 \/ Q2 *)
        let _Q = Ident.create @@ fresh_Q_name () in
        let _ = env.te <- TE.add _Q ty2 env.te in
        let _ = _assert @@ _Forall_St2 (fun (stl,stg) -> let a = [??stl;??stg] in
                    b_app(_Q,a) @<=> ?|| [b_app(_Q1,a); b_app(_Q2,a)]) in
          (* stableQ1 and stableQ2 are already VCs. stableQ follows. *)
          _Q
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"update",_),_,_)},
                  [(_,Some e1); (_,Some e2); (_,Some e3)]) 
        when (Ident.name id = "SQL") -> 
        begin
          match (e1.exp_desc, e2.exp_desc, e3.exp_desc) with
          | (Texp_construct (_,table_cons,[]), (* Table being updated *)
             Texp_function (_,[s_case],_), (* SET function g *)
             Texp_function (_,[w_case],_)) (* WHERE function f *) -> 
              let _ = printf "SQL.update table_name g f\n" in
              let _U = Ident.create @@ fresh_U_name () in
              (* TE[_U :-> St*St*St -> Bool]*)
              let _ = env.te <- TE.add _U ty3 env.te in
              let u_def stg stl stl' l = 
                let st = flush(??stl,??stg) in
                let r_in_st = value(st,??l) in
                (* r_in_st meets the search criterion (i.e.,
                 * f(value(flush(σl,σg),l))=true)*)
                let ([w_arg],w_body) = Misc.extract_lambda w_case in
                let w_pred = expr_to_pred 
                                (VE.add w_arg r_in_st VE.empty) w_body in 
                let tname = Ident.create @@ String.lowercase_ascii @@ 
                              table_cons.cstr_name in
                (* grd_pred <=> l∈dom(flush(σl,σg)) 
                 *              /\ table(value(flush(σl,σg),l)) = table_name 
                 *              /\ f(value(flush(σl,σg),l)) *)
                let grd_pred = ?&&[??l @: dom(st); 
                                   table(value(st,??l)) @== ??tname; 
                                   w_pred] in
                let r_in_stl' = value(??stl',??l) in
                let ([old_r],s_body) = Misc.extract_lambda s_case in
                (* x :-> (σl>>σg)(l) => x' :-> σl'(l) *)
                let new_r = Ident.create @@ (Ident.name old_r)^"'" in
                let s_pred = expr_to_pred (VE.add new_r r_in_stl' @@ 
                                           VE.add old_r r_in_st VE.empty) s_body in 
                (* mod_pred <=> l∈dom(σl') /\ g(value(σl',l)) *)
                let mod_pred = (??l @: dom(??stl')) @&& s_pred in
                (* inv_pred <=> IF l∈dom(σl) 
                 *              THEN l∈dom(σl') /\ value(σl',l) = value(σl,l) 
                 *              ELSE ~(l∈dom(σl')) *)
                let inv_pred = ITE (??l @: dom(??stl), 
                                    ?&& [??l @: dom(??stl'); 
                                         value(??stl',??l) @== value(??stl,??l)], 
                                    Not (??l @: dom(??stl'))) in
                  ITE(grd_pred, mod_pred, inv_pred) in
              (* Define _U *)
              let _U_def = _Forall_St3 @@ fun (stg,stl,stl') ->
                  b_app(_U,[??stg;??stl;??stl']) 
                            @<=> _Forall_L1 @@ u_def stg stl stl' in
              let _ = _assert _U_def in
              (* Q(σl',σg) <=> ∃σl. P(σl,σg) /\ _U(σg,σl,σl')*)
              let _Q = Ident.create @@ fresh_Q_name () in
              let _ = env.te <- TE.add _Q ty2 env.te in 
              let ex_asn stl' stg stl = ?&& [b_app(_P,[??stl;??stg]); 
                                             b_app(_U,[??stg;??stl;??stl'])] in
              let asn (stl',stg) = 
                b_app(_Q,[??stl';??stg]) @<=> _Exists_St1 (ex_asn stl' stg) in
              let _ = _assert @@ _Forall_St2 asn in
              (* stability of _Q *)
              let _stableQ = Ident.create @@ "rstable"^(Ident.name _Q) in
              let _ = env.te <- TE.add _stableQ Type.Bool env.te in
              let _ = _assert @@ read_stability_asn(_stableQ,_Q) in
              let _ = env.vcs <- _stableQ::env.vcs in
                _Q
          | _ -> failwith "doIt_exp: SQL.update impossible case"
        end
    (* e1;e2 *)
    | Texp_sequence (e1,e2) ->
        let _Q1 = doIt_exp env e1 _P in
        let _Q2 = doIt_exp env e2 _Q1 in
          _Q2
    (* () *)
    | Texp_construct (_,{cstr_name="()"}, []) -> _P
    (* unsupported *)
    | _ ->
        let _ = Printtyped.expression 0 (Format.std_formatter) exp in 
          failwith "doIt_exp: Unimpl."

let doIt_txn env (Fun.T txn_fn) (Spec.Txn txn) _I =
  let _ = printf "-------------------------------------\n" in
  let _ = printf "   Analyzing %s ...\n" txn.name in
  let _ = printf "-------------------------------------\n" in
  (*let init_phi = env.phi in*)
  let iso_spec = Isolation.specification_of txn.iso in
  (* Phi <- Phi /\ iso_spec *)
  let _ = env.phi <- env.phi @&& iso_spec in
  let _G = txn.guarantee in
  let _P = Ident.create @@ fresh_Q_name () in
  (* TE[_P :-> Type.St*Type.St -> Type.Bool] *)
  let _ = env.te <- TE.add _P ty2 env.te in
  (* Phi <- Phi /\ (_P(stl,stg) <=> (dom(stl)=empty) /\ I(stg))*)
  let _P_def = Forall ([Type.St; Type.St], 
                function [stl; stg] -> b_app(_P,[??stl;??stg]) @<=> 
                  ?&& [dom(??stl) @== ??(L.empty); 
                       b_app(_I,[??stg])]) in
  let _ = env.phi <- env.phi @&& _P_def in
  (* Start analyzing the txn function *)
  (* TE[arg_i :-> arg_i_T]*) 
  let _ = env.te <- List.fold_left 
                      (fun te (arg_id,arg_tyd) -> 
                         TE.add arg_id (type_of_tyd env.ke arg_tyd) te) 
                      env.te txn_fn.args_t in
  (* {P,env} txn_fn.body {Q,env'} *)
  let _Q = doIt_exp env txn_fn.body _P in
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
  let fa_asn1 = _Forall_St2 @@ fun (stl,stg) ->
    b_app(_Q,[??stl;??stg]) @=> b_app(_G,[??stl @>> ??stg; ??stg]) in
  let fa_asn2 = _Forall_St2 @@ fun (stg,stg') ->
        (b_app(_I,[??stg]) @&& b_app(_G,[??stg;??stg'])) 
              @=> b_app(_I,[??stg']) in
  let _ = _assert @@ 
          BoolExpr(??_soundG) @<=> ?&& [fa_asn1; fa_asn2] in
  let _ = env.vcs <- _soundG::env.vcs in
  let _ = print_env env in
  let _ = Z3E.doIt (env.ke,env.te,env.phi) env.vcs in
    ()

let doIt (ke,te,phi) (App.T app) (Spec.T spec) = 
  let _I = spec.invariant in
  let spec_of_txn (Fun.T {name}) = 
    List.find (fun (Spec.Txn txn_spec) -> 
                 txn_spec.name = Ident.name name) spec.txns in
  (* Fixme :remove this *)
  let txns = [List.hd @@ List.rev app.txns] in
  let _ = List.iter (fun txn -> 
                       let env = {txn=Fun.name txn; ke=ke; 
                                  te=te; phi=phi; vcs=[]} in
                         doIt_txn env txn (spec_of_txn txn) _I) txns in
    failwith "Unimpl."

