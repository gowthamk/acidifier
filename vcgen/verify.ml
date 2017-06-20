open Utils
open Types
open Typedtree
open Speclang
open Specelab
module P = Predicate
open P

let fresh_Q_name = gen_name "Q"

type env = {txn: Ident.t; 
            mutable ke: KE.t; 
            mutable te: TE.t; 
            mutable phi: P.t; 
            mutable vcs: Ident.t list;}

let printf = Printf.printf
let sprintf = Printf.sprintf
let ppf = Format.std_formatter
let not_found msg = (Printf.printf "%s\n" msg; raise Not_found)
let ty2 = Type.Arrow (Type.Tuple [Type.St; Type.St], Type.Bool)

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
  let _ = Printtyp.type_expr strf tye in
  let _ = printf "of_tye(%s)\n" @@ 
            Format.flush_str_formatter () in
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

let read_stability_def(_stableQ,_Q) = 
  BoolExpr(??_stableQ) 
      @<=> Forall ([Type.St; Type.St; Type.St], fun [stl;stg;stg'] -> 
                      ?&& [b_app(_Q,[??stl;??stg]);
                           b_app(L._Rl,[??stl;??stg;??stg'])]
                  @=> b_app(_Q,[??stl;??stg']))

let doIt_valbind env (lhs_id,lhs_tye,rhs_exp) _P = 
  (*let ty = type_of_tye env.ke lhs_tye in
  let _ = env.te <- TE.add lhs_id ty env.te in
  let _ = print_env env in*)
  let _ = printf "doIt_valbind" in
  let _assert = _assert env in
    match rhs_exp.exp_desc with 
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"select1",_),_,_)},
                  [(Asttypes.Nolabel,Some e1); 
                   (Asttypes.Nolabel,Some e2)]) when (Ident.name id = "SQL") -> 
        begin
          (* It is clear now that the type of lhs is Type.Rec. *)
          match (e1.exp_desc,e2.exp_desc) with
          | (Texp_construct (_,{cstr_name="::"},
                             [{exp_desc=Texp_construct (_,table_cons,[])}; 
                              {exp_desc=Texp_construct (_,{cstr_name="[]"},[])}]), 
             Texp_function (arg_label,cases,_)) -> 
              let _ = printf "SQL.select1 table_name fun\n" in
              (* TE[lhs_id :-> Type.Rec] *)
              let _ = env.te <- TE.add lhs_id Type.Rec env.te in
              let table_name = Ident.create @@ String.lowercase_ascii @@ 
                               table_cons.cstr_name in
              (* table(lhs_id) = table_name *)
              let _ = _assert (table(??lhs_id) @== ??table_name) in
              (* Q(σl,σg) <=> P(σl,σg) /\ 
               *               ∃(l:Loc). l∈dom(σg) /\ value(σg,l) = lhs_id*)
              let _Q = Ident.create @@ fresh_Q_name () in
              let _ = env.te <- TE.add _Q ty2 env.te in 
              let exists_l_in stg= Exists ([Type.Loc], 
                                    function [l] -> 
                                      ?&& [??l @: dom(??stg); 
                                           value(??stg,??l) @== ??lhs_id]) in
              let asn (stl,stg) = 
                b_app(_Q,[??stl;??stg]) @<=> ?&& [b_app(_P,[??stl;??stg]); 
                                                  exists_l_in stg] in
              let _ = _assert @@ Forall ([Type.St; Type.St], 
                                         fun [stl;stg] -> asn (stl,stg)) in
              (* stability of _Q *)
              let _stableQ = Ident.create @@ "stable"^(Ident.name _Q) in
              let _ = _assert @@ read_stability_def(_stableQ,_Q) in
              let _ = env.vcs <- _stableQ::env.vcs in
              let _ = print_env env in
                failwith "Unimpl."
          | (Texp_construct (_,{cstr_name="::"},args), _) ->
              failwith "doIt_valbind: SQL join Unimpl.\n"
          | _ -> failwith "doIt_valbind: SQL.select1 impossible case"
        end
    | _ -> failwith "doIt_valbind: Unimpl.\n"

let rec doIt_exp env (exp:Typedtree.expression) _P = 
  let _ = print_env env in
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
    | _ -> failwith "doIt_exp: Unimpl."

let doIt_txn env (Fun.T txn_fn) (Spec.Txn txn) _I =
  let _ = printf "-------------------------------------\n" in
  let _ = printf "   Analyzing %s ...\n" txn.name in
  let _ = printf "-------------------------------------\n" in
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

