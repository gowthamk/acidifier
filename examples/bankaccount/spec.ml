open Speclang
module E = Expr
module P = Predicate
module S = Set
open E
open P
open S

type txn = Txn of {name: string; 
                   guarantee: Ident.t; 
                   iso: Isolation.t}

type t = T of {txns: txn list;
               asserts: P.t list}

let id (x) = App (L.get_accessor "id", [x], Type.Id)
let name (x) = App (L.get_accessor "name", [x], Type.String)
let cbal (x) = App (L.get_accessor "cbal", [x], Type.Int)
let sbal (x) = App (L.get_accessor "sbal", [x], Type.Int)
let user_account = Var (Ident.create "user_account", Type.Table)

let withdraw_G: state expr * state expr -> pred = fun (st,st') ->
  _Exists2 (Type.Id,Type.Int) @@ fun (i,amt) -> 
    st' @== (st @>>= fun x -> 
                      let t_set = _SLit @@ 
                        fun x' -> 
                            ?&& [id(x') @== id(x);
                                  name(x') @== name(x);
                                  sbal(x') @== sbal(x);
                                  table(x') @== table(x);
                                  cbal(x') @== (cbal(x) @- amt)] in
                      let f_set = _SConst [x] in 
                        SITE (?&& [id(x) @== i; 
                                   cbal(x) @>= amt], 
                              t_set, f_set))

let deposit_G (st,st') = st' @== st

let save_G (st,st') = st' @== st
  (*Exists ([Type.Rec], 
          function [l] ->     
            (?&& [??l @: ??st;
                  dom_eq(??st',??st);
                  table(value(??st,??l)) @== user_account;
                  table(value(??st',??l)) @== user_account; 
                  id(value(??st',??l)) @== id(value(??st,??l));
                  sbal(value(??st',??l)) @>= ConstInt(0);
                  cbal(value(??st',??l)) @>= ConstInt(0);
                  Forall ([Type.loc], function [l'] ->
                            (??l' @!= ??l) @=> 
                                (value(??st',??l') @== value(??st,??l')))])) *)

let inv (st) = 
  _Forall_Rec1 @@ function (r)->
        (r @: st) @=> ?&& [cbal(r) @>= !! 0; 
                               sbal(r) @>= !! 0]

let basic_axioms () = truee
  (*Forall ([Type.St; Type.Rec; Type.Rec], 
         function [st; l1; l2] -> 
           let anteP = (?&& [??l1 @: ??st;
                             ??l2 @: ??st;
                             id(value(??st,??l1)) @== id(value(??st,??l2))]) in 
           let conseqP = ??l1 @== ??l2 in
             anteP @=> conseqP)*)

let _G_w = Ident.create "G_w"
let _G_d = Ident.create "G_d"
let _G_s = Ident.create "G_s"

let spec () =  
  let withdraw_spec = Txn {name="withdraw_txn"; 
                           guarantee=_G_w; 
                           iso=Isolation.RC} in
  let deposit_spec = Txn {name="deposit_txn"; 
                           guarantee=_G_d; 
                           iso=Isolation.RC} in
  let save_spec = Txn {name="save_txn"; 
                            guarantee=_G_s; 
                            iso=Isolation.RR} in
  let define_G _G g = _Forall_St2 @@ fun (st,st') ->
                            b_app(_G,[st; st']) @<=> g(st,st') in
  let define_I () = _Forall_St1 @@ fun st -> _I(st) @<=> inv(st)in
  let asserts = [basic_axioms (); 
                 define_G _G_w withdraw_G; 
                 define_G _G_d deposit_G; 
                 define_G _G_s save_G; 
                 define_I ()] in
    T {txns = [withdraw_spec; deposit_spec; save_spec]; 
       asserts = asserts}
