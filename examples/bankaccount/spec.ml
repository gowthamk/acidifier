open Speclang
module E = Expr
module P = Predicate
open E
open P

type txn = Txn of {name: string; 
                   guarantee: Ident.t; 
                   iso: Isolation.t}

type t = T of {txns: txn list;
               invariant: Ident.t;
               asserts: P.t list}

let id (x) = App (L.get_accessor "id", [x])
let cbal (x) = App (L.get_accessor "cbal", [x])
let sbal (x) = App (L.get_accessor "sbal", [x])
(* let user_account = App (Ident.create "User_account", [])*)
let user_account = ??(Ident.create "user_account")

let withdraw_G (st,st') = 
  Exists ([Type.Loc], 
          function [l] ->     
            (?&& [??l @: dom(??st);
                  dom(??st') @== dom(??st);
                  table(value(??st,??l)) @== user_account;
                  table(value(??st',??l)) @== user_account; 
                  id(value(??st',??l)) @== id(value(??st,??l));
                  sbal(value(??st',??l)) @== sbal(value(??st,??l));
                  cbal(value(??st',??l)) @>= ConstInt(0);
                  Forall ([Type.loc], function [l'] ->
                            (??l' @!= ??l) @=> 
                                (value(??st',??l') @== value(??st,??l')))]))


let deposit_G (st,st') = withdraw_G (st,st')

let save_G (st,st') = 
  Exists ([Type.Loc], 
          function [l] ->     
            (?&& [??l @: dom(??st);
                  dom(??st') @== dom(??st);
                  table(value(??st,??l)) @== user_account;
                  table(value(??st',??l)) @== user_account; 
                  id(value(??st',??l)) @== id(value(??st,??l));
                  sbal(value(??st',??l)) @>= ConstInt(0);
                  cbal(value(??st',??l)) @>= ConstInt(0);
                  Forall ([Type.loc], function [l'] ->
                            (??l' @!= ??l) @=> 
                                (value(??st',??l') @== value(??st,??l')))]))

let inv (st) = 
  Forall ([Type.Loc], function [l] ->
        (?&& [cbal(value(??st,??l)) @>= ConstInt(0); 
              sbal(value(??st,??l)) @>= ConstInt(0)]))

let basic_axioms () = 
  Forall ([Type.St; Type.Loc; Type.Loc], 
         function [st; l1; l2] -> 
           let anteP = (?&& [??l1 @: dom(??st);
                             ??l2 @: dom(??st);
                             id(value(??st,??l1)) @== id(value(??st,??l2))]) in 
           let conseqP = ??l1 @== ??l2 in
             anteP @=> conseqP)

let _G_w = Ident.create "G_w"
let _G_d = Ident.create "G_d"
let _G_s = Ident.create "G_s"
let _I = Ident.create "I"

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
  let define_G _G g = Forall ([Type.St; Type.St], 
                              function [st; st'] -> 
                                b_app(_G,[??st; ??st']) @<=> g(st,st')) in
  let define_I () = Forall ([Type.St], 
                            function [st] -> b_app(_I,[??st]) @<=> inv(st)) in
  let asserts = [basic_axioms (); 
                 define_G _G_w withdraw_G; 
                 define_G _G_d deposit_G; 
                 define_G _G_s save_G; 
                 define_I ()] in
    T {txns = [withdraw_spec; deposit_spec; save_spec]; 
       invariant = _I;
       asserts = asserts}
