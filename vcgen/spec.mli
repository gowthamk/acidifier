open Speclang

type txn = Txn of {name: string; 
                   guarantee: Ident.t; 
                   iso: Isolation.t}

type t = T of {txns: txn list;
               invariant: Ident.t;
               asserts: Predicate.t list}


val spec: unit -> t
