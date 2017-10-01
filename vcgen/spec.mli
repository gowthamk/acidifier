open Speclang

type txn = Txn of {name: string; 
                   guarantee: Ident.t; 
                   iso: Isolation.t}

type t = T of {txns: txn list;
               asserts: Predicate.t list}


val spec: unit -> t
