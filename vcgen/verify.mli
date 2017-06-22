open Specelab
module P = Speclang.Predicate

type env = {txn: Ident.t; 
            mutable ke: KE.t; 
            mutable te: TE.t; 
            mutable phi: P.t; 
            mutable vcs: Ident.t list;}
(*
 * (Θ,Γ,Φ) ⊢ s◀τ
 *)
val doIt: KE.t(*Θ*)*TE.t(*Γ*)*P.t(*Φ*) -> App.t(*s*) -> Spec.t(*τ*) -> unit
