open Specelab
module P = Speclang.Predicate

(*
 * (Θ,Γ,Φ) ⊢ s◀τ
 *)
val doIt: KE.t(*Θ*)*TE.t(*Γ*)*P.t(*Φ*) -> App.t(*s*) -> Spec.t(*τ*) -> unit
