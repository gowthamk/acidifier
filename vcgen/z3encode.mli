open Speclang
open Specelab
module P = Predicate
(*
 * (Θ,Γ) ⊢ Φ ⇒ vcs 
 *)
val doIt: (KE.t*TE.t*P.t) -> Ident.t list(*vcs*) -> bool
