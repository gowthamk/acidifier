open Speclang
open Specelab
module P = Predicate
(*
 * (Θ,Γ) ⊢ Φ ⇒ ψ
 *)
type res =  UNSATISFIABLE | UNKNOWN | SATISFIABLE 
val check_validity: (KE.t*TE.t*P.t(*φ*)) -> P.t(*ψ*) -> bool -> res
