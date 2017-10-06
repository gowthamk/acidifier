open Speclang
open Specelab
module P = Predicate
(*
 * (Θ,Γ) ⊢ Φ ⇒ ψ
 *)
type res = SAT | UNSAT | UNKNOWN
val check_validity: (KE.t*TE.t*P.t(*φ*)) -> P.t(*ψ*) -> res
