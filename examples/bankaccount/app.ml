(* open Utils*)
let unimpl () = failwith "Unimpl"
let print x = ()


module U = Unix

module SQL = struct
  let select = unimpl ()
  let select1 = unimpl ()
  let insert = unimpl ()
  let delete = unimpl ()
  let update = unimpl ()
end

module S = struct
  include List
  let size = length
  let foreach = iter
  let max f l = unimpl ()
  let min f l = unimpl ()
  let sum f l = unimpl ()
end

type id



type table_name = 
  | User_account

type user_account = {id: id; name: string; 
                     mutable cbal: int; mutable sbal: int}
(*
 * Withdraw transaction
 * G = {(σ,σ') | I(σ) ∧ I(σ') ∧ 
 *               ∃ρ.∃x. ρ∈dom(σ) ∧ σ'=σ[ρ → σ(ρ) with cbal=x]}
 *)
let withdraw_txn u_id amt = 
  let user = SQL.select1 (* from tables *)[User_account] 
               (* all records u where *)(fun u -> u.id = u_id) in
    if user.cbal >= amt 
    then
      SQL.update (* table *)User_account
        (* modify record u as *)(fun u -> u.cbal <- user.cbal - amt)
        (* where u satisfies *)(fun u -> u.id = u_id)
    else
      ()
(*
 * Deposit transaction
 * G = {(σ,σ') | I(σ) ∧ I(σ') ∧ 
 *               ∃ρ.∃x. ρ∈dom(σ) ∧ σ'=σ[ρ → σ(ρ) with cbal=x]}
 *)
let deposit_txn u_id amt = 
  let user = SQL.select1 [User_account] 
               (fun u -> u.id = u_id) in
      SQL.update User_account
        (fun u -> u.cbal <- user.cbal + amt)
        (fun u -> u.id = u_id)
(*
 * Save transaction
 * G = {(σ,σ') | I(σ) ∧ I(σ') ∧ 
 *               ∃ρ.∃x.∃y. ρ∈dom(σ) ∧ σ'=σ[ρ → σ(ρ) 
 *                                      with cbal=x ∧ sbal=y]}
 *)
let save_txn u_id amt = 
  let user = SQL.select1 [User_account] 
               (fun u -> u.id = u_id) in
    if user.cbal >= amt 
    then
      SQL.update User_account
        (fun u -> 
           begin
             u.cbal <- user.cbal - amt;
             u.sbal <- user.sbal + amt;
           end)
        (fun u -> u.id = u_id)
    else
      ()

(*
 * Invariants
 *)
(*let inv1 () = 
  forall (u:User_account). u.cbal >=0 && u.sbal >=0*)

