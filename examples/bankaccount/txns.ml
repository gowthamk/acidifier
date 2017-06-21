(* open Utils*)
let unimpl () = failwith "Unimpl"
let print x = ()


type table_name = 
  | User_account


module U = Unix

module SQL : 
sig
  val select1: table_name list -> ('a -> bool) -> 'a
  val select: table_name list -> ('a -> bool) -> 'a list
  val insert: table_name -> 'a -> unit
  val delete: table_name -> ('a -> bool) -> unit
  val update: table_name -> ('a -> unit) -> ('a -> bool) -> unit
end = 
struct
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


type user_account = {mutable id: id; mutable name: string; 
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
        (* modify record u as *)(fun u -> 
                                   begin
                                     u.id <-u.id;
        (* invariance needs to *)    u.cbal <- user.cbal - amt;
        (*be specified explicitly *) u.sbal <- u.sbal;
                                     u.name <- u.name;
                                   end)
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
        (fun u -> begin
                    u.id <-u.id;
                    u.cbal <- user.cbal + amt;
                    u.sbal <- u.sbal;
                    u.name <- u.name;
                  end)
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
        (fun u -> begin
                    u.id <-u.id;
                    u.name <- u.name;
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

