open Speclang
open Light_env

module KE : LIGHT_ENV with type elem = Kind.t
module TE : LIGHT_ENV with type elem = some Type.t

val doIt: App.t -> KE.t * TE.t * Predicate.t
