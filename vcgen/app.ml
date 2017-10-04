open Typedtree
open Speclang

module Coltype = 
struct
  type t = Id | String | Int | Bool | Date | Option of t
  let rec to_string = function
    | Id -> "id" | String -> "string" | Int -> "int" | Bool -> "bool"
    | Date -> "date" | Option t -> (to_string t)^" option"
end
module Tableschema = 
struct
  type t = T of {name: string;
                 cols: (string * some_type) list}
  let make ~name ~cols = T {name=name; cols=cols}
  let print (T{name;cols}) = 
    let cols = List.map (fun (col_n,SomeType col_t) -> 
                           col_n^":"^(Type.to_string col_t)) cols in
    begin
      Printf.printf "Table %s:\n  {%s}\n" name @@
        String.concat ", " cols
    end

  let name (T{name}) = name
  let cols (T{cols}) = cols
end

type t = T of {schemas: Tableschema.t list;
               txns: Fun.t list}

let make ~schemas ~txns = T {schemas; txns}
