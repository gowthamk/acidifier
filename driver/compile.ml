(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 2002 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* The batch compiler *)

open Misc
open Format
open Typedtree
open Compenv

(* Compile a .mli file *)

(* Keep in sync with the copy in optcompile.ml *)

let tool_name = "ocamlc"

let interface ppf sourcefile outputprefix =
  Compmisc.init_path false;
  let modulename = module_of_filename ppf sourcefile outputprefix in
  Env.set_unit_name modulename;
  let initial_env = Compmisc.initial_env () in
  let ast = Pparse.parse_interface ~tool_name ppf sourcefile in
  if !Clflags.dump_parsetree then fprintf ppf "%a@." Printast.interface ast;
  if !Clflags.dump_source then fprintf ppf "%a@." Pprintast.signature ast;
  let tsg = Typemod.type_interface initial_env ast in
  if !Clflags.dump_typedtree then fprintf ppf "%a@." Printtyped.interface tsg;
  let sg = tsg.sig_type in
  if !Clflags.print_types then
    Printtyp.wrap_printing_env initial_env (fun () ->
        fprintf std_formatter "%a@."
          Printtyp.signature (Typemod.simplify_signature sg));
  ignore (Includemod.signatures initial_env sg sg);
  Typecore.force_delayed_checks ();
  Warnings.check_fatal ();
  if not !Clflags.print_types then begin
    let deprecated = Builtin_attributes.deprecated_of_sig ast in
    let sg =
      Env.save_signature ~deprecated sg modulename (outputprefix ^ ".cmi")
    in
    Typemod.save_signature modulename tsg outputprefix sourcefile
      initial_env sg ;
  end

(* Compile a .ml file *)

let print_if ppf flag printer arg =
  if !flag then fprintf ppf "%a@." printer arg;
  arg

let (++) x f = f x

let implementation ppf sourcefile outputprefix =
  Compmisc.init_path false;
  let modulename = module_of_filename ppf sourcefile outputprefix in
  Env.set_unit_name modulename;
  let env = Compmisc.initial_env() in
  try
    let (typedtree, coercion) =
      Pparse.parse_implementation ~tool_name ppf sourcefile
      ++ print_if ppf Clflags.dump_parsetree Printast.implementation
      ++ print_if ppf Clflags.dump_source Pprintast.structure
      ++ Timings.(time (Typing sourcefile))
          (Typemod.type_implementation sourcefile outputprefix modulename env)
      ++ print_if ppf Clflags.dump_typedtree
        Printtyped.implementation_with_coercion in
    let app = Extract.doIt ppf typedtree in
    let module KE = Specelab.KE in 
    let module TE = Specelab.TE in
    let module P = Speclang.Predicate in
    let (ke,te,phi) = Specelab.doIt app in
    let _ = begin
              Printf.printf "----- Kind Env ----\n";
              KE.print ke;
              Printf.printf "----- Type Env ----\n";
              TE.print te;
              Printf.printf "----- Context ----\n";
              let pstr =  match phi with 
                | P.And ps -> String.concat "\n" @@ 
                                List.map P.to_string ps
                | _ -> P.to_string phi in
              Printf.printf "%s\n" pstr;
            end in
    (*let _ = Verify.doIt (ke,te,phi) app (Spec.spec()) in*)
      if !Clflags.print_types then begin
        Warnings.check_fatal ();
        Stypes.dump (Some (outputprefix ^ ".annot"))
      end else ()
  with x ->
    Stypes.dump (Some (outputprefix ^ ".annot"));
    raise x

let c_file name =
  Location.input_name := name;
  if Ccomp.compile_file name <> 0 then exit 2
