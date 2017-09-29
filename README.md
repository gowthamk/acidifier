## Acidifier ##

Created from OCaml 4.03 compiler frontend. 

### Building ###


1. `./configure`
2. `make`

A working installation of OCaml 4.03 or higher is assumed. In
particular, `ocamlc`, `ocamlopt`, `ocamllex`, `ocamlyacc` and
`ocamlde` tools are needed.

### Caveats ###
1. Magic number check has been turned off; see
   typing/cmi_format.ml:60. This lets the implementation use the same
   Pervasives library as the system ocaml.


