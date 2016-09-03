#
# Pure OCaml, no packages, no _tags 
#

# bin-annot is required for Merlin and other IDE-like tools

OCB_FLAGS = -use-ocamlfind #-tag bin_annot
OCB = 		ocamlbuild $(OCB_FLAGS)

all: 		native byte 

clean:
		$(OCB) -clean

native: 
		$(OCB) ssnimp_ba_eg.native

byte:
		$(OCB) ssnimp_ba_eg.byte

profile:
		$(OCB) -tag profile ssnimp_ba_eg.native

debug:
		$(OCB) -tag debug ssnimp_ba_eg.byte

test: 		native
		./ssnimp_ba_eg.native "OCaml" "OCamlBuild" "users"

.PHONY: 	all clean byte native profile debug test
