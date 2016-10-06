#
# Pure OCaml, no packages, no _tags 
#

# bin-annot is required for Merlin and other IDE-like tools

OCB_FLAGS = -use-ocamlfind #-tag bin_annot
OCB = 		ocamlbuild $(OCB_FLAGS)
FNAME = ssnimp_ba_eg2#ssnimp_mb_eg

all: 		native byte 
		mkdir -p Graphs

clean:
		$(OCB) -clean

native: 
		$(OCB) $(FNAME).native

byte:
		$(OCB) $(FNAME).byte

profile:
		$(OCB) -tag profile $(FNAME).native

debug:
		$(OCB) -tag debug $(FNAME).byte

test: 		native
		./$(FNAME).native 

.PHONY: 	all clean byte native profile debug test
