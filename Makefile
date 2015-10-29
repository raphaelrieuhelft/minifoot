export OCAMLMAKEFILE = OcamlMakefile
export OCAMLYACC = ocamlyacc -v
export OCAMLC = ocamlc -dtypes
export OCAMLOPT = ocamlopt -dtypes
export OCAMLMKTOP = ocamlmktop -dtypes

INCLUDES = 

PARSING = misc.mli misc.ml location.mli location.ml parsetree.mli parsetree.ml config.mli config.ml defs.mli defs.ml print.mli print.ml error.mli error.ml parser.mly lexer.mll
PARSING_TRASH = parser.output

TOPLEVEL_SOURCES = $(PARSING) symbheap.mli symbheap.ml ast.mli ast.ml vcgen.mli vcgen.ml entailment.mli entailment.ml  symbexe.mli symbexe.ml toplevel.ml
TOPLEVEL_TRASH = $(PARSING_TRASH)
TOPLEVEL = SOURCES="$(TOPLEVEL_SOURCES)" \
           RESULT=toplevel \
           TRASH="$(TOPLEVEL_TRASH)"

MAIN = SOURCES="$(TOPLEVEL_SOURCES) main.ml" \
       LIBS="str" \
       RESULT=minifoot \
       TRASH="$(TOPLEVEL_TRASH)"

default: minifoot

all: toplevel minifoot.byte minifoot-gui.byte minifoot minifoot-gui

.PHONY: minifoot
minifoot:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) byte-code

.PHONY: toplevel
toplevel:
	$(MAKE) -f $(OCAMLMAKEFILE) $(TOPLEVEL) byte-code-library

clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINGUI) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPTGUI) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(TOPLEVEL) clean
	rm *.annot

depend:
	ocamldep $(INCLUDES) *.mli *.ml > .depend
include .depend
