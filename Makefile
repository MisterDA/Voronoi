RESULT=voronoi
SOURCES=src/examples.ml src/sat_solver.mli src/sat_solver.ml src/voronoi.ml
LIBS=graphics

OCAMLMAKEFILE=OCamlMakefile
include $(OCAMLMAKEFILE)

dist: clean
	base=$$(basename $${PWD}) && name='decimo-zibulski' && \
	cd .. && mv $${base} $${name} && \
	tar czvf $${name}.tar.gz $${name} --exclude-vcs && \
	mv $${name} $${base} && cd $${base}

.PHONY: dist
