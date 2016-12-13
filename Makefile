all: build

build:
	ocamlbuild -pkg graphics project.native -I src

rapport: build
	ocamldoc -latex -charset "utf-8" -noheader -notoc -notrailer \
	-colorize-code -o rapport/ocamldoc.tex -d rapport -I _build/src \
		src/voronoi.ml
	pdflatex -output-format pdf -output-directory rapport rapport/rapport.tex

dist: rapport
	base=$$(basename "$${PWD}") && name='decimo-zibulski' && cd .. && \
	tar -c --exclude-vcs --exclude-vcs-ignores -zvf "$${name}.tar.gz" \
		--transform="s,^$${base},$${name},g" --show-transformed-names \
		--exclude="_build" --exclude='ocamldoc.*' --exclude-caches \
		"$${base}"

clean:
	ocamlbuild -clean
	rm -rf rapport/*.aux rapport/*.log rapport/ocamldoc.*

.PHONY: build dist rapport clean
