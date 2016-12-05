all:
	ocamlbuild -pkg graphics voronoi.native -I src

dist: report clean
	base=$$(basename "$${PWD}") && name='decimo-zibulski' && \
	cd .. && mv "$${base}" "$${name}" && \
	tar --exclude-vcs -czvf "$${name}.tar.gz" --exclude-vcs-ignores "$${name}" && \
	mv "$${name}" "$${base}"

report:
	cd 'report' && pdflatex 'report.tex'

clean:
	ocamlbuild -clean
	rm -rf report/*.aux report/*.log

.PHONY: dist clean report
