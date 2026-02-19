

all:
	dune build

clean:
	dune clean

ignore:
	svn propset svn:ignore -F .cvsignore .

svg: all graph.pdf

graph.pdf:
	cp _build/default/graph.dpd .
	dpd2dot -keep-trans graph.dpd
	dot -Tsvg graph.dot > graph.svg
	inkscape --export-filename=graph.pdf graph.svg

graph4.pdf:
	cp _build/default/graph4.dpd .
	dpd2dot -keep-trans graph4.dpd
	dot -Tsvg graph4.dot > graph4.svg
	inkscape --export-filename=graph4.pdf graph4.svg

graph5.pdf:
	cp _build/default/graph5.dpd .
	dpd2dot -keep-trans graph5.dpd
	dot -Tsvg graph5.dot > graph5.svg
	inkscape --export-filename=graph5.pdf graph5.svg
