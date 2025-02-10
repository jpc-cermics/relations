

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





