

all:
	dune build

clean:
	dune clean

ignore:
	svn propset svn:ignore -F .cvsignore .

