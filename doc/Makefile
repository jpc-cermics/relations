SHELL=/bin/sh
MAKEFLAGS += --no-print-directory

PDF= \
	allsnippets.pdf \

all: movies_ $(PDF)

movies_:
	@+${MAKE} -C movies all

allsnippets.pdf: movies allsnippets.tex snippets.tex
	pdflatex allsnippets

%.pdf : %.tex
	pdflatex $*.tex
	bibtex $*
	pdflatex $*.tex
	pdflatex $*.tex

clean:
	@+${MAKE} -C movies clean
	@rm -f $(PDF)
	@rm -f *.aux *.log *.toc *.bbl *.pdf *.blg *.dvi *.ps *.nav *.out *.snm *.vrb *.synctex.gz
	@echo cleaned

distclean: clean
	@+${MAKE} -C movies clean
	@rm -fr auto

ignore:
	svn propset svn:ignore -F .cvsignore .


