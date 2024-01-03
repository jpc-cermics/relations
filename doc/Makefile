SHELL=/bin/sh

PDF= \
	Conditional_Separation_Binary_Relation.pdf \
	tuto.pdf \

all: movies $(PDF)

movies:
	@+${MAKE} -C movies all

tuto.pdf: movies tuto.tex 
	pdflatex tuto

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






