COQMFFLAGS := -Q . RL

ALLVFILES := ssrel.v rel.v aacset.v \
	erel3.v \
	paper_relations.v \
	paper_csbr_rel.v \
	paper_csbr_paths.v \
	paper_tcs_facts.v \
	paper_csbr.v \
	paper_tcs.v \



# erel.v erel3.v ssrel.v aacrel.v paper_relations.v paper_csbr_rel.v paper_csbr_paths.v paper_tcs_facts.v paper_csbr.v paper_tcs.v cssrel.v crel.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) imp.ml imp.mli imp1.ml imp1.mli imp2.ml imp2.mli

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean

ignore:
	svn propset svn:ignore -F .cvsignore .
