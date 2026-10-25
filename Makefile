

all:
	dune build --display short

# temps de compilation par fichier, pour les fichiers recompilés par le
# dernier appel à dune (make all times ; tout : make clean all times)
times:
	@dune trace cat | jq -r 'select(.name=="finish" and .args.process_args[0]=="compile") | [.dur, .args.process_args[-1]] | @tsv' \
	  | sort -rn | awk -F'\t' '{printf "%8.2f s  %s\n", $$1, $$2}'

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

# instrumentation RelationAlgebra: quels lemmes les tactiques de rel_ra.v
# prouvent-elles seules ?  cf. probe/README.md
FILE ?= paper_relations.v
PROBE = probe/probe_$(notdir $(FILE))

probe: all
	python3 probe/ra_probe.py $(FILE) > $(PROBE)
	rocq compile -Q _build/default RL -Q probe Probe $(PROBE) \
	  | sed -n 's/^RAP "\(.*\)" \(.*\)$$/\1\t\2/p' > $(PROBE:.v=.log)
	@echo "--- $(FILE): $$(wc -l < $(PROBE:.v=.log)) lemmes ---"
	@cut -f2 $(PROBE:.v=.log) | sort | uniq -c | sort -rn
