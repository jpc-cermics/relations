export coq_root := ../../_build/default
export snippets_root := ./snippets
assets_root := $(snippets_root)/assets

include config.mk

SNIPPETS = \
	snippets/erel3/ActiveOe-n.tex \
	snippets/erel3/Active-n.tex \
	snippets/erel3/Aeop-n.tex \
	snippets/erel3/all_notation-n.tex \
	snippets/erel3/Chrel-n.tex \
	snippets/erel3/D_U-n.tex \
	snippets/erel3/EPath2inter-n.tex \
	snippets/erel3/EPath2new-n.tex \
	snippets/erel3/EPath3new-n.tex \
	snippets/erel3/Lift_lemma2-n.tex \
	snippets/erel3/Lift_lemma-n.tex \
	snippets/erel3/Oedge-n.tex \
	snippets/erel3/TCP-n.tex \
	snippets/erel3/U_ge_1p-n.tex \
	snippets/erel3/U_ge_1-n.tex \
	snippets/paper_csbr/L7_csbr-n.tex \
	snippets/paper_csbr_paths/dsepnota-n.tex \
	snippets/rel/S1-n.tex \
	snippets/rel/S2-n.tex \
	snippets/rel/S3-n.tex \
	snippets/seq1/all_notation-n.tex \
	snippets/seq1/LiftO-n.tex \
	snippets/seq1/Sn-n.tex \
	snippets/seq1/Lift-n.tex \
	snippets/seq1/O-n.tex \
	snippets/seq1/pair-n.tex \
	snippets/ssrel/clos_refl_trans-n.tex \
	snippets/ssrel/clos_rt-n.tex \
	snippets/ssrel/relation-n.tex \

all: allstd allplus

targets.mk: gen_targets.py
	@$(PYTHON) gen_targets.py "$(coq_root)" "$(snippets_root)" > "$@"

include targets.mk

.PHONY: all clean

allstd: $(targets) 
	@$(PYTHON) ./driver.py --frontend coq --backend assets --output-directory $(assets_root) -

clean:
	rm -fr $(snippets_root) 
	rm -f targets.mk
	rm -f $(SNIPPETS)

clean-snippets:
	@rm -f $(SNIPPETS)

ignore:
	svn propset svn:ignore -F .cvsignore .

new: snippets/erel3/D_Un.tex

SED= -e 's/{exists}/{\\(\\exists\\)}/g' -e 's/{forall}/{\\(\\forall\\)}/g' -e 's/⊥/\\(\\bot\\))/g' \
	-e 's/Δ/\\(\\Delta\\))/g' -e 's+{/\\PYZbs{}+{\\(\\,\\wedge\\,\\)+g' \

SEDP=-e 's/\\PY{o}{\[\\PYZbs{}}\\PY{k+kr}{in}/\\PY{k+kr}{\\(\\in\\)}/g' \
	-e 's/\[\\PYZbs{}in\]/\[\\(\\in\\)\]/g' \

allplus: $(SNIPPETS)

snippets/erel3/ActiveOe-n.tex: snippets/erel3/ActiveOe.tex
	@sed $(SED)  $< > $@

snippets/erel3/Active-n.tex: snippets/erel3/Active.tex
	@sed $(SED)  $< > $@

snippets/erel3/Aeop-n.tex: snippets/erel3/Aeop.tex
	@sed $(SED)  $< > $@

snippets/erel3/all_notation-n.tex: snippets/erel3/all_notation.tex
	@sed $(SED)  $< > $@

snippets/erel3/Chrel-n.tex: snippets/erel3/Chrel.tex
	@sed $(SED)  $< > $@

snippets/erel3/D_U-n.tex: snippets/erel3/D_U.tex
	@sed $(SED)  $< > $@

snippets/erel3/EPath1-n.tex: snippets/erel3/EPath1.tex
	@sed $(SED)  $< > $@

snippets/erel3/EPath2inter-n.tex: snippets/erel3/EPath2inter.tex
	@sed $(SED)  $< > $@

snippets/erel3/EPath2new-n.tex: snippets/erel3/EPath2new.tex
	@sed $(SED)  $< > $@

snippets/erel3/EPath3new-n.tex: snippets/erel3/EPath3new.tex
	@sed $(SED)  $< > $@

snippets/erel3/Lift_lemma2-n.tex: snippets/erel3/Lift_lemma2.tex
	@sed $(SED)  $< > $@

snippets/erel3/Lift_lemma-n.tex: snippets/erel3/Lift_lemma.tex
	@sed $(SED)  $< > $@

snippets/erel3/Oedge-n.tex: snippets/erel3/Oedge.tex
	@sed $(SED)  $< > $@

snippets/erel3/TCP-n.tex: snippets/erel3/TCP.tex
	@sed $(SED)  $< > $@

snippets/erel3/U_ge_1p-n.tex: snippets/erel3/U_ge_1p.tex
	@sed $(SED)  $< > $@

snippets/erel3/U_ge_1-n.tex: snippets/erel3/U_ge_1.tex
	@sed $(SED)  $< > $@

snippets/paper_csbr/L7_csbr-n.tex: snippets/paper_csbr/L7_csbr.tex
	@sed $(SED)  $< > $@

snippets/paper_csbr_paths/dsepnota-n.tex: snippets/paper_csbr_paths/dsepnota.tex
	@sed $(SED)  $< > $@

snippets/rel/S1-n.tex: snippets/rel/S1.tex
	@sed $(SED)  $< > $@

snippets/rel/S2-n.tex: snippets/rel/S2.tex
	@sed $(SED)  $< > $@

snippets/rel/S3-n.tex: snippets/rel/S3.tex
	@sed $(SED)  $< > $@

snippets/seq1/all_notation-n.tex: snippets/seq1/all_notation.tex
	@sed $(SED)  $< > $@

snippets/seq1/LiftO-n.tex: snippets/seq1/LiftO.tex
	@sed $(SED)  $< > $@

snippets/seq1/Lift-n.tex: snippets/seq1/Lift.tex
	@sed $(SED)  $< > $@

snippets/seq1/Sn-n.tex: snippets/seq1/Sn.tex
	@sed $(SED)  $< > $@

snippets/seq1/O-n.tex: snippets/seq1/O.tex
	@sed $(SED)  $< > $@

snippets/seq1/pair-n.tex: snippets/seq1/pair.tex
	@sed $(SED)  $< > $@

snippets/ssrel/clos_refl_trans-n.tex: snippets/ssrel/clos_refl_trans.tex
	@sed $(SED)  $< > $@

snippets/ssrel/clos_rt-n.tex: snippets/ssrel/clos_rt.tex
	@sed $(SED)  $< > $@

snippets/ssrel/relation-n.tex: snippets/ssrel/relation.tex
	@sed $(SED)  $< > $@


