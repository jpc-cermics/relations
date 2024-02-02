export coq_root := ../../_build/default
export snippets_root := ./snippets
assets_root := $(snippets_root)/assets

include config.mk

SNIPPETS = \
	snippets/erel3/ActiveOe-n.tex \
	snippets/erel3/Active-n.tex \
	snippets/erel3/Aeop-n.tex \
	snippets/seq1/all_notation-n.tex \
	snippets/seq1/Chrel-n.tex \
	snippets/erel3/D_U-n.tex \
	snippets/erel3/D_U_a-n.tex \
	snippets/seq1/Lift_lemma2-n.tex \
	snippets/seq1/Lift_lemma-n.tex \
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
	snippets/seq1/RPath_equiv-n.tex \
	snippets/seq1/Lift_Suc-n.tex \
	snippets/seq1/Rpath_L1-n.tex \
	snippets/seq1/DI-n.tex \
	snippets/seq1/Lift_inj-n.tex \
	snippets/seq1/Lift_surj-n.tex \
	snippets/seq1/Epath_gt-n.tex \
	snippets/seq1/D_P-n.tex \
	snippets/seq1/D_V-n.tex \
	snippets/seq1/DP_DV-n.tex \
	snippets/seq1/Pe-n.tex \
	snippets/seq1/Epe-n.tex \
	snippets/erel3/U_gt-n.tex \
	snippets/erel3/ChrelO-n.tex \

all: allstd allplus

targets.mk: gen_targets.py
	@$(PYTHON) gen_targets.py "$(coq_root)" "$(snippets_root)" > "$@"

include targets.mk

.PHONY: all clean

allstd: $(targets) 
	@$(PYTHON) ./driver.py --frontend coq --backend assets --output-directory $(assets_root) -

clean:
	@rm -fr $(snippets_root) 
	@rm -f targets.mk
	@rm -f $(SNIPPETS)

clean-snippets:
	@rm -f $(SNIPPETS)

ignore:
	svn propset svn:ignore -F .cvsignore .

new: snippets/erel3/D_Un.tex

SED= -e 's/{exists}/{\\(\\exists\\)}/g' -e 's/{forall}/{\\(\\forall\\)}/g' -e 's/⊥/\\(\\bot\\))/g' \
	-e 's/Δ/\\(\\Delta\\))/g' -e 's+{/\\PYZbs{}+{\\(\\,\\wedge\\,\\)+g' \
	-e 's/\\PY{o}{\\PYZbs{}}\\PY{k+kr}{in}/\\(\\in\\)/g' \
	-e 's/\\PY{o}{\[\\PYZbs{}}\\PY{k+kr}{in}\\PY{o}{\]}/\\([{\\in}]\\)/g' \


SEDP=-e 's/\\PY{o}{\[\\PYZbs{}}\\PY{k+kr}{in}/\\PY{k+kr}{\\(\\in\\)}/g' \
	-e 's/\[\\PYZbs{}in\]/\[\\(\\in\\)\]/g' \




allplus: $(SNIPPETS)

snippets/%-n.tex: snippets/%.tex
	@echo -n create $@
	@sed $(SED)  $< > $@
	@echo done


