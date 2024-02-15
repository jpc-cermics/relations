export coq_root := ../../_build/default
export snippets_root := ./snippets
assets_root := $(snippets_root)/assets

include config.mk

SNIPPETS = \
	snippets/seq1/ActiveOe-n.tex \
	snippets/erel3/Active-n.tex \
	snippets/erel3/Dseparated-n.tex \
	snippets/erel3/Aeop-n.tex \
	snippets/seq1/allnotation-n.tex \
	snippets/seq1/Chrel-n.tex \
	snippets/seq1/DU-n.tex \
	snippets/seq1/DUa-n.tex \
	snippets/seq1/DUaone-n.tex \
	snippets/seq1/Liftlemma-n.tex \
	snippets/seq1/Oedge-n.tex \
	snippets/seq1/TCP-n.tex \
	snippets/seq1/Ugeone-n.tex \
	snippets/paper_csbr/Lsevencsbr-n.tex \
	snippets/paper_csbr_paths/dsepnota-n.tex \
	snippets/rel/Sone-n.tex \
	snippets/rel/Stwo-n.tex \
	snippets/rel/Sthree-n.tex \
	snippets/seq1/LiftO-n.tex \
	snippets/seq1/Sn-n.tex \
	snippets/seq1/Lift-n.tex \
	snippets/seq1/OO-n.tex \
	snippets/seq1/pair-n.tex \
	snippets/ssrel/closrefltrans-n.tex \
	snippets/ssrel/closrt-n.tex \
	snippets/ssrel/relation-n.tex \
	snippets/seq1/RPathequiv-n.tex \
	snippets/seq1/RPath-n.tex \
	snippets/seq1/LiftSuc-n.tex \
	snippets/seq1/RpathLone-n.tex \
	snippets/seq1/DI-n.tex \
	snippets/seq1/Liftinj-n.tex \
	snippets/seq1/Liftsurj-n.tex \
	snippets/seq1/Epathgt-n.tex \
	snippets/seq1/DP-n.tex \
	snippets/seq1/DV-n.tex \
	snippets/seq1/DPDV-n.tex \
	snippets/seq1/Pe-n.tex \
	snippets/seq1/Epe-n.tex \
	snippets/seq1/Ugt-n.tex \
	snippets/seq1/ChrelO-n.tex \
	snippets/seq1/EpeLift-n.tex \
	snippets/seq1/PeUnLift-n.tex \
	snippets/seq1/EopeLiftO-n.tex \
	snippets/seq1/Eope-n.tex \
	snippets/seq1/PeUnLiftO-n.tex \
	snippets/seq1/Activeeq-n.tex \
	snippets/seq1/allL-n.tex \
	snippets/seq1/Atr-n.tex \

all: allstd allplus ../snippets.tex

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

SED= \
	-e 's/{exists}/{\\(\\exists\\)}/g' \
	-e 's/{forall}/{\\(\\forall\\)}/g' \
	-e 's/⊥/\\(\\bot\\))/g' \
	-e 's/Δ/\\(\\Delta\\)/g' \
	-e 's+{/\\PYZbs{}+{\\(\\,\\wedge\\,\\)+g' \
	-e 's/\\PY{o}{\\PYZbs{}}\\PY{k+kr}{in}/\\(\\in\\)/g' \
	-e 's/\\PY{o}{\[\\PYZbs{}}\\PY{k+kr}{in}\\PY{o}{\]}/\\([{\\in}]\\)/g' \
	-e 's/\[\\PYZbs{}in\]/\\([{\\in}]\\)/g' \
	-e 's/`;`/;/g' \
	-e 's/`|`/\\(\\cup\\)/g' \
	-e 's/`&`/\\(\\cap\\)/g' \
	-e 's+{\\PYZbs{}/+{\\(\\,\\vee\\,\\)+g' \
	-e 's+{\\PYZlt{}\\PYZhy{}\\PYZgt{}}+{\\(\\leftrightarrow\\)}+g' \
	-e 's+{\\PYZhy{}\\PYZgt{}}+{\\(\\rightarrow\\)}+g' \
	-e 's+{`\\PYZam{}`}+{\\(\\cap\\)}+g' \
	-e 's+~\\PY{o}{;}~+\\PY{o}{;}+g' \

allplus: $(SNIPPETS)

snippets/%-n.tex: snippets/%.tex
	@echo -n create $@
	@echo -n '\\newcommand{\\Snippet' > $@
	@echo -n `basename $*` >> $@
	@echo '}{' >> $@
	@sed $(SED)  $< >> $@
	@echo '}' >> $@
	@echo done

../snippets.tex : $(SNIPPETS)
	@cat $(SNIPPETS) > ../snippets.tex
	@echo ../snippets.tex updated


