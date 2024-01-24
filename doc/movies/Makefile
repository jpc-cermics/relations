export coq_root := ../../_build/default
export snippets_root := ./snippets
assets_root := $(snippets_root)/assets

include config.mk

SNIPPETS =  snippets/erel3/D_Un.tex snippets/erel3/TCPn.tex snippets/paper_csbr_paths/dsepnotan.tex

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

ignore:
	svn propset svn:ignore -F .cvsignore .

new: snippets/erel3/D_Un.tex

SED= -e 's/{exists}/{\\(\\exists\\)}/g' -e 's/{forall}/{\\(\\forall\\)}/g' -e 's/⊥/\\(\\bot\\))/g'

allplus: $(SNIPPETS)

snippets/erel3/D_Un.tex : snippets/erel3/D_U.tex
	@sed $(SED)  $< > $@

snippets/erel3/TCPn.tex : snippets/erel3/TCP.tex
	@sed $(SED)  $< > $@

snippets/paper_csbr_paths/dsepnotan.tex : snippets/paper_csbr_paths/dsepnota.tex
	@sed $(SED)  $< > $@


