export coq_root := ../../_build/default
export snippets_root := ./snippets
assets_root := $(snippets_root)/assets

include config.mk

default: all  snippets/erel3/D_Un.tex

targets.mk: gen_targets.py
	@$(PYTHON) gen_targets.py "$(coq_root)" "$(snippets_root)" > "$@"

include targets.mk

.PHONY: all clean

all: $(targets)
	@$(PYTHON) ./driver.py --frontend coq --backend assets --output-directory $(assets_root) -

clean:
	rm -fr $(snippets_root) 
	rm -f targets.mk

ignore:
	svn propset svn:ignore -F .cvsignore .

new: snippets/erel3/D_Un.tex

snippets/erel3/D_Un.tex : snippets/erel3/D_U.tex
	@sed -e 's/{exists}/{\\(\\exists\\)}/g' $< > $@

