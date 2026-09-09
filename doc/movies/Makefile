export coq_root := ../../_build/default
export snippets_root := ./snippets
assets_root := $(snippets_root)/assets

include config.mk

SNIPPETS = \
	snippets/paper_csbr/dsepnota-n.tex \
	snippets/paper_csbr/theoremfive-n.tex \
	snippets/paper_csbr/Lseptone-n.tex \
	snippets/paper_csbr/Lsepttwo-n.tex \
	snippets/paper_csbr/Lseptthree-n.tex \
	snippets/paper_csbr/Lseptfour-n.tex \
	snippets/paper_monochromatic/Chains-n.tex \
	snippets/paper_monochromatic/Mono-n.tex \
	snippets/paper_monochromatic/SType-n.tex \
	snippets/paper_monochromatic/Scal-n.tex \
	snippets/paper_monochromatic/Scalnotempty-n.tex \
	snippets/paper_monochromatic/leSetone-n.tex \
	snippets/paper_monochromatic/leset-n.tex \
	snippets/paper_monochromatic/lesetI-n.tex \
	snippets/paper_monochromatic/Elt-n.tex \
	snippets/paper_monochromatic/Sinf-n.tex \
	snippets/paper_monochromatic/RC-n.tex \
	snippets/paper_monochromatic/lesetporder-n.tex \
	snippets/paper_monochromatic/totalRC-n.tex \
	snippets/paper_monochromatic/totalRCPTr-n.tex \
	snippets/paper_monochromatic/ChooseRCCi-n.tex \
	snippets/paper_monochromatic/ChooseRCSi-n.tex \
	snippets/paper_monochromatic/SinfScal-n.tex \
	snippets/paper_monochromatic/SinfScalP-n.tex \
	snippets/paper_monochromatic/SmaxSType-n.tex \
	snippets/paper_monochromatic/Smax-n.tex \
	snippets/paper_monochromatic/IsMaximal-n.tex \
	snippets/paper_monochromatic/TmI-n.tex \
	snippets/paper_monochromatic/Sbunp-n.tex \
	snippets/paper_monochromatic/factone-n.tex \
	snippets/paper_monochromatic/facttwo-n.tex \
	snippets/paper_monochromatic/factthree-n.tex \
	snippets/paper_monochromatic/factfour-n.tex \
	snippets/paper_monochromatic/factfive-n.tex \
	snippets/paper_monochromatic/factsix-n.tex \
	snippets/paper_monochromatic/factseven-n.tex \
	snippets/paper_monochromatic/facteight-n.tex \
	snippets/paper_monochromatic/factnine-n.tex \
	snippets/paper_monochromatic/factten-n.tex \
	snippets/paper_monochromatic/facteleven-n.tex \
	snippets/paper_monochromatic/Sx-n.tex \
	snippets/paper_monochromatic/Tm-n.tex \
	snippets/paper_monochromatic/Sxm-n.tex \
	snippets/paper_monochromatic/Sxone-n.tex \
	snippets/paper_monochromatic/infasym-n.tex \
	snippets/paper_monochromatic/MainTh-n.tex \
	snippets/paper_monochromatic/SSWTh-n.tex \
	snippets/paper_monochromatic/Monotopath-n.tex \
	snippets/paper_monochromatic_f/AsymdPV-n.tex \
	snippets/paper_relations/Aw-n.tex \
	snippets/rel/RelIndep-n.tex \
	snippets/rel/Rloop-n.tex \
	snippets/rel/asym-n.tex \
	snippets/rel/lefttotal-n.tex \
	snippets/rel/iicfun-n.tex \
	snippets/rel/iic-n.tex \
	snippets/rel/iicinj-n.tex \
	snippets/rel/chains-n.tex \
	snippets/seq1/Chrel-n.tex \
	snippets/seq1/DI-n.tex \
	snippets/seq1/Lift-n.tex \
	snippets/seq1/LiftLift-n.tex \
	snippets/seq1/Liftinj-n.tex \
	snippets/seq1/Liftlemma-n.tex \
	snippets/seq1/Liftnota-n.tex \
	snippets/seq1/Liftsurj-n.tex \
	snippets/seq1/RPath-n.tex \
	snippets/seq1/RPathequiv-n.tex \
	snippets/seq1/RpathLone-n.tex \
	snippets/seq1/TCP-n.tex \
	snippets/seq1/allL-n.tex \
	snippets/seq1/allnotation-n.tex \
	snippets/seq2/tcpuniq-n.tex \
	snippets/ssrel/closrefltrans-n.tex \
	snippets/ssrel/closrt-n.tex \
	snippets/ssrel/relation-n.tex \
	snippets/paper_kernels/GSSW-n.tex \
	snippets/paper_kernels/GSSWp-n.tex \
	snippets/paper_kernels/GSSWpN-n.tex \
	snippets/paper_kernels/GSSWpp-n.tex \
	snippets/paper_kernels/GSSWppN-n.tex \
	snippets/paper_kernels/SSWext-n.tex \
	snippets/paper_kernels/SSWextN-n.tex \
	snippets/paper_kernels/SSWextNN-n.tex \
	snippets/paper_kernels/ABkernels-n.tex \
	snippets/paper_kernels/ABkernelsN-n.tex \
	snippets/paper_kernels/MLinf-n.tex \
	snippets/paper_kernels/MLinfN-n.tex \
	snippets/paper_kernels/ChampetierContext-n.tex \
	snippets/paper_kernels/FinCaseChampetier-n.tex \
	snippets/paper_kernels/BlidiaEngelContext-n.tex \
	snippets/paper_kernels/FinCaseBH-n.tex \
	snippets/paper_kernels/MLPdcContext-n.tex \
	snippets/paper_kernels/MLPdc-n.tex \
	snippets/paper_kernels/iicasymToiicinj-n.tex \
	snippets/paper_kernels_common/lesetN-n.tex \
	snippets/paper_kernels_common/lesetporderN-n.tex \
	snippets/paper_kernels_common/preabsorbentN-n.tex \
	snippets/paper_kernels_common/absorbentN-n.tex \
	snippets/paper_kernels_common/prekernelN-n.tex \
	snippets/paper_kernels_common/kernelN-n.tex \
	snippets/paper_kernels_common/STypeN-n.tex \
	snippets/paper_kernels_common/ScalN-n.tex \
	snippets/paper_kernels_common/ScalnotemptyN-n.tex \
	snippets/paper_kernels_common/EltN-n.tex \
	snippets/paper_kernels_common/leSetoneN-n.tex \
	snippets/paper_kernels_common/SinfN-n.tex \
	snippets/paper_kernels_common/IsMaximalN-n.tex \
	snippets/paper_kernels_common/MaximalZorn-n.tex \
	snippets/paper_kernels_common/extend-n.tex \
	snippets/paper_kernels_common/CyclicBHlem-n.tex \
	snippets/paper_kernels_common/assumptionsdefs-n.tex \
	snippets/paper_kernels_common/MaximalFin-n.tex \

OBSOL= \
	snippets/paper_csbr_paths/Active-n.tex \
	snippets/paper_csbr_paths/ActiveOe-n.tex \
	snippets/paper_csbr_paths/Activeeq-n.tex \
	snippets/paper_csbr_paths/Aeop-n.tex \
	snippets/paper_csbr_paths/Atr-n.tex \
	snippets/paper_csbr_paths/ChrelO-n.tex \
	snippets/paper_csbr_paths/DP-n.tex \
	snippets/paper_csbr_paths/DPDV-n.tex \
	snippets/paper_csbr_paths/DU-n.tex \
	snippets/paper_csbr_paths/DUa-n.tex \
	snippets/paper_csbr_paths/DUaone-n.tex \
	snippets/paper_csbr_paths/DV-n.tex \
	snippets/paper_csbr_paths/Dseparated-n.tex \
	snippets/paper_csbr_paths/Eope-n.tex \
	snippets/paper_csbr_paths/EopeLiftO-n.tex \
	snippets/paper_csbr_paths/Epathgt-n.tex \
	snippets/paper_csbr_paths/Epe-n.tex \
	snippets/paper_csbr_paths/EpeLift-n.tex \
	snippets/paper_csbr_paths/LiftO-n.tex \
	snippets/paper_csbr_paths/OO-n.tex \
	snippets/paper_csbr_paths/Oedge-n.tex \
	snippets/paper_csbr_paths/Pe-n.tex \
	snippets/paper_csbr_paths/PeUnLift-n.tex \
	snippets/paper_csbr_paths/PeUnLiftO-n.tex \
	snippets/paper_csbr_paths/Ugeone-n.tex \
	snippets/paper_csbr_paths/Ugt-n.tex \
	snippets/paper_csbr_paths/pair-n.tex \



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
	@rm -f $(SNIPPETS) $(OBSOL)

clean-snippets:
	@rm -f $(SNIPPETS) $(OBSOL)

ignore:
	svn propset svn:ignore -F .cvsignore .

new: snippets/erel3/D_Un.tex

SED= \
	-e 's/{exists}/{\\(\\exists\\)}/g' \
	-e 's/{forall}/{\\(\\forall\\)}/g' \
	-e 's/⊥/\\(\\bot\\)/g' \
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
	-e 's+Suc\\PYZbs{}in+Suc{\\(\\in\\)}+g' \
	-e 's+L\\PYZbs{}in+L{\\(\\in\\)}+g' \
	-e 's/ \\PY{k+kn}{Notation}/ ~~\\PY{k+kn}{Notation}/g' \
	-e 's/\\begin{alectryon}/%/g' \
	-e 's/\\end{alectryon}//g' \
	-e 's+{\\PYZti{}+{\\(\\neg\\)+g' \
	-e 's+`\\PYZlt{}=`+\\(\\subset\\)+g' \

allplus: $(SNIPPETS) $(OBSOL)

snippets/%-n.tex: snippets/%.tex
	@echo -n create $@
	@echo -n '\\newcommand{\\Snippet' > $@
	@echo -n `basename $*` >> $@
	@echo '}{' >> $@
	@sed $(SED)  $< >> $@
	@echo '}' >> $@
	@echo done

../snippets.tex : $(SNIPPETS) $(OBSOL)
	@cat $(SNIPPETS) $(OBSOL) > ../snippets.tex
	@echo ../snippets.tex updated


