KNOWNTARGETS := CoqMakefile
KNOWNFILES := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

# %: invoke-coqmakefile
# 	@true

theories/Spec.v: ott/test.ott
	ott -i ott/test.ott -o $@

tex/test.tex: ott/test.ott
	ott -tex_wrap false -i ott/test.ott -o $@
Rel.pdf: Rel.tex tex/test.tex
	xelatex Rel.tex -o $@
