KNOWNTARGETS := CoqMakefile
KNOWNFILES := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: all clean invoke-coqmakefile $(KNOWNFILES)

all: invoke-coqmakefile
	@true

clean: invoke-coqmakefile
	@true

theories/Spec.v: ott/type.ott ott/term.ott ott/context.ott
	ott -i ott/type.ott -i ott/term.ott -i ott/context.ott -o $@

tex/test.tex: ott/type.ott ott/term.ott ott/context.ott
	ott -tex_wrap false -i ott/type.ott -i ott/term.ott -i ott/context.ott -o $@
Rel.pdf: Rel.tex tex/test.tex
	xelatex Rel.tex -o $@
