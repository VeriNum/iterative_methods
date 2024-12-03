# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile extra-stuff extra-stuff2
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

ifneq ($(MAKECMDGOALS),run-clightgen)
ifneq ($(MAKECMDGOALS),clean)
Makefile.coq: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

invoke-coqmakefile: Makefile.coq
	$(MAKE) --no-print-directory -f Makefile.coq $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)
endif
endif
####################################################################
##                      Your targets here                         ##
####################################################################

run-clightgen: cholesky.v

clean:
	rm -f Makefile.coq Makefile.coq.conf
	rm -f cholesky.v
	rm -f *.o *.vo *.vos *.vok *.glob

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
