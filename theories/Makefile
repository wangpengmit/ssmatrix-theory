MODULES := \
	mxutil \
	bimodule \
	derivation \
	mxmodule \
	mxdiff \
	nfun \
	example_appendix \
	example \

VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	COQC='coqc' $(MAKE) -f Makefile.coq

COQARGS := 
COQC    := coqc $(COQARGS)

Makefile.coq: Makefile $(VS)
	coq_makefile $(COQARGS) $(VS) -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
