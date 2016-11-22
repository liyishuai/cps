LNGEN = /Users/sweirich/github/deepspec/corespec/lngen-0.3/lngen
METALIB = /Users/sweirich/github/deepspec/metalib
OTT_SOURCE = systemt
FILES = systemt_ott systemt_inf
VOFILES  = $(foreach i, $(FILES), $(i).vo)

coq: $(VOFILES)

%_ott.v: %.ott Makefile
	ott -i $*.ott -o $*_ott.v -coq_lngen true
	make METALIB.FIX_$*_ott

%_inf.v: %.ott %_ott.v Makefile
	$(LNGEN) --coq-no-proofs --coq $*_inf.v --coq-ott $*_ott --coq-loadpath . $*.ott
	make METALIB.FIX_$*_inf

%.vo: %.v Makefile
	coqc -R $(METALIB) Metalib $*

# Target to be called with some filename appended to it; it will fix the imports to metalib
METALIB.FIX_%:
	sed -i -e 's/Metatheory/Metalib.Metatheory/g' $*.v
