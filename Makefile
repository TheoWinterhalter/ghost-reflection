all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

autosubst:
	cd theories/autosubst ; \
	$(MAKE) -f Makefile

clean-assumptions: all
	rm theories/Assumptions.vo

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean clean-assumptions autosubst
