COQINCLUDES=-R src/CoqUp CoqUp

COQEXEC=$(COQBIN)coqtop $(COQINCLUDES) -batch -load-vernac-source
COQMAKE="$(COQBIN)coq_makefile"

VS=$(wildcard src/CoqUp/*.v)

.PHONY: all install coq clean

all:
	$(MAKE) coq
	$(MAKE) extraction

install:
	$(MAKE) -f Makefile.coq install

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

extraction: extraction/STAMP

extraction/STAMP:
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) ./extraction/Extraction.v
	touch $@

Makefile.coq: Makefile
	$(COQBIN)coq_makefile $(COQINCLUDES) $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f Makefile.coq
