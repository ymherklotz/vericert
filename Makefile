COMPCERTRECDIRS=lib common $(ARCHDIRS) backend cfrontend driver flocq exportclight \
  MenhirLib cparser

COMPCERTCOQINCLUDES=$(foreach d, $(RECDIRS), -R lib/CompCert/$(d) compcert.$(d))

COQINCLUDES=-R src/CoqUp CoqUp $(COMPCERTCOQINCLUDES)

COQEXEC=$(COQBIN)coqtop $(COQINCLUDES) -batch -load-vernac-source
COQMAKE="$(COQBIN)coq_makefile"

VS=$(wildcard src/CoqUp/*.v)

.PHONY: all install coq clean

all:
	(cd lib/CompCert && ./configure x86_64-linux)
	$(MAKE) -C lib/CompCert all
	$(MAKE) coq
	$(MAKE) compile

install:
	$(MAKE) -f Makefile.coq install

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

extraction: extraction/STAMP

compile: extraction/STAMP
	@echo "OCaml bin/coqup"
	@mkdir -p bin
	@dune build extraction/main.exe
	@cp _build/default/extraction/main.exe bin/coqup

extraction/STAMP:
	@echo "COQEXEC ./extraction/Extraction.v"
	@$(COQEXEC) ./extraction/Extraction.v
	@touch $@

Makefile.coq:
	@echo "COQMAKE Makefile.coq"
	@$(COQBIN)coq_makefile $(COQINCLUDES) $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

clean::
	rm -f */*.v.d */*.glob */*.vo */*~ *~
