COMPCERTRECDIRS := lib common $(ARCHDIRS) backend cfrontend driver flocq exportclight \
  MenhirLib cparser

COMPCERTCOQINCLUDES := $(foreach d, $(COMPCERTRECDIRS), -R lib/CompCert/$(d) compcert.$(d))

COQINCLUDES := -R src/Common CoqUp.Common -R src/Verilog CoqUp.Verilog -R src/Driver CoqUp.Driver -R src/Extraction CoqUp.Extraction $(COMPCERTCOQINCLUDES)

COQEXEC := $(COQBIN)coqtop $(COQINCLUDES) -batch -load-vernac-source
COQMAKE := "$(COQBIN)coq_makefile"

COQUPDIRS := SMTrans Common Driver Verilog
VS := $(foreach d, $(COQUPDIRS), src/$(d)/*.v)

.PHONY: all install proof clean

all:
	(cd lib/CompCert && ./configure x86_64-linux)
	$(MAKE) -C lib/CompCert all
	$(MAKE) proof
	$(MAKE) compile

install:
	$(MAKE) -f Makefile.coq install

proof: Makefile.coq
	$(MAKE) -f Makefile.coq

extraction: src/Extraction/STAMP

compile: src/Extraction/STAMP
	@echo "OCaml bin/coqup"
	@mkdir -p bin
	@dune build src/Extraction/Driver.exe
	@cp _build/default/src/Extraction/Driver.exe bin/coqup

src/Extraction/STAMP:
	@echo "COQEXEC ./src/Extraction/Extraction.v"
	@$(COQEXEC) ./src/Extraction/Extraction.v
	@touch $@

Makefile.coq:
	@echo "COQMAKE Makefile.coq"
	$(COQBIN)coq_makefile $(COQINCLUDES) $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

clean::
	rm -f */*.v.d */*.glob */*.vo */*~ *~
