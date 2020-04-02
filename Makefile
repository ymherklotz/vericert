COMPCERTRECDIRS := lib common x86_64 x86 backend cfrontend driver flocq exportclight \
  MenhirLib cparser

COMPCERTCOQINCLUDES := $(foreach d, $(COMPCERTRECDIRS), -R lib/CompCert/$(d) compcert.$(d))

COQINCLUDES := -R src/common coqup.common -R src/verilog coqup.verilog \
               -R src/extraction coqup.extraction -R src/translation coqup.translation \
               -R src coqup $(COMPCERTCOQINCLUDES)

COQEXEC := $(COQBIN)coqtop $(COQINCLUDES) -batch -load-vernac-source
COQMAKE := "$(COQBIN)coq_makefile"

COQUPDIRS := translation common verilog
VSSUBDIR := $(foreach d, $(COQUPDIRS), src/$(d)/*.v)
VS := src/Compiler.v $(VSSUBDIR)

PREFIX ?= .

.PHONY: all install proof clean extraction test

all: lib/COMPCERTSTAMP
	$(MAKE) proof
	$(MAKE) compile

lib/COMPCERTSTAMP:
	(cd lib/CompCert && ./configure x86_64-linux)
	$(MAKE) -C lib/CompCert
	touch $@

install:
	install -d $(PREFIX)/bin
	install -C _build/default/driver/compcert.ini $(PREFIX)/bin/.
	install -C _build/default/driver/CoqupDriver.exe $(PREFIX)/bin/coqup

proof: Makefile.coq
	$(MAKE) -f Makefile.coq
	@rm -f src/extraction/STAMP

extraction: src/extraction/STAMP

test:
	./test/test_all.sh ./test

compile: src/extraction/STAMP
	@echo "OCaml bin/coqup"
	@mkdir -p bin
	@dune build driver/CoqupDriver.exe
	@cp lib/CompCert/compcert.ini _build/default/driver/.

src/extraction/STAMP:
	@echo "COQEXEC ./src/extraction/Extraction.v"
	@$(COQEXEC) ./src/extraction/Extraction.v
	@touch $@

Makefile.coq:
	@echo "COQMAKE Makefile.coq"
	$(COQBIN)coq_makefile $(COQINCLUDES) $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

clean::
	rm -f */*.v.d */*.glob */*.vo */*~ *~
