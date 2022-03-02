UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
	ARCH := verilog-linux
endif
ifeq ($(UNAME_S),Darwin)
	ARCH := verilog-macosx
endif

COQINCLUDES := -R src/common vericert.common \
               -R src/extraction vericert.extraction \
               -R src/hls vericert.hls \
               -R src vericert

COQEXEC := $(COQBIN)coqtop $(COQINCLUDES) -batch -load-vernac-source
COQMAKE := $(COQBIN)coq_makefile

COQDOCFLAGS := --no-lib-name -l

VS := src/Compiler.v src/Simulator.v src/HLSOpts.v $(foreach d, common hls bourdoncle, src/$(d)/*.v)

PREFIX ?= .

.PHONY: all install proof clean extraction test

all:
	$(MAKE) proof
	$(MAKE) compile

install:
	install -d $(PREFIX)/bin
	sed -i'' -e 's/arch=verilog/arch=x86/' _build/default/driver/compcert.ini
	install -C _build/default/driver/compcert.ini $(PREFIX)/bin/.
	install -C _build/default/driver/VericertDriver.exe $(PREFIX)/bin/vericert

proof: Makefile.coq
	$(MAKE) -f Makefile.coq
	@rm -f src/extraction/STAMP

doc: Makefile.coq
	$(MAKE) COQDOCFLAGS="$(COQDOCFLAGS)" -f Makefile.coq html
	cp ./docs/res/coqdoc.css html/.

doc-pdf: Makefile.coq
	$(MAKE) COQDOCFLAGS="$(COQDOCFLAGS)" -f Makefile.coq all.tex

extraction: src/extraction/STAMP

test:
	$(MAKE) -C test

compile: src/extraction/STAMP
	@echo "OCaml bin/vericert"
	@mkdir -p bin
	@dune build driver/VericertDriver.exe
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
	$(MAKE) -C test clean
	rm -f Makefile.coq

clean::
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f src/extraction/*.ml src/extraction/*.mli
