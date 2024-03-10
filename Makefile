UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
	ARCH := verilog-linux
endif
ifeq ($(UNAME_S),Darwin)
	ARCH := verilog-macosx
endif

COMPCERTRECDIRS := lib common verilog backend cfrontend driver exportclight cparser

COQINCLUDES := -R src/common vericert.common \
               -R src/extraction vericert.extraction \
               -R src/hls vericert.hls \
               -R src vericert \
               $(foreach d, $(COMPCERTRECDIRS), -R lib/CompCert/$(d) compcert.$(d)) \
               -R lib/CompCert/flocq Flocq \
               -R lib/CompCert/MenhirLib MenhirLib

COQEXEC := $(COQBIN)coqtop $(COQINCLUDES) -batch -load-vernac-source
COQMAKE := $(COQBIN)coq_makefile

COQDOCFLAGS := --no-lib-name -l

VS := src/Compiler.v src/Simulator.v src/HLSOpts.v $(foreach d, common hls, src/$(d)/*.v)

PREFIX ?= .

.PHONY: all install proof clean extraction test

all: lib/COMPCERTSTAMP
	$(MAKE) proof
	$(MAKE) compile

lib/CompCert/Makefile.config: lib/CompCert/configure
	(cd lib/CompCert && ./configure --ignore-coq-version $(ARCH))

lib/COMPCERTSTAMP: lib/CompCert/Makefile.config
	$(MAKE) HAS_RUNTIME_LIB=false CLIGHTGEN=false INSTALL_COQDEV=false -C lib/CompCert
	touch $@

install:
	install -d $(PREFIX)/bin
	sed -i'' -e 's/arch=verilog/arch=x86/' _build/default/driver/compcert.ini
	install -C _build/default/driver/compcert.ini $(PREFIX)/bin/.
	install -C _build/default/driver/VericertDriver.exe $(PREFIX)/bin/vericert-original

proof: Makefile.coq
	$(MAKE) -f Makefile.coq
	@rm -f src/extraction/STAMP

doc: Makefile.coq
	$(MAKE) COQDOCFLAGS="$(COQDOCFLAGS)" -f Makefile.coq html

extraction: src/extraction/STAMP

test:
	./test/test_all.sh ./test

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
	rm -f Makefile.coq

clean::
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f src/extraction/*.ml src/extraction/*.mli
