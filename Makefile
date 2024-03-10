UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
	ARCH := verilog-linux
endif
ifeq ($(UNAME_S),Darwin)
	ARCH := verilog-macosx
endif
ifeq ($(UNAME_S),FreeBSD)
	ARCH := verilog-bsd
endif

COMPCERTRECDIRS := lib common verilog backend cfrontend driver cparser

COQINCLUDES := -R src vericert \
               $(foreach d, $(COMPCERTRECDIRS), -R lib/CompCert/$(d) compcert.$(d)) \
               -R lib/CompCert/flocq Flocq \
               -R lib/CompCert/MenhirLib MenhirLib \
               -R lib/cohpred/theory cohpred_theory \
               -R lib/cohpred/smtcoq/src SMTCoq


COQEXEC := $(COQBIN)coqtop $(COQINCLUDES) -batch -load-vernac-source
COQMAKE := $(COQBIN)coq_makefile

COQDOCFLAGS := --no-lib-name -l
ALECTRYON_OPTS := --no-header --html-minification --long-line-threshold 80 \
                  --coq-driver sertop_noexec $(COQINCLUDES)

VS := src/Compiler.v src/Simulator.v src/HLSOpts.v $(foreach d, common hls bourdoncle, $(wildcard src/$(d)/*.v))

PREFIX ?= .

.PHONY: all install proof clean extraction test force

all: lib/COMPCERTSTAMP lib/COHPREDSTAMP
	$(MAKE) proof
	$(MAKE) compile

lib/CompCert/Makefile.config: lib/CompCert/configure
	(cd lib/CompCert && ./configure --ignore-coq-version $(ARCH))

lib/COMPCERTSTAMP: lib/CompCert/Makefile.config
	$(MAKE) HAS_RUNTIME_LIB=false CLIGHTGEN=false INSTALL_COQDEV=false -C lib/CompCert
	touch $@

lib/COHPREDSTAMP:
	$(MAKE) -C lib/cohpred
	touch lib/COHPREDSTAMP

install: doc/vericert.1
	sed -i'' -e 's/arch=verilog/arch=x86/' _build/default/driver/compcert.ini
	install -d $(PREFIX)/bin
	install -C -m 644 _build/default/driver/compcert.ini $(PREFIX)/bin
	install -C _build/default/driver/VericertDriver.exe $(PREFIX)/bin/vericert
	install -d $(PREFIX)/share/man/man1
	install -C -m 644 $< $(PREFIX)/share/man/man1

install-test: # doc/vericert.1
	sed -i'' -e 's/arch=verilog/arch=x86/' _build/default/driver/compcert.ini
	install -d $(PREFIX)/bin
	install -C -m 644 _build/default/driver/compcert.ini $(PREFIX)/bin
	install -C _build/default/debug/VericertTest.exe $(PREFIX)/bin/vericert-test

proof: Makefile.coq
	$(MAKE) -f Makefile.coq
	@rm -f src/extraction/STAMP

doc-html: $(patsubst src/%.v,html/%.html,$(VS))

html/%.html: src/%.v
	@mkdir -p $(dir $@)
	@echo "ALECTRYON" $@; alectryon $(ALECTRYON_OPTS) $< -o $@

coqdoc: Makefile.coq
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

Makefile.coq _CoqProject: force
	@echo "COQMAKE Makefile.coq"
	$(COQBIN)coq_makefile $(COQINCLUDES) $(VS) -o Makefile.coq
	echo "$(COQINCLUDES)" >_CoqProject

force:

doc/vericert.1:
	$(MAKE) -C doc -f Makefile.extr vericert.1

detangle-all:
	emacs --batch --eval "(progn(require 'org)(require 'ob-tangle)\
        (setq org-src-preserve-indentation t)\
        $(foreach vs,$(VS),(org-babel-detangle \"$(vs)\"))\
        (org-save-all-org-buffers))"

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -C test clean
	rm -f Makefile.coq

clean::
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f src/extraction/*.ml src/extraction/*.mli

clean-all:
	(cd lib/CompCert; git clean -dfx)
	(cd lib/cohpred/smtcoq; git clean -dfx)
	(cd lib/cohpred; git clean -dfx)
	git clean -dfx
