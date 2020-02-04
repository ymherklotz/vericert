IGNORE:=

LIBVS:=$(wildcard src/CoqUp/Lib/*.v)
LIBVS:=$(filter-out $(IGNORE:%=%.v),$(LIBVS))

VS:=$(wildcard src/CoqUp/*.v)
VS:=$(filter-out $(LIBVS) $(IGNORE:%=%.v),$(VS))

.PHONY: all install coq clean

ARGS := -R src/CoqUp CoqUp

all: coq

install:
	$(MAKE) -f Makefile.coq install

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(LIBVS) $(VS)
	$(COQBIN)coq_makefile $(ARGS) $(LIBVS) $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f Makefile.coq
