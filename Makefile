IGNORE:=

LIBVS:=$(wildcard CoqUp/Lib/*.v)
LIBVS:=$(filter-out $(IGNORE:%=%.v),$(LIBVS))

VS:=$(wildcard CoqUp/*.v)
VS:=$(filter-out $(LIBVS) $(IGNORE:%=%.v),$(VS))

.PHONY: coq clean

ARGS := -R CoqUp CoqUp

coq: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all

Makefile.coq.all: Makefile $(LIBVS) $(VS)
	$(COQBIN)coq_makefile $(ARGS) $(LIBVS) $(VS) -o Makefile.coq.all

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f Makefile.coq.all
