VERICERT ?= /Users/ymherklotz/projects/vericert/bin/vericert
VERICERT_OPTS ?= -DSYNTHESIS -fschedule -fif-conv -dgblseq -dgblpar

IVERILOG ?= iverilog
IVERILOG_OPTS ?=

VERILATOR ?= verilator
VERILATOR_OPTS ?= -Wno-fatal -Wno-lint -Wno-style -Wno-WIDTH --top main --exe $(HOME)/projects/vericert/scripts/verilator_main.cpp

TARGETS ?=

%.sv: %.c
	@echo -e "\033[0;35mMAKE\033[0m" $<
	$(VERICERT) $(VERICERT_OPTS) $< -o $@

%.iver: %.sv
	$(IVERILOG) -o $@ $(IVERILOG_OPTS) $<

%.gcc: %.c
	$(CC) $(CFLAGS) $< -o $@

%.verilator: %.sv
	$(VERILATOR) $(VERILATOR_OPTS) --Mdir $@ --cc $<
	@echo -e $(MAKE) -C $@ -f Vmain.mk
	@$(MAKE) -C $@ -f Vmain.mk &>/dev/null

%: %.iver %.gcc %.verilator
	cp $< $@

all: $(TARGETS)

clean:
	rm -f *.iver
	rm -f *.v
	rm -f *.sv
	rm -f *.gcc
	rm -f *.clog
	rm -f *.tmp
	rm -f $(TARGETS)
	rm -f *.{0,1,2,3,4,5,6,7,8,9}
	rm -f *.smt2
	rm -f *.log
	rm -f *.dot
	rm -f *.vtlog
	rm -f *.txt
	rm -rf *.verilator

.PRECIOUS: %.v %.gcc %.iver
.PHONY: all clean
.SUFFIXES:
