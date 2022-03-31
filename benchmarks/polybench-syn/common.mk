VERICERT ?= vericert
VERICERT_OPTS ?= -DSYNTHESIS -fschedule

IVERILOG ?= iverilog
IVERILOG_OPTS ?=

VERILATOR ?= verilator
VERILATOR_OPTS ?= -Wno-fatal -Wno-lint -Wno-style -Wno-WIDTH --top main --exe /home/ymherklotz/projects/vericert/scripts/verilator_main.cpp

TARGETS ?=

%.v: %.c
	@echo -e "\033[0;35mMAKE\033[0m" $<
	$(VERICERT) $(VERICERT_OPTS) $< -o $@

%.iver: %.v
	$(IVERILOG) -o $@ $(IVERILOG_OPTS) $<

%.gcc: %.c
	$(CC) $(CFLAGS) $< -o $@

%.verilator: %.v
	$(VERILATOR) $(VERILATOR_OPTS) --Mdir $@ --cc $<
	@echo -e $(MAKE) -C $@ -f Vmain.mk
	@$(MAKE) -C $@ -f Vmain.mk &>/dev/null

%: %.iver %.gcc %.verilator
	cp $< $@

all: $(TARGETS)

clean:
	rm -f *.iver
	rm -f *.v
	rm -f *.gcc
	rm -f *.clog
	rm -f *.tmp
	rm -f $(TARGETS)
	rm -rf *.verilator

.PRECIOUS: %.v %.gcc %.iver
.PHONY: all clean
.SUFFIXES:
