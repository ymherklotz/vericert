VERICERT ?= vericert
VERICERT_OPTS ?= -DSYNTHESIS -fschedule

IVERILOG ?= iverilog
IVERILOG_OPTS ?=

VERILATOR ?= verilator
VERILATOR_OPTS ?= -Wno-fatal --top main --exe /home/ymherklotz/projects/vericert/driver/verilator_main.cpp

TARGETS ?=

%.v: %.c
	$(VERICERT) $(VERICERT_OPTS) $< -o $@

%.iver: %.v
	$(IVERILOG) -o $@ $(IVERILOG_OPTS) $<

%.gcc: %.c
	$(CC) $(CFLAGS) $< -o $@

%.verilator: %.v
	$(VERILATOR) $(VERILATOR_OPTS) --Mdir $@ --cc $<
	$(MAKE) -C $@ -f Vmain.mk

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
