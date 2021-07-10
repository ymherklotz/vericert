VERICERT ?= vericert
VERICERT_OPTS ?= -DSYNTHESIS

IVERILOG ?= iverilog
IVERILOG_OPTS ?=

%.v: %.c
	$(VERICERT) $(VERICERT_OPTS) $< -o $@

%.iver: %.v
	$(IVERILOG) $(IVERILOG_OPTS) $< -o $@

%.gcc: %.c
	$(CC) $(CFLAGS) $< -o $@

%: %.iver %.gcc
	cp $< $@

clean:
	rm -f *.iver
	rm -f *.v
	rm -f *.gcc

.PRECIOUS: %.v
.PHONY: all clean
.SUFFIXES:
