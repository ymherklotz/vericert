VERICERT ?= vericert
VERICERT_OPTS ?= -DSYNTHESIS

IVERILOG ?= iverilog
IVERILOG_OPTS ?=

TARGETS ?=

%.v: %.c
	$(VERICERT) $(VERICERT_OPTS) $< -o $@

%.iver: %.v
	$(IVERILOG) $(IVERILOG_OPTS) $< -o $@

%.gcc: %.c
	$(CC) $(CFLAGS) $< -o $@

%: %.iver %.gcc
	cp $< $@

all: $(TARGETS)

clean:
	rm -f *.iver
	rm -f *.v
	rm -f *.gcc
	rm -f $(TARGETS)

.PRECIOUS: %.v %.gcc %.iver
.PHONY: all clean
.SUFFIXES:
