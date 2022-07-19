CC ?= gcc
VERICERT ?= vericert
VERICERT_OPTS ?= -O0 -finline -fschedule -fif-conv -drtl -dgblseq -dgblpar
IVERILOG ?= iverilog
IVERILOG_OPTS ?=

TESTS := $(patsubst %.c,%.check,$(wildcard *.c))

all: $(TESTS)

%.gcc.out: %.gcc
	@./$< ; echo "$$?" >$@

%.o: %.c
	@$(CC) $(CFLAGS) -c -o $@ $<

%.gcc: %.o
	@$(CC) $(CFLAGS) -o $@ $<

%.sv: %.c
	$(VERICERT) $(VERICERT_OPTS) -o $@ $<

%.iver: %.sv
	@$(IVERILOG) $(IVERILOG_OPTS) -o $@ -- $<

%.veri.out: %.iver
	@./$< | tail -n1 | sed -r -e 's/[^0-9]*([0-9]+)/\1/' >$@

%.check: %.gcc.out %.veri.out
	@diff $^ >$@
	@printf "\033[0;36mOK\033[0m\t$(patsubst %.check,%,$@)\n"

clean:
	rm -f *.check *.gcc *.gcc.out *.o *.sv *.iver *.veri.out
