CC ?= gcc
VERICERT ?= vericert
VERICERT_OPTS ?= -fschedule -fif-conv
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

%.v: %.c
	$(VERICERT) $(VERICERT_OPTS) -o $@ $<

%.iver: %.v
	@$(IVERILOG) $(IVERILOG_OPTS) -o $@ -- $<

%.veri.out: %.iver
	@./$< | tail -n1 | sed -r -e 's/[^0-9]*([0-9]+)/\1/' >$@

%.check: %.gcc.out %.veri.out
	@diff $^ >$@
	@printf "\033[0;36mOK\033[0m\t$(patsubst %.check,%,$@)\n"

clean:
	rm -f *.check *.gcc *.gcc.out *.o *.v *.iver *.veri.out
