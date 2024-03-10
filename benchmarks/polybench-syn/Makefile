VERICERT ?= /home/pldi/vericert-pldi2024/bin/vericert
VERICERT_OPTS ?= -DSYNTHESIS -fschedule

IVERILOG ?= iverilog
IVERILOG_OPTS ?=

VERILATOR ?= verilator
VERILATOR_OPTS ?= -Wno-fatal -Wno-lint -Wno-style -Wno-WIDTH --top main --exe $(HOME)/vericert-pldi2024/scripts/verilator_main.cpp

TARGETS := $(foreach t,adi fdtd-2d heat-3d jacobi-1d jacobi-2d seidel-2d,stencils/$(t)) \
           $(foreach t,floyd-warshall nussinov,medley/$(t)) \
           $(foreach t,gemm gemver gesummv symm syr2k syrk trmm,linear-algebra/blas/$(t)) \
           $(foreach t,2mm 3mm atas bicg doitgen mvt,linear-algebra/kernels/$(t)) \
           $(foreach t,cholesky durbin lu ludcmp trisolv,linear-algebra/solvers/$(t)) \
           $(foreach t,covariance,data-mining/$(t))

all: $(TARGETS)

all-sv: $(foreach t,$(TARGETS),$(t).sv)
all-time-sv: $(foreach t,$(TARGETS),$(t).time.sv)

%.sv: %.c
	@echo -e "\033[0;35mMAKE\033[0m" $<
	$(VERICERT) $(VERICERT_OPTS) $< -o $@

%.time.sv: %.c
	@echo -e "\033[0;35mMAKE\033[0m" $<
	{ \
	start=$$(date +%s%N) ; \
	$(VERICERT) $(VERICERT_OPTS) $< -o $@ ; \
	end=$$(date +%s%N) ; \
	echo $(@:.time.sv=),$$(($$(($$end-$$start))/1000000)) >>time.csv ; \
    }

%.iver: %.sv
	$(IVERILOG) -o $@ $(IVERILOG_OPTS) $<

%.gcc: %.c
	$(CC) $(CFLAGS) $< -o $@

%.verilator: %.sv
	$(VERILATOR) $(VERILATOR_OPTS) --Mdir $@ --cc $<
	@echo -e $(MAKE) -C $@ -f Vmain.mk
	@make -C $@ -f Vmain.mk &>/dev/null

%: %.iver %.gcc %.verilator
	cp $< $@

stencils/adi.sv: VERICERT_OPTS += -O0 -finline
stencils/adi.time.sv: VERICERT_OPTS += -O0 -finline

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

.PRECIOUS: %.sv %.gcc %.iver %.verilator
.PHONY: all clean
.SUFFIXES:
