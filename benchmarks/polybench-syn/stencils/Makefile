TARGETS := adi fdtd-2d heat-3d jacobi-1d jacobi-2d seidel-2d

include ../common.mk

adi.v: adi.c
	@echo -e "\033[0;35mMAKE\033[0m" $<
	$(VERICERT) $(VERICERT_OPTS) -O0 -finline $< -o $@
