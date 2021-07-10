TARGETS := floyd-warshall nussinov

include ../common.mk

floyd-warshall.v: floyd-warshall.c
	$(VERICERT) $(VERICERT_OPTS) -O0 -finline $< -o $@
