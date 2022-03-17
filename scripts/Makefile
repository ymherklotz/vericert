all: synthesis

synthesis: synthesis-results.scm
	chicken-csc -static -o $@ $<

install: synthesis
	install -s $< ~/.local/bin

.PHONY: all install
