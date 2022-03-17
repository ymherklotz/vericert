PREFIX ?= ..

all: synthesis

%: %.scm
	chicken-csc -static -o $@ $<

%.1: %.org
	emacs --batch --file $< --load ../docs/res/publish.el --funcall org-man-export-to-man
	cp $(<:.org=.man) $@

install: synthesis-results synthesis-results.1
	install -d $(PREFIX)/bin
	install -C synthesis-results $(PREFIX)/bin
	install -d $(PREFIX)/share/man/man1
	install -C synthesis-results.1 $(PREFIX)/share/man/man1

.PHONY: all install
