PREFIX ?= ..

all: synthesis-results

%: %.scm
	$(eval TMP := $(shell mktemp))
	echo "(main (command-line-arguments))" >$(TMP)
	chicken-csc -static -epilogue $(TMP) -output-file $@ $<
	rm $(TMP)

%.1: %.org
	emacs --batch --file $< --load ../docs/res/publish.el --funcall org-man-export-to-man
	mv $(<:.org=.man) $@

install: synthesis-results synthesis-results.1
	install -d $(PREFIX)/bin
	install -C synthesis-results $(PREFIX)/bin
	install -d $(PREFIX)/share/man/man1
	install -C -m 644 synthesis-results.1 $(PREFIX)/share/man/man1

clean:
	rm -f synthesis-results synthesis-results.1
	rm -f *.link

.PHONY: all install
