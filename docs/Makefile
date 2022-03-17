all: manual src man-html

install-deps:
	emacs --batch --load ./res/install-deps.el

%.man: %.org
	emacs --batch --file $< --load ./res/publish.el --funcall org-man-export-to-man

%.html: %.org
	emacs --batch --file $< --load ./res/publish.el --funcall org-html-export-to-html

manual:
	mkdir -p manual
	emacs --batch --file documentation.org --load ./res/publish.el --funcall org-texinfo-export-to-texinfo
	makeinfo --html --number-sections --no-split \
        --css-ref "https://www.gnu.org/software/emacs/manual.css" \
        vericert.texi -o ./manual/index.html
	cp -r images ./manual/.

man-html: man.html
	mkdir -p man
	cp man.html ./man/vericert.1.html

vericert.1: man.man
	cp $< $@

src:
	$(MAKE) -C .. doc
	cp -r ../html src

upload:
	tar caf docs.tar.xz manual man src
	rsync docs.tar.xz "zk@leika.ymhg.org:~"

.PHONY: all upload manual man src install-deps man-html

clean:
	rm -rf manual man src
	rm -f docs.tar.xz
