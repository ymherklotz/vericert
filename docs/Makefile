all: manual src man-html

install-deps:
	emacs --batch --load ./res/install-deps.el

manual:
	mkdir -p manual
	emacs --batch --file documentation.org --load ./res/publish-manual.el
	makeinfo --html --number-sections --no-split \
        --css-ref "https://www.gnu.org/software/emacs/manual.css" \
        vericert.texi -o ./manual/index.html
	cp -r images ./manual/.

man-html:
	mkdir -p man
	emacs --batch --file man.org --load ./res/publish-html.el
	cp man.html ./man/vericert.1.html

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
