# Minimal makefile for Sphinx documentation
#

# You can set these variables from the command line, and also
# from the environment for the first two.
SPHINXOPTS        ?=
SPHINXBUILD       ?= sphinx-build
SOURCEDIR         = .
BUILDDIR          = _build
SOURCE_DATE_EPOCH = $(shell git log -1 --format=%ct)

VS_DOCS := Compiler.v hls/RTLBlockInstr.v hls/RTLBlockgen.v hls/RTLBlockgenproof.v

# Put it first so that "make" without argument is like "make help".
help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

.PHONY: help Makefile

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefile
	$(foreach d,$(VS_DOCS),cp ../src/$(d) src/$(d);)
	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)
