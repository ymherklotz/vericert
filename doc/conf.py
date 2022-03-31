# Configuration file for the Sphinx documentation builder.
#
# This file only contains a selection of the most common options. For a full
# list see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Path setup --------------------------------------------------------------

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.
#
# import os
# import sys
# sys.path.insert(0, os.path.abspath('.'))


# -- Project information -----------------------------------------------------

project = 'Vericert'
copyright = '2022  Yann Herklotz, John Wickerson'
author = 'Yann Herklotz, John Wickerson'

# The full version, including alpha/beta/rc tags
release = 'v1.2.2'


# -- General configuration ---------------------------------------------------

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = [ "alectryon.sphinx" ]

# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store']

pygments_style = "emacs"


# -- Options for HTML output -------------------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
html_theme = 'sphinx_rtd_theme'

html_logo = "_static/images/vericert-main.svg"

html_theme_options = {
    'style_nav_header_background': '#fff5db'
}

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['_static']

html_css_files = [
    'css/custom.css',
]


# -- LaTeX configuration -----------------------------------------------------

latex_engine = "xelatex"


# -- Alectryon configuration -------------------------------------------------

import alectryon.docutils
alectryon.docutils.CACHE_DIRECTORY = "_build/alectryon/"
alectryon.docutils.LONG_LINE_THRESHOLD = 80

alectryon.docutils.AlectryonTransform.DRIVER_ARGS["sertop"] = [
    "-R" "../src,vericert",
    "-R" "../lib/CompCert/lib,compcert.lib",
    "-R" "../lib/CompCert/common,compcert.common",
    "-R" "../lib/CompCert/verilog,compcert.verilog",
    "-R" "../lib/CompCert/backend,compcert.backend",
    "-R" "../lib/CompCert/cfrontend,compcert.cfrontend",
    "-R" "../lib/CompCert/driver,compcert.driver",
    "-R" "../lib/CompCert/cparser,compcert.cparser",
    "-R" "../lib/CompCert/flocq,Flocq",
    "-R" "../lib/CompCert/MenhirLib,MenhirLib"
]
