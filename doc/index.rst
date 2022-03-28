.. Vericert documentation master file, created by
   sphinx-quickstart on Sat Mar 26 18:15:40 2022.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

Vericert's Documentation
========================

A formally verified high-level synthesis (HLS) tool written in Coq, building on top of `CompCert
<https://github.com/AbsInt/CompCert>`_ This ensures the correctness of the C to Verilog translation
according to our Verilog semantics and CompCert's C semantics, removing the need to check the
resulting hardware for behavioural correctness.

Features
--------

The project is currently a work in progress.  Currently, the following C features are supported and
have all been proven correct, providing a verified translation from C to Verilog:

- all int operations,
- non-recursive function calls,
- local arrays and pointers, and
- control-flow structures such as if-statements, for-loops, etc...

.. toctree::
   :maxdepth: 2
   :caption: Content

   vericert

.. toctree::
   :maxdepth: 1
   :caption: Sources

   src/Compiler
   src/hls/RTLBlockInstr
   src/hls/RTLBlockgen
   src/hls/RTLBlockgenproof

Publications
------------

:OOPSLA '21: Yann Herklotz, James D. Pollard, Nadesh Ramanathan, and John Wickerson. Formal
             Verification of High-Level Synthesis. In *Proc. ACM Program. Lang.* 5, OOPSLA, 2021.

:LATTE '21: Yann Herklotz and John Wickerson. High-level synthesis tools should be proven
            correct. In *Workshop on Languages, Tools, and Techniques for Accelerator
            Design*, 2021.

Mailing lists
-------------

For discussions, you can join the following mailing list: `lists.sr.ht/~ymherklotz/vericert-discuss <https://lists.sr.ht/~ymherklotz/vericert-discuss>`_.

For contributing patches to the `sourcehut <https://sr.ht/~ymherklotz/vericert/>`_ repository:
`lists.sr.ht/~ymherklotz/vericert-devel <https://lists.sr.ht/~ymherklotz/vericert-devel>`_.

Indices
=======

* :ref:`genindex`
* :ref:`search`
