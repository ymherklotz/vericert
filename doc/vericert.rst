===============
Vericert Manual
===============


Introduction
------------

Vericert translates C code into a hardware description language called Verilog, which can then be
synthesised into hardware, to be placed onto a field-programmable gate array (FPGA) or
application-specific integrated circuit (ASIC).

.. _fig:design:

.. figure:: /_static/images/toolflow.png

    Current design of Vericert, where HTL is an intermediate language representing a finite state
    machine with data-path (FSMD) and Verilog is the target language.

The design shown in Figure `fig:design`_ shows how Vericert leverages an existing verified C
compiler called `CompCert <https://compcert.org/compcert-C.html>`_ to perform this translation.

.. index:: vericert

.. _building:

Building Vericert
-----------------


Testing
~~~~~~~

To test out ``vericert`` you can try the following examples which are in the test folder using the
following:

.. code:: shell

    ./bin/vericert test/loop.c -o loop.v
    ./bin/vericert test/conditional.c -o conditional.v
    ./bin/vericert test/add.c -o add.v

Or by running the test suite using the following command:

.. code:: shell

    make test

.. _using-vericert:

.. index:: vericert

Using Vericert
--------------

Vericert can be used to translate a subset of C into Verilog.  As a simple example, consider the
following C file (``main.c``):

.. code:: C

    void matrix_multiply(int first[2][2], int second[2][2], int multiply[2][2]) {
        int sum = 0;
        for (int c = 0; c < 2; c++) {
            for (int d = 0; d < 2; d++) {
                for (int k = 0; k < 2; k++) {
                    sum = sum + first[c][k]*second[k][d];
                }
                multiply[c][d] = sum;
                sum = 0;
            }
        }
    }

    int main() {
        int f[2][2] = {{1, 2}, {3, 4}};
        int s[2][2] = {{5, 6}, {7, 8}};
        int m[2][2] = {{0, 0}, {0, 0}};

        matrix_multiply(f, s, m);
        return m[1][1];
    }

It can be compiled using the following command, assuming that vericert is somewhere on the path.

.. code:: shell

    vericert main.c -o main.v

The Verilog file contains a top-level test-bench, which can be given to any Verilog simulator to
simulate the hardware, which should give the same result as executing the C code.  Using `Icarus
Verilog <http://iverilog.icarus.com/>`_ as an example:

.. code:: shell

    iverilog -o main_v main.v

When executing, it should therefore print the following:

.. code:: shell

    $ ./main_v
    finished: 50

This gives the same result as executing the C in the following way:

.. code:: shell

    $ gcc -o main_c main.c
    $ ./main_c
    $ echo $?
    50

Man pages
~~~~~~~~~

.. _unreleased-features:

Unreleased Features
-------------------

The following are unreleased features in Vericert that are currently being worked on and have not
been completely proven correct yet.  Currently this includes features such as:

- `scheduling`_,

- `operation-chaining`_,

- `if-conversion`_, and

- `functions`_.

This page gives some preliminary information on how the features are implemented and how the proofs
for the features are being done.  Once these features are properly implemented, they will be added
to the proper documentation.

.. _scheduling:

Scheduling
~~~~~~~~~~

Scheduling is an optimisation which is used to run various instructions in parallel that are
independent to each other.

.. _operation-chaining:

Operation Chaining
~~~~~~~~~~~~~~~~~~

Operation chaining is an optimisation that can be added on to scheduling and allows for the
sequential execution of instructions in a clock cycle, while executing other instructions in
parallel in the same clock cycle.

.. _if-conversion:

If-conversion
~~~~~~~~~~~~~

If-conversion is an optimisation which can turn code with simple control flow into a single block
(called a hyper-block), using predicated instructions.

.. _functions:

Functions
~~~~~~~~~

Functions are currently only inlined in Vericert, however, we are working on a proper interface to
integrate function calls into the hardware.

.. _coq-style-guide:

Coq Style Guide
---------------

This style guide was taken from `Silveroak <https://github.com/project-oak/silveroak>`_, it outlines
code style for Coq code in this repository. There are certainly other valid strategies and opinions
on Coq code style; this is laid out purely in the name of consistency. For a visual example of the
style, see the `example`_ at the bottom of this file.

.. _code-organization:

Code organization
~~~~~~~~~~~~~~~~~

.. _legal-banner:

Legal banner
^^^^^^^^^^^^

- Files should begin with a copyright/license banner, as shown in the example above.

.. _import-statements:

Import statements
^^^^^^^^^^^^^^^^^

- ``Require Import`` statements should all go at the top of the file, followed by file-wide ``Import``
  statements.

  - =Import=s often contain notations or typeclass instances that might override notations or
    instances from another library, so it’s nice to highlight them separately.

- One ``Require Import`` statement per line; it’s easier to scan that way.

- ``Require Import`` statements should use “fully-qualified” names (e.g. ``Require Import
  Coq.ZArith.ZArith`` instead of ``Require Import ZArith``).

  - Use the ``Locate`` command to find the fully-qualified name!

- ``Require Import``’s should go in the following order:

  1. Standard library dependencies (start with ``Coq.``)

  2. External dependencies (anything outside the current project)

  3. Same-project dependencies

- ``Require Import``’s with the same root library (the name before the first ``.``) should be
  grouped together. Within each root-library group, they should be in alphabetical order (so
  ``Coq.Lists.List`` before ``Coq.ZArith.ZArith``).

.. _notations-and-scopes:

Notations and scopes
^^^^^^^^^^^^^^^^^^^^

- Any file-wide ``Local Open Scope``’s should come immediately after the =Import=s (see example).

  - Always use ``Local Open Scope``; just ``Open Scope`` will sneakily open the scope for those who
    import your file.

- Put notations in their own separate modules or files, so that those who import your file can
  choose whether or not they want the notations.

  - Conflicting notations can cause a lot of headache, so it comes in very handy to leave this
    flexibility!

.. _formatting:

Formatting
~~~~~~~~~~

.. _line-length:

Line length
^^^^^^^^^^^

- Maximum line length 80 characters.

  - Many Coq IDE setups divide the screen in half vertically and use only half to display source
    code, so more than 80 characters can be genuinely hard to read on a laptop.

.. _whitespace-and-indentation:

Whitespace and indentation
^^^^^^^^^^^^^^^^^^^^^^^^^^

- No trailing whitespace.

- Spaces, not tabs.

- Files should end with a newline.

  - Many editors do this automatically on save.

- Colons may be either “English-spaced”, with no space before the colon and one space after (``x:
  nat``) or “French-spaced”, with one space before and after (``x : nat``).

- Default indentation is 2 spaces.

  - Keeping this small prevents complex proofs from being indented ridiculously far, and matches IDE
    defaults.

- Use 2-space indents if inserting a line break immediately after:

  - ``Proof.``

  - ``fun <...> =>``

  - ``forall <...>,``

  - ``exists <....>,``

- The style for indenting arguments in function application depends on where you make a line
  break. If you make the line break immediately after the function name, use a 2-space
  indent. However, if you make it after one or more arguments, align the next line with the first
  argument:

  .. code:: coq

      (Z.pow
         1 2)
      (Z.pow 1 2 3
             4 5 6)

- ``Inductive`` cases should not be indented. Example:

  .. code:: coq

      Inductive Foo : Type :=
      | FooA : Foo
      | FooB : Foo
      .

- ``match`` or ``lazymatch`` cases should line up with the “m” in ``match`` or “l” in ``lazymatch``,
  as in the following examples:

  .. code:: coq

      match x with
      | 3 => true
      | _ => false
      end.

      lazymatch x with
      | 3 => idtac
      | _ => fail "Not equal to 3:" x
      end.

      repeat match goal with
             | _ => progress subst
             | _ => reflexivity
             end.

      do 2 lazymatch goal with
           | |- context [eq] => idtac
           end.

.. _definitions-and-fixpoints:

Definitions and Fixpoints
~~~~~~~~~~~~~~~~~~~~~~~~~

- It’s okay to leave the return type of ``Definition``’s and ``Fixpoint``’s implicit
  (e.g. ``Definition x := 5`` instead of ``Definition x : nat := 5``) when the type is very simple
  or obvious (for instance, the definition is in a file which deals exclusively with operations on
  ``Z``).

.. _inductives:

Inductives
~~~~~~~~~~

- The ``.`` ending an ``Inductive`` can be either on the same line as the last case or on its own
  line immediately below. That is, both of the following are acceptable:

  .. code:: coq

      Inductive Foo : Type :=
      | FooA : Foo
      | FooB : Foo
      .
      Inductive Foo : Type :=
      | FooA : Foo
      | FooB : Foo.

.. _lemmatheorem-statements:

Lemma/Theorem statements
~~~~~~~~~~~~~~~~~~~~~~~~

- Generally, use ``Theorem`` for the most important, top-level facts you prove and ``Lemma`` for
  everything else.

- Insert a line break after the colon in the lemma statement.

- Insert a line break after the comma for ``forall`` or ``exist`` quantifiers.

- Implication arrows (``->``) should share a line with the previous hypothesis, not the following
  one.

- There is no need to make a line break after every ``->``; short preconditions may share a line.

.. _proofs-and-tactics:

Proofs and tactics
~~~~~~~~~~~~~~~~~~

- Use the ``Proof`` command (lined up vertically with ``Lemma`` or ``Theorem`` it corresponds to) to
  open a proof, and indent the first line after it 2 spaces.

- Very small proofs (where ``Proof. <tactics> Qed.`` is <= 80 characters) can go all in one line.

- When ending a proof, align the ending statement (``Qed``, ``Admitted``, etc.) with ``Proof``.

- Avoid referring to autogenerated names (e.g. ``H0``, ``n0``). It’s okay to let Coq generate these
  names, but you should not explicitly refer to them in your proof. So ``intros; my_solver`` is
  fine, but ``intros; apply H1; my_solver`` is not fine.

  - You can force a non-autogenerated name by either putting the variable before the colon in the
    lemma statement (``Lemma foo x : ...`` instead of ``Lemma foo : forall x, ...``), or by passing
    arguments to ``intros`` (e.g. ``intros ? x`` to name the second argument ``x``)

- This way, the proof won’t break when new hypotheses are added or autogenerated variable names
  change.

- Use curly braces ``{}`` for subgoals, instead of bullets.

- *Never write tactics with more than one subgoal focused.* This can make the proof very confusing
  to step through! If you have more than one subgoal, use curly braces.

- Consider adding a comment after the opening curly brace that explains what case you’re in (see
  example).

  - This is not necessary for small subgoals but can help show the major lines of reasoning in large
    proofs.

- If invoking a tactic that is expected to return multiple subgoals, use ``[ | ... | ]`` before the
  ``.`` to explicitly specify how many subgoals you expect.

  - Examples: ``split; [ | ].`` ``induction z; [ | | ].``

  - This helps make code more maintainable, because it fails immediately if your tactic no longer
    solves as many subgoals as expected (or unexpectedly solves more).

- If invoking a string of tactics (composed by ``;``) that will break the goal into multiple
  subgoals and then solve all but one, still use ``[ ]`` to enforce that all but one goal is solved.

  - Example: ``split; try lia; [ ]``.

- Tactics that consist only of ``repeat``-ing a procedure (e.g. ``repeat match``, ``repeat first``)
  should factor out a single step of that procedure a separate tactic called ``<tactic name>_step``,
  because the single-step version is much easier to debug. For instance:

  .. code:: coq

      Ltac crush_step :=
        match goal with
        | _ => progress subst
        | _ => reflexivity
        end.
      Ltac crush := repeat crush_step.

.. _naming:

Naming
~~~~~~

- Helper proofs about standard library datatypes should go in a module that is named to match the
  standard library module (see example).

  - This makes the helper proofs look like standard-library ones, which is helpful for categorizing
    them if they’re genuinely at the standard-library level of abstraction.

- Names of modules should start with capital letters.

- Names of inductives and their constructors should start with capital letters.

- Names of other definitions/lemmas should be snake case.

.. _example:

Example
~~~~~~~

A small standalone Coq file that exhibits many of the style points.

.. code:: coq

    (*
     * Vericert: Verified high-level synthesis.
     * Copyright (C) 2021 Name <email@example.com>
     *
     * <License...>
     *)

      Require Import Coq.Lists.List.
      Require Import Coq.micromega.Lia.
      Require Import Coq.ZArith.ZArith.
      Import ListNotations.
      Local Open Scope Z_scope.

      (* Helper proofs about standard library integers (Z) go within [Module Z] so
         that they match standard-library Z lemmas when used. *)
      Module Z.
        Lemma pow_3_r x : x ^ 3 = x * x * x.
        Proof. lia. Qed. (* very short proofs can go all on one line *)

        Lemma pow_4_r x : x ^ 4 = x * x * x * x.
        Proof.
          change 4 with (Z.succ (Z.succ (Z.succ (Z.succ 0)))).
          repeat match goal with
                 | _ => rewrite Z.pow_1_r
                 | _ => rewrite Z.pow_succ_r by lia
                 | |- context [x * (?a * ?b)] =>
                   replace (x * (a * b)) with (a * b * x) by lia
                 | _ => reflexivity
                 end.
        Qed.
      End Z.
      (* Now we can access the lemmas above as Z.pow_3_r and Z.pow_4_r, as if they
         were in the ZArith library! *)

      Definition bar (x y : Z) := x ^ (y + 1).

      (* example with a painfully manual proof to show case formatting *)
      Lemma bar_upper_bound :
        forall x y a,
          0 <= x <= a -> 0 <= y ->
          0 <= bar x y <= a ^ (y + 1).
      Proof.
        (* avoid referencing autogenerated names by explicitly naming variables *)
        intros x y a Hx Hy. revert y Hy x a Hx.
        (* explicitly indicate # subgoals with [ | ... | ] if > 1 *)
        cbv [bar]; refine (natlike_ind _ _ _); [ | ].
        { (* y = 0 *)
          intros; lia. }
        { (* y = Z.succ _ *)
          intros.
          rewrite Z.add_succ_l, Z.pow_succ_r by lia.
          split.
          { (* 0 <= bar x y *)
            apply Z.mul_nonneg_nonneg; [ lia | ].
            apply Z.pow_nonneg; lia. }
          { (* bar x y < a ^ y *)
            rewrite Z.pow_succ_r by lia.
            apply Z.mul_le_mono_nonneg; try lia;
              [ apply Z.pow_nonneg; lia | ].
            (* For more flexible proofs, use match statements to find hypotheses
               rather than referring to them by autogenerated names like H0. In this
               case, we'll take any hypothesis that applies to and then solves the
               goal. *)
            match goal with H : _ |- _ => apply H; solve [auto] end. } }
      Qed.

      (* Put notations in a separate module or file so that importers can
         decide whether or not to use them. *)
      Module BarNotations.
        Infix "#" := bar (at level 40) : Z_scope.
        Notation "x '##'" := (bar x x) (at level 40) : Z_scope.
      End BarNotations.
