- [Features](#features)
  - [Building](#building)
    - [Downloading Vericert and CompCert](#downloading-compcert)
    - [Setting up Nix](#setting-up-nix)
    - [Makefile build](#makefile-build)
  - [Running](#running)
  - [Citation](#org28fad40)
  - [License](#org5eb199f)

<a href="https://vericert.ymhg.org"><img src="https://vericert.ymhg.org/vericert-main.svg" width="100%" height="144" /></a>

<p align=center><a href="https://github.com/ymherklotz/vericert/actions"><img src="https://github.com/ymherklotz/vericert/workflows/CI/badge.svg" /></a>&nbsp;<a href="https://vericert.ymhg.org/"><img src="https://github.com/ymherklotz/vericert-docs/workflows/docs/badge.svg" /></a></p>

A formally verified high-level synthesis (HLS) tool written in Coq, building on top of [CompCert](https://github.com/AbsInt/CompCert). This ensures the correctness of the C to Verilog translation according to our Verilog semantics and CompCert&rsquo;s C semantics, removing the need to check the resulting hardware for behavioural correctness.


<a id="features"></a>

# Features

Currently all proofs of the following features have been completed.

-   all int operations,
-   non-recursive function calls,
-   local arrays and pointers
-   control-flow structures such as if-statements, for-loops, etc&#x2026;


<a id="building"></a>

# Building

To build Vericert, the provided [Makefile](file:///Makefile) can be used. External dependencies are needed to build the project, which can be pulled in automatically with [nix](https://nixos.org/nix/) using the provided [default.nix](file:///default.nix) and [shell.nix](file:///shell.nix) files.

The project is written in Coq, a theorem prover, which is extracted to OCaml so that it can then be compiled and executed. The dependencies of this project are the following:

-   [Coq](https://coq.inria.fr/): theorem prover that is used to also program the HLS tool.
-   [OCaml](https://ocaml.org/): the OCaml compiler to compile the extracted files.
-   [dune](https://github.com/ocaml/dune): build tool for ocaml projects to gather all the ocaml files and compile them in the right order.
-   [menhir](http://gallium.inria.fr/~fpottier/menhir/): parser generator for ocaml.
-   [findlib](https://github.com/ocaml/ocamlfind) to find installed OCaml libraries.
-   [GCC](https://gcc.gnu.org/): compiler to help build CompCert.

These dependencies can be installed manually, or automatically through Nix.


<a id="downloading-compcert"></a>

## Downloading Vericert and CompCert

CompCert is added as a submodule in the `lib/CompCert` directory. It is needed to run the build process below, as it is the one dependency that is not downloaded by nix, and has to be downloaded together with the repository. To clone CompCert together with this project, and check it out at the correct revision, you can run:

```shell
git clone -b v1.2.2 --recursive https://github.com/ymherklotz/vericert
```

If the repository is already cloned, you can run the following command to make sure that CompCert is also downloaded and the correct branch is checked out:

```shell
git checkout v1.2.2
git submodule update --init
```


<a id="setting-up-nix"></a>

## Setting up Nix

Nix is a package manager that can create an isolated environment so that the builds are reproducible. Once nix is installed, it can be used in the following way.

To open a shell which includes all the necessary dependencies, one can use:

```shell
nix-shell
```

which will open a shell that has all the dependencies loaded.


<a id="makefile-build"></a>

## Makefile build

If the dependencies were installed manually, or if one is in the `nix-shell`, the project can be built by running:

```shell
make -j8
```

and installed locally, or under the `PREFIX` location using:

```shell
  make install
```

Which will install the binary in `./bin/vericert` by default. However, this can be changed by changing the `PREFIX` environment variable, in which case the binary will be installed in `$PREFIX/bin/vericert`.


<a id="running"></a>

# Running

To test out `vericert` you can try the following examples which are in the test folder using the following:

```shell
./bin/vericert test/loop.c -o loop.v
./bin/vericert test/conditional.c -o conditional.v
./bin/vericert test/add.c -o add.v
```


<a id="org28fad40"></a>

# Citation

If you use Vericert in any way, please cite it using our [OOPSLA&rsquo;21 paper](https://yannherklotz.com/papers/fvhls_oopsla21.pdf):

```bibtex
@inproceedings{herklotz21_fvhls,
  author = {Herklotz, Yann and Pollard, James D. and Ramanathan, Nadesh and Wickerson, John},
  title = {Formal Verification of High-Level Synthesis},
  year = {2021},
  number = {OOPSLA},
  numpages = {30},
  month = {11},
  journal = {Proc. ACM Program. Lang.},
  volume = {5},
  publisher = {Association for Computing Machinery},
  address = {New York, NY, USA},
  doi = {10.1145/3485494}
}
```


<a id="org5eb199f"></a>

# License

This project is licensed under [GPLv3](https://www.gnu.org/licenses/gpl-3.0.en.html). The license can be seen in [LICENSE](LICENSE).

The following external code and its license is present in this repository:

-   **[src/pipelining](src/pipelining):** MIT

```text
Copyright (c) 2008,2009,2010 Jean-Baptiste Tristan and INRIA
```
