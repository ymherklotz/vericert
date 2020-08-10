# Vericert

![CI](https://github.com/ymherklotz/vericert/workflows/CI/badge.svg)
![Admitted](https://ymherklotz.github.io/vericert/assets/admitted.svg)

A formally verified high-level synthesis (HLS) tool written in Coq, building on top of [CompCert](https://github.com/AbsInt/CompCert).  This ensures the correctness of the C to Verilog translation according to our Verilog semantics and CompCert's C semantics, removing the need to check the resulting hardware for behavioural correctness.

## Features

The project is currently a work in progress, so proofs remain to be finished.  Currently, the following C features are supported, but are not all proven correct yet:

- all int operations,
- non-recursive function calls,
- local arrays and pointers
- control-flow structures such as if-statements, for-loops, etc...

## Building

To build Vericert, the provided [Makefile](/Makefile) can be used. External dependencies are needed to build the project, which can be pulled in automatically with [nix](https://nixos.org/nix/) using the provided [default.nix](/default.nix) and [shell.nix](/shell.nix) files.

The project is written in Coq, a theorem prover, which is extracted to OCaml so that it can then be compiled and executed. The dependencies of this project are the following:

- [Coq](https://coq.inria.fr/): theorem prover that is used to also program the HLS tool.
- [OCaml](https://ocaml.org/): the OCaml compiler to compile the extracted files.
- [bbv](https://github.com/mit-plv/bbv): an efficient bit vector library.
- [dune](https://github.com/ocaml/dune): build tool for ocaml projects to gather all the ocaml files and compile them in the right order.
- [menhir](http://gallium.inria.fr/~fpottier/menhir/): parser generator for ocaml.
- [findlib](https://github.com/ocaml/ocamlfind) to find installed OCaml libraries.
- [GCC](https://gcc.gnu.org/): compiler to help build CompCert.

These dependencies can be installed manually, or automatically through Nix.

### Downloading CompCert

CompCert is added as a submodule in the `lib/CompCert` directory. It is needed to run the build process below, as it is the one dependency that is not downloaded by nix, and has to be downloaded together with the repository. To clone CompCert together with this project, you can run:

``` shell
git clone --recursive https://github.com/ymherklotz/vericert
```

If the repository is already cloned, you can run the following command to make sure that CompCert is also downloaded:

``` shell
git submodule update --init
```

### Setting up Nix

Nix is a package manager that can create an isolated environment so that the builds are reproducible. Once nix is installed, it can be used in the following way.

To open a shell which includes all the necessary dependencies, one can use:

``` shell
nix-shell
```

which will open a shell that has all the dependencies loaded.

### Makefile build

If the dependencies were installed manually, or if one is in the `nix-shell`, the project can be built by running:

``` shell
make -j8
```

and installed locally, or under the `PREFIX` location using:

``` shell
make install
```

Which will install the binary in `./bin/vericert` by default. However, this can be changed by changing the `PREFIX` environment variable, in which case the binary will be installed in `$PREFIX/bin/vericert`.

## Running

To test out `vericert` you can try the following examples which are in the test folder using the following:

``` shell
./bin/vericert test/loop.c -o loop.v
./bin/vericert test/conditional.c -o conditional.v
./bin/vericert test/add.c -o add.v
```
