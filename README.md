# Coqup

A formally verified HLS tool in Coq, building on top of [CompCert](https://github.com/AbsInt/CompCert).

## Building

To build coqup, the provided [Makefile](/Makefile) can be used. External dependencies are needed to build the project, which can be pulled in automatically with [nix](https://nixos.org/nix/) using the provided [default.nix](/default.nix) and [shell.nix](/shell.nix) files.

The project is written in Coq, a theorem prover, which is extracted to OCaml so that it can then be compiled and executed. The dependencies of this project are the following:

- [Coq](https://coq.inria.fr/): theorem prover that is used to also program the HLS tool.
- [OCaml](https://ocaml.org/): the OCaml compiler to compile the extracted files.
- [bbv](https://github.com/mit-plv/bbv): an efficient bit vector library.
- [dune](https://github.com/ocaml/dune): build tool for ocaml projects to gather all the ocaml files and compile them in the right order.
- [menhir](http://gallium.inria.fr/~fpottier/menhir/): parser generator for ocaml.
- [findlib](https://github.com/ocaml/ocamlfind) to find installed OCaml libraries.
- [GCC](https://gcc.gnu.org/): compiler to help build CompCert.

These dependencies can be installed manually, or automatically through Nix.

### Setting up Nix

Nix is a package manager that can create an isolated environment so that the builds are reproducible. Once nix is installed, it can be used in the following way.

To just build the project once, the following command can be executed.

``` shell
nix-build
```

The output will then be in `results/bin/coqup`.

To open a shell which includes all the necessary dependencies instead, one can use:

``` shell
nix-shell
```

which will open a shell that has all the dependencies loaded.

### Makefile build

If the dependencies were installed manually, or if one is in the `nix-shell`, the project can be built by running:

``` shell
make
```

Which will install the binary in `./bin/coqup` by default. However, this can be changed by changing the `PREFIX` environment variable, in which case the binary will be installed in `$PREFIX/bin/coqup`.
