with import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/8dd8bd8be74879f9f7919b16a4cb5ab2a75f18e5.tar.gz") {};
let
  ncoq = coq_8_13;
  ncoqPackages = coqPackages_8_13;
in
stdenv.mkDerivation {
  name = "vericert";
  src = ./.;

  buildInputs = [ ncoq dune_2 gcc
                  ncoq.ocaml ncoq.ocamlPackages.findlib ncoq.ocamlPackages.menhir
                  ncoq.ocamlPackages.ocamlgraph
                ];

  enableParallelBuilding = true;
}
