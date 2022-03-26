with import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/00197eff36bb8f7dd7f53a59f730e1fd8e11b1f4.tar.gz") {};
let
  ncoq = coq_8_14;
  ncoqPackages = coqPackages_8_14;
in
stdenv.mkDerivation {
  name = "vericert";
  src = ./.;

  buildInputs = [ ncoq dune_2 gcc
                  ncoq.ocaml ncoq.ocamlPackages.findlib ncoq.ocamlPackages.menhir
                  ncoq.ocamlPackages.ocamlgraph ncoq.ocamlPackages.merlin
                  ncoq.ocamlPackages.menhirLib

                  ncoqPackages.serapi
                  python3
                  python3Packages.alectryon
                ];

  enableParallelBuilding = true;
}
