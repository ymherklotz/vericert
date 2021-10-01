with import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/1a56d76d718afb6c47dd96602c915b6d23f7c45d.tar.gz") {};
let
  ncoq = coq_8_13;
  ncoqPackages = coqPackages_8_13;
in
stdenv.mkDerivation {
  name = "vericert";
  src = ./.;

  buildInputs = [ ncoq dune_2 gcc
                  ncoq.ocaml ncoq.ocamlPackages.findlib ncoq.ocamlPackages.menhir
                  ncoq.ocamlPackages.ocamlgraph ncoq.ocamlPackages.merlin
                  ncoq.ocamlPackages.menhirLib

                  ncoqPackages.serapi
                  python3 python3Packages.docutils python3Packages.pygments
                  python3Packages.dominate
                  python3Packages.pelican
                ];

  enableParallelBuilding = true;
}
