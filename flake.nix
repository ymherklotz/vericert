{
  description = "Vericert dependencies";

  inputs = { nixpkgs.url = "github:nixos/nixpkgs"; };

  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      ncoq = pkgs.coq_8_14;
      ncoqPackages = pkgs.coqPackages_8_14;
      dpkgs = nixpkgs.legacyPackages.x86_64-darwin;
      dncoq = dpkgs.coq_8_14;
      dncoqPackages = dpkgs.coqPackages_8_14;
    in {
      devShell.x86_64-linux = pkgs.mkShell {
        buildInputs = with pkgs;
          [ ncoq
            dune_2
            gcc
            ncoq.ocaml
            ncoq.ocamlPackages.findlib
            ncoq.ocamlPackages.menhir
            ncoq.ocamlPackages.ocamlgraph
            ncoq.ocamlPackages.menhirLib

            ncoq.ocamlPackages.ocp-indent
            ncoq.ocamlPackages.utop

            ncoqPackages.serapi
            python3
            python3Packages.alectryon
            python3Packages.sphinx_rtd_theme
          ];
      };
      devShell.x86_64-darwin = dpkgs.mkShell {
        buildInputs = with dpkgs;
          [ dncoq
            dune_2
            gcc
            dncoq.ocaml
            dncoq.ocamlPackages.findlib
            dncoq.ocamlPackages.menhir
            dncoq.ocamlPackages.ocamlgraph
            dncoq.ocamlPackages.menhirLib

            dncoq.ocamlPackages.ocp-indent
            dncoq.ocamlPackages.utop

            dncoqPackages.serapi
            python3
            python3Packages.alectryon
            python3Packages.sphinx_rtd_theme
          ];
      };
    };
}
