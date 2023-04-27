{
  description = "Vericert dependencies";

  inputs = { nixpkgs.url = "github:nixos/nixpkgs"; };

  outputs = { self, nixpkgs }:
    let vericertDevPackages = pkgs:
          let
            ncoq = pkgs.coq_8_17;
            ncoqPackages = pkgs.coqPackages_8_17;
          in
            pkgs.mkShell {
              buildInputs = with pkgs;
                [ ncoq ncoq.ocaml ncoqPackages.serapi dune_3 gcc python3 ]
                ++ (with ncoq.ocamlPackages; [ findlib menhir menhirLib ocamlgraph ocp-indent utop merlin ])
                ++ (with python3Packages; [ alectryon sphinx_rtd_theme ]);
            };
    in {
      devShell.x86_64-linux = vericertDevPackages nixpkgs.legacyPackages.x86_64-linux;
      devShell.x86_64-darwin = vericertDevPackages nixpkgs.legacyPackages.x86_64-darwin;
    };
}
