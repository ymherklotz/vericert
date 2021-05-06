with import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/269fc4ddb896c1c5994eb4bb8c750ec18cb3db82.tar.gz") {};
let
  ncoq = coq_8_12;
  ncoqPackages = coqPackages_8_12;
  bbv = ncoqPackages.callPackage
    ( { coq, stdenv, fetchFromGitHub }:
      stdenv.mkDerivation {
        name = "coq${coq.coq-version}-bbv";

        src = fetchFromGitHub {
          owner = "mit-plv";
          repo = "bbv";
          rev = "5099237c52d2910f79a1a3ca9ae4dfa80129bf86";
          sha256 = "0qnha333h7dc8105prdxvmkgy6l8swvyf6kz9v5s5dk4dvr5nra8";
        };

        buildInputs = with coq.ocamlPackages; [ ocaml camlp5 ];
        propagatedBuildInputs = [ coq ];
        enableParallelBuilding = true;

        installPhase = ''
          make -f Makefile.coq.all install COQLIB='$(out)/lib/coq/${coq.coq-version}/'
        '';
      } ) { };
in
stdenv.mkDerivation {
  name = "vericert";
  src = ./.;

  buildInputs = [ ncoq ncoqPackages.coqhammer cvc4 eprover z3-tptp dune_2 gcc
                  ocaml ocamlPackages.findlib ocamlPackages.menhir
                  ocamlPackages.ocamlgraph
                ];

  enableParallelBuilding = true;
}
