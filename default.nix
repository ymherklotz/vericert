with import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/00197eff36bb8f7dd7f53a59f730e1fd8e11b1f4.tar.gz") {};
let
  ncoq = coq_8_14;
  ncoqPackages = coqPackages_8_14;
  ncompcert = ncoqPackages.callPackage
    ( { coq, flocq, ocamlPackages, gcc, stdenv, fetchFromGithub, mkCoqDerivation }:
      mkCoqDerivation {
        pname = "compcert";
        owner = "ymherklotz";
        releaseRev = v: "v${v}";

        defaultVersion = "3.10";

        src = fetchFromGitHub {
          owner = "ymherklotz";
          repo = "CompCert";
          rev = "4fa0349a2f5477a78b249ac0e762a5d32e0722d7";
          sha256 = "Rqw9xvqyT43IfhNpuCN3guUb+62bhPOA/O8Frg3Poxc=";
        };

        buildInputs = with ocamlPackages; [ ocaml findlib gcc menhir menhirLib ] ++ [ coq ];
        propagatedBuildInputs = [ flocq ];

        enableParallelBuilding = true;

        outputs = [ "out" "lib" ];

        configurePhase = ''
          ./configure \
          -prefix $out \
          -coqdevdir $lib/lib/coq/${coq.coq-version}/user-contrib/compcert/ \
          -no-runtime-lib \
          -no-standard-headers \
          -install-coqdev \
          -use-external-Flocq \
          ${if stdenv.isDarwin then "verilog-macosx" else "verilog-linux"}
        '';

        meta = with lib; {
          description = "Formally verified C compiler";
          homepage    = "https://compcert.org";
          license     = licenses.inria-compcert;
          platforms   = [ "x86_64-linux" "x86_64-darwin" ];
          maintainers = [ ];
        };
      } ) { } ;
in
ncoqPackages.mkCoqDerivation {
  pname = "vericert";
  src = ./.;

  owner = "ymherklotz";
  releaseRev = v: "v${v}";

  defaultVersion = "3.10";

  buildInputs = with ncoq.ocamlPackages; [ ncoq dune_2 gcc
                                           ncoq.ocaml findlib
                                           ocamlgraph merlin
                                           ncompcert
                                         ];

  enableParallelBuilding = true;
}
