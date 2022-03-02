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
          rev = "4f467596f8674f5f4fbf84a793cb8fcfc35a44a2";
          sha256 = "0m435pscfdb4irjxhzazzpl8jv63piwl4rb3nnpdirs9dg7msl2j";
        };

        buildInputs = with ocamlPackages; [ ocaml findlib menhir menhirLib gcc ] ++ [ coq ];
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
                                           ncoq.ocaml findlib menhir
                                           ocamlgraph merlin
                                           menhirLib
                                           ncompcert
                                         ];

  enableParallelBuilding = true;
}
