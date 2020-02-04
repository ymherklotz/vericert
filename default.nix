with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "CoqUp";
  src = ./.;

  buildInputs = [ coq_8_10 ];

  buildPhase = "make";
}
