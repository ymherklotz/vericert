with import <nixpkgs> {};

mkShell {
  buildInputs = (import ./.).buildInputs;
}
