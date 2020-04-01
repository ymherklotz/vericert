with import <nixpkgs> {};

mkShell {
  buildInputs = (import ./.).buildInputs ++ [ocamlPackages.ocp-indent verilog];
}
