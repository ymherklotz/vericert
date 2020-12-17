with import <nixpkgs> {};

mkShell {
  buildInputs = (import ./.).buildInputs ++ [ ocamlPackages.ocp-indent
                                              ocamlPackages.merlin ocamlPackages.utop
                                              # (import ./.)
                                            ];
}
