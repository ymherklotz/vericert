with import <nixpkgs> {};
mkShell {
  buildInputs = [ coq_8_10 ocamlPackages.menhir dune
                  ocaml ocamlPackages.findlib ];
}
