{ nixpkgs ? import <nixpkgs> {}
}:
with nixpkgs;
let
  coqPackages = coqPackages_8_11;
in
mkShell {
  buildInputs = [
    coqPackages.coq
  ];
  COQBIN = "";
  name = "mtc";
}
