{ lib
, pkgs ? import ./devtools/nixpkgs.nix {}
, withDoc ? true
, withExtraction ? true
, withOCamlDev ? true }:

pkgs.mkShell {
  nativeBuildInputs = with pkgs.buildPackages; [
    # Base packages
    gnumake
  ] ++ [
    # Packages used by the Rocq library
    rocq-core
    rocqPackages.stdlib
    ocamlPackages.findlib
  ] ++ (lib.optionals withDoc [
    # Packages for building the documentation
    pandoc
  ]) ++ (lib.optionals withExtraction [
    # Packages for building the extraction
    ocaml
    dune_3
    pkgs.ocamlPackages.menhir
  ]) ++ (lib.optionals withOCamlDev [
    # Packages for developing the non-critical OCaml code
    pkgs.ocamlPackages.ocaml-lsp
    pkgs.ocamlPackages.ocamlformat
    pkgs.ocamlPackages.ocp-indent
    pkgs.ocamlPackages.ocp-index
    pkgs.ocamlPackages.merlin
  ]);
}
