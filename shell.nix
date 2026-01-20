{ pkgs ? import ./devtools/nixpkgs.nix {} }:

pkgs.mkShell {
  nativeBuildInputs = with pkgs.buildPackages; [
    gnumake
    rocq-core
    rocqPackages.stdlib
    ocamlPackages.findlib
    pandoc
  ];
}
