{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  nativeBuildInputs = with pkgs.buildPackages; [
    gnumake
    rocq-core
    rocqPackages.stdlib
    coqPackages.autosubst
  ];
}
