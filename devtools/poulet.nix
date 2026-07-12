{ lib, stdenv, pkgs, ... }:

stdenv.mkDerivation rec {
  name = "poulet";
  version = "dev";

  src = lib.cleanSource ./..;

  nativeBuildInputs = with pkgs; [
    rocq-core
    rocqPackages.stdlib
    ocaml
    dune_3
    ocamlPackages.findlib
    ocamlPackages.menhir
  ];

  buildPhase = ''
    make poulet
  '';

  installPhase = ''
    mkdir -p $out/bin
    cp checker/_build/default/bin/main.exe $out/bin/poulet
  '';
}
