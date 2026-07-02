{ lib, mkRocqDerivation, rocqPackages }:

with lib; mkRocqDerivation {
  pname = "tableaux";
  version = "dev";
  src = lib.cleanSource ./..;

  propagatedBuildInputs = [
    rocqPackages.stdlib
  ];
}
