{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
  };

  outputs = { nixpkgs, self, ... }: let
    forAllSystems = fn:
      nixpkgs.lib.genAttrs [
        "x86_64-linux"
        "aarch64-linux"
      ] (system: fn system nixpkgs.legacyPackages.${system});

  in {
    packages = forAllSystems (system: pkgs: {
      default = self.packages.${system}.rocqPackages.rocq-tableaux;
      rocqPackages.rocq-tableaux =
        pkgs.callPackage ./devtools/rocq-tableaux.nix {
          mkRocqDerivation = pkgs.rocqPackages.mkRocqDerivation;
        };
    });

    devShells = forAllSystems (system: pkgs:
      { default = import ./shell.nix { lib = pkgs.lib; pkgs = pkgs; }; });
  };
}
