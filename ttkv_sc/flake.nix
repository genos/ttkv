{
  description = "Scala TTKV";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.11";
  };

  outputs = {
    self,
    flake-utils,
    nixpkgs,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs {inherit system;};
    in {
      packages.default = pkgs.writeShellApplication {
        name = "ttkv";
        runtimeInputs = [pkgs.sbt];
        text = ''
          ${pkgs.sbt}/bin/sbt test
        '';
      };
    });
}
