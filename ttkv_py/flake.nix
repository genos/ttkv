{
  description = "Python TTKV";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-22.11";
  };

  outputs = {
    self,
    flake-utils,
    nixpkgs,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs {inherit system;};
      python = pkgs.python311.withPackages (p: [p.hypothesis p.pytest]);
    in {
      packages.default = pkgs.writeShellApplication {
        name = "ttkv";
        text = ''
          pytest ttkv_spec.py
        '';
      };
    });
}
