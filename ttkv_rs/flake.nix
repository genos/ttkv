{
  inputs = {
    flake-utils = {
      url = "github:numtide/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    naersk = {
      url = "github:nix-community/naersk";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.11";
  };

  outputs = {
    self,
    flake-utils,
    naersk,
    nixpkgs,
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = (import nixpkgs) {
          inherit system;
        };
        buildInputs = [] ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [pkgs.libiconv];
        naersk' = pkgs.callPackage naersk {};
      in {
        packages.default = naersk'.buildPackage {
          src = ./.;
          inherit buildInputs;
        };
        devShells.default = pkgs.mkShell {
          nativeBuildInputs = with pkgs; [rustc cargo];
          inherit buildInputs;
        };
      }
    );
}
