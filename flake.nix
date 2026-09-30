{
  description = "AYXG shared formal STS library environment";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/e7a3ca8092b61ff85b6a45bf863ea2b2d6a661b3";
  inputs.lean4-nix = {
    url = "github:heartpunk/lean4-nix/118d8caf67fbe0975ea014bcd6d501951219e6d8";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  outputs = { nixpkgs, lean4-nix, ... }:
    let
      systems = [ "aarch64-darwin" "x86_64-linux" ];
    in {
      devShells = nixpkgs.lib.genAttrs systems (system:
        let pkgs = import nixpkgs {
          inherit system;
          overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
        };
        in {
          default = pkgs.mkShell {
            packages = [ pkgs.git pkgs.lean pkgs.python312
              (if pkgs.stdenv.isLinux then pkgs.bazel_9 else pkgs.bazelisk)
            ];
          };
        });
    };
}
