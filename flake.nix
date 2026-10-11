{
  description = "AYXG shared formal STS library environment";
  inputs.ifrl.url = "git+ssh://git@github.com/heartpunk/ifrl.git?ref=ci/wave-1&rev=5cca8cb3235ebe8288e43a254d05380b10189f37&allRefs=1";
  inputs.nixpkgs.follows = "ifrl/nixpkgs";
  inputs.lean4-nix = {
    follows = "ifrl/lean4-nix";
  };
  outputs = { nixpkgs, lean4-nix, ifrl, ... }:
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
            inputsFrom = [ ifrl.devShells.${system}.default ];
            packages = [ pkgs.git pkgs.lean pkgs.python312
              (if pkgs.stdenv.isLinux then pkgs.bazel_9 else pkgs.bazelisk)
            ];
          };
        });
    };
}
