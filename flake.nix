{
  description = "AYXG shared formal STS library environment";
  inputs.ifrl.url = "git+ssh://git@github.com/heartpunk/ifrl.git?ref=ci/wave-1&rev=5cca8cb3235ebe8288e43a254d05380b10189f37&allRefs=1";
  inputs.nixpkgs.follows = "ifrl/nixpkgs";
  inputs.lean4-nix = {
    follows = "ifrl/lean4-nix";
  };
  inputs.floatlib-src = {
    url = "github:lean-dojo/FloatLib/1e83f09ed8c41a953cf8f93d26c210778177b94a";
    flake = false;
  };
  outputs = { nixpkgs, lean4-nix, ifrl, floatlib-src, ... }:
    let
      systems = [ "aarch64-darwin" "x86_64-linux" ];
    in {
      devShells = nixpkgs.lib.genAttrs systems (system:
        let pkgs = import nixpkgs {
          inherit system;
          overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
        };
        in let floatlib = pkgs.applyPatches {
          name = "floatlib-ayxg-scoped";
          src = floatlib-src;
          patches = [ ./nix/floatlib-smt-rna.patch ];
        };
        in {
          default = pkgs.mkShell {
            inputsFrom = [ ifrl.devShells.${system}.default ];
            packages = [ pkgs.git pkgs.lean pkgs.python312
              (if pkgs.stdenv.isLinux then pkgs.bazel_9 else pkgs.bazelisk)
            ];
            shellHook = ''
              export AYXG_FLOATLIB_SOURCE="${floatlib}"
              export AYXG_FLOATLIB_SOURCE_KEY="222236f04b51cfbf170bd4894542c9ac97436b15"
            '';
          };
          # CI needs only the project toolchain. The full shared shell also
          # realizes Angr's Python closure, whose upstream Mistune timing tests
          # can fail on loaded builders before AYXG checks start.
          ci = pkgs.mkShell {
            packages = [ pkgs.git pkgs.lean pkgs.python312
              (if pkgs.stdenv.isLinux then pkgs.bazel_9 else pkgs.bazelisk)
            ];
            AYXG_NIX_LIBSTDCXX_ROOT =
              pkgs.lib.optionalString pkgs.stdenv.isLinux "${pkgs.stdenv.cc.cc.lib}";
            shellHook = ''
              export AYXG_FLOATLIB_SOURCE="${floatlib}"
              export AYXG_FLOATLIB_SOURCE_KEY="222236f04b51cfbf170bd4894542c9ac97436b15"
            '';
          };
        });
    };
}
