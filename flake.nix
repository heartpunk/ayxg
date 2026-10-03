{
  description = "AYXG shared formal STS library environment";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/e7a3ca8092b61ff85b6a45bf863ea2b2d6a661b3";
  inputs.lean4-nix = {
    url = "github:heartpunk/lean4-nix/118d8caf67fbe0975ea014bcd6d501951219e6d8";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  inputs.floatlib = {
    url = "github:lean-dojo/FloatLib/1e83f09ed8c41a953cf8f93d26c210778177b94a";
    flake = false;
  };
  outputs = { nixpkgs, lean4-nix, floatlib, ... }:
    let
      systems = [ "aarch64-darwin" "x86_64-linux" ];
    in {
      devShells = nixpkgs.lib.genAttrs systems (system:
        let pkgs = import nixpkgs {
          inherit system;
          overlays = [ (final: prev: {
            lean = (prev.callPackage "${lean4-nix}/lib/toolchain.nix" {}).fetchBinaryLean
              ((import ./nix/lean-4.34.nix) // {
                inherit (import "${lean4-nix}/manifests/v4.31.0.nix") bootstrap buildLeanPackage;
              });
          }) ];
        };
        floatlibSource = pkgs.applyPatches {
          name = "floatlib-smt-rna";
          src = floatlib;
          patches = [ ./nix/floatlib-smt-rna.patch ];
        };
        in {
          default = pkgs.mkShell {
            AYXG_FLOATLIB_SOURCE = "${floatlibSource}";
            shellHook = ''
              export FLOATLIB_BUILD_DIR="$PWD/.lake/floatlib-build"
            '';
            AYXG_NIX_LIBSTDCXX_ROOT = pkgs.lib.optionalString pkgs.stdenv.isLinux "${pkgs.stdenv.cc.cc.lib}";
            packages = [ pkgs.git pkgs.lean (pkgs.python312.withPackages (ps: [ (import ./nix/z3-python.nix { inherit pkgs; }) ps.pytest ps.hypothesis ]))
              (if pkgs.stdenv.isLinux then pkgs.bazel_9 else pkgs.bazelisk)
            ];
          };
        });
    };
}
