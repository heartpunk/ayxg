{
  description = "AYXG shared formal STS library environment";
  inputs.ifrl.url = "github:heartpunk/ifrl/5cfc9560617ba75e5088e5cb67cecbbab20ad1ee";
  inputs.nixpkgs.follows = "ifrl/nixpkgs";
  inputs.lean4-nix.follows = "ifrl/lean4-nix";
  inputs.floatlib-src = {
    url = "github:lean-dojo/FloatLib/d24844f039320a024c7548f992920562d9a71a60";
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
          patches = [
            # Preserve the existing axiom-footprint workaround. Only the RNA
            # patch is retired by the Lean 4.36 upstream FloatLib migration.
            ./nix/floatlib-axiom-footprint-lean436.patch
          ];
        };
        in let z3Python = import ./nix/z3-python.nix { inherit pkgs; };
          python = pkgs.python312.withPackages (_: [ z3Python ]);
          bazel = import (ifrl.outPath + "/nix/bazel.nix") { inherit pkgs; };
          projectShell = {
            packages = [ pkgs.git pkgs.curl pkgs.lean python bazel ];
            AYXG_NIX_LIBSTDCXX_ROOT =
              pkgs.lib.optionalString pkgs.stdenv.isLinux "${pkgs.stdenv.cc.cc.lib}";
            shellHook = ''
              export AYXG_FLOATLIB_SOURCE="${floatlib}"
              export AYXG_FLOATLIB_SOURCE_KEY="d24844f039320a024c7548f992920562d9a71a60-axiom-footprint"
            '';
          };
        in {
          default = pkgs.mkShell (projectShell // {
            inputsFrom = [ ifrl.devShells.${system}.default ];
            IFRL_ANGR_ENVIRONMENT = "${ifrl.packages.${system}.angr-python}";
          });
          ci = pkgs.mkShell projectShell;
        });
    };
}
