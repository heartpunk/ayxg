{
  description = "AYXG shared formal STS library environment";
  inputs.ifrl.url = "github:heartpunk/ifrl/e8974a263d6784422e90b076e9a058a6737f4ef1";
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
          patches = [
            # TODO(upstream-floatlib-smt-rna): AYXG #3
            # Propose the five-mode SMT/RNA
            # extension upstream as a separate feature; replace this patch
            # when a compatible upstream implementation covers its semantics.
            ./nix/floatlib-smt-rna.patch
            # TODO(upstream-floatlib-axioms): AYXG #2
            # Port the axiom-footprint cleanup
            # to upstream FloatLib and submit it; retire this patch once a
            # compatible pin includes it and the rfl/axiom regressions pass.
            # If this requires a Lean upgrade, coordinate Mathlib, IFRL, and
            # lean4-nix pins across AYXG and WRUH rather than bumping FloatLib alone.
            ./nix/floatlib-axiom-footprint.patch
          ];
        };
        in let z3Python = import ./nix/z3-python.nix { inherit pkgs; };
          python = pkgs.python312.withPackages (_: [ z3Python ]);
          # Use the same platform-specific Bazel package as the shared runtime.
          bazel = import (ifrl.outPath + "/nix/bazel.nix") { inherit pkgs; };
          projectShell = {
            packages = [ pkgs.git pkgs.lean python bazel ];
            AYXG_NIX_LIBSTDCXX_ROOT =
              pkgs.lib.optionalString pkgs.stdenv.isLinux "${pkgs.stdenv.cc.cc.lib}";
            shellHook = ''
              export PATH="${python}/bin:$PATH"
              export AYXG_FLOATLIB_SOURCE="${floatlib}"
              export AYXG_FLOATLIB_SOURCE_KEY="7553d244c7a4e02ffbbdc21eb66b70b9f37bb5e39e6f36a2dedb7834e1f830af"
            '';
          };
        in {
          # The full contributor shell includes the shared runtime.
          default = pkgs.mkShell (projectShell // {
            inputsFrom = [ ifrl.devShells.${system}.default ];
          });
          # CI needs only the project toolchain. The full shared shell also
          # realizes Angr's Python closure, whose upstream Mistune timing tests
          # can fail on loaded builders before AYXG checks start.
          ci = pkgs.mkShell projectShell;
        });
    };
}
