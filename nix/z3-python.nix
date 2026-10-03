# Unmodified official release wheels; no solver patches.
{ pkgs }:
let
  wheels = {
    x86_64-linux = {
      url = "https://files.pythonhosted.org/packages/34/de/30329041d9a2dda11308576a80b5db17060e4b03a7ba7f550437fb38dd6b/z3_solver-5.1.0.0-py3-none-manylinux_2_27_x86_64.whl";
      sha256 = "dfad9e309d7010b1ff6bdb33f21570a1603ef4727373221c7117a74448f0cfef";
    };
    aarch64-darwin = {
      url = "https://files.pythonhosted.org/packages/01/9a/cdb6db09d6aff6a803a94505aa24666db5e47df7aad0f2b1b0ddcb52ed12/z3_solver-5.1.0.0-py3-none-macosx_13_0_arm64.whl";
      sha256 = "399a38a85d784105e5df5a05c04a581481bfdb80af7424779cf76fa843b4e66c";
    };
  };
in pkgs.python312Packages.buildPythonPackage {
  pname = "z3-solver";
  version = "5.1.0.0";
  format = "wheel";
  src = pkgs.fetchurl wheels.${pkgs.stdenv.hostPlatform.system};
  nativeBuildInputs = pkgs.lib.optionals pkgs.stdenv.isLinux [ pkgs.autoPatchelfHook ];
  buildInputs = pkgs.lib.optionals pkgs.stdenv.isLinux [ pkgs.stdenv.cc.cc.lib ];
  pythonImportsCheck = [ "z3" ];
}
