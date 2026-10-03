"""Build a pinned lean.py FFI-only expression oracle in a disposable directory.

Run under `nix develop --command python ...` so Lean follows AYXG's toolchain.
This copies source snapshots, never changes AYXG's Lake dependencies or sources.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import shutil
import subprocess

REVISION = "5c972d1b0ceae56051b1e9960fe907e206a6a3bc"
FFI_IMPORTS = "\n".join("import LeanPy." + module for module in
                        ["Registry", "TypeRepr", "Attr", "Export", "Python"]) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("workdir", type=Path)
    parser.add_argument("--lean-py-source", type=Path)
    args = parser.parse_args()
    source = Path(__file__).resolve().parents[1]
    work = args.workdir.resolve()
    if work == source or source in work.parents:
        raise SystemExit("Use a disposable directory outside AYXG")
    work.mkdir(parents=True, exist_ok=True)
    shutil.copytree(source / "Ayxg", work / "Ayxg", dirs_exist_ok=True)
    for name in ["Ayxg.lean", "lean-toolchain"]:
        shutil.copy2(source / name, work / name)
    for name in ["Bridge.lean", "lakefile.toml"]:
        shutil.copy2(source / "tests" / "lean_bridge" / name, work / name)
    shutil.copytree(source / "tests" / "lean_bridge" / "Bridge", work / "Bridge", dirs_exist_ok=True)
    floatlib = os.environ.get("AYXG_FLOATLIB_SOURCE")
    if not floatlib:
        raise SystemExit("AYXG_FLOATLIB_SOURCE must be provided by nix develop")
    pinned_floatlib = Path(floatlib)
    writable_floatlib = work / ("floatlib-" + pinned_floatlib.name)
    if not writable_floatlib.exists():
        shutil.copytree(pinned_floatlib, writable_floatlib, ignore=shutil.ignore_patterns(".lake"))
        if writable_floatlib.resolve().is_relative_to(Path("/nix/store")):
            raise SystemExit("refuse to modify immutable Nix source")
        writable_floatlib.chmod(writable_floatlib.stat().st_mode | 0o200)
        for item in writable_floatlib.rglob("*"):
            item.chmod(item.stat().st_mode | 0o200)
    floatlib = str(writable_floatlib)
    lake_config = work / "lakefile.toml"
    lake_config.write_text(lake_config.read_text() + '\n[[require]]\nname = "floatlib"\npath = ' + repr(floatlib).replace("'", '"') + '\n')
    os.environ["FLOATLIB_BUILD_DIR"] = str(work / ".lake" / "floatlib-build")
    leanpy = work / "leanpy"
    if not leanpy.exists():
        if args.lean_py_source:
            shutil.copytree(args.lean_py_source.resolve(), leanpy,
                            ignore=shutil.ignore_patterns(".lake", "__pycache__", ".venv"))
        else:
            subprocess.run(["git", "clone", "--no-checkout", "https://github.com/BasisResearch/lean.py", str(leanpy)], check=True)
            subprocess.run(["git", "fetch", "--depth", "1", "origin", REVISION], cwd=leanpy, check=True)
            subprocess.run(["git", "checkout", "--detach", REVISION], cwd=leanpy, check=True)
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=leanpy, text=True).strip()
    if actual != REVISION:
        raise SystemExit(f"lean.py must be pinned to {REVISION}, found {actual}")
    (leanpy / "LeanPy.lean").write_text(FFI_IMPORTS)
    lakefile = leanpy / "lakefile.lean"
    contents = lakefile.read_text()
    # The FFI closure uses neither dependency. Their pinned versions fail on
    # Lean 4.31; do not load/build their prover modules for expression evaluation.
    contents = contents.replace('require Pantograph from git\n  "https://github.com/leanprover/Pantograph.git" @ "dev"\n', '')
    contents = contents.replace('require Regex from git\n  "https://github.com/pandaman64/lean-regex.git" @ "v4.29.0" / "regex"\n', '')
    lakefile.write_text(contents)
    # Lake drops now-unused dependency entries on update; keep all paths explicit.
    subprocess.run(["lake", "update"], cwd=work, check=True)
    from project_bridge_libraries import project_libraries
    project_libraries(work, writable_floatlib, source / "tests/lean_bridge/ImportOutline.lean")
    subprocess.run(["lake", "build", "Bridge"], cwd=work, check=True)
    print(f"Bridge ready: {work}")


if __name__ == "__main__":
    main()
