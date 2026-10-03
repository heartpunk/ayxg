set -eu
mkdir -p /tmp/ayxg-fp-5599129e
tar -xf /tmp/ayxg-fp-5599129e.tar -C /tmp/ayxg-fp-5599129e
cd /tmp/ayxg-fp-5599129e
nix develop --command /bin/sh -c 'set -eu
export FLOATLIB_BUILD_DIR=/tmp/ayxg-fp-7bafb784/.lake/floatlib-build
PYTHONPATH="$PWD/tests" python - <<'"'"'PY'"'"'
from pathlib import Path
from project_bridge_libraries import project_libraries
work=Path("/tmp/ayxg-fp-bridge-scoped-v9")
floatlibs=list(work.glob("floatlib-*"));assert len(floatlibs)==1
project_libraries(work,floatlibs[0],Path("tests/lean_bridge/ImportOutline.lean").resolve())
PY
cp tests/lean_bridge/Bridge.lean /tmp/ayxg-fp-bridge-scoped-v9/Bridge.lean
cp tests/lean_bridge/Bridge/Examples.lean /tmp/ayxg-fp-bridge-scoped-v9/Bridge/Examples.lean
cd /tmp/ayxg-fp-bridge-scoped-v9
lake build Bridge
cd /tmp/ayxg-fp-5599129e
PYTHONPATH="$PWD/python:/tmp/ayxg-fp-bridge-scoped-v9/leanpy" python tests/differential_fp.py --bridge-project /tmp/ayxg-fp-bridge-scoped-v9 --examples 20 --artifacts /tmp/ayxg-fp-ffi-scoped-v18'
