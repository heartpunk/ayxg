set -eu
mkdir -p /tmp/ayxg-fp-24f6686b
tar -xf /tmp/ayxg-fp-24f6686b.tar -C /tmp/ayxg-fp-24f6686b
cd /tmp/ayxg-fp-24f6686b
nix develop --command /bin/sh -c 'set -eu
export FLOATLIB_BUILD_DIR=/tmp/ayxg-fp-7bafb784/.lake/floatlib-build
export PYTHONPATH="$PWD/python:/tmp/ayxg-fp-bridge-scoped-v9/leanpy"
python tests/differential_fp.py --bridge-project /tmp/ayxg-fp-bridge-scoped-v9 --examples 20 --artifacts /tmp/ayxg-fp-ffi-scoped-v19'
