export PATH=/run/current-system/sw/bin:/usr/bin:/bin
export LEAN_NUM_THREADS=4
export PYTHONDONTWRITEBYTECODE=1
source_snapshot=/tmp/ayxg-expression-parity-8e680778
bridge=/tmp/ayxg-fp-bridge-scoped-v9
mkdir -p "$source_snapshot"
tar -xf /tmp/ayxg-expression-parity-8e680778.tar -C "$source_snapshot" || exit 1
cp -R "$source_snapshot/Ayxg/." "$bridge/Ayxg/"
cp "$source_snapshot/Ayxg.lean" "$bridge/Ayxg.lean"
cp "$source_snapshot/tests/lean_bridge/Bridge.lean" "$bridge/Bridge.lean"
cd "$source_snapshot" || exit 1
export PYTHONPATH="$source_snapshot/python:$bridge/leanpy"
export FLOATLIB_BUILD_DIR="$bridge/.lake/floatlib-build"
nix develop --command bash -c 'cd /tmp/ayxg-fp-bridge-scoped-v9 && lake build Bridge && cd /tmp/ayxg-expression-parity-8e680778 && python tests/differential_bindings.py --bridge-project /tmp/ayxg-fp-bridge-scoped-v9 --artifacts /tmp/ayxg-binding-dag4-evidence' > /tmp/ayxg-binding-dag4.log 2>&1
status=$?
printf '%s\n' "$status" > /tmp/ayxg-binding-dag4.exit
exit "$status"
