#!/usr/bin/env bash
set -euo pipefail
# Run with WRUH's pinned nativeObserver environment. Sources are passed in,
# rather than reimplementing or vendoring the shared native observer.
src=${1:?observer source directory required}
shim=${2:?native shim directory required}
out=${3:?output directory required}
bridge=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)/ObserverBridge.lean
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cp "$shim/MemoryWrite.lean" "$src/InstallationEncoding.lean" "$src/FlagsBuffer.lean" "$src/Observer.lean" "$bridge" "$out/"
cd "$out"
export LEAN_PATH=".$(test -z "${LEAN_PATH:-}" || printf ':%s' "$LEAN_PATH")"
export LEAN_NUM_THREADS=1
for module in MemoryWrite InstallationEncoding FlagsBuffer Observer ObserverBridge; do
  lean -o "$module.olean" -c "$module.c" "$module.lean"
done
leanc -O2 MemoryWrite.c InstallationEncoding.c FlagsBuffer.c Observer.c ObserverBridge.c \
  "$src/transport.S" "$shim/write_memory.S" -o observer-bridge
