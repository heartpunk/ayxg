#!/usr/bin/env bash
set -euo pipefail
# Compile the normal Wruh CLI modules against the already built AYXG checkout.
wruh=${1:?WRUH source directory required}
ayxg=${2:?built AYXG source directory required}
out=${3:?output directory required}
mkdir -p "$out/Wruh"
out=$(cd -- "$out" && pwd)
ayxg=$(cd -- "$ayxg" && pwd)
lean_bin=$(command -v lean)
search="$out:$ayxg/.lake/build/lib/lean"
for package in "$ayxg"/.lake/packages/* "$ayxg"/.lake/floatlib-source-*; do
  if [[ -d "$package/.lake/build/lib/lean" ]]; then
    search="$search:$package/.lake/build/lib/lean"
  fi
done
export LEAN_PATH="$search"
export LEAN_NUM_THREADS=1
cd "$out"
for module in Observation FreshExtraction FreshTransform AngrDriver AngrMain; do
  cp "$wruh/Wruh/$module.lean" "$out/Wruh/$module.lean"
  lean -o "Wruh/$module.olean" "Wruh/$module.lean"
done
cat > "$out/wruh-fresh" <<SCRIPT
#!/usr/bin/env bash
export LEAN_PATH='$search'
exec '$lean_bin' --run '$out/Wruh/AngrMain.lean' "\$@"
SCRIPT
chmod +x "$out/wruh-fresh"
