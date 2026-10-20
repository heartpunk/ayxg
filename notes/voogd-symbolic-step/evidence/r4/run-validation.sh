#!/usr/bin/env bash
set -euo pipefail
export PATH=/run/current-system/sw/bin:/nix/var/nix/profiles/default/bin:/etc/profiles/per-user/heartpunk/bin
export LEAN_NUM_THREADS=1
task_root=/tmp/ayxg-review-r4-20261019
exec > "$task_root/validation.log" 2>&1
trap 'result=$?; printf "%s\n" "$result" > "$task_root/exit-status"' EXIT
cd "$task_root/repo"
date -u
git rev-parse HEAD
nix develop .#ci --no-write-lock-file --option max-jobs 1 --option cores 1 --command bash -euo pipefail -c '
  lean --version
  lake -R env true
  old=.lake/floatlib-source-ef0b76aca0bef24d14fc02c13e3cc93e2923eb5c7b3e47b097bd9dea1b4bcda8/.lake/build
  new=.lake/floatlib-source-$AYXG_FLOATLIB_SOURCE_KEY/.lake
  mkdir -p "$new"
  cp -a --reflink=auto "$old" "$new/"
  lake -H -Kjobs=1 build Ayxg
  lake env lean tests/lean/FPAxiomRegression.lean
  lake env lean tests/lean/SymbolicStepExamples.lean
  lake env lean tests/lean_bridge/Bridge/Examples.lean
  lake env lean notes/voogd-symbolic-step/ProofAudit.lean
'
date -u
