#!/usr/bin/env bash
set -euo pipefail
export PATH=/run/current-system/sw/bin:/nix/var/nix/profiles/default/bin:/etc/profiles/per-user/heartpunk/bin
task_root=/tmp/ayxg-review-r3-20261019
exec > "$task_root/validation.log" 2>&1
trap 'result=$?; printf "%s\n" "$result" > "$task_root/exit-status"' EXIT
cd "$task_root/repo"
export LEAN_NUM_THREADS=1
date -u
git rev-parse HEAD
nix develop .#ci --no-write-lock-file --option max-jobs 0 --option cores 1 --command bash -euo pipefail -c '
  lean --version
  lake -Kjobs=1 build Ayxg
  lake env lean tests/lean/SymbolicStepExamples.lean
  lake env lean tests/lean_bridge/Bridge/Examples.lean
  lake env lean notes/voogd-symbolic-step/ProofAudit.lean
'
date -u
