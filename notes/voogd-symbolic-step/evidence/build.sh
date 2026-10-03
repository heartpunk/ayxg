#!/usr/bin/env bash
set -u
export PATH=/run/current-system/sw/bin:/usr/bin:/bin
export WRUH_AYXG_SOURCE=/tmp/ayxg-lean-fresh-transform-05d140bc
export LEAN_NUM_THREADS=4
cd /tmp/wruh-lean-fresh-transform-20261003
nix develop path:/tmp/ayxg-lean-fresh-transform-05d140bc --command bash -c 'lake build Ayxg && lake env lean /tmp/ayxg-lean-fresh-transform-05d140bc/tests/lean/SymbolicStepExamples.lean && lake env lean /tmp/ayxg-lean-fresh-transform-05d140bc/notes/voogd-symbolic-step/ProofAudit.lean' > /tmp/ayxg-voogd-r2.log 2>&1
status=$?
printf '%s\n' "$status" > /tmp/ayxg-voogd-r2.exit
exit "$status"
