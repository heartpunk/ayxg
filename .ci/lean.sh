#!/usr/bin/env bash
set -euo pipefail
lake exe cache get
lake build Ayxg
lake env lean -DwarningAsError=true tests/lean/FPAxiomRegression.lean
lake env lean -DwarningAsError=true notes/voogd-symbolic-step/ProofAudit.lean
bazel build --jobs=2 //...
bazel test --jobs=2 //... --test_output=errors
