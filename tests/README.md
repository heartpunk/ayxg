# Expression differential tests

The oracle calls actual `Ayxg.QfAbv.Eval.eval` via lean.py's native FFI. A small
JSON elaborator reconstructs intrinsically typed expressions/environments;
arrays are compared extensionally by enumerating their bounded index domain.
No update, step, composition, or segment tests are included here.

The pinned lean.py revision is `5c972d1b0ceae56051b1e9960fe907e206a6a3bc`.
Its FFI-only imports work with Lean 4.31. Its full Kernel/Z3 dependency closure
does not; the disposable test checkout excludes those imports and dependencies.
The real AYXG library has no lean.py dependency.

Build once (Python 3.12, uv, git, and AYXG's Nix environment):

```sh
nix develop --command python tests/prepare_lean_bridge.py /tmp/ayxg-differential
uv venv --python python3.12 /tmp/ayxg-differential/venv
uv pip install --python /tmp/ayxg-differential/venv/bin/python hypothesis pycparser
nix develop --command env PYTHONPATH=python:/tmp/ayxg-differential/leanpy \
  /tmp/ayxg-differential/venv/bin/python tests/differential_expr.py \
  --bridge-project /tmp/ayxg-differential --examples 200 \
  --artifacts /tmp/ayxg-differential-results
```

Each admitted root operator gets its own Hypothesis run. Generators preserve
context/sort constraints while shrinking; they also generate shared Python DAG
nodes. BV widths include 1,2,3,4,8,16,32,64; array index widths are 1..4.
`summary.json` records actual call counts and failures. Mismatch JSON files
retain the shrinking counterexample and both observed results; the Hypothesis
database preserves failing examples. The Lean FFI runs in a persistent child
process so native failures become shrinkable test failures instead of killing
Hypothesis. Per-call timeout is 20 seconds and is reported as an error.

The first campaign exposed a native Lean panic on huge shift counts. AYXG now
saturates oversized shifts before performing any intermediate Nat shift,
preserving SMT-LIB results. This is independent of array semantics.
