# Expression differential tests

The oracle calls actual `Ayxg.QfAbv.Eval.eval` via lean.py's native FFI. A small
JSON elaborator reconstructs intrinsically typed expressions/environments;
arrays are compared extensionally by enumerating their bounded index domain.
The expression campaign is in `differential_expr.py`; transition checks are
in `differential_transition.py`. Segment tests are not included.

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

## Updates, guarded steps, and composition

Using the same built bridge and environment:

```sh
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=python:/tmp/ayxg-differential/leanpy \
  /tmp/ayxg-differential/venv/bin/python tests/differential_transition.py \
  --bridge-project /tmp/ayxg-differential --examples 1000 \
  --artifacts /tmp/ayxg-transition-results
```

The bridge elaborates heterogeneous typed updates and steps, then calls actual
Lean `StateUpdate.eval`, `StateUpdate.compose`, `QFAbvStep.compose`, and identity
constructors. Step execution uses the defining guard and update semantics.
Every request compares ten results with Python, including composed and sequential
updates/steps and left/right identity composition. Arrays are compared by their
entire bounded index domain, not finite-support representation equality.

Five Hypothesis campaigns cover homogeneous and independently generated
heterogeneous contexts, forced enabled guards, and each disabled guard position.
Contexts can be empty, reorder declarations, or reuse a name at a different sort.
Twelve explicit cases independently assert swaps, lifted guards, and array
store/read aliasing through reordered/renamed contexts. The summary records
actual case counts, observed operator/context/guard coverage, and failures.
Failing requests/results are saved while Hypothesis shrinks; its database
retains failing examples. Production sources are unchanged by this campaign.
