# Expression differential tests

The oracle calls actual `Ayxg.QfAbv.Eval.eval` via lean.py's native FFI. A small
JSON elaborator reconstructs intrinsically typed expressions/environments;
arrays are compared extensionally by enumerating their bounded index domain.
The expression, transition, and segment campaigns are in
`differential_expr.py`, `differential_transition.py`, and
`differential_segment.py`. `tests/unit` contains pytest contract examples and
Hypothesis properties. Run them in the shared flake environment:
`nix develop .#ci --command bash -c 'PYTHONPATH=python python -m pytest -p no:cacheprovider -q tests/unit'`.

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

## Bounded segments and shared references

After rebuilding the same bridge, run `tests/differential_segment.py` with
`--bridge-project`, `--examples`, and `--artifacts` as above. It compares output
sets for input adapter → 0..3 body transitions → any enabled exit adapter.
Both sides construct the actual segment datatypes and use their existing
primitive evaluators; the exploration loops are test-only. This is not a proof
of completeness for unbounded `Segment.denotes`.

The generated cases cover array states, heterogeneous adapter contexts, two
body branches, zero or multiple exits, enabled and disabled input/output guards,
and every bound 0..3 separately. Explicit +1/+2 branching cases assert exact
output sets at each bound, independently of the cross-language comparison. The
`mixed_exits` lane checks distinct exit relations while the first exit is
disabled. Each language also constructs a segment DAG with two parents
referencing the same child and compares child-reference output sets to direct
use. Containment edges do not execute parent or child segments in sequence.
Failing requests and results are saved while Hypothesis shrinks; `summary.json`
records each bound, empty/nonempty and multiple output sets, distinct exits,
branching bodies, arrays, and true/false outcomes of state-dependent guard
evaluations.


## Basic Python contract suite

Run with the standard pytest runner from the shared flake environment:

```sh
nix develop .#ci --command bash -c 'PYTHONPATH=python python -m pytest -p no:cacheprovider -q tests/unit'
```

The unit suite checks sort/expression serialization and rejection contracts,
every admitted operator with an explicit expected evaluation, public constructor
helpers, and SMT-defined divide-by-zero, overshift, sign-extension, and modular
arithmetic edges. It also checks array/value/context validation, extensional
equality, evaluator context checks, update/step validation, STS label
membership, and control projections. Hypothesis properties cover simultaneous
swap and substitution, update identity, composition and associativity, guarded
step composition, and extensional array state equality across alternate
finite-support encodings. Explicit differential cases include empty contexts,
heterogeneous contexts, guards evaluated after the preceding update, and the
true/false outcomes of state-dependent guard evaluations.

`tests/lean_bridge/Bridge/Examples.lean` is compiled with the existing FFI
bridge build. It exercises parallel-let shadowing, renaming, substitution,
symbolic-label composition, QF_ABV STS/control views, and direct segment
denotation. It also constructs generic STS/LTS runs (empty, one-step,
concatenated, branching, cyclic, label-sensitive, and dead-end cases), accepted
segment-DAG shapes and rejected order/key cases, plus a concrete legacy
symbolic-system run converted to an LTS trace.
