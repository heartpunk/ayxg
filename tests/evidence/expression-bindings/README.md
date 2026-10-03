# Canonical expression binding parity — 2026-10-03

Workspace: `/Users/sophiesmithburg/workspaces/ayxg-expression-parity`.
Bookmark: `expression-parity`. Baseline: `179342d8a0b63dcdea34c4db45cd29a04ca782f0`.
Validated implementation: `8e6807783f95272bd7b663f44eb057457de74d07`.
No push or merge.

## Implemented

Python's canonical TypedExpr now supports positional variables and parallel
binding groups, matching Lean's existing Var and Expr.letPar. All RHSs use the
old context; the body uses the ordered new bindings followed by the old context.
Duplicate names remain distinguishable by position. Named lookup selects the
first declaration. Capture-avoiding substitution, context checking, update
composition, evaluation, Z3 interpretation and DAG serialization handle these
constructs directly. Scoped memoization distinguishes lexical environments;
Z3 caches additionally distinguish solver contexts and variable assignments.

The canonical shared DAG retains binding declarations and positional indices.
Ayxg.QfAbv.JsonCodec reads that DAG directly into typed Lean expressions,
without expanding it into a JSON tree or eliminating bindings. Any string is
valid binding-name metadata, including WRUH's leading-underscore temporaries.
Zero-width extension amounts are accepted (the operand's width stays positive).

## Evidence

- Python: 66 tests and 200 subtests passed.
- Linux Lean FFI: 640 Python/Lean/Z3 comparisons passed: 80 generated pairs
  across eight families (parallel RHS, nested shadowing, shared body across
  scopes, empty group, Boolean, array, rounding-mode, floating-point bindings).
- Unit properties additionally cover capture avoidance, indexed substitution,
  ordered array snapshots, identity/composition, serialization, malformed
  references and cache isolation. FP coverage here concerns bindings, not a
  new FP arithmetic campaign.
- Independent source review identified cross-environment Z3 cache reuse;
  corrected and covered by regression tests before the final runs.

Commands:

```sh
nix develop --command env PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=python python -m pytest tests/unit -q
nix develop --command python tests/prepare_lean_bridge.py /tmp/ayxg-bindings-bridge
nix develop --command env PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=python:/tmp/ayxg-bindings-bridge/leanpy python tests/differential_bindings.py --bridge-project /tmp/ayxg-bindings-bridge --artifacts /tmp/ayxg-binding-evidence
```

The recorded run reused the existing source-derived Lake bridge on NixOS;
`linux-run.sh` records exact snapshot and build paths. Only frozen local source
was staged remotely. Unit ayxg-binding-dag4-20261003: 4 GiB memory, zero swap,
400% CPU, CPUs 2–5, TasksMax 256; exit 0. Observed during execution: 606 MB peak,
29.2 CPU seconds (not final totals; transient unit metrics expired).
Entrapta package temperature before launch: 46°C; high 79°C, critical 89°C.

Earlier run dag3 was INCOMPLETE: omitted static-library reader symbols caused
FFI startup failure, repeated by Hypothesis until a 4 GiB OOM. The reader is now
included through Ayxg.lean; an oracle startup smoke check runs before Hypothesis.
No passing claim relies on that failed run.

## Boundary of this result

This closes the positional/parallel-binding representation gap and validates
Python-produced shared DAGs interpreted directly by Lean. The subsequent writer tranche below supplies Lean shared-DAG output too.
Production WRUH driver hookup and universal Python/Lean extraction
correspondence remain separate work. Bare variable_sorts() intentionally rejects free positional
references without a context; consumers must validate using QFAbvContext.
No decoder-correctness proof or replacement semantic-transport theorem was
introduced.

## Lean writer follow-up — completed; pause requested

Validated implementation: `d26bcfc339455407b7776260a5a0c6b37d9ce822`.
`writeRootsDag` handles every Lean Expr constructor, directly emitting the same
shared-DAG schema consumed by Python. Output nodes are structurally interned
using shallow records containing child indices. Bindings remain bindings.
Variable occurrences are emitted by typed position, retaining shadowing.
BV literals are canonicalized modulo width, matching their Lean evaluation.

NixOS Lake/lean.py build and both differential programs: exit 0.
- 640 binding cases: Python→Lean→Python exact canonical DAG equality,
  plus existing Lean/Python/Z3 evaluation comparisons.
- 480 further operator cases: round-trip evaluation equality, writer
  idempotence, and shared-root identity. BV/array generators run 10 examples
  per operator; FP operators run one finite-valued case per rounding mode.
- Named variables return in positional form; the existing FP constructor
  reader represents fp_construct using fpFromBits/concat, so that shorthand
  round-trips semantically, not with identical operator spelling.

Logs, counts, exact launch script and systemd resource log are in `writer/`.
Reuse the prior reproduction commands, then run:

```sh
nix develop --command env PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=python:/tmp/ayxg-bindings-bridge/leanpy python tests/differential_codec.py --bridge-project /tmp/ayxg-bindings-bridge --artifacts /tmp/ayxg-codec-evidence
```

Limits: these checks concern the positive-width SMT-LIB domain, not Lean's
extra zero-width BV inhabitants. The input-traversal defect noted in this initial tranche is fixed by the
cache follow-up below. This tranche supplies no
decoder proof or universal transport proof.

STOP here per user: do not resume WRUH correspondence automatically.

## Input DAG traversal fix — completed

Final validated source: `2b3ae4f05f82cc7b27e90e74e739a444cded172e`.
Compiled Lean serialization checks a (runtime address, serialized sort) cache
before recursion and retains each cached input object until serialization ends.
The existing structural interner still deduplicates equal output nodes.
The traversal implementation is shared between the structural reference and
the compiled identity-cache implementation (`implemented_by`); the latter
uses Lean's runtime pointer primitive. This is tested runtime code, not an
additional kernel theorem or change to STS semantics.

Final Linux run exit 0:
- 640 binding round trips and Lean/Python/Z3 comparisons.
- 480 operator round trips.
- Depth-80 doubling DAG: 81 distinct nodes; exact shared output preserved,
  within the oracle's 20-second per-request limit.
- One runtime variable object reused across Boolean and BV sorts, checking
  type-erasure-sensitive memoization.

Total codec program checks: 482. All passed. Logs, counts, resource metadata,
launch script and independent review are in `writer-cache/`.
No WRUH investigation resumed. Paused after committing the correction.
