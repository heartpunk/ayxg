# Voogd symbolic stepping over AYXG STSes

Workspace `/Users/sophiesmithburg/workspaces/ayxg-voogd-symbolic-step`, bookmark `voogd-symbolic-step`, exclusively foreground-owned. Baseline `1cd06bae64a14b793e464a5aea959a1b20aed429`. Existing workspaces remain unchanged.

Read AKVI at `ae73063b8bc134a1b49b02a2e6ce9d8746c7472a`: `Akvi/VoogdAlgebra.lean` and `Akvi/BVTraceExecution.lean`. Its `eval_compose`, `sat_and`, `sat_lift` laws are implemented here by existing AYXG `QFAbvStep.compose` and `compose_denotes_iff`. No AKVI dependency is added.

The exact goal is the implemented `symbolicStep_denotes_iff`, with the existing source model's `toLTS.canStep` on the right. `symbolicStep_sound` and `symbolicStep_complete` expose the two directions under the same initial valuation. The theorem is generic in contexts, model, input symbolic state, valuation, and target, with arbitrary existing `FPInterpretation`. There is no source coverage premise or assumed outcome correspondence. No new symbolic-state or STS representation is introduced.

Existing composition recursively substitutes expressions. The result family is hash-consed with Lean's standard `ShareCommon.shareCommon'`: semantically the identity, implemented by the Lean runtime's common-subobject sharing primitive. This preserves a shared output graph; it does not claim to eliminate transient allocation during existing recursive substitution. No custom unsafe implementation or equality oracle is added.

## Validation: PASS

Tested revision `2886db473761eb1db00ada44dce303583f7774c8`. Later commit is evidence/docs only. New/changed Lean source hashes match the executed snapshot; see `evidence/tested-sources.json`.

Linux `lake build Ayxg` passed. All 12 bounded examples in `tests/lean/SymbolicStepExamples.lean` checked, plus the executable allocation check printed `shared successor object: PASS`. Examples exercise noncommuting arithmetic updates (increment then double), guards tested after substitution, complementary branches, input guard rejection, source edge order/count, an empty model, and the general completeness theorem. The theorem itself is generic over every supported context/sort (including arrays and FP); these bounded examples do not purport to enumerate those domains.

The four audited theorems have no proof admissions. Soundness, completeness and the combined iff depend only on `propext`, `Classical.choice`, and `Quot.sound`; length uses only `propext`. The unsafe pointer-equality check exists solely in the test file and contributes nothing to any proof. `ShareCommon.shareCommon'` is a standard Lean value-preserving runtime primitive with a logical identity definition; no new axiom is added.

r1 failed on declaration-modifier placement (`omit` after a doc comment), fixed without changing semantic statements. r2 passed in 16.023s wall / 14.631s CPU, 442.2 MiB peak. Full logs retained. Existing dependency linter warnings remain.

### Reproduce from an AYXG checkout

```sh
nix develop --command lake build Ayxg
nix develop --command lake env lean tests/lean/SymbolicStepExamples.lean
nix develop --command lake env lean notes/voogd-symbolic-step/ProofAudit.lean
```

Execution reused the previous idle Lake dependency root `/tmp/wruh-lean-fresh-transform-20261003`, where AYXG is a declared path dependency at `/tmp/ayxg-lean-fresh-transform-05d140bc`. `nix develop path:/tmp/ayxg-lean-fresh-transform-05d140bc --command lake build Ayxg` builds that AYXG library; examples/audit used absolute paths through `lake env lean`. Exact launch script retained. No WRUH source changes, manual runfiles, copied build outputs or remote source edits. Frozen local commits were transferred between completed runs.

### Resources

Inspected NixOS, Abraxas and Hotei before launch. NixOS had 18 logical CPUs, 92 GiB RAM / 89 GiB available, low load; existing reservations were 80 GiB REAPI and 1 GiB/two-CPU tmux. Reused bounded detached user-systemd settings: `MemoryMax=4G`, `MemorySwapMax=0`, `CPUQuota=400%`, `AllowedCPUs=2-5`, `TasksMax=256`, `LEAN_NUM_THREADS=4`. Units `ayxg-voogd-r1` and `ayxg-voogd-r2`; journals retained. Entrapta physical CPU was 34°C before and 40°C after, high 79°C / critical 89°C. No jobs interrupted.

### Independent goal-alignment and correctness review

One read-only Sol reviewer examined the original goal and source definitions before completion. It explicitly checked whether the theorem could pass without connecting to the source STS. Finding: no correctness or goal-alignment defect. `toLTS.canStep` uses membership in the same source model plus its existing edge semantics, with the same initial valuation throughout. Heterogeneous input contexts are preserved; no pruning/correspondence premise. Count is proved explicitly; order follows from map and is checked by the focused example. Review was source-only, no builds/edits; single model family, not provider diversity.

### Completion boundary

Completed: AYXG one-step symbolic execution, sound and complete against the existing source STS concrete transition relation, committed with checks. No changes to supported semantics, STS representation or FP interpretation. No push or merge.

Next proposed tranche: WRUH's extraction algorithm and universal semantic transport theorem. This stepper is its reference engine, not that extraction theorem. Do not begin the next tranche without user authorization.
