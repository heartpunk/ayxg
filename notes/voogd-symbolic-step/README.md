# Voogd symbolic stepping over AYXG STSes

Workspace `/Users/sophiesmithburg/workspaces/ayxg-voogd-symbolic-step`, bookmark `voogd-symbolic-step`, exclusively foreground-owned. Baseline `1cd06bae64a14b793e464a5aea959a1b20aed429`. Existing workspaces remain unchanged.

Read AKVI at `ae73063b8bc134a1b49b02a2e6ce9d8746c7472a`: `Akvi/VoogdAlgebra.lean` and `Akvi/BVTraceExecution.lean`. Its `eval_compose`, `sat_and`, `sat_lift` laws are implemented here by existing AYXG `QFAbvStep.compose` and `compose_denotes_iff`. No AKVI dependency is added.

The exact goal is the implemented `symbolicStep_denotes_iff`: a returned successor with the original edge label denotes the target exactly when the input guard holds and `model.toLTS.Tr ⟨(), input.update.eval ρ⟩ edge ⟨(), target⟩` holds. `symbolicStep_sound` and `symbolicStep_complete` expose the two directions under the same initial valuation. The theorem is generic in contexts, model, input symbolic state, valuation, and target, with arbitrary existing `FPInterpretation`. There is no source coverage premise or assumed outcome correspondence. No new symbolic-state or STS representation is introduced.

Existing composition recursively substitutes expressions. The result family is hash-consed with Lean's standard `ShareCommon.shareCommon'`: semantically the identity, implemented by the Lean runtime's common-subobject sharing primitive. This preserves a shared output graph; it does not claim to eliminate transient allocation during existing recursive substitution. No custom unsafe implementation or equality oracle is added.

## Axiom cleanup and validation (r4): PASS

`Env` and the unchanged `symbolicStep_length` statement now depend on exactly `[propext]`. The other five declarations in `ProofAudit.lean` still report `[propext, Classical.choice, Quot.sound]`; this is not a claim to eliminate those axioms from the full evaluator.

The scoped FloatLib patch replaces the IEEE format-bound proofs with direct arithmetic lemmas and reads exponent/fraction fields as natural numbers, avoiding intermediate bit-vector bounds proofs. AYXG's fraction-width proof also uses the direct arithmetic lemma. The format and field-extraction values remain definitionally equal to their previous definitions. `tests/lean/FPAxiomRegression.lean` checks those equalities with `rfl` and guards the two exact axiom lists; CI runs it after the Lean build. No theorem statements, assumptions, or upstream dependency revisions changed.

Validation ran on NixOS with the pinned Lean 4.34.0 environment: the full AYXG library, the new regression, symbolic-step examples, standalone bridge examples, and the six-declaration proof audit passed. The executed snapshot is identified by [43 source/configuration hashes](evidence/r4/source-hashes.txt), all checked against the local files. The build rehashed its inputs while reusing dependency outputs. [Full log](evidence/r4/validation.log), [launch script](evidence/r4/run-validation.sh), and [resource record](evidence/r4/resources.properties) are retained. The bounded `fleet-build.slice` child exited 0, used 234.440 CPU seconds, and peaked at 1,290,223,616 bytes within its 2 GiB limit.

Reproduce the checks from the current checkout:

```sh
nix develop .#ci --no-write-lock-file --command bash -euo pipefail -c '
  lake -R -H build Ayxg
  lake env lean tests/lean/FPAxiomRegression.lean
  lake env lean tests/lean/SymbolicStepExamples.lean
  lake env lean tests/lean_bridge/Bridge/Examples.lean
  lake env lean notes/voogd-symbolic-step/ProofAudit.lean
'
```

The [original dependency paths](evidence/r4/axiom-paths.log) also explain the `Quot.sound` findings: generated `omega` proofs used function extensionality, and the intermediate bit-vector bounds proof reached it through the natural-number bitwise library. These paths no longer occur in the length theorem's dependencies. The original path-inspection helper is retained as [AxiomPaths.lean](evidence/r4/AxiomPaths.lean); its log describes the pre-fix snapshot.

## Historical labeled STS review fixes and validation (r3): PASS

Tested implementation: `d1e060d5fca857c2148fce69b59b58ff03e48e40`. The following evidence commit changes documentation only. Source hashes for the executed Lean files and build configuration are in [evidence/r3/source-hashes.txt](evidence/r3/source-hashes.txt).

- `WholeRegion.pre` and its underlying `Region.pre` require canonical guarded-update semantics in their definitions. The existing equality premise is required when constructing a predecessor, rather than only when invoking its correctness theorem. `RegionAlgebra.pre` supplies its stored canonicity proof.
- `ofSymbolicSuccessors_transition_iff` states exactly which transitions the constructor admits. `ofSymbolicSuccessors_symbolicStep_transition_iff` connects a packaged symbolic step to the source model's labeled transition, preserving its edge label and input guard/update.
- The explanation above now states the current labeled `toLTS.Tr` contract. The r2 review and results below remain historical evidence, not a review of the new declarations.

On NixOS, using this checkout's pinned `.#ci` environment and Lean 4.34.0 (`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`), these checks passed:

```sh
nix develop .#ci --no-write-lock-file --command lake -Kjobs=1 build Ayxg
nix develop .#ci --no-write-lock-file --command lake env lean tests/lean/SymbolicStepExamples.lean
nix develop .#ci --no-write-lock-file --command lake env lean tests/lean_bridge/Bridge/Examples.lean
nix develop .#ci --no-write-lock-file --command lake env lean notes/voogd-symbolic-step/ProofAudit.lean
```

The six audited declarations have no admitted proofs. Their current axiom footprint is `[propext, Classical.choice, Quot.sound]`, **including `symbolicStep_length`**. Restricting that proof to `List.length_map` does not remove dependencies reached through its STS argument type. This differs from the historical r2 length result below.

The r3 audit traced the choice dependency through `Env` → `Denote` → `FPValue` → `FPFormat.floatFormat` → FloatLib's `FloatFormat.ieee` → `ieeeBias_le_maxFiniteExponent` → `Nat.pow_lt_pow_right`. The last lemma refers to an iff theorem whose opposite direction uses `Classical.not_imp`. A scratch proof of the identical format bound removed choice but retained `Quot.sound`. This was initially deferred; r4 resolves the complete `symbolicStep_length` footprint above. The [dependency audit](evidence/r3/env-axiom-audit.log), [scratch proof](evidence/r3/PowDependencyAudit.lean), and [scratch result](evidence/r3/pow-dependency-audit.log) retain that intermediate evidence.

The [validation log](evidence/r3/validation.log) records the full library build, examples, and theorem audit. The bounded job used `MemoryMax=2G`, `MemorySwapMax=0`, `CPUQuota=200%`, and `LEAN_NUM_THREADS=1` under `fleet-build.slice`; it exited 0, peaked at 495,407,104 bytes, and used 22.619 CPU seconds. [Launch script](evidence/r3/run.sh) and [resource record](evidence/r3/resources.properties) are retained. Existing dependency outputs were reused. Repository sources and Git metadata were copied from the local checkout; no remote source edits or dependency overrides were used. The standalone Lean bridge examples passed; the separate LeanPy/FFI harness was not validated in this run.

## Historical validation (r2): PASS

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

One read-only Sol reviewer examined the original goal and source definitions before completion. It explicitly checked whether the theorem could pass without connecting to the source STS. Finding: no correctness or goal-alignment defect. That review covered the earlier statement's source-edge membership and edge semantics, with the same initial valuation throughout; it predates the current labeled `toLTS.Tr` statement. Heterogeneous input contexts are preserved; no pruning/correspondence premise. Count is proved explicitly; order follows from map and is checked by the focused example. Review was source-only, no builds/edits; single model family, not provider diversity.

### Historical completion boundary (r2)

Completed: AYXG one-step symbolic execution, sound and complete against the existing source STS concrete transition relation, committed with checks. No changes to supported semantics, STS representation or FP interpretation. No push or merge.

Next proposed tranche: WRUH's extraction algorithm and universal semantic transport theorem. This stepper is its reference engine, not that extraction theorem. Do not begin the next tranche without user authorization.
