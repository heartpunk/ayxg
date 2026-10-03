# Voogd symbolic stepping over AYXG STSes

Workspace `/Users/sophiesmithburg/workspaces/ayxg-voogd-symbolic-step`, bookmark `voogd-symbolic-step`, exclusively foreground-owned. Baseline `1cd06bae64a14b793e464a5aea959a1b20aed429`. Existing workspaces remain unchanged.

Read AKVI at `ae73063b8bc134a1b49b02a2e6ce9d8746c7472a`: `Akvi/VoogdAlgebra.lean` and `Akvi/BVTraceExecution.lean`. Its `eval_compose`, `sat_and`, `sat_lift` laws are implemented here by existing AYXG `QFAbvStep.compose` and `compose_denotes_iff`. No AKVI dependency is added.

The exact goal is the implemented `symbolicStep_denotes_iff`, with the existing source model's `toLTS.canStep` on the right. `symbolicStep_sound` and `symbolicStep_complete` expose the two directions under the same initial valuation. The theorem is generic in contexts, model, input symbolic state, valuation, and target, with arbitrary existing `FPInterpretation`. There is no source coverage premise or assumed outcome correspondence. No new symbolic-state or STS representation is introduced.

Existing composition recursively substitutes expressions. The result family is hash-consed with Lean's standard `ShareCommon.shareCommon'`: semantically the identity, implemented by the Lean runtime's common-subobject sharing primitive. This preserves a shared output graph; it does not claim to eliminate transient allocation during existing recursive substitution. No custom unsafe implementation or equality oracle is added.

Validation pending. This tranche is the AYXG symbolic stepper only, not WRUH extraction or its transport theorem.
