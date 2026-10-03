# Focused independent cache review — 2026-10-03

Reviewer: /root/writer_cache_review, GPT-6 Sol; read-only source review.
No builds, remote operations or edits by reviewer.

Scope: input identity cache, retained object lifetime, Lean erased indices,
writer state updates, and shared-DAG regression sensitivity.

Finding: cache key (runtime address, serialized sort) accounts for all emitted
constructor data that can vary under erased types. Variable positions depend
on Var constructors; binding metadata is explicit. Retention keeps objects
alive until the write ends. No further implementation defect identified.

Test finding: separate calls creating differently typed variables need not
produce one shared runtime object. Corrected in 2b3ae4f0 with a test-only
unsafeCast that reuses exactly one .var .here object at two valid sorts.
The fixture has a safe structural reference and a compiled shared-object
implementation; production expression semantics are unchanged.

The depth-80 doubling DAG has 81 nodes but 2**80 expanded leaf paths; the
compiled oracle must serialize it within its existing 20-second request limit.
A missing identity cache cannot feasibly pass this check.

Runtime pointer caching uses implemented_by, not a kernel proof of codec
correctness. No proof or trust claim was added by this review.
