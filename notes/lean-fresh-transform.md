# Shared support for WRUH's Lean fresh transformer

Dedicated workspace: `/Users/sophiesmithburg/workspaces/ayxg-lean-fresh-transform`.
Bookmark: `lean-fresh-transform`.
Baseline: `d35e2e4a921868907dada2a09a96caea4251f06b`.
Tested implementation: `95241959a439b40a9b5ebf8abc025c6975c0f55e`.

- `Ayxg/QfAbv/LetChain.lean`: ordered groups of existing typed parallel bindings; expression/update closure by nested `letPar`, with exact environment-denotation proofs. Expression bodies and supplied binding/RHS objects are retained, avoiding recursive substitution expansion.
- `Ayxg/QfAbv/ByteMemory.lean`: positive-width little-endian symbolic loads/stores with concrete denotation functions and proofs. Index width is generic; finite-width address wrap and write order are preserved.

These are generic expression operations. Fresh extraction control, primitive observations, and the guarded local transport theorem live in WRUH.

Validation: Linux/NixOS, Lean 4.34, qualified Nix + Lake. WRUH revision `a7086d2b25bca7a903e0d47f9b9882caede4cc1b` built its library and 14 focused examples against this exact AYXG source. Five preservation-theorem audits showed only Lean's standard `propext`, `Classical.choice`, `Quot.sound`; no proof admissions.

Reproduce from that WRUH checkout:

```sh
export WRUH_AYXG_SOURCE=/absolute/path/to/ayxg
export LEAN_NUM_THREADS=4
nix develop path:/absolute/path/to/ayxg --command lake -R update ayxg
nix develop path:/absolute/path/to/ayxg --command lake build Wruh Wruh.FreshTransformExamples
nix develop path:/absolute/path/to/ayxg --command lake env lean notes/lean-fresh-transform/ProofAudit.lean
```

Full commands, frozen-input hashes, build logs, read-only semantic review, scope and resource records are in WRUH's `notes/lean-fresh-transform/`. No production Python hookup, whole-driver proof, STS assembly or pushes/merges were performed.
