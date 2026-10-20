# FP integration scope and provenance

Python transport/converter tranche: 09169378; five SMT rounding modes and all
non-Real standard FP operation families, plus Z3 fp.to_ieee_bv.

Source: [SMT-LIB FloatingPoint 2.7](https://smt-lib.org/theories-FloatingPoint.shtml),
[BTRW15 formal semantics](https://smt-lib.org/papers/BTRW15.pdf). The formal
conversion definition rounds to an integer, then checks its BV range. The short
theory-page note about negative unsigned inputs is less precise than that rule.
No host float operations are used. No NaN payload, signaling-vs-quiet distinction,
IEEE exception flag or trap is claimed by the SMT carrier.

FP generic SMT equality is reflexive on the single NaN and distinguishes signed
zeros. fp.eq is false on NaN and identifies signed zeros. Undefined casts and
NaN-to-bits remain exact symbolic functions; the concrete interpreter accepts an explicit immutable FPInterpretation.
Omitting it, or a required key, reports UnderspecifiedFPError. NaN-to-bits
choices must be NaN encodings; invalid casts may choose any width-correct BV. Opposite
signed-zero fp.min/max requires an explicit consistent interpretation too.

Lean uses user-selected FloatLib, upstream commit
1e83f09ed8c41a953cf8f93d26c210778177b94a (2026-09-30), MIT license, Lean/Mathlib4.34.
The upstream public IEEERoundingMode has four constructors, so the scoped SMT
extension adds a five-mode interface and reuses existing exact policy rounding
for RNA. The extension's proof target is SMT.Proof; broad upstream builds are
not required. Scoped revision222236f04b51cfbf170bd4894542c9ac97436b15 is
reconstructed from the upstream pin plus nix/floatlib-smt-rna.patch; the manifest
records its exact hash. The RNA quotient nearest-adjacent and halfway rule and
four-mode preservation theorems typecheck. Full IEEE arithmetic/sqrt refinement
theorems are not claimed: correctness evidence additionally includes exact
operational differential checks against pinned Z3. RNA sqrt now uses exact IEEE
code search/squared midpoint comparisons, with no RNE finite-case fallback.

Lean4.34 binary hashes are official GitHub release asset digests; existing pinned
lean4-nix's binary loader is reused with a local manifest because its manifest
set ends at4.31. No sibling toolchain workspace was changed.

Preliminary local Python:10 unit tests pass,160 operation/mode transport subcases,
special values, equality distinction, RNE/RNA tie, DAG substitution and typed
valuation. Local Z34.16 is not authoritative (known baseline array bug); supported
pinned5.1 Linux results will be recorded separately.


Linux evidence (Abraxas): full twelve-module AYXG core, including substitution,
update and composition laws, typechecked at0d279809 against scoped FloatLib.
Corrected sqrt plus1,305 FloatLib/Z35.1 differential fixtures passed: all five
modes; tiny3/4 and binary32; special/subnormal/random patterns; FMA independent
third operands plus cancellation/overflow/underflow; casts and finite roundToInt.
These fixtures are concrete examples, not a full arithmetic proof or exhaustive
bit-pattern enumeration. Actual pinned lean.py generic-AST correspondence passed9,350 comparisons:
34 families, tiny3/4, binary32 and binary64, all five rounding modes. Its explicit
interpretation chooses canonical NaN bits, invalid casts=0, opposite-zero ties
with the left sign. These are comparisons, not9,350 distinct bit-patterns;
mode-independent families repeat deterministic cases across modes. Preserve
run-v18.json and python-lean-coverage-v18.json for exact commands/counts.
Reviewer-requested augmentation passed9,419 comparisons, adding69 guaranteed
NaN/signed-zero equality and comparison, opposite-zero min/max, positive/negative
half-ULP rounding ties in all five modes, and independent-operand FMA cancellation
cases. Coverage is recorded per format in python-lean-coverage-v19.json. These
are closed operation expressions; this does not claim arbitrary deeply nested
FP program or native hardware correspondence.

Public root Lake metadata: qualified `lake update` generated the pinned manifest;
qualified `lake env true` passed on NixOS. The writable dependency copy is keyed
by scoped source revision222236f0, so the committed path is independent of Nix
store hashes on different platforms. This metadata check did not rebuild the
whole root library; the full library modules were built in the real FFI closure.

The current checkout also applies `nix/floatlib-axiom-footprint.patch`. It uses
direct arithmetic proofs for the IEEE format bounds and reads exponent/fraction
fields without intermediate bounded bit-vectors. The field values are
definitionally equal to the original expressions; two upstream proof scripts
drop rewrites made unnecessary by that simplification. The upstream FloatLib and
Mathlib revisions remain unchanged. `tests/lean/FPAxiomRegression.lean` checks
these equalities and requires exactly `[propext]` for `Env` and
`symbolicStep_length`.

The writable-source key is now
`7553d244c7a4e02ffbbdc21eb66b70b9f37bb5e39e6f36a2dedb7834e1f830af`:
SHA-256 of the upstream revision plus a newline, then the exact bytes of
`floatlib-smt-rna.patch` followed by `floatlib-axiom-footprint.patch`. It identifies
this patched source set; the earlier evidence above retains its original source
revision.
