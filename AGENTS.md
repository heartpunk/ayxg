# Lean QF_ABV STS API guidance

For new Lean models, tests, and libraries, use
`Ayxg.LTS.QfAbv.SymbolicTransitionSystem C Γ E` as the supported QF_ABV
transition-system interface. Its states carry a QF_ABV environment `Γ` and a
control value `C`; its edges carry QF_ABV guard/update semantics. Use `C = Unit`
when the model has no separate structural control site.

`Ayxg.QfAbv.QFAbvSTS Γ` is deprecated for new dependencies and retained for
existing proofs and compatibility during migration. Do not add new public APIs,
tests, or examples that depend on it. When updating existing code, prefer the
source-indexed interface and preserve the current step relation.

This is an API-status and contribution rule, not a removal of QF_ABV support or
a compile-time Lean deprecation attribute. The QF_ABV context, expressions,
steps, guards, and updates remain supported. The generic `Ayxg.STS State Label`
is a separate general abstraction and is not deprecated by this guidance.

When constructing a source-indexed model, ensure each edge stored at `c` has
semantic source `c`; keep the source index and edge semantics consistent.
