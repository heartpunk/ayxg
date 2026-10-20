# Lean QF_ABV STS API guidance

For Lean models, tests, and libraries, use
`Ayxg.LTS.QfAbv.SymbolicTransitionSystem C Γ E` as the supported QF_ABV
transition-system interface. Its states carry a QF_ABV environment `Γ` and a
control value `C`; its edges carry QF_ABV guard/update semantics. Use `C = Unit`
when the model has no separate structural control site.

Preserve the complete labeled step relation when constructing models and
transformations. `QFAbvStep` is defined in `Ayxg.QfAbv.Step`;
the QF_ABV context, expressions, guards, and updates describe its semantics.
The generic `Ayxg.STS State Label` is a separate abstraction.

The Python implementation exposes `ayxg.QFAbvSTS`.

When constructing a source-indexed model, ensure each edge stored at `c` has
semantic source `c`; keep the source index and edge semantics consistent.
