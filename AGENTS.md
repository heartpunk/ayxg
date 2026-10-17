# Lean QF_ABV STS API guidance

For new Lean models, tests, and libraries, use
`Ayxg.LTS.QfAbv.SymbolicTransitionSystem C Γ E` as the supported QF_ABV
transition-system interface. Its states carry a QF_ABV environment `Γ` and a
control value `C`; its edges carry QF_ABV guard/update semantics. Use `C = Unit`
when the model has no separate structural control site.

The old Lean `Ayxg.QfAbv.QFAbvSTS Γ` interface has been removed. Use the
source-indexed interface and preserve the complete labeled step relation when
migrating existing code. `QFAbvStep` remains available from
`Ayxg.QfAbv.Step`; the QF_ABV context, expressions, guards, and updates remain
supported. The generic `Ayxg.STS State Label` is a separate abstraction.

The Python `ayxg.QFAbvSTS` is a separate API and is not this Lean interface.

When constructing a source-indexed model, ensure each edge stored at `c` has
semantic source `c`; keep the source index and edge semantics consistent.
