# ayxg

A symbolic transition system library with Python and Lean implementations and tested execution correspondence.

For Lean, use `Ayxg.LTS.QfAbv.SymbolicTransitionSystem C Γ E`.

`QFAbvStep Γ` is a guarded transition within the state context `Γ`.
`QFAbvAdapter Γin Γout` is a separate guarded transformer between state
contexts; use it for entry and exit interfaces. Both have composition that
substitutes earlier updates into later guards. Python provides the same
distinction as `QFAbvStep` and `QFAbvAdapter`.

ayxg models give a few useful affordances:

- you can backwards slice and compose to get an smt-lib translation of any straight line execution path of the binary
- you can prove over 'em in lean, as there's a lean embedding
- the lean embedding has a region algebra a la [henzinger et al](https://doi.org/10.1145/1042038.1042039) if ur into that
