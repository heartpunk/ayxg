# ayxg

A symbolic transition system library with Python and Lean implementations and tested execution correspondence.

For Lean, use `Ayxg.LTS.QfAbv.SymbolicTransitionSystem C Γ E`.

ayxg models give a few useful affordances:

- you can backwards slice and compose to get an smt-lib translation of any straight line execution path of the binary
- you can prove over 'em in lean, as there's a lean embedding
- the lean embedding has a region algebra a la [henzinger et al](https://doi.org/10.1145/1042038.1042039) if ur into that
