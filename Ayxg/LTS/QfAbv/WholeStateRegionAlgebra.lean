import Ayxg.LTS.QfAbv.RegionFinite

namespace Ayxg.LTS.QfAbv

open _root_.Ayxg.QfAbv

variable [FPInterpretation]

/-- Equip a source-indexed whole-state system with the existing region
algebra. `Unit` is its structural control; all program control is in `Γ`. -/
def wholeStateRegionAlgebra {Γ : Ctx}
    (system : SymbolicTransitionSystem Unit Γ (SymbolicTransition Unit Γ))
    (canonical : system.edgeSemantics = SymbolicTransition.edgeSemantics)
    (observables : Region.Observables Unit Γ) : RegionAlgebra Unit Γ :=
  RegionAlgebra.ofFiniteControls system canonical [()] (by intro c; cases c; simp)
    observables

end Ayxg.LTS.QfAbv
