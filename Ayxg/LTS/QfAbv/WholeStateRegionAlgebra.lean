import Ayxg.LTS.QfAbv.STSBridge
import Ayxg.LTS.QfAbv.RegionFinite

namespace Ayxg.QfAbv.QFAbvSTS

variable [FPInterpretation]

/-- Equip a whole-state QF_ABV system with the existing region algebra.

The caller chooses the finite observables of the modeled program. `Unit` adds
no control component beyond the complete environment already used by this STS.
The bridge preserves its one-step transition relation exactly. -/
def toRegionAlgebra {Γ : Ctx} (model : QFAbvSTS Γ)
    (observables : _root_.Ayxg.LTS.QfAbv.Region.Observables Unit Γ) :
    _root_.Ayxg.LTS.QfAbv.RegionAlgebra Unit Γ :=
  _root_.Ayxg.LTS.QfAbv.RegionAlgebra.ofFiniteControls
    model.toControlSystem rfl [()] (by intro c; cases c; simp) observables

end Ayxg.QfAbv.QFAbvSTS
