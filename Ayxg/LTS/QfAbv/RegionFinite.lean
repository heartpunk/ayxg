import Ayxg.LTS.QfAbv.RegionAlgebra
import Ayxg.LTS.QfAbv.FiniteEnv

namespace Ayxg
namespace LTS
namespace QfAbv

open _root_.Ayxg.QfAbv

namespace RegionAlgebra

/-- Build the semantic region-algebra package using AYXG's complete QF_ABV
environment enumeration. The caller supplies the finite control sites and
observables of the existing transition system. Effective execution additionally
depends on the caller-supplied functions noted in `RegionAlgebra`. -/
def ofFiniteControls {C : Type} [DecidableEq C]
    [_root_.Ayxg.QfAbv.FPInterpretation] {Γ : Ctx}
    (system : SymbolicTransitionSystem C Γ (SymbolicTransition C Γ))
    (canonical : system.edgeSemantics = SymbolicTransition.edgeSemantics)
    (controls : List C) (controls_complete : ∀ c : C, c ∈ controls)
    (observables : Region.Observables C Γ) : RegionAlgebra C Γ where
  system := system
  canonical := canonical
  controls := controls
  controls_complete := controls_complete
  envs := enumerateEnv Γ
  envs_complete := mem_enumerateEnv
  observables := observables

end RegionAlgebra

end QfAbv
end LTS
end Ayxg
