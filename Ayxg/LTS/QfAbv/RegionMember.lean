import Ayxg.LTS.QfAbv.Region

namespace Ayxg
namespace LTS
namespace QfAbv

open _root_.Ayxg.QfAbv

namespace Region

/-- Check whether an existing configuration belongs to a region. -/
def member [_root_.Ayxg.QfAbv.FPInterpretation]
    {C : Type} {Γ : Ctx} (region : Region C Γ)
    (cfg : Config C Γ) : Bool :=
  Eval.evalBool cfg.env (region.formulaAt cfg.control)

theorem member_eq_true_iff [_root_.Ayxg.QfAbv.FPInterpretation]
    {C : Type} {Γ : Ctx} (region : Region C Γ)
    (cfg : Config C Γ) :
    region.member cfg = true ↔ region.Holds cfg := by
  rfl

end Region

end QfAbv
end LTS
end Ayxg
