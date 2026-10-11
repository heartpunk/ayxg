import Ayxg.LTS.QfAbv.SymbolicTransitionSystem

namespace Ayxg
namespace LTS
namespace QfAbv

open _root_.Ayxg.QfAbv

/-- A QF_ABV region assigns a Boolean formula to each existing control site. -/
structure Region (C : Type) (Γ : Ctx) where
  formulaAt : C → Expr Γ .bool

namespace Region

/-- The subset of existing configurations denoted by a region. -/
def Holds [_root_.Ayxg.QfAbv.FPInterpretation]
    {C : Type} {Γ : Ctx} (region : Region C Γ)
    (cfg : Config C Γ) : Prop :=
  Eval.evalBool cfg.env (region.formulaAt cfg.control) = true

end Region

end QfAbv
end LTS
end Ayxg
