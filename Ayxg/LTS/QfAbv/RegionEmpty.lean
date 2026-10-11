import Ayxg.LTS.QfAbv.RegionMember

namespace Ayxg
namespace LTS
namespace QfAbv

open _root_.Ayxg.QfAbv

namespace Region

/-- Decide emptiness by checking every supplied control and environment. The
lists must cover their respective types for the correctness theorem below. -/
def empty [_root_.Ayxg.QfAbv.FPInterpretation]
    {C : Type} {Γ : Ctx} (controls : List C) (envs : List (Env Γ))
    (region : Region C Γ) : Bool :=
  controls.all fun c =>
    envs.all fun env =>
      !(region.member { control := c, env := env })

/-- Under complete enumerations, the Boolean scan agrees with the semantic
absence of any configuration in the region. -/
theorem empty_eq_true_iff [_root_.Ayxg.QfAbv.FPInterpretation]
    {C : Type} {Γ : Ctx} (controls : List C) (envs : List (Env Γ))
    (hcontrols : ∀ c : C, c ∈ controls)
    (henvs : ∀ env : Env Γ, env ∈ envs)
    (region : Region C Γ) :
    region.empty controls envs = true ↔
      ∀ cfg : Config C Γ, ¬ region.Holds cfg := by
  simp only [empty, List.all_eq_true]
  constructor
  · intro h ⟨c, env⟩
    have hb := h c (hcontrols c) env (henvs env)
    simpa [member, Holds] using hb
  · intro h c hc env he
    have hn := h { control := c, env := env }
    simpa [member, Holds] using hn

end Region

end QfAbv
end LTS
end Ayxg
