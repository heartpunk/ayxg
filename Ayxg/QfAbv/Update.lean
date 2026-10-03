import Ayxg.QfAbv.Subst

namespace Ayxg
namespace QfAbv

variable [FPInterpretation]

/-- A simultaneous expression-backed state update from an old context `Γold` to
an output context.

Every right-hand side is typed in the same old context `Γold`, so sibling
assignments are not visible while evaluating the update. This is the transition-
level analogue of SMT-LIB parallel binding groups. -/
inductive StateUpdate (Γold : Ctx) : Ctx → Type where
  | nil : StateUpdate Γold []
  | cons {d : Decl} {Γout : Ctx} :
      Expr Γold d.sort → StateUpdate Γold Γout → StateUpdate Γold (d :: Γout)

namespace StateUpdate

/-- Build the dense update induced by a typed family of right-hand sides. -/
private def ofFamily : {Γold Γout : Ctx} →
    ({s : TermSort} → Var Γout s → Expr Γold s) → StateUpdate Γold Γout
  | _, [], _ => .nil
  | _, _ :: _, rhs =>
      .cons (rhs .here) (ofFamily (fun x => rhs (.there x)))

/-- The canonical dense identity update over a QF_ABV context. -/
def identity (Γ : Ctx) : StateUpdate Γ Γ :=
  ofFamily (fun x => Expr.var x)

/-- Evaluate a simultaneous update. All right-hand sides are evaluated in the
old environment, and the resulting values are assembled into the output
environment. -/
def eval {Γold Γout : Ctx} (env : Env Γold) : StateUpdate Γold Γout → Env Γout
  | .nil => Env.nil
  | .cons rhs rest => Env.cons (Eval.eval env rhs) (eval env rest)

private theorem lookup_eval_ofFamily : {Γold Γout : Ctx} →
    (rhs : {s : TermSort} → Var Γout s → Expr Γold s) →
    (env : Env Γold) → {s : TermSort} → (x : Var Γout s) →
    Env.lookup ((ofFamily rhs).eval env) x = Eval.eval env (rhs x)
  | _, [], _, _, _, x => nomatch x
  | Γold, _ :: Γout, rhs, env, _, .here => rfl
  | Γold, _ :: Γout, rhs, env, _, .there x => by
      simpa [ofFamily, eval, Env.lookup] using
        (lookup_eval_ofFamily
          (Γold := Γold) (Γout := Γout)
          (fun x => rhs (.there x)) env x)

private theorem env_eq_of_lookup_eq : {Γ : Ctx} →
    (left right : Env Γ) →
    (∀ {s : TermSort} (x : Var Γ s),
      Env.lookup left x = Env.lookup right x) →
    left = right
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons leftHead leftTail, .cons rightHead rightTail, h => by
      have hHead := h Var.here
      have hTail := env_eq_of_lookup_eq leftTail rightTail (fun x => h (.there x))
      cases hHead
      cases hTail
      rfl

/-- Evaluating the canonical identity update leaves the environment unchanged. -/
theorem eval_identity {Γ : Ctx} (env : Env Γ) :
    (identity Γ).eval env = env := by
  apply env_eq_of_lookup_eq
  intro s x
  simpa [identity, Eval.eval] using
    (lookup_eval_ofFamily
      (Γold := Γ) (Γout := Γ)
      (fun x => Expr.var x) env x)

/-- View a simultaneous state update as the typed substitution that maps each
output variable to its old-context right-hand side. -/
def toSubst : {Γold Γout : Ctx} → StateUpdate Γold Γout → Subst Γout Γold
  | _, _, .nil => fun x => nomatch x
  | _, _, .cons rhs rest =>
      fun
        | .here => rhs
        | .there x => toSubst rest x

/-- Evaluating the substitution view of a state update produces exactly the
same output environment as evaluating the state update directly. -/
theorem eval_eq_subst_eval : {Γold Γout : Ctx} →
    (u : StateUpdate Γold Γout) → (env : Env Γold) →
    Subst.eval (toSubst u) env = u.eval env
  | _, _, .nil, _ => rfl
  | _, _, .cons _ rest, env => by
      simp [toSubst, Subst.eval, eval, eval_eq_subst_eval rest env]

/-- Pointwise lookup form of `eval_eq_subst_eval`. -/
theorem lookup_eval_eq_eval_toSubst {Γold Γout : Ctx}
    (u : StateUpdate Γold Γout) (env : Env Γold)
    {s : TermSort} (x : Var Γout s) :
    Env.lookup (u.eval env) x = Eval.eval env (u.toSubst x) := by
  rw [← eval_eq_subst_eval u env]
  exact Subst.eval_lookup (toSubst u) env x

/-- Sequentially compose simultaneous state updates by substituting the left
update into every right-hand side of the right update. -/
def compose : {Γ₀ Γ₁ Γ₂ : Ctx} →
    StateUpdate Γ₀ Γ₁ → StateUpdate Γ₁ Γ₂ → StateUpdate Γ₀ Γ₂
  | _, _, _, _, .nil => .nil
  | _, _, _, left, .cons rhs rest => .cons (Expr.subst left.toSubst rhs) (compose left rest)

/-- Evaluating composed state updates is the same as evaluating the left update
first and then the right update. -/
theorem eval_compose : {Γ₀ Γ₁ Γ₂ : Ctx} →
    (left : StateUpdate Γ₀ Γ₁) → (right : StateUpdate Γ₁ Γ₂) → (env : Env Γ₀) →
    (left.compose right).eval env = right.eval (left.eval env)
  | _, _, _, left, .nil, env => rfl
  | _, _, _, left, .cons rhs rest, env => by
      dsimp [compose, eval]
      rw [Expr.eval_subst left.toSubst env rhs]
      rw [eval_eq_subst_eval left env]
      rw [eval_compose left rest env]

/-- Left composition by identity is extensionally neutral. -/
theorem eval_identity_compose {Γ Γout : Ctx}
    (update : StateUpdate Γ Γout) (env : Env Γ) :
    ((identity Γ).compose update).eval env = update.eval env := by
  rw [eval_compose, eval_identity]

/-- Right composition by identity is extensionally neutral. -/
theorem eval_compose_identity {Γold Γ : Ctx}
    (update : StateUpdate Γold Γ) (env : Env Γold) :
    (update.compose (identity Γ)).eval env = update.eval env := by
  rw [eval_compose, eval_identity]

end StateUpdate

end QfAbv
end Ayxg
