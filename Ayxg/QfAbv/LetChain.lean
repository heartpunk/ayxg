import Ayxg.QfAbv.Update

namespace Ayxg.QfAbv

/-- Ordered groups of existing parallel bindings. Later groups may refer to
previous groups; each group retains SMT-LIB parallel-let semantics. -/
inductive LetChain : Ctx → Ctx → Type where
  | nil : LetChain Γ Γ
  | snoc : LetChain Γ Δ → Bindings Δ Θ → LetChain Γ Θ

namespace LetChain

/-- Close an expression with nested existing lets. The body is never traversed;
binding objects and their RHS expression DAGs are reused across closed fields. -/
def close : LetChain Γ Δ → ({s : TermSort} → Expr Δ s → Expr Γ s)
  | .nil => fun body => body
  | .snoc prefix bindings =>
      let outer := close prefix
      fun body => outer (.letPar bindings body)

/-- Close every RHS of a simultaneous update in the same binding environment. -/
def closeUpdate (chain : LetChain Γ Δ) :
    {Θ : Ctx} → StateUpdate Δ Θ → StateUpdate Γ Θ
  | _, .nil => .nil
  | _, .cons rhs rest => .cons (chain.close rhs) (chain.closeUpdate rest)

variable [FPInterpretation]

/-- Independently evaluate the successive binding environments. -/
def eval : LetChain Γ Δ → Env Γ → Env Δ
  | .nil, env => env
  | .snoc prefix bindings, env => Eval.evalBindings (prefix.eval env) bindings

/-- Nested-let closure preserves the environment-based meaning of a term. -/
theorem eval_close (chain : LetChain Γ Δ) (env : Env Γ) (term : Expr Δ s) :
    Eval.eval env (chain.close term) = Eval.eval (chain.eval env) term := by
  induction chain with
  | nil => rfl
  | snoc prefix bindings ih =>
      dsimp [close, eval]
      rw [ih]
      rfl

/-- Every output field uses the same input and the same resolved temporaries. -/
theorem eval_closeUpdate (chain : LetChain Γ Δ) (env : Env Γ)
    (update : StateUpdate Δ Θ) :
    (chain.closeUpdate update).eval env = update.eval (chain.eval env) := by
  induction update with
  | nil => rfl
  | cons rhs rest ih =>
      simp only [closeUpdate, StateUpdate.eval, eval_close, ih]

end LetChain
end Ayxg.QfAbv
