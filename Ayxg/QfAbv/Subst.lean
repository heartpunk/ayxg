import Ayxg.QfAbv.Eval

namespace Ayxg
namespace QfAbv

/-- Typed expression substitution from a source context to a destination context.

`Subst Γsrc Γdst` maps every variable in `Γsrc` to an expression over `Γdst`
of the same sort. This is the intrinsically typed QF_ABV analogue of the
ICTAC/Voogd substitution map from variables to expressions. -/
abbrev Subst (Γsrc Γdst : Ctx) : Type :=
  ∀ {s : TermSort}, Var Γsrc s → Expr Γdst s

namespace Subst

/-- Evaluate a typed substitution in a destination environment, producing the
source-shaped environment obtained by evaluating each replacement expression. -/
def eval : {Γsrc Γdst : Ctx} → Subst Γsrc Γdst → Env Γdst → Env Γsrc
  | [], _, _, _ => Env.nil
  | _ :: _, _, σ, env =>
      Env.cons (Eval.eval env (σ Var.here))
        (eval (fun x => σ (Var.there x)) env)

/-- Looking up a variable in an evaluated substitution environment is the same
as evaluating that variable's replacement expression directly. -/
theorem eval_lookup : {Γsrc Γdst : Ctx} → (σ : Subst Γsrc Γdst) →
    (env : Env Γdst) → {s : TermSort} → (x : Var Γsrc s) →
    Env.lookup (eval σ env) x = Eval.eval env (σ x)
  | [], _, _, _, _, x => nomatch x
  | _ :: _, _, _, _, _, .here => rfl
  | _ :: _, _, σ, env, _, .there x => eval_lookup (fun y => σ (Var.there y)) env x

end Subst

/-- Typed variable renaming from a source context to a destination context. -/
abbrev Renaming (Γsrc Γdst : Ctx) : Type :=
  ∀ {s : TermSort}, Var Γsrc s → Var Γdst s

namespace Renaming

/-- View a renaming as the substitution that maps each variable to the renamed
variable expression. -/
def toSubst (ρ : Renaming Γsrc Γdst) : Subst Γsrc Γdst :=
  fun x => Expr.var (ρ x)

end Renaming

mutual

/-- Rename all free variables in an expression according to `ρ`. `letPar`
binders extend/shadow structurally: fresh bound variables are preserved as
fresh variables, while outer variables are routed through the lifted renaming. -/
def Expr.rename {Γsrc Γdst : Ctx} (ρ : Renaming Γsrc Γdst) :
    {s : TermSort} → Expr Γsrc s → Expr Γdst s
  | _, .var x => .var (ρ x)
  | _, .boolLit b => .boolLit b
  | _, .bvLit w v => .bvLit w v
  | _, .constArray iw vw value => .constArray iw vw (Expr.rename ρ value)
  | _, .boolNot p => .boolNot (Expr.rename ρ p)
  | _, .boolAnd p q => .boolAnd (Expr.rename ρ p) (Expr.rename ρ q)
  | _, .boolOr p q => .boolOr (Expr.rename ρ p) (Expr.rename ρ q)
  | _, .ite c t e => .ite (Expr.rename ρ c) (Expr.rename ρ t) (Expr.rename ρ e)
  | _, .bvBin op w a b => .bvBin op w (Expr.rename ρ a) (Expr.rename ρ b)
  | _, .bvNot w e => .bvNot w (Expr.rename ρ e)
  | _, .zeroExt w n e => .zeroExt w n (Expr.rename ρ e)
  | _, .signExt w n e => .signExt w n (Expr.rename ρ e)
  | _, .extract spec e => .extract spec (Expr.rename ρ e)
  | _, .concat wHi wLo l r => .concat wHi wLo (Expr.rename ρ l) (Expr.rename ρ r)
  | _, .select iw vw mem key => .select iw vw (Expr.rename ρ mem) (Expr.rename ρ key)
  | _, .store iw vw mem key value =>
      .store iw vw (Expr.rename ρ mem) (Expr.rename ρ key) (Expr.rename ρ value)
  | _, .bvUlt w lhs rhs => .bvUlt w (Expr.rename ρ lhs) (Expr.rename ρ rhs)
  | _, .bvUle w lhs rhs => .bvUle w (Expr.rename ρ lhs) (Expr.rename ρ rhs)
  | _, .bvSlt w lhs rhs => .bvSlt w (Expr.rename ρ lhs) (Expr.rename ρ rhs)
  | _, .bvSle w lhs rhs => .bvSle w (Expr.rename ρ lhs) (Expr.rename ρ rhs)
  | _, .eqBool lhs rhs => .eqBool (Expr.rename ρ lhs) (Expr.rename ρ rhs)
  | _, .eqBv w lhs rhs => .eqBv w (Expr.rename ρ lhs) (Expr.rename ρ rhs)
  | _, .letPar bs body =>
      let renamed := Bindings.renameAndLift ρ bs
      .letPar renamed.2.1 (Expr.rename renamed.2.2 body)

/-- Rename a parallel binding group and lift the renaming through the fresh
binders it introduces. The returned destination context is the old destination
context extended by the same fresh binder spine. -/
def Bindings.renameAndLift {Γsrc Γdst : Ctx} (ρ : Renaming Γsrc Γdst) :
    {Γsrc' : Ctx} → Bindings Γsrc Γsrc' →
      Σ Γdst', Bindings Γdst Γdst' × Renaming Γsrc' Γdst'
  | _, .nil => ⟨Γdst, .nil, ρ⟩
  | _, .cons name sort rhs rest =>
      let renamed := Bindings.renameAndLift ρ rest
      let d : Decl := { name := name, sort := sort }
      ⟨d :: renamed.1,
        .cons name sort (Expr.rename ρ rhs) renamed.2.1,
        fun x =>
          match x with
          | Var.here => Var.here
          | Var.there x => Var.there (renamed.2.2 x)⟩

end

namespace Expr

/-- Weaken an expression under one fresh context declaration. -/
def weaken {Γ : Ctx} {s : TermSort} (d : Decl) (e : Expr Γ s) : Expr (d :: Γ) s :=
  Expr.rename (fun x => Var.there x) e

end Expr

mutual


/-- Evaluating a renamed expression in a destination environment agrees with
evaluating the original expression in a source environment when the destination
environment agrees with the source environment along the renaming. -/
theorem Expr.eval_rename {Γsrc Γdst : Ctx} (ρ : Renaming Γsrc Γdst)
    (envSrc : Env Γsrc) (envDst : Env Γdst)
    (hρ : ∀ {s : TermSort} (x : Var Γsrc s), Env.lookup envDst (ρ x) = Env.lookup envSrc x) :
    {s : TermSort} → (e : Expr Γsrc s) →
    Eval.eval envDst (Expr.rename ρ e) = Eval.eval envSrc e
  | _, .var x => hρ x
  | _, .boolLit _ => rfl
  | _, .bvLit _ _ => rfl
  | _, .constArray _ _ value => by
      simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ value]
  | _, .boolNot p => by simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ p]
  | _, .boolAnd p q => by
      simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ p,
        Expr.eval_rename ρ envSrc envDst hρ q]
  | _, .boolOr p q => by
      simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ p,
        Expr.eval_rename ρ envSrc envDst hρ q]
  | _, .ite c t e => by
      simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ c,
        Expr.eval_rename ρ envSrc envDst hρ t, Expr.eval_rename ρ envSrc envDst hρ e]
  | _, .bvBin _ _ a b => by
      simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ a,
        Expr.eval_rename ρ envSrc envDst hρ b]
  | _, .bvNot _ e => by simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ e]
  | _, .zeroExt _ _ e => by simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ e]
  | _, .signExt _ _ e => by simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ e]
  | _, .extract _ e => by simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ e]
  | _, .concat _ _ l r => by
      simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ l,
        Expr.eval_rename ρ envSrc envDst hρ r]
  | _, .select _ _ mem key => by
      simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ mem,
        Expr.eval_rename ρ envSrc envDst hρ key]
  | _, .store _ _ mem key value => by
      simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ mem,
        Expr.eval_rename ρ envSrc envDst hρ key, Expr.eval_rename ρ envSrc envDst hρ value]
  | _, .bvUlt _ lhs rhs => by
      simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ lhs,
        Expr.eval_rename ρ envSrc envDst hρ rhs]
  | _, .bvUle _ lhs rhs => by
      simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ lhs,
        Expr.eval_rename ρ envSrc envDst hρ rhs]
  | _, .bvSlt _ lhs rhs => by
      simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ lhs,
        Expr.eval_rename ρ envSrc envDst hρ rhs]
  | _, .bvSle _ lhs rhs => by
      simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ lhs,
        Expr.eval_rename ρ envSrc envDst hρ rhs]
  | _, .eqBool lhs rhs => by
      simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ lhs,
        Expr.eval_rename ρ envSrc envDst hρ rhs]
  | _, .eqBv _ lhs rhs => by
      simp [Expr.rename, Eval.eval, Expr.eval_rename ρ envSrc envDst hρ lhs,
        Expr.eval_rename ρ envSrc envDst hρ rhs]
  | _, .letPar bs body => by
      dsimp [Expr.rename, Eval.eval]
      let renamed := Bindings.renameAndLift ρ bs
      exact Expr.eval_rename renamed.2.2 (Eval.evalBindings envSrc bs)
        (Eval.evalBindings envDst renamed.2.1)
        (Bindings.renameAndLift_lookup ρ bs envSrc envDst hρ) body

/-- Lookup compatibility for `Bindings.renameAndLift`: after evaluating renamed
bindings in a destination environment, the lifted renaming observes the same
values as the original binding group evaluated in the source environment. -/
theorem Bindings.renameAndLift_lookup : {Γsrc Γdst : Ctx} → (ρ : Renaming Γsrc Γdst) →
    {Γsrc' : Ctx} → (bs : Bindings Γsrc Γsrc') →
    (envSrc : Env Γsrc) → (envDst : Env Γdst) →
    (hρ : ∀ {s : TermSort} (x : Var Γsrc s), Env.lookup envDst (ρ x) = Env.lookup envSrc x) →
    let renamed := Bindings.renameAndLift ρ bs
    ∀ {s : TermSort} (x : Var Γsrc' s),
      Env.lookup (Eval.evalBindings envDst renamed.2.1) (renamed.2.2 x) =
        Env.lookup (Eval.evalBindings envSrc bs) x
  | _, _, ρ, _, .nil, envSrc, envDst, hρ => by
      dsimp [Bindings.renameAndLift, Eval.evalBindings]
      intro x
      exact hρ x
  | _, _, ρ, _, .cons name sort rhs rest, envSrc, envDst, hρ => by
      dsimp [Bindings.renameAndLift, Eval.evalBindings]
      intro x
      cases x with
      | here =>
          exact Expr.eval_rename ρ envSrc envDst hρ rhs
      | there x =>
          exact Bindings.renameAndLift_lookup ρ rest envSrc envDst hρ x

end

namespace Expr

/-- Weakening ignores the fresh head value during evaluation. -/
theorem eval_weaken {Γ : Ctx} {s : TermSort} (d : Decl) (e : Expr Γ s)
    (v : Denote d.sort) (env : Env Γ) :
    Eval.eval (Env.cons v env) (Expr.weaken d e) = Eval.eval env e :=
  Expr.eval_rename (fun x => Var.there x) env (Env.cons v env) (fun _ => rfl) e

end Expr

namespace Subst

/-- Evaluating a substitution whose RHSs have been weakened under a fresh head
declaration ignores that fresh head value. -/
theorem eval_weaken : {Γsrc Γdst : Ctx} → (σ : Subst Γsrc Γdst) →
    (d : Decl) → (v : Denote d.sort) → (env : Env Γdst) →
    Subst.eval (fun x => Expr.weaken d (σ x)) (Env.cons v env) = Subst.eval σ env
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, σ, d, v, env => by
      simp [Subst.eval, Expr.eval_weaken, eval_weaken (fun x => σ (Var.there x)) d v env]

end Subst

mutual

/-- Apply a typed substitution to every free variable in an expression.

For `letPar`, the binding RHSs are substituted in the outer context, while the
body is substituted with a lifted substitution that maps fresh binders to
themselves and routes outer variables through `σ`. -/
def Expr.subst {Γsrc Γdst : Ctx} (σ : Subst Γsrc Γdst) :
    {s : TermSort} → Expr Γsrc s → Expr Γdst s
  | _, .var x => σ x
  | _, .boolLit b => .boolLit b
  | _, .bvLit w v => .bvLit w v
  | _, .constArray iw vw value => .constArray iw vw (Expr.subst σ value)
  | _, .boolNot p => .boolNot (Expr.subst σ p)
  | _, .boolAnd p q => .boolAnd (Expr.subst σ p) (Expr.subst σ q)
  | _, .boolOr p q => .boolOr (Expr.subst σ p) (Expr.subst σ q)
  | _, .ite c t e => .ite (Expr.subst σ c) (Expr.subst σ t) (Expr.subst σ e)
  | _, .bvBin op w a b => .bvBin op w (Expr.subst σ a) (Expr.subst σ b)
  | _, .bvNot w e => .bvNot w (Expr.subst σ e)
  | _, .zeroExt w n e => .zeroExt w n (Expr.subst σ e)
  | _, .signExt w n e => .signExt w n (Expr.subst σ e)
  | _, .extract spec e => .extract spec (Expr.subst σ e)
  | _, .concat wHi wLo l r => .concat wHi wLo (Expr.subst σ l) (Expr.subst σ r)
  | _, .select iw vw mem key => .select iw vw (Expr.subst σ mem) (Expr.subst σ key)
  | _, .store iw vw mem key value =>
      .store iw vw (Expr.subst σ mem) (Expr.subst σ key) (Expr.subst σ value)
  | _, .bvUlt w lhs rhs => .bvUlt w (Expr.subst σ lhs) (Expr.subst σ rhs)
  | _, .bvUle w lhs rhs => .bvUle w (Expr.subst σ lhs) (Expr.subst σ rhs)
  | _, .bvSlt w lhs rhs => .bvSlt w (Expr.subst σ lhs) (Expr.subst σ rhs)
  | _, .bvSle w lhs rhs => .bvSle w (Expr.subst σ lhs) (Expr.subst σ rhs)
  | _, .eqBool lhs rhs => .eqBool (Expr.subst σ lhs) (Expr.subst σ rhs)
  | _, .eqBv w lhs rhs => .eqBv w (Expr.subst σ lhs) (Expr.subst σ rhs)
  | _, .letPar bs body =>
      let substituted := Bindings.substAndLift σ bs
      .letPar substituted.2.1 (Expr.subst substituted.2.2 body)

/-- Substitute a parallel binding group and lift the substitution through its
fresh binders.

The returned destination context is the old destination context extended by the
same fresh binder spine. The lifted substitution preserves those fresh binders
as variables and weakens substituted outer expressions underneath them. -/
def Bindings.substAndLift {Γsrc Γdst : Ctx} (σ : Subst Γsrc Γdst) :
    {Γsrc' : Ctx} → Bindings Γsrc Γsrc' →
      Σ Γdst', Bindings Γdst Γdst' × Subst Γsrc' Γdst'
  | _, .nil => ⟨Γdst, .nil, σ⟩
  | _, .cons name sort rhs rest =>
      let substituted := Bindings.substAndLift σ rest
      let d : Decl := { name := name, sort := sort }
      ⟨d :: substituted.1,
        .cons name sort (Expr.subst σ rhs) substituted.2.1,
        fun x =>
          match x with
          | Var.here => Expr.var Var.here
          | Var.there x => Expr.weaken d (substituted.2.2 x)⟩

end

mutual

/-- Substitution commutes with expression evaluation. This is the typed QF_ABV
analogue of ICTAC's `comp_sub` / `comp_subB`: evaluating the syntactically
substituted expression in the destination environment agrees with evaluating the
original expression in the environment induced by the substitution. -/
theorem Expr.eval_subst {Γsrc Γdst : Ctx} (σ : Subst Γsrc Γdst) (env : Env Γdst) :
    {s : TermSort} → (e : Expr Γsrc s) →
    Eval.eval env (Expr.subst σ e) = Eval.eval (Subst.eval σ env) e
  | _, .var x => (Subst.eval_lookup σ env x).symm
  | _, .boolLit _ => rfl
  | _, .bvLit _ _ => rfl
  | _, .constArray _ _ value => by
      simp [Expr.subst, Eval.eval, Expr.eval_subst σ env value]
  | _, .boolNot p => by simp [Expr.subst, Eval.eval, Expr.eval_subst σ env p]
  | _, .boolAnd p q => by
      simp [Expr.subst, Eval.eval, Expr.eval_subst σ env p, Expr.eval_subst σ env q]
  | _, .boolOr p q => by
      simp [Expr.subst, Eval.eval, Expr.eval_subst σ env p, Expr.eval_subst σ env q]
  | _, .ite c t e => by
      simp [Expr.subst, Eval.eval, Expr.eval_subst σ env c, Expr.eval_subst σ env t,
        Expr.eval_subst σ env e]
  | _, .bvBin _ _ a b => by
      simp [Expr.subst, Eval.eval, Expr.eval_subst σ env a, Expr.eval_subst σ env b]
  | _, .bvNot _ e => by simp [Expr.subst, Eval.eval, Expr.eval_subst σ env e]
  | _, .zeroExt _ _ e => by simp [Expr.subst, Eval.eval, Expr.eval_subst σ env e]
  | _, .signExt _ _ e => by simp [Expr.subst, Eval.eval, Expr.eval_subst σ env e]
  | _, .extract _ e => by simp [Expr.subst, Eval.eval, Expr.eval_subst σ env e]
  | _, .concat _ _ l r => by
      simp [Expr.subst, Eval.eval, Expr.eval_subst σ env l, Expr.eval_subst σ env r]
  | _, .select _ _ mem key => by
      simp [Expr.subst, Eval.eval, Expr.eval_subst σ env mem, Expr.eval_subst σ env key]
  | _, .store _ _ mem key value => by
      simp [Expr.subst, Eval.eval, Expr.eval_subst σ env mem, Expr.eval_subst σ env key,
        Expr.eval_subst σ env value]
  | _, .bvUlt _ lhs rhs => by
      simp [Expr.subst, Eval.eval, Expr.eval_subst σ env lhs, Expr.eval_subst σ env rhs]
  | _, .bvUle _ lhs rhs => by
      simp [Expr.subst, Eval.eval, Expr.eval_subst σ env lhs, Expr.eval_subst σ env rhs]
  | _, .bvSlt _ lhs rhs => by
      simp [Expr.subst, Eval.eval, Expr.eval_subst σ env lhs, Expr.eval_subst σ env rhs]
  | _, .bvSle _ lhs rhs => by
      simp [Expr.subst, Eval.eval, Expr.eval_subst σ env lhs, Expr.eval_subst σ env rhs]
  | _, .eqBool lhs rhs => by
      simp [Expr.subst, Eval.eval, Expr.eval_subst σ env lhs, Expr.eval_subst σ env rhs]
  | _, .eqBv _ lhs rhs => by
      simp [Expr.subst, Eval.eval, Expr.eval_subst σ env lhs, Expr.eval_subst σ env rhs]
  | _, .letPar bs body => by
      dsimp [Expr.subst, Eval.eval]
      let substituted := Bindings.substAndLift σ bs
      calc
        Eval.eval (Eval.evalBindings env substituted.2.1) (Expr.subst substituted.2.2 body)
            = Eval.eval (Subst.eval substituted.2.2 (Eval.evalBindings env substituted.2.1)) body :=
                Expr.eval_subst substituted.2.2 (Eval.evalBindings env substituted.2.1) body
        _ = Eval.eval (Eval.evalBindings (Subst.eval σ env) bs) body := by
                rw [Bindings.substAndLift_eval σ bs env]

/-- Evaluating substituted bindings and then the lifted substitution gives the
same extended environment as evaluating the original bindings in the
substitution-induced source environment. -/
theorem Bindings.substAndLift_eval : {Γsrc Γdst : Ctx} → (σ : Subst Γsrc Γdst) →
    {Γsrc' : Ctx} → (bs : Bindings Γsrc Γsrc') → (env : Env Γdst) →
    let substituted := Bindings.substAndLift σ bs
    Subst.eval substituted.2.2 (Eval.evalBindings env substituted.2.1) =
      Eval.evalBindings (Subst.eval σ env) bs
  | _, _, σ, _, .nil, env => by
      rfl
  | _, _, σ, _, .cons name sort rhs rest, env => by
      dsimp [Bindings.substAndLift, Eval.evalBindings]
      rw [Expr.eval_subst σ env rhs]
      dsimp [Subst.eval, Eval.eval]
      change Env.cons (d := { name := name, sort := sort }) (Eval.eval (Subst.eval σ env) rhs)
          (Subst.eval
            (fun x => Expr.weaken { name := name, sort := sort }
              ((Bindings.substAndLift σ rest).2.2 x))
            (Env.cons (d := { name := name, sort := sort }) (Eval.eval (Subst.eval σ env) rhs)
              (Eval.evalBindings env (Bindings.substAndLift σ rest).2.1))) =
        Env.cons (d := { name := name, sort := sort }) (Eval.eval (Subst.eval σ env) rhs)
          (Eval.evalBindings (Subst.eval σ env) rest)
      rw [Subst.eval_weaken (Bindings.substAndLift σ rest).2.2
        { name := name, sort := sort } (Eval.eval (Subst.eval σ env) rhs)
        (Eval.evalBindings env (Bindings.substAndLift σ rest).2.1)]
      rw [Bindings.substAndLift_eval σ rest env]

end

end QfAbv
end Ayxg
