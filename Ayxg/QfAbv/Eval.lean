import Ayxg.QfAbv.Ast

namespace Ayxg
namespace QfAbv

/-- SMT-style array value: total map from bit-vector indices to bit-vector values. -/
abbrev Mem (iw vw : Nat) := BitVec iw → BitVec vw

/-- Semantic carrier of a QF_ABV sort. -/
abbrev Denote : TermSort → Type
  | .bool => Bool
  | .bv w => BitVec w
  | .array iw vw => Mem iw vw

/-- A total typed environment assigning every declaration in a context its value. -/
inductive Env : Ctx → Type where
  | nil : Env []
  | cons {d : Decl} {Γ : Ctx} : Denote d.sort → Env Γ → Env (d :: Γ)

namespace Env

/-- Total lookup for typed de Bruijn variables. -/
def lookup : {Γ : Ctx} → Env Γ → Var Γ s → Denote s
  | [], .nil, x => nomatch x
  | _ :: _, .cons v _, .here => v
  | _ :: _, .cons _ env, .there x => lookup env x

end Env

namespace Eval

@[inline] def BvBinOp.apply (w : Nat) (op : BvBinOp) (a b : BitVec w) : BitVec w :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b
  | .udiv => a / b
  | .urem => a % b
  | .and => a &&& b
  | .or => a ||| b
  | .xor => a ^^^ b
  | .shl => a <<< b
  | .lshr => a >>> b
  | .ashr => BitVec.sshiftRight' a b

@[inline] def memLoad {iw vw : Nat} (m : Mem iw vw) (addr : BitVec iw) : BitVec vw :=
  m addr

@[inline] def memStore {iw vw : Nat} (m : Mem iw vw)
    (addr : BitVec iw) (value : BitVec vw) : Mem iw vw :=
  fun a => if a = addr then value else m a

@[inline] def memConst {iw vw : Nat} (value : BitVec vw) : Mem iw vw :=
  fun _ => value

mutual

/-- Total denotation of typed QF_ABV expressions. -/
def eval : {Γ : Ctx} → Env Γ → {s : TermSort} → Expr Γ s → Denote s
  | _, env, _, Expr.var x => Env.lookup env x
  | _, _, .bool, Expr.boolLit b => b
  | _, _, .bv w, Expr.bvLit _ v => BitVec.ofNat w v
  | _, env, .array _ _, Expr.constArray _ _ value => memConst (eval env value)
  | _, env, .bool, Expr.boolNot p => !(eval env p)
  | _, env, .bool, Expr.boolAnd p q => eval env p && eval env q
  | _, env, .bool, Expr.boolOr p q => eval env p || eval env q
  | _, env, _, Expr.ite c t e => if eval env c then eval env t else eval env e
  | _, env, .bv w, Expr.bvBin op _ a b => BvBinOp.apply w op (eval env a) (eval env b)
  | _, env, .bv _, Expr.bvNot _ e => ~~~ (eval env e)
  | _, env, .bv _, Expr.zeroExt w n e => BitVec.zeroExtend (w + n) (eval env e)
  | _, env, .bv _, Expr.signExt w n e => BitVec.signExtend (w + n) (eval env e)
  | _, env, .bv _, Expr.extract spec e => BitVec.extractLsb spec.hi spec.lo (eval env e)
  | _, env, .bv _, Expr.concat _ _ l r => eval env l ++ eval env r
  | _, env, .bv _, Expr.select _ _ mem key => memLoad (eval env mem) (eval env key)
  | _, env, .array _ _, Expr.store _ _ mem key value =>
      memStore (eval env mem) (eval env key) (eval env value)
  | _, env, .bool, Expr.bvUlt _ lhs rhs => (eval env lhs).ult (eval env rhs)
  | _, env, .bool, Expr.bvUle _ lhs rhs => (eval env lhs).ule (eval env rhs)
  | _, env, .bool, Expr.bvSlt _ lhs rhs => (eval env lhs).slt (eval env rhs)
  | _, env, .bool, Expr.bvSle _ lhs rhs => (eval env lhs).sle (eval env rhs)
  | _, env, .bool, Expr.eqBool lhs rhs => eval env lhs == eval env rhs
  | _, env, .bool, Expr.eqBv _ lhs rhs => eval env lhs == eval env rhs
  | _, env, _, Expr.letPar bindings body => eval (evalBindings env bindings) body

/-- Evaluate a parallel binding group: every RHS is evaluated in the old environment. -/
def evalBindings : {Γ Γ' : Ctx} → Env Γ → Bindings Γ Γ' → Env Γ'
  | _, _, env, Bindings.nil => env
  | _, _, env, Bindings.cons name sort rhs rest =>
      Env.cons (eval env rhs) (evalBindings env rest)

end

@[simp] def evalBool {Γ : Ctx} (env : Env Γ) (e : Expr Γ .bool) : Bool :=
  eval env e

@[simp] def evalBv {Γ : Ctx} (env : Env Γ) {w : Nat}
    (e : Expr Γ (.bv w)) : BitVec w :=
  eval env e

@[simp] def evalArr {Γ : Ctx} (env : Env Γ) {iw vw : Nat}
    (e : Expr Γ (.array iw vw)) : Mem iw vw :=
  eval env e

end Eval

end QfAbv
end Ayxg
