import Ayxg.QfAbv.Ast
import Ayxg.QfAbv.FpEval

namespace Ayxg
namespace QfAbv

/-- SMT-style array value: total map from bit-vector indices to bit-vector values. -/
abbrev Mem (iw vw : Nat) := BitVec iw → BitVec vw

/-- Semantic carrier of a QF_ABV sort. -/
abbrev Denote : TermSort → Type
  | .bool => Bool
  | .bv w => BitVec w
  | .array iw vw => Mem iw vw
  | .fp f => FPValue f
  | .roundingMode => RoundingMode

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

variable [FPInterpretation]

namespace Eval

@[inline] def BvBinOp.apply (w : Nat) (op : BvBinOp) (a b : BitVec w) : BitVec w :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b
  | .udiv => BitVec.smtUDiv a b
  | .sdiv => BitVec.smtSDiv a b
  | .urem => a % b
  | .and => a &&& b
  | .or => a ||| b
  | .xor => a ^^^ b
  | .shl => if b.toNat < w then a <<< b else 0
  | .lshr => if b.toNat < w then a >>> b else 0
  | .ashr =>
      if b.toNat < w then BitVec.sshiftRight' a b
      else if a.msb then BitVec.allOnes w else 0

@[inline] def memLoad {iw vw : Nat} (m : Mem iw vw) (addr : BitVec iw) : BitVec vw :=
  m addr

@[inline] def memStore {iw vw : Nat} (m : Mem iw vw)
    (addr : BitVec iw) (value : BitVec vw) : Mem iw vw :=
  fun a => if a = addr then value else m a

@[inline] def memConst {iw vw : Nat} (value : BitVec vw) : Mem iw vw :=
  fun _ => value

/-- Extensional equality over the entire finite bit-vector index domain. -/
def memEqual {iw vw : Nat} (left right : Mem iw vw) : Bool :=
  (List.range (2 ^ iw)).all fun i =>
    left (BitVec.ofNat iw i) == right (BitVec.ofNat iw i)

mutual

/-- Total denotation of typed QF_ABV expressions. -/
def eval : {Γ : Ctx} → Env Γ → {s : TermSort} → Expr Γ s → Denote s
  | _, env, _, Expr.var x => Env.lookup env x
  | _, _, .bool, Expr.boolLit b => b
  | _, _, .bv w, Expr.bvLit _ v => BitVec.ofNat w v
  | _, _, .roundingMode, Expr.rmLit mode => mode
  | _, env, .fp f, Expr.fpFromBits _ e => FPValue.ofBits f (eval env e)
  | _, env, .bv _, Expr.fpToBits _ e => FPEval.toBits (eval env e)
  | _, env, .fp _, Expr.fpUnary op _ e => FPEval.unary op (eval env e)
  | _, env, .fp _, Expr.fpBinary op _ a b => FPEval.binary op (eval env a) (eval env b)
  | _, env, .fp _, Expr.fpRounded op _ rm a b => FPEval.rounded op (eval env rm) (eval env a) (eval env b)
  | _, env, .fp _, Expr.fpFma _ rm a b c => FPEval.fma (eval env rm) (eval env a) (eval env b) (eval env c)
  | _, env, .fp _, Expr.fpSqrt _ rm e => FPEval.sqrt (eval env rm) (eval env e)
  | _, env, .fp _, Expr.fpRoundToIntegral _ rm e => FPEval.roundToIntegral (eval env rm) (eval env e)
  | _, env, .bool, Expr.fpCompare op _ a b => FPEval.compare op (eval env a) (eval env b)
  | _, env, .bool, Expr.fpClassify op _ e => FPEval.classify op (eval env e)
  | _, env, .bv _, Expr.fpToBv signed _ width rm e => FPEval.toBV signed width (eval env rm) (eval env e)
  | _, env, .fp _, Expr.fpFromBv signed _ f rm e => FPEval.fromBV signed f (eval env rm) (eval env e)
  | _, env, .fp _, Expr.fpCast src dst rm e => FPEval.cast src dst (eval env rm) (eval env e)
  | _, env, .bool, Expr.eqFp _ a b => decide (eval env a = eval env b)
  | _, env, .bool, Expr.eqRoundingMode a b => eval env a == eval env b
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
  | _, env, .bool, Expr.eqArray _ _ lhs rhs => memEqual (eval env lhs) (eval env rhs)
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
