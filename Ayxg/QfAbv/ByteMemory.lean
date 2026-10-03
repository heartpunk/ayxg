import Ayxg.QfAbv.Eval

namespace Ayxg.QfAbv.ByteMemory

/-- `extra + 1` bytes; every constructed bit-vector has positive width. -/
abbrev Width (extra : Nat) := 8 + 8 * extra

/-- Little-endian load. Reuse the supplied memory/address expressions; no
read definition is recursively substituted into another expression. -/
def loadLE {Γ : Ctx} {iw : Nat} (extra : Nat)
    (memory : Expr Γ (.array iw 8)) (address : Expr Γ (.bv iw)) :
    Expr Γ (.bv (Width extra)) :=
  (List.range (extra + 1)).foldl (fun acc offset =>
    .bvBin .or (Width extra) acc
      (.bvBin .shl (Width extra)
        (.zeroExt 8 (8 * extra)
          (.select iw 8 memory (.bvBin .add iw address (.bvLit iw offset))))
        (.bvLit (Width extra) (8 * offset)))) (.bvLit (Width extra) 0)

/-- Little-endian store. Later byte writes remain outside earlier stores,
including when finite-width address arithmetic wraps and aliases. -/
def storeLE {Γ : Ctx} {iw : Nat} (extra : Nat)
    (memory : Expr Γ (.array iw 8)) (address : Expr Γ (.bv iw))
    (value : Expr Γ (.bv (Width extra))) : Expr Γ (.array iw 8) :=
  let byte : Nat → Expr Γ (.bv 8) := fun offset =>
    .extract { hi := 7, lo := 0, hi_lt_width := by unfold Width; omega,
               lo_le_hi := by omega }
      (.bvBin .lshr (Width extra) value (.bvLit (Width extra) (8 * offset)))
  (List.range (extra + 1)).foldl (fun current offset =>
    .store iw 8 current (.bvBin .add iw address (.bvLit iw offset)) (byte offset)) memory

/-- Concrete byte packing, using the same SMT-LIB bit-vector operations as
AYXG evaluation. Byte i occupies bits 8*i through 8*i+7. -/
def loadValue {iw : Nat} (extra : Nat) (memory : Mem iw 8) (address : BitVec iw) :
    BitVec (Width extra) :=
  (List.range (extra + 1)).foldl (fun acc offset =>
    acc ||| Eval.BvBinOp.apply (Width extra) .shl
      (BitVec.zeroExtend (Width extra) (memory (address + BitVec.ofNat iw offset)))
      (BitVec.ofNat (Width extra) (8 * offset))) 0

/-- Ordered concrete byte writes, including address wraparound. -/
def storeValue {iw : Nat} (extra : Nat) (memory : Mem iw 8) (address : BitVec iw)
    (value : BitVec (Width extra)) : Mem iw 8 :=
  (List.range (extra + 1)).foldl (fun current offset =>
    Eval.memStore current (address + BitVec.ofNat iw offset)
      (BitVec.extractLsb 7 0 (Eval.BvBinOp.apply (Width extra) .lshr value
        (BitVec.ofNat (Width extra) (8 * offset))))) memory

variable [FPInterpretation]

/-- Expression construction transports the concrete little-endian load. -/
theorem eval_loadLE {Γ : Ctx} {iw : Nat} (extra : Nat) (env : Env Γ)
    (memory : Expr Γ (.array iw 8)) (address : Expr Γ (.bv iw)) :
    Eval.eval env (loadLE extra memory address) =
      loadValue extra (Eval.eval env memory) (Eval.eval env address) := by
  let step := fun (acc : Expr Γ (.bv (Width extra))) (offset : Nat) =>
    Expr.bvBin .or (Width extra) acc
      (.bvBin .shl (Width extra)
        (.zeroExt 8 (8 * extra)
          (.select iw 8 memory (.bvBin .add iw address (.bvLit iw offset))))
        (.bvLit (Width extra) (8 * offset)))
  let concrete := fun (acc : BitVec (Width extra)) (offset : Nat) =>
    acc ||| Eval.BvBinOp.apply (Width extra) .shl
      (BitVec.zeroExtend (Width extra)
        ((Eval.eval env memory) (Eval.eval env address + BitVec.ofNat iw offset)))
      (BitVec.ofNat (Width extra) (8 * offset))
  have go (offsets : List Nat) (acc : Expr Γ (.bv (Width extra))) :
      Eval.eval env (offsets.foldl step acc) = offsets.foldl concrete (Eval.eval env acc) := by
    induction offsets generalizing acc with
    | nil => rfl
    | cons offset rest ih =>
      simp only [List.foldl_cons, ih]
      rfl
  exact go (List.range (extra + 1)) (.bvLit (Width extra) 0)

/-- Expression construction transports ordered little-endian writes. -/
theorem eval_storeLE {Γ : Ctx} {iw : Nat} (extra : Nat) (env : Env Γ)
    (memory : Expr Γ (.array iw 8)) (address : Expr Γ (.bv iw))
    (value : Expr Γ (.bv (Width extra))) :
    Eval.eval env (storeLE extra memory address value) =
      storeValue extra (Eval.eval env memory) (Eval.eval env address) (Eval.eval env value) := by
  unfold storeLE storeValue
  generalize List.range (extra + 1) = offsets
  induction offsets generalizing memory with
  | nil => rfl
  | cons offset rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    rfl

end Ayxg.QfAbv.ByteMemory
