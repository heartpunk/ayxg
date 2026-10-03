"""Implementation of SMT FP operations through the canonical Z3 converter."""
from __future__ import annotations
import z3
from .expr import TermSort, TypedExpr
from .fp import FPValue, RoundingMode, UnderspecifiedFPError, FPInterpretation, fp_bits

_ROUNDING = {"RNE": z3.RNE, "RNA": z3.RNA, "RTP": z3.RTP, "RTN": z3.RTN, "RTZ": z3.RTZ}
FP_Z3_OPERATORS = {
    z3.Z3_OP_FPA_FP: "fp_construct",
    z3.Z3_OP_FPA_ABS: "fp_abs", z3.Z3_OP_FPA_NEG: "fp_neg",
    z3.Z3_OP_FPA_ADD: "fp_add", z3.Z3_OP_FPA_SUB: "fp_sub",
    z3.Z3_OP_FPA_MUL: "fp_mul", z3.Z3_OP_FPA_DIV: "fp_div",
    z3.Z3_OP_FPA_FMA: "fp_fma", z3.Z3_OP_FPA_SQRT: "fp_sqrt",
    z3.Z3_OP_FPA_REM: "fp_rem", z3.Z3_OP_FPA_ROUND_TO_INTEGRAL: "fp_round_to_integral",
    z3.Z3_OP_FPA_MIN: "fp_min", z3.Z3_OP_FPA_MAX: "fp_max",
    z3.Z3_OP_FPA_EQ: "fp_eq", z3.Z3_OP_FPA_LT: "fp_lt", z3.Z3_OP_FPA_LE: "fp_le",
    z3.Z3_OP_FPA_GT: "fp_gt", z3.Z3_OP_FPA_GE: "fp_ge",
    z3.Z3_OP_FPA_IS_NORMAL: "fp_is_normal", z3.Z3_OP_FPA_IS_SUBNORMAL: "fp_is_subnormal",
    z3.Z3_OP_FPA_IS_ZERO: "fp_is_zero", z3.Z3_OP_FPA_IS_INF: "fp_is_infinite",
    z3.Z3_OP_FPA_IS_NAN: "fp_is_nan", z3.Z3_OP_FPA_IS_NEGATIVE: "fp_is_negative",
    z3.Z3_OP_FPA_IS_POSITIVE: "fp_is_positive",
    z3.Z3_OP_FPA_TO_FP: "fp_to_fp", z3.Z3_OP_FPA_TO_FP_UNSIGNED: "ubv_to_fp",
    z3.Z3_OP_FPA_TO_SBV: "fp_to_sbv", z3.Z3_OP_FPA_TO_UBV: "fp_to_ubv",
    z3.Z3_OP_FPA_TO_IEEE_BV: "fp_to_ieee_bv",
}
_FUNCTIONS = {
    "fp_construct": z3.fpFP, "fp_abs": z3.fpAbs, "fp_neg": z3.fpNeg,
    "fp_add": z3.fpAdd, "fp_sub": z3.fpSub, "fp_mul": z3.fpMul, "fp_div": z3.fpDiv,
    "fp_fma": z3.fpFMA, "fp_sqrt": z3.fpSqrt, "fp_rem": z3.fpRem,
    "fp_round_to_integral": z3.fpRoundToIntegral, "fp_min": z3.fpMin, "fp_max": z3.fpMax,
    "fp_eq": z3.fpEQ, "fp_lt": z3.fpLT, "fp_le": z3.fpLEQ, "fp_gt": z3.fpGT, "fp_ge": z3.fpGEQ,
    "fp_is_normal": z3.fpIsNormal, "fp_is_subnormal": z3.fpIsSubnormal, "fp_is_zero": z3.fpIsZero,
    "fp_is_infinite": z3.fpIsInf, "fp_is_nan": z3.fpIsNaN,
    "fp_is_negative": z3.fpIsNegative, "fp_is_positive": z3.fpIsPositive,
    "fp_to_ieee_bv": z3.fpToIEEEBV,
}

def rounding_mode_to_z3(mode: str, ctx: z3.Context) -> z3.FPRMRef:
    return _ROUNDING[mode](ctx=ctx)

def fp_node_to_z3(node: TypedExpr, args: tuple[z3.ExprRef, ...], ctx: z3.Context) -> z3.ExprRef:
    from .z3 import sort_to_z3
    if node.op in _FUNCTIONS:
        return _FUNCTIONS[node.op](*args, ctx=ctx)
    if node.op == "bv_to_fp":
        return z3.fpBVToFP(args[0], sort_to_z3(node.sort, ctx), ctx=ctx)
    if node.op in {"sbv_to_fp", "ubv_to_fp", "fp_to_fp"}:
        fn = {"sbv_to_fp": z3.fpSignedToFP, "ubv_to_fp": z3.fpUnsignedToFP, "fp_to_fp": z3.fpToFP}[node.op]
        return fn(*args, sort_to_z3(node.sort, ctx), ctx=ctx)
    if node.op in {"fp_to_sbv", "fp_to_ubv"}:
        fn = z3.fpToSBV if node.op == "fp_to_sbv" else z3.fpToUBV
        return fn(*args, sort_to_z3(node.sort, ctx), ctx=ctx)
    raise ValueError(node.op)

def fp_leaf_from_z3(expr: z3.ExprRef, sort: TermSort) -> TypedExpr | None:
    kind = expr.decl().kind()
    rm_kinds = {z3.Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN: "RNE", z3.Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY: "RNA", z3.Z3_OP_FPA_RM_TOWARD_POSITIVE: "RTP", z3.Z3_OP_FPA_RM_TOWARD_NEGATIVE: "RTN", z3.Z3_OP_FPA_RM_TOWARD_ZERO: "RTZ"}
    if kind in rm_kinds:
        return TypedExpr("rm_lit", sort, value=rm_kinds[kind])
    if z3.is_fp_value(expr):
        eb, sb = sort.require_fp_widths()
        if expr.isNaN():
            bits = (((1 << eb) - 1) << (sb - 1)) | 1
        elif expr.isInf():
            bits = (int(expr.isNegative()) << (eb + sb - 1)) | (((1 << eb) - 1) << (sb - 1))
        else:
            bits = z3.simplify(z3.fpToIEEEBV(expr, ctx=expr.ctx)).as_long()
        return fp_bits(sort, bits)
    return None

def value_to_z3(value: FPValue | RoundingMode | bool | int, sort: TermSort, ctx: z3.Context) -> z3.ExprRef:
    from .z3 import expr_to_z3
    if sort.kind == "fp":
        if not isinstance(value, FPValue) or value.sort != sort:
            raise ValueError("FP valuation sort mismatch")
        return expr_to_z3(fp_bits(sort, value.bits), {}, ctx)
    if sort.kind == "rm":
        return rounding_mode_to_z3(RoundingMode(value).value, ctx)
    if sort.kind == "bool":
        return z3.BoolVal(value, ctx=ctx)
    return z3.BitVecVal(value, sort.require_bv_width(), ctx=ctx)

def evaluate_fp_node(node: TypedExpr, values: tuple, fp_interpretation: FPInterpretation | None = None) -> FPValue | RoundingMode | bool | int:
    """Evaluate defined ground operations; never pick unspecified output bits.

    Z3 simplification retains invalid casts and NaN-to-bits as terms. Detect
    those before returning a concrete value; repeated evaluation thus cannot
    invent mutually inconsistent interpretations of the same function.
    """
    ctx = z3.Context()
    if node.op == "rm_lit":
        return RoundingMode(node.value)
    if node.op in {"fp_min", "fp_max"}:
        lhs, rhs = values
        eb, sb = node.args[0].sort.require_fp_widths()
        zero_sign = 1 << (eb + sb - 1)
        if isinstance(lhs, FPValue) and isinstance(rhs, FPValue) and {lhs.bits, rhs.bits} == {0, zero_sign}:
            if fp_interpretation is None:
                raise UnderspecifiedFPError("SMT fp.min/max of opposite signed zeros requires an interpretation")
            return fp_interpretation.resolve(node, values)
    args = tuple(value_to_z3(v, a.sort, ctx) for v, a in zip(values, node.args, strict=True))
    result = z3.simplify(fp_node_to_z3(node, args, ctx))
    if node.sort.kind == "bool" and (z3.is_true(result) or z3.is_false(result)):
        return z3.is_true(result)
    if node.sort.kind == "bv" and z3.is_bv_value(result):
        return result.as_long()
    if node.sort.kind == "fp" and z3.is_fp_value(result):
        leaf = fp_leaf_from_z3(result, node.sort)
        assert leaf is not None
        return FPValue(node.sort, leaf.args[0].value)
    if fp_interpretation is not None and node.op in {"fp_to_sbv", "fp_to_ubv", "fp_to_ieee_bv"}:
        return fp_interpretation.resolve(node, values)
    raise UnderspecifiedFPError(f"ground SMT FP operation has no determined concrete value: {result.sexpr()}")
