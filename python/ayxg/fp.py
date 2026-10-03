"""SMT-LIB FP typing and exact values; no host floating-point arithmetic.

SMT FP has one NaN value: payload/sign are intentionally not preserved here.
Hardware status flags and traps are outside this theory. The Z3 extension
fp.to_ieee_bv (not a standard SMT-LIB operator) is unspecified on NaN;
invalid fp.to_[su]bv, and fp.min/max signed-zero ties remain underspecified.
"""
from __future__ import annotations
from dataclasses import dataclass
from enum import Enum
from collections.abc import Mapping
from types import MappingProxyType
from .expr import ArtifactError, BOOL, TermSort, TypedExpr

class RoundingMode(str, Enum):
    RNE = "RNE"
    RNA = "RNA"
    RTP = "RTP"
    RTN = "RTN"
    RTZ = "RTZ"

RM = TermSort.rounding_mode()
FP_UNARY = {"fp_abs", "fp_neg"}
FP_CLASSIFY = {"fp_is_normal", "fp_is_subnormal", "fp_is_zero", "fp_is_infinite", "fp_is_nan", "fp_is_negative", "fp_is_positive"}
FP_COMPARE = {"fp_eq", "fp_lt", "fp_le", "fp_gt", "fp_ge"}
FP_BINARY = {"fp_rem", "fp_min", "fp_max"}
FP_ROUNDED_BINARY = {"fp_add", "fp_sub", "fp_mul", "fp_div"}

def check_fp_node(node: TypedExpr) -> None:
    op, args, sort = node.op, node.args, node.sort
    def require(ok: bool) -> None:
        if not ok:
            raise ArtifactError(f"{op} operand/result sorts disagree")
    if op == "fp_construct":
        eb, sb = sort.require_fp_widths()
        require(tuple(a.sort for a in args) == (TermSort.bv(1), TermSort.bv(eb), TermSort.bv(sb - 1)))
    elif op == "bv_to_fp":
        eb, sb = sort.require_fp_widths()
        require(len(args) == 1 and args[0].sort == TermSort.bv(eb + sb))
    elif op in FP_UNARY | FP_CLASSIFY:
        require(len(args) == 1 and args[0].sort.kind == "fp" and sort == (BOOL if op in FP_CLASSIFY else args[0].sort))
    elif op in FP_COMPARE | FP_BINARY:
        require(len(args) == 2 and args[0].sort.kind == "fp" and args[0].sort == args[1].sort and sort == (BOOL if op in FP_COMPARE else args[0].sort))
    elif op in FP_ROUNDED_BINARY | {"fp_fma"}:
        require(len(args) == (4 if op == "fp_fma" else 3) and args[0].sort == RM and sort.kind == "fp" and all(a.sort == sort for a in args[1:]))
    elif op in {"fp_sqrt", "fp_round_to_integral"}:
        require(len(args) == 2 and args[0].sort == RM and sort.kind == "fp" and args[1].sort == sort)
    elif op == "fp_to_ieee_bv":
        require(len(args) == 1 and args[0].sort.kind == "fp")
        eb, sb = args[0].sort.require_fp_widths()
        require(sort == TermSort.bv(eb + sb))
    elif op in {"fp_to_sbv", "fp_to_ubv"}:
        require(len(args) == 2 and args[0].sort == RM and args[1].sort.kind == "fp" and sort.kind == "bv")
    elif op in {"sbv_to_fp", "ubv_to_fp", "fp_to_fp"}:
        require(len(args) == 2 and args[0].sort == RM and sort.kind == "fp" and args[1].sort.kind == ("fp" if op == "fp_to_fp" else "bv"))
    else:
        raise ArtifactError(f"unknown FP operator: {op}")

@dataclass(frozen=True)
class FPValue:
    """Canonical SMT FP value encoded by interchange bits (all NaNs collapse)."""
    sort: TermSort
    bits: int
    def __post_init__(self) -> None:
        eb, sb = self.sort.require_fp_widths()
        if type(self.bits) is not int or not 0 <= self.bits < 1 << (eb + sb):
            raise ArtifactError("FP value outside interchange width")
        exp = (self.bits >> (sb - 1)) & ((1 << eb) - 1)
        fraction = self.bits & ((1 << (sb - 1)) - 1)
        if exp == (1 << eb) - 1 and fraction:
            object.__setattr__(self, "bits", (((1 << eb) - 1) << (sb - 1)) | 1)

class UnderspecifiedFPError(ArtifactError):
    """Concrete evaluation cannot pick an arbitrary interpretation silently."""

def rm_literal(mode: RoundingMode) -> TypedExpr:
    return TypedExpr("rm_lit", RM, value=mode.value)

def fp_bits(sort: TermSort, bits: int) -> TypedExpr:
    eb, sb = sort.require_fp_widths()
    return TypedExpr("bv_to_fp", sort, (TypedExpr.bv_lit(eb + sb, bits),))

@dataclass(frozen=True)
class UnderspecifiedFPKey:
    """Ordered typed arguments identify one application of an SMT function."""
    op: str
    result_sort: TermSort
    arguments: tuple[tuple[TermSort, FPValue | RoundingMode | int], ...]

    @classmethod
    def from_node(cls, node: TypedExpr, values: tuple) -> UnderspecifiedFPKey:
        return cls(node.op, node.sort, tuple((a.sort, v) for a, v in zip(node.args, values, strict=True)))

@dataclass(frozen=True)
class FPInterpretation:
    """Explicit immutable, consistent choices for underspecified applications.

    No choice is inferred. A missing key raises UnderspecifiedFPError. NaN bit
    choices must encode NaN; signed-zero ties choose one of the two zeros;
    invalid FP-to-BV choices may be any value of the declared BV width.
    """
    choices: Mapping[UnderspecifiedFPKey, FPValue | int]

    def __post_init__(self) -> None:
        object.__setattr__(self, "choices", MappingProxyType(dict(self.choices)))

    def resolve(self, node: TypedExpr, values: tuple) -> FPValue | int:
        key = UnderspecifiedFPKey.from_node(node, values)
        if key not in self.choices:
            raise UnderspecifiedFPError(f"missing explicit FP interpretation: {key}")
        result = self.choices[key]
        if node.op in {"fp_min", "fp_max"}:
            eb, sb = node.sort.require_fp_widths()
            if not isinstance(result, FPValue) or result.sort != node.sort or result.bits not in {0, 1 << (eb + sb - 1)}:
                raise ArtifactError("signed-zero choice must be a zero of the result sort")
        elif node.op in {"fp_to_sbv", "fp_to_ubv", "fp_to_ieee_bv"}:
            if type(result) is not int or not 0 <= result < 1 << node.sort.require_bv_width():
                raise ArtifactError("FP interpretation result outside declared BV width")
            if node.op == "fp_to_ieee_bv":
                f = node.args[0].sort
                eb, sb = f.require_fp_widths()
                if (result >> (sb - 1)) & ((1 << eb) - 1) != (1 << eb) - 1 or result & ((1 << (sb - 1)) - 1) == 0:
                    raise ArtifactError("NaN-to-bits choice must encode NaN")
        else:
            raise ArtifactError("interpretation supplied for a defined FP operation")
        return result
