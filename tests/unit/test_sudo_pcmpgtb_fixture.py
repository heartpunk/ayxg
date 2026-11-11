"""Check retained Wruh vector updates; this is not a native comparison."""
import json
from pathlib import Path

import pytest

from ayxg import BVSort, Declaration, QFAbvContext, QFAbvExpr, QFAbvValuation, eval_expr
from ayxg.expr import TermSort, TypedExpr

FIXTURES = Path(__file__).resolve().parents[1] / "regressions" / "sudo-pcmpgtb"


@pytest.mark.parametrize("occurrence,dest,src,encoded,address", [
    (933, "zmm0", "zmm6", "660f64c6", 0x436cc5),
    (934, "zmm1", "zmm0", "660f64c8", 0x436cc9),
])
def test_retained_vector_update(occurrence, dest, src, encoded, address):
    fixture = json.loads((FIXTURES / f"{occurrence}.json").read_text())
    origin = fixture["occurrence"]["origin"]
    edge = fixture["edge"]
    assert (FIXTURES / f"{occurrence}.bin").read_bytes() == bytes.fromhex(encoded)
    assert origin["instruction_bytes"] == encoded
    assert origin["canonical_address"] == edge["source"] == address
    assert edge["edge_id"] == {"static_occurrence_id": occurrence, "outcome_id": 0}
    update = next(x["value"] for x in edge["summary"]["simultaneous_update"] if x["name"] == dest)
    expression = TypedExpr.from_data(update)
    context = QFAbvContext(tuple(Declaration(name, TermSort.bv(512)) for name in (dest, src)))
    # Include equal lanes and both directions across the signed boundary.
    left = bytes([0x80, 0x7f, 0xff, 0, 0x80, 0x7f, 1, 0xfe] * 2)
    right = bytes([0x7f, 0x80, 0, 0xff, 0x80, 0x7f, 0xfe, 1] * 2)
    upper = int.from_bytes(bytes(range(48)), "little") << 128
    state = QFAbvValuation(context, (upper | int.from_bytes(left, "little"), int.from_bytes(right, "little")))
    result = eval_expr(QFAbvExpr(context, BVSort(512), expression), state)
    signed = lambda value: value if value < 128 else value - 256
    expected = bytes(0xff if signed(a) > signed(b) else 0 for a, b in zip(left, right))
    assert result == upper | int.from_bytes(expected, "little")
