import json
import pytest
from ayxg.codec import dumps, loads
from ayxg.expr import TypedExpr

def test_shared_expression_roundtrip():
    leaf = TypedExpr.bool_lit(True)
    expr = TypedExpr.binary("bool_and", leaf, leaf)
    value = loads(dumps({"a": expr, "b": expr}))
    assert value["a"] is value["b"]
    assert value["a"].args[0] is value["a"].args[1]

def test_deep_dag_roundtrip():
    expr = TypedExpr.bool_lit(True)
    for _ in range(2000):
        expr = TypedExpr.binary("bool_and", expr, expr)
    wire = dumps({"expression": expr})
    assert len(json.loads(wire)["expression_dag"]["nodes"]) == 2001
    decoded = loads(wire)["expression"]
    for _ in range(2000):
        assert decoded.args[0] is decoded.args[1]
        decoded = decoded.args[0]
    assert decoded.value is True

def test_forward_reference_rejected():
    wire = {"schema": "ayxg-artifact-dag-v1", "expression_dag": {"encoding":"typed-expr-roots-dag-v1", "roots":[0], "nodes":[{"op":"bool_not", "sort":{"kind":"bool"}, "args":[0]}]}, "payload":{"$expr":0}}
    with pytest.raises(ValueError, match="earlier"):
        loads(json.dumps(wire))
