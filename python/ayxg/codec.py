"""Shared artifact codec, reusing Ghot's typed-expr-roots-dag-v1.

Encoder imported from Ghot61d60539 extractor/artifact.py; node ordering and
signature are unchanged. Its Lean counterpart is Ghot.QfAbv.TypedArtifact.
"""
from __future__ import annotations
import json
from typing import Any
from .expr import TypedExpr

def typed_expr_roots_dag(
    roots: tuple[TypedExpr, ...],
) -> dict[str, object]:
    """Encode typed roots as one deterministic structural DAG."""

    by_identity: dict[int, tuple[TypedExpr, int]] = {}
    by_signature: dict[tuple[object, ...], int] = {}
    nodes: list[dict[str, object]] = []

    for root in roots:
        pending: list[tuple[TypedExpr, bool]] = [(root, False)]
        while pending:
            node, expanded = pending.pop()
            cached = by_identity.get(id(node))
            if cached is not None and cached[0] is node:
                continue
            if not expanded:
                pending.append((node, True))
                for child in reversed(node.args):
                    child_cached = by_identity.get(id(child))
                    if child_cached is None or child_cached[0] is not child:
                        pending.append((child, False))
                continue
            child_indices = tuple(
                by_identity[id(child)][1] for child in node.args
            )
            signature = (
                node.op,
                node.sort.kind,
                node.sort.exponent_bits,
                node.sort.significand_bits,
                node.sort.width,
                node.sort.index_width,
                node.sort.value_width,
                node.name,
                node.value,
                node.amount,
                node.hi,
                node.lo,
                node.index,
                node.bindings,
                child_indices,
            )
            index = by_signature.get(signature)
            if index is None:
                index = len(nodes)
                by_signature[signature] = index
                record: dict[str, object] = {
                    "op": node.op,
                    "sort": node.sort.to_data(),
                    "args": list(child_indices),
                }
                for field in ("name", "value", "amount", "hi", "lo", "index"):
                    value = getattr(node, field)
                    if value is not None:
                        record[field] = value
                if node.bindings is not None:
                    record["bindings"] = [d.to_data() for d in node.bindings]
                nodes.append(record)
            by_identity[id(node)] = (node, index)

    return {
        "encoding": "typed-expr-roots-dag-v1",
        "roots": [by_identity[id(root)][1] for root in roots],
        "nodes": nodes,
    }

SCHEMA = "ayxg-artifact-dag-v1"

def dumps(payload: Any, *, indent: int | None = None, sort_keys: bool = True) -> str:
    roots: list[TypedExpr] = []
    memo: dict[int, tuple[dict, TypedExpr]] = {}

    def expression(root: dict) -> TypedExpr:
        stack = [(root, False)]
        while stack:
            node, ready = stack.pop()
            if id(node) in memo:
                continue
            args = node.get("args", [])
            if not ready:
                stack.append((node, True))
                stack.extend((arg, False) for arg in reversed(args))
                continue
            data = dict(node)
            if "args" in data:
                data["args"] = [memo[id(arg)][1] for arg in args]
            memo[id(node)] = (node, TypedExpr.from_data(data))
        return memo[id(root)][1]

    def pack(value: Any) -> Any:
        if isinstance(value, dict) and "op" in value and "sort" in value:
            value = expression(value)
        if isinstance(value, TypedExpr):
            index = len(roots)
            roots.append(value)
            return {"$expr": index}
        if isinstance(value, dict):
            return {key: pack(item) for key, item in value.items()}
        if isinstance(value, (list, tuple)):
            return [pack(item) for item in value]
        return value

    packed = pack(payload)
    return json.dumps({"schema": SCHEMA, "expression_dag": typed_expr_roots_dag(tuple(roots)),
                       "payload": packed}, indent=indent, sort_keys=sort_keys, separators=(",", ":")) + "\n"

def loads(text: str) -> Any:
    document = json.loads(text)
    if not isinstance(document, dict) or set(document) != {"schema", "expression_dag", "payload"} or document["schema"] != SCHEMA:
        raise ValueError("expected AYXG artifact DAG")
    dag = document["expression_dag"]
    if not isinstance(dag, dict) or set(dag) != {"encoding", "nodes", "roots"} or dag["encoding"] != "typed-expr-roots-dag-v1":
        raise ValueError("expected typed expression roots DAG")
    if not isinstance(dag["nodes"], list) or not isinstance(dag["roots"], list):
        raise ValueError("DAG nodes and roots must be lists")
    nodes: list[TypedExpr] = []
    for index, record in enumerate(dag["nodes"]):
        if not isinstance(record, dict) or "args" not in record:
            raise ValueError("DAG node must contain args")
        refs = record["args"]
        if not isinstance(refs, list) or any(type(ref) is not int or not 0 <= ref < index for ref in refs):
            raise ValueError("expression arguments must reference earlier nodes")
        data = dict(record)
        if data.get("op") in {"var", "bool_lit", "bv_lit", "rm_lit"}:
            if refs:
                raise ValueError("leaf has arguments")
            del data["args"]
        else:
            data["args"] = [nodes[ref] for ref in refs]
        nodes.append(TypedExpr.from_data(data, f"nodes[{index}]"))
    if any(type(ref) is not int or not 0 <= ref < len(nodes) for ref in dag["roots"]):
        raise ValueError("DAG root index out of bounds")
    roots = [nodes[ref] for ref in dag["roots"]]

    def unpack(value: Any) -> Any:
        if isinstance(value, dict):
            if "$expr" in value:
                if set(value) != {"$expr"} or type(value["$expr"]) is not int or not 0 <= value["$expr"] < len(roots):
                    raise ValueError("invalid expression reference")
                return roots[value["$expr"]]
            return {key: unpack(item) for key, item in value.items()}
        if isinstance(value, list):
            return [unpack(item) for item in value]
        return value
    return unpack(document["payload"])
