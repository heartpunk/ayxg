"""Capture-avoiding simultaneous substitution over the canonical expression DAG."""
from __future__ import annotations
from collections.abc import Mapping, Sequence
from dataclasses import replace
from .expr import ArtifactError, Declaration, TypedExpr, free_references


def _rewrite(expressions: Sequence[TypedExpr], replacements: Mapping[str, TypedExpr],
             positional: Sequence[TypedExpr] | None, shift: int = 0) -> tuple[TypedExpr, ...]:
    captures = {ref for ref in free_references((*replacements.values(), *(positional or ()))) if isinstance(ref, str)}
    used = set(captures)
    todo = list(expressions)
    seen: set[int] = set()
    while todo:
        node = todo.pop()
        if id(node) in seen:
            continue
        seen.add(id(node))
        if node.name is not None:
            used.add(node.name)
        used.update(d.name for d in node.bindings or ())
        todo.extend(node.args)
    memo: dict[tuple[int, tuple[Declaration, ...]], TypedExpr] = {}
    renamed: dict[tuple[int, tuple[Declaration, ...]], tuple[Declaration, ...]] = {}
    inserted: dict[tuple[int, int], TypedExpr] = {}
    for root in expressions:
        stack = [(root, (), False)]
        while stack:
            node, scope, ready = stack.pop()
            key = (id(node), scope)
            if key in memo:
                continue
            if node.op == 'var':
                result = node
                replacement = None
                if node.index is not None:
                    if node.index >= len(scope):
                        if positional is not None:
                            index = node.index - len(scope)
                            if index >= len(positional):
                                raise ArtifactError('substitution position outside context')
                            replacement = positional[index]
                        elif shift:
                            result = TypedExpr.at(node.index + shift, node.sort)
                else:
                    bound = next((i for i, d in enumerate(scope) if d.name == node.name), None)
                    if bound is not None:
                        # Positional reference remains exact even when a binder is renamed.
                        result = TypedExpr.at(bound, node.sort)
                    else:
                        replacement = replacements.get(node.name)
                if replacement is not None:
                    if replacement.sort != node.sort:
                        raise ArtifactError('replacement has wrong sort')
                    ik = (id(replacement), len(scope))
                    if ik not in inserted:
                        inserted[ik] = (_rewrite((replacement,), {}, None, len(scope))[0]
                                        if scope else replacement)
                    result = inserted[ik]
                memo[key] = result
                continue
            if node.op == 'let_par':
                assert node.bindings is not None
                child_scopes = [scope] * len(node.bindings) + [node.bindings + scope]
                if key not in renamed:
                    decls = []
                    for declaration in node.bindings:
                        name = declaration.name
                        if name in captures:
                            index = 0
                            while f'ayxg_binding_{index}' in used:
                                index += 1
                            name = f'ayxg_binding_{index}'
                            used.add(name)
                        decls.append(Declaration(name, declaration.sort))
                    renamed[key] = tuple(decls)
            else:
                child_scopes = [scope] * len(node.args)
            if ready:
                args = tuple(memo[(id(arg), child_scope)] for arg, child_scope in zip(node.args, child_scopes, strict=True))
                bindings = renamed.get(key, node.bindings)
                memo[key] = (node if bindings == node.bindings and all(a is b for a, b in zip(args, node.args, strict=True))
                             else replace(node, args=args, bindings=bindings))
            else:
                stack.append((node, scope, True))
                stack.extend((arg, child_scope, False) for arg, child_scope in reversed(tuple(zip(node.args, child_scopes, strict=True)))
                             if (id(arg), child_scope) not in memo)
    return tuple(memo[(id(root), ())] for root in expressions)


def substitute_exprs(expressions: Sequence[TypedExpr], replacements: Mapping[str, TypedExpr], *,
                     positional: Sequence[TypedExpr] | None = None) -> tuple[TypedExpr, ...]:
    """Substitute free names/positions simultaneously; preserve local binders."""
    if not replacements and positional is None:
        return tuple(expressions)
    return _rewrite(expressions, replacements, positional)


def substitute_expr(expression: TypedExpr, replacements: Mapping[str, TypedExpr]) -> TypedExpr:
    return substitute_exprs((expression,), replacements)[0]
