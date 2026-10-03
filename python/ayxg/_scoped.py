"""Iterative expression interpretation with lexical scopes and shared DAGs."""
from __future__ import annotations
from collections.abc import Callable, Sequence
from typing import TypeVar
from .expr import ArtifactError, TypedExpr

V = TypeVar('V')

def interpret(roots: Sequence[TypedExpr], environment: Sequence[tuple[str, V]],
              apply: Callable[[TypedExpr, tuple[V, ...]], V], *,
              branch: Callable[[V], bool] | None = None,
              root_memo: dict[object, tuple[TypedExpr, V]] | None = None,
              cache_scope: object = None) -> tuple[V, ...]:
    scopes = [tuple(environment)]
    root_nodes: dict[int, TypedExpr] = {}
    extensions: dict[tuple[int, int], int] = {}
    memo: dict[tuple[int, int], V] = {}
    for root in roots:
        stack = [(root, 0, False)]
        while stack:
            node, scope, ready = stack.pop()
            key = (id(node), scope)
            if scope == 0:
                root_nodes[id(node)] = node
            if key in memo:
                continue
            if scope == 0 and root_memo is not None and (cache_scope, id(node)) in root_memo and root_memo[(cache_scope, id(node))][0] is node:
                memo[key] = root_memo[(cache_scope, id(node))][1]
                continue
            if node.op == 'var':
                env = scopes[scope]
                if node.index is not None:
                    if node.index >= len(env):
                        raise ArtifactError('variable position outside context')
                    memo[key] = env[node.index][1]
                else:
                    found = next((i for i, (name, _) in enumerate(env) if name == node.name), None)
                    if found is None:
                        raise ArtifactError(f'undeclared variable {node.name!r}')
                    memo[key] = env[found][1]
                continue
            if node.op == 'let_par':
                assert node.bindings is not None
                if not ready:
                    stack.append((node, scope, True))
                    stack.extend((rhs, scope, False) for rhs in reversed(node.args[:-1])
                                 if (id(rhs), scope) not in memo)
                    continue
                if key not in extensions:
                    extensions[key] = len(scopes)
                    scopes.append(tuple((d.name, memo[(id(rhs), scope)]) for d, rhs in
                                        zip(node.bindings, node.args[:-1], strict=True)) + scopes[scope])
                body_scope = extensions[key]
                body_key = (id(node.args[-1]), body_scope)
                if body_key not in memo:
                    stack.extend(((node, scope, True), (node.args[-1], body_scope, False)))
                    continue
                memo[key] = memo[body_key]
                continue
            if branch is not None and node.op in {'ite', 'bool_and', 'bool_or'}:
                condition = node.args[0]
                ck = (id(condition), scope)
                if ck not in memo:
                    stack.extend(((node, scope, False), (condition, scope, False)))
                    continue
                test = branch(memo[ck])
                if (node.op == 'bool_and' and not test) or (node.op == 'bool_or' and test):
                    memo[key] = memo[ck]
                    continue
                chosen = node.args[1 if test or node.op != 'ite' else 2]
                chosen_key = (id(chosen), scope)
                if chosen_key not in memo:
                    stack.extend(((node, scope, False), (chosen, scope, False)))
                    continue
                memo[key] = memo[chosen_key]
                continue
            if ready:
                memo[key] = apply(node, tuple(memo[(id(arg), scope)] for arg in node.args))
            else:
                stack.append((node, scope, True))
                stack.extend((arg, scope, False) for arg in reversed(node.args)
                             if (id(arg), scope) not in memo)
    if root_memo is not None:
        root_memo.update(((cache_scope, identity), (node, memo[(identity, 0)])) for identity, node in root_nodes.items())
    return tuple(memo[(id(root), 0)] for root in roots)
