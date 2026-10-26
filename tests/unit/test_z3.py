"""Canonical converter contracts and SMT semantic round trips."""
import unittest
import ctypes
import os
if location := os.environ.get("AYXG_LIBSTDCXX_RLOCATION"):
    from python.runfiles import runfiles
    library = runfiles.Create().Rlocation(location)
    if library is None:
        raise RuntimeError("declared Z3 C++ runtime is missing")
    _LIBSTDCXX = ctypes.CDLL(library, mode=ctypes.RTLD_GLOBAL)
import z3
from ayxg.expr import ArtifactError, UnsupportedTheoryError, BOOL, TermSort, TypedExpr
from ayxg.z3 import (expr_from_z3, expr_to_z3, sort_from_z3, sort_to_z3,
                     declaration_variables, typed_conversion_cache)

class ConversionTests(unittest.TestCase):
    def test_operation_roundtrips(self):
        ctx = z3.Context()
        x, y = z3.BitVecs("x y", 8, ctx=ctx)
        b, c = z3.Bools("b c", ctx=ctx)
        a = z3.Array("a", z3.BitVecSort(8,ctx), z3.BitVecSort(8,ctx))
        terms = [b, z3.BoolVal(True,ctx), x, z3.BitVecVal(255,8,ctx),
                 z3.Not(b), z3.And(b,c), z3.Or(b,c), ~x,
                 x+y, x-y, x*y, z3.UDiv(x,y), x / y, z3.URem(x,y),
                 x&y, x|y, x^y, x<<y, z3.LShR(x,y), x>>y,
                 z3.ULT(x,y), z3.ULE(x,y), x<y, x<=y, z3.UGE(x,y),
                 x==y, z3.Distinct(x,y), z3.If(b,x,y),
                 z3.ZeroExt(8,x), z3.SignExt(8,x), z3.Extract(5,2,x),
                 z3.Concat(x,y,x), z3.K(z3.BitVecSort(8,ctx),x),
                 z3.Select(a,x), z3.Store(a,x,y), a==z3.Store(a,x,y), z3.Distinct(a,z3.Store(a,x,y))]
        variables = {"x":x,"y":y,"b":b,"c":c,"a":a}
        for term in terms:
            with self.subTest(op=term.decl().name()):
                typed = expr_from_z3(term)
                rebuilt = expr_to_z3(typed,variables,ctx)
                solver=z3.Solver(ctx=ctx); solver.add(term != rebuilt)
                self.assertEqual(solver.check(),z3.unsat)

    def test_signed_division_imports_and_exports_as_signed(self):
        ctx = z3.Context()
        x, y = z3.BitVecs("x y", 8, ctx=ctx)
        term = x / y
        typed = expr_from_z3(term)
        self.assertEqual(typed.op, "bv_sdiv")
        rebuilt = expr_to_z3(typed, {"x": x, "y": y}, ctx)
        solver = z3.Solver(ctx=ctx)
        solver.add(term != rebuilt)
        self.assertEqual(solver.check(), z3.unsat)

    def test_signed_greater_than_imports_as_reversed_signed_less_than(self):
        ctx = z3.Context()
        x, y = z3.BitVecs("x y", 8, ctx=ctx)
        term = x > y
        typed = expr_from_z3(term)
        self.assertEqual(typed.op, "bv_slt")
        self.assertEqual((typed.args[0].name, typed.args[1].name), ("y", "x"))
        rebuilt = expr_to_z3(typed, {"x": x, "y": y}, ctx)
        solver = z3.Solver(ctx=ctx)
        solver.add(term != rebuilt)
        self.assertEqual(solver.check(), z3.unsat)

        edge_cases = (
            (0x7F, 0x80, True),
            (0x80, 0x7F, False),
            (0xFF, 0x00, False),
            (0x00, 0xFF, True),
            (0x80, 0x80, False),
        )
        for left, right, expected in edge_cases:
            with self.subTest(left=left, right=right):
                evaluated = z3.simplify(z3.substitute(
                    rebuilt,
                    (x, z3.BitVecVal(left, 8, ctx=ctx)),
                    (y, z3.BitVecVal(right, 8, ctx=ctx)),
                ))
                self.assertEqual(z3.is_true(evaluated), expected)

    def test_signed_division_evaluator_matches_z3(self):
        from ayxg import BVSort, Declaration, QFAbvContext, QFAbvExpr, QFAbvValuation, eval_expr

        ctx = z3.Context()
        for width in (1, 2, 3, 4, 8, 16, 32, 64, 128):
            x, y = z3.BitVecs("x y", width, ctx=ctx)
            reference = x / y
            typed = TypedExpr.from_data(expr_from_z3(reference).to_data())
            context = QFAbvContext(tuple(
                Declaration(name, TermSort.bv(width)) for name in ("x", "y")
            ))
            expression = QFAbvExpr(context, BVSort(width), typed)
            sign, mask = 1 << (width - 1), (1 << width) - 1
            # Exhaust all small widths; larger widths include zero, both signs,
            # truncating quotients, signed overflow, and values beyond float precision.
            values = range(1 << width) if width <= 4 else sorted({
                0, 1, 2, 3, 7, sign - 1, sign, sign + 1,
                mask - 6, mask - 2, mask - 1, mask,
            })
            for left in values:
                for right in values:
                    with self.subTest(width=width, left=left, right=right):
                        expected = z3.simplify(z3.substitute(reference,
                            (x, z3.BitVecVal(left, width, ctx=ctx)),
                            (y, z3.BitVecVal(right, width, ctx=ctx)))).as_long()
                        actual = eval_expr(expression, QFAbvValuation(context, (left, right)))
                        self.assertEqual(actual, expected)

    def test_array_equality_ground_witness(self):
        sort = z3.BitVecSort(4)
        left = z3.K(sort, z3.BitVecVal(0, 1))
        right = z3.K(sort, z3.BitVecVal(1, 1))
        for i in [2, 3, 4, 5, 6, 10, 11]:
            left = z3.Store(left, z3.BitVecVal(i, 4), z3.BitVecVal(1, 1))
        for i in [0, 1, 7, 9, 12, 13, 14, 15]:
            right = z3.Store(right, z3.BitVecVal(i, 4), z3.BitVecVal(0, 1))
        self.assertEqual(z3.simplify(z3.Select(left, z3.BitVecVal(8, 4))).as_long(), 0)
        self.assertEqual(z3.simplify(z3.Select(right, z3.BitVecVal(8, 4))).as_long(), 1)
        solver = z3.Solver(); solver.add(left == right)
        self.assertEqual(solver.check(), z3.unsat, z3.get_version_string())

    def test_sorts_and_declarations(self):
        from ayxg.expr import Declaration
        ctx=z3.Context()
        declarations=tuple(Declaration(n,s) for n,s in [
            ("b",BOOL),("v",TermSort.bv(8)),("a",TermSort.array(8,16))])
        variables=declaration_variables(declarations,ctx)
        for d in declarations:
            self.assertEqual(sort_from_z3(sort_to_z3(d.sort,ctx)), d.sort)
            self.assertEqual(sort_from_z3(variables[d.name].sort()),d.sort)

    def test_rejections(self):
        ctx=z3.Context()
        with self.assertRaises(UnsupportedTheoryError): expr_from_z3(z3.Int("i",ctx))
        x=z3.BitVec("x",8,ctx)
        with self.assertRaises(UnsupportedTheoryError): expr_from_z3(-x)
        with self.assertRaises(ArtifactError): expr_to_z3(TypedExpr.var("x",TermSort.bv(16)),{"x":x},ctx)
        with self.assertRaises(ArtifactError): expr_to_z3(TypedExpr.var("missing",TermSort.bv(8)),{},ctx)

    def test_cache_scopes_and_contexts(self):
        ctx=z3.Context(); x=z3.BitVec("x",8,ctx)
        with typed_conversion_cache():
            first=expr_from_z3(x)
            with typed_conversion_cache(): self.assertIs(expr_from_z3(x),first)
            other=z3.Context(); y=z3.BitVec("y",8,other)
            self.assertEqual(expr_from_z3(y).name,"y")
            expr=expr_from_z3(x+x)
            self.assertIs(expr.args[0],expr.args[1])
        self.assertIsNot(expr_from_z3(x),first)
        with self.assertRaises(RuntimeError):
            with typed_conversion_cache(): raise RuntimeError("probe")
        with typed_conversion_cache(): self.assertEqual(expr_from_z3(x).name,"x")

    def test_deep_forward_dag(self):
        ctx=z3.Context(); x=z3.BitVec("x",8,ctx)
        node=TypedExpr.var("x",TermSort.bv(8))
        for _ in range(2000): node=TypedExpr.binary("bv_add",node,node)
        memo={}; result=expr_to_z3(node,{"x":x},ctx,memo=memo)
        self.assertEqual(len(memo),2001)
        self.assertEqual(result.size(),8)
        self.assertIs(expr_to_z3(node,{"x":x},ctx,memo=memo),result)

if __name__ == "__main__": unittest.main()
