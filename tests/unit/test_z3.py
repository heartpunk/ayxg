"""Canonical converter contracts and SMT semantic round trips."""
import unittest
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
                 x+y, x-y, x*y, z3.UDiv(x,y), z3.URem(x,y),
                 x&y, x|y, x^y, x<<y, z3.LShR(x,y), x>>y,
                 z3.ULT(x,y), z3.ULE(x,y), x<y, x<=y, z3.UGE(x,y),
                 x==y, z3.Distinct(x,y), z3.If(b,x,y),
                 z3.ZeroExt(8,x), z3.SignExt(8,x), z3.Extract(5,2,x),
                 z3.Concat(x,y,x), z3.K(z3.BitVecSort(8,ctx),x),
                 z3.Select(a,x), z3.Store(a,x,y)]
        variables = {"x":x,"y":y,"b":b,"c":c,"a":a}
        for term in terms:
            with self.subTest(op=term.decl().name()):
                typed = expr_from_z3(term)
                rebuilt = expr_to_z3(typed,variables,ctx)
                solver=z3.Solver(ctx=ctx); solver.add(term != rebuilt)
                self.assertEqual(solver.check(),z3.unsat)

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
