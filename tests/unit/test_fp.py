"""FP contracts: every admitted family, five rounding modes, SMT special values."""
import unittest
import ctypes
import os
if location := os.environ.get("AYXG_LIBSTDCXX_RLOCATION"):
    from python.runfiles import runfiles
    library = runfiles.Create().Rlocation(location)
    if library is None: raise RuntimeError("declared Z3 C++ runtime missing")
    _LIBSTDCXX = ctypes.CDLL(library, mode=ctypes.RTLD_GLOBAL)
import z3
from ayxg.expr import BOOL, ArtifactError, TermSort, TypedExpr
from ayxg.fp import FPValue, RM, RoundingMode, fp_bits, rm_literal, UnderspecifiedFPError, FPInterpretation, UnderspecifiedFPKey
from ayxg.fp_z3 import FP_Z3_OPERATORS, evaluate_fp_node
from ayxg.z3 import expr_from_z3, expr_to_z3, sort_from_z3, sort_to_z3, typed_conversion_cache
from ayxg.substitution import substitute_expr
from ayxg.codec import dumps, loads
from ayxg.qfabv import QFAbvContext, QFAbvExpr, QFAbvValuation, FPSort, RoundingModeSort, BVSort, decode_sort
from ayxg.eval import eval_expr
from ayxg.expr import Declaration

class FloatingPointTests(unittest.TestCase):
    def test_sort_roundtrip(self):
        ctx = z3.Context()
        for sort in (TermSort.fp(8,24), TermSort.fp(11,53), TermSort.fp(15,64), RM):
            with self.subTest(sort=sort):
                self.assertEqual(TermSort.from_data(sort.to_data()), sort)
                self.assertEqual(sort_from_z3(sort_to_z3(sort,ctx)),sort)
                self.assertEqual(decode_sort(sort).encode(),sort)
        for e,s in ((1,24),(8,1),(True,24)):
            with self.assertRaises(ArtifactError): TermSort.fp(e,s)

    def test_all_families_roundtrip(self):
        c=z3.Context();f=z3.Float32(c);a=z3.FP("a",f);b=z3.FP("b",f);bv=z3.BitVec("bits",32,c)
        for mode in RoundingMode:
            r=expr_to_z3(rm_literal(mode),{},c)
            calls=[("fpAdd",(r,a,b)),("fpSub",(r,a,b)),("fpMul",(r,a,b)),("fpDiv",(r,a,b)),("fpFMA",(r,a,b,a)),("fpSqrt",(r,a)),("fpRoundToIntegral",(r,a)),("fpToSBV",(r,a,z3.BitVecSort(32,c))), ("fpToUBV",(r,a,z3.BitVecSort(32,c))), ("fpToFP",(r,a,z3.Float64(c))), ("fpSignedToFP",(r,bv,f)),("fpUnsignedToFP",(r,bv,f))]
            calls += [(n,(a,b)) for n in ("fpRem","fpMin","fpMax","fpEQ","fpLT","fpLEQ","fpGT","fpGEQ")]
            calls += [(n,(a,)) for n in ("fpAbs","fpNeg","fpIsNormal","fpIsSubnormal","fpIsZero","fpIsInf","fpIsNaN","fpIsNegative","fpIsPositive","fpToIEEEBV")]
            calls += [("fpBVToFP",(bv,f)),("fpFP",(z3.BitVec("sign",1,c),z3.BitVec("exp",8,c),z3.BitVec("frac",23,c)))]
            for name,args in calls:
                with self.subTest(mode=mode,op=name):
                    expr=getattr(z3,name)(*args,ctx=c)
                    typed=expr_from_z3(expr)
                    variables={str(v.decl().name()):v for v in (a,b,bv,*args) if z3.is_const(v) and v.decl().kind()==z3.Z3_OP_UNINTERPRETED}
                    for n,w in (("sign",1),("exp",8),("frac",23)): variables[n]=z3.BitVec(n,w,c)
                    self.assertTrue(z3.eq(expr,expr_to_z3(typed,variables,c)))
                    decoded=loads(dumps(typed.to_data()))
                    self.assertEqual(decoded,typed)

    def test_special_literals_and_smt_equality(self):
        c=z3.Context();sort=TermSort.fp(8,24)
        for bits in (0,0x80000000,1,0x7f800000,0xff800000,0x7fc12345,0x3f800000):
            expr=fp_bits(sort,bits);value=evaluate_fp_node(expr,(bits,))
            self.assertEqual(value,FPValue(sort,bits))
            leaf=expr_from_z3(z3.simplify(expr_to_z3(expr,{},c)))
            self.assertEqual(evaluate_fp_node(leaf,(leaf.args[0].value,)),value)
        p=FPValue(sort,0);n=FPValue(sort,0x80000000);nan=FPValue(sort,0x7fc00000)
        a=TypedExpr.var("a",sort);b=TypedExpr.var("b",sort)
        self.assertTrue(evaluate_fp_node(TypedExpr("fp_eq",BOOL,(a,b)),(p,n)))
        self.assertFalse(evaluate_fp_node(TypedExpr("fp_eq",BOOL,(a,b)),(nan,nan)))
        context=QFAbvContext((Declaration("a",sort),Declaration("b",sort)))
        self.assertFalse(eval_expr(QFAbvExpr(context,decode_sort(BOOL),TypedExpr.equal(a,b)),QFAbvValuation(context,(p,n))))
        self.assertTrue(eval_expr(QFAbvExpr(context,decode_sort(BOOL),TypedExpr.equal(a,b)),QFAbvValuation(context,(nan,nan))))

    def test_rounding_tie(self):
        f=TermSort.fp(8,24);a=TypedExpr.var("a",f);b=TypedExpr.var("b",f)
        results={}
        for mode in RoundingMode:
            op=TypedExpr("fp_add",f,(rm_literal(mode),a,b))
            results[mode]=evaluate_fp_node(op,(mode,FPValue(f,0x3f800000),FPValue(f,0x33800000))).bits
        self.assertEqual(results,{RoundingMode.RNE:0x3f800000,RoundingMode.RNA:0x3f800001,RoundingMode.RTP:0x3f800001,RoundingMode.RTN:0x3f800000,RoundingMode.RTZ:0x3f800000})

    def test_dag_substitution_and_valuation(self):
        f=TermSort.fp(8,24);a=TypedExpr.var("a",f);r=TypedExpr.var("r",RM)
        root=TypedExpr("fp_add",f,(r,a,a));sub=substitute_expr(root,{"a":fp_bits(f,0x3f800000)})
        self.assertIs(sub.args[1],sub.args[2])
        c=QFAbvContext((Declaration("a",f),Declaration("r",RM)))
        expression=QFAbvExpr(c,FPSort(8,24),root)
        self.assertEqual(eval_expr(expression,QFAbvValuation(c,(FPValue(f,0x3f800000),RoundingMode.RNE))).bits,0x40000000)
        with self.assertRaises(ValueError): QFAbvValuation(c,(1,RoundingMode.RNE))

    def test_signed_zero_minmax_not_silently_chosen(self):
        f=TermSort.fp(8,24);a=TypedExpr.var("a",f);b=TypedExpr.var("b",f)
        for op in ("fp_min","fp_max"):
            with self.assertRaises(UnderspecifiedFPError):
                evaluate_fp_node(TypedExpr(op,f,(a,b)),(FPValue(f,0),FPValue(f,0x80000000)))

    def test_invalid_cast_not_silently_chosen(self):
        f=TermSort.fp(8,24);a=TypedExpr.var("a",f);r=rm_literal(RoundingMode.RTZ)
        expr=TypedExpr("fp_to_sbv",TermSort.bv(8),(r,a))
        with self.assertRaises(UnderspecifiedFPError): evaluate_fp_node(expr,(RoundingMode.RTZ,FPValue(f,0x7fc00000)))


    def test_explicit_consistent_interpretations(self):
        f=TermSort.fp(8,24);a=TypedExpr.var("a",f);b=TypedExpr.var("b",f)
        p,n=FPValue(f,0),FPValue(f,0x80000000)
        node=TypedExpr("fp_min",f,(a,b));key=UnderspecifiedFPKey.from_node(node,(p,n))
        choices={key:n};interpretation=FPInterpretation(choices);choices[key]=p
        self.assertEqual(evaluate_fp_node(node,(p,n),interpretation),n)
        self.assertEqual(evaluate_fp_node(node,(p,n),interpretation),n)
        with self.assertRaises(UnderspecifiedFPError): evaluate_fp_node(node,(n,p),interpretation)
        bad=FPInterpretation({key:FPValue(f,1)})
        with self.assertRaises(ValueError): evaluate_fp_node(node,(p,n),bad)
        nan=FPValue(f,0x7fc00000);bits=TypedExpr("fp_to_ieee_bv",TermSort.bv(32),(a,))
        key=UnderspecifiedFPKey.from_node(bits,(nan,))
        self.assertEqual(evaluate_fp_node(bits,(nan,),FPInterpretation({key:0xffc12345})),0xffc12345)
        with self.assertRaises(ValueError): evaluate_fp_node(bits,(nan,),FPInterpretation({key:0}))
        cast=TypedExpr("fp_to_sbv",TermSort.bv(8),(rm_literal(RoundingMode.RNE),a))
        vals=(RoundingMode.RNE,nan);key=UnderspecifiedFPKey.from_node(cast,vals)
        self.assertEqual(evaluate_fp_node(cast,vals,FPInterpretation({key:42})),42)
        with self.assertRaises(ValueError): evaluate_fp_node(cast,vals,FPInterpretation({key:256}))

    def test_inactive_underspecified_branch_not_evaluated(self):
        f=TermSort.fp(8,24);bad=TypedExpr("fp_to_sbv",TermSort.bv(8),(rm_literal(RoundingMode.RTZ),fp_bits(f,0x7fc00000)))
        node=TypedExpr.ite(TypedExpr.bool_lit(True),TypedExpr.bv_lit(8,1),bad)
        c=QFAbvContext(())
        self.assertEqual(eval_expr(QFAbvExpr(c,BVSort(8),node),QFAbvValuation(c,())),1)
        pred=TypedExpr.equal(bad,TypedExpr.bv_lit(8,0))
        for op,first in (("bool_and",False),("bool_or",True)):
            expr=TypedExpr(op,BOOL,(TypedExpr.bool_lit(first),pred))
            self.assertEqual(eval_expr(QFAbvExpr(c,decode_sort(BOOL),expr),QFAbvValuation(c,())),first)

    def test_dag_preserves_mixed_fp_format(self):
        a=TypedExpr.var("same",TermSort.fp(8,24));b=TypedExpr.var("same",TermSort.fp(11,53))
        roots=loads(dumps([a.to_data(),b.to_data()]))
        self.assertEqual([root.sort for root in roots],[a.sort,b.sort])

if __name__ == "__main__": unittest.main()
