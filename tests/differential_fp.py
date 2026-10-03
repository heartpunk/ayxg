"""Actual Lean/Python FP correspondence, every non-Real admitted family.
Fixture interpretation is explicit: canonical NaN bits, invalid BV casts zero,
opposite-zero min/max left sign. Defined results use SMT-LIB semantics.
"""
from __future__ import annotations
import argparse
from collections import Counter
import json
from pathlib import Path
from hypothesis import given, settings, strategies as st
from ayxg.expr import BOOL, TermSort, TypedExpr
from ayxg.fp import FPValue, FPInterpretation, UnderspecifiedFPKey, UnderspecifiedFPError, RoundingMode, fp_bits, rm_literal
from ayxg.eval import eval_expr
from ayxg.qfabv import QFAbvContext, QFAbvExpr, QFAbvValuation, decode_sort
from differential_expr import LeanOracle

OPS=('rm_lit','bv_to_fp','fp_construct','fp_abs','fp_neg','fp_add','fp_sub','fp_mul','fp_div','fp_fma','fp_sqrt','fp_rem','fp_round_to_integral','fp_min','fp_max','fp_eq','fp_lt','fp_le','fp_gt','fp_ge','fp_is_normal','fp_is_subnormal','fp_is_zero','fp_is_infinite','fp_is_nan','fp_is_negative','fp_is_positive','fp_to_ieee_bv','fp_to_sbv','fp_to_ubv','sbv_to_fp','ubv_to_fp','fp_to_fp','eq')

def expression(op,eb,sb,a,b,c,mode):
    f=TermSort.fp(eb,sb);x,y,z=(fp_bits(f,n) for n in (a,b,c));r=rm_literal(mode)
    if op=='rm_lit':return r
    if op=='bv_to_fp':return x
    if op=='fp_construct':return TypedExpr(op,f,(TypedExpr.bv_lit(1,a>>(eb+sb-1)),TypedExpr.bv_lit(eb,(a>>(sb-1))&((1<<eb)-1)),TypedExpr.bv_lit(sb-1,a&((1<<(sb-1))-1))))
    if op in {'fp_abs','fp_neg'}:return TypedExpr(op,f,(x,))
    if op in {'fp_add','fp_sub','fp_mul','fp_div'}:return TypedExpr(op,f,(r,x,y))
    if op=='fp_fma':return TypedExpr(op,f,(r,x,y,z))
    if op in {'fp_sqrt','fp_round_to_integral'}:return TypedExpr(op,f,(r,x))
    if op in {'fp_rem','fp_min','fp_max'}:return TypedExpr(op,f,(x,y))
    if op in {'fp_eq','fp_lt','fp_le','fp_gt','fp_ge'}:return TypedExpr(op,BOOL,(x,y))
    if op.startswith('fp_is_'):return TypedExpr(op,BOOL,(x,))
    if op=='fp_to_ieee_bv':return TypedExpr(op,TermSort.bv(eb+sb),(x,))
    if op in {'fp_to_sbv','fp_to_ubv'}:return TypedExpr(op,TermSort.bv(8),(r,x))
    if op in {'sbv_to_fp','ubv_to_fp'}:return TypedExpr(op,f,(r,TypedExpr.bv_lit(8,a&255)))
    if op=='fp_to_fp':return TypedExpr(op,TermSort.fp(8,24) if eb in {3,11} else TermSort.fp(11,53),(r,x))
    if op=='eq':return TypedExpr.equal(x,y)
    raise ValueError(op)

def main():
    p=argparse.ArgumentParser();p.add_argument('--bridge-project',type=Path,required=True);p.add_argument('--artifacts',type=Path,default=Path('.differential-fp'));p.add_argument('--examples',type=int,default=20);args=p.parse_args();args.artifacts.mkdir(parents=True,exist_ok=True)
    oracle=LeanOracle(args.bridge_project,args.artifacts);counts=Counter();format_counts=Counter();corners=0;ctx=QFAbvContext(());state=QFAbvValuation(ctx,())
    def evaluate(node):return eval_expr(QFAbvExpr(ctx,decode_sort(node.sort),node),state)
    def check(node):
        try:value=evaluate(node)
        except UnderspecifiedFPError:
            vals=tuple(evaluate(x) for x in node.args)
            choice=vals[0] if node.op in {'fp_min','fp_max'} else vals[0].bits if node.op=='fp_to_ieee_bv' else 0
            interpretation=FPInterpretation({UnderspecifiedFPKey.from_node(node,vals):choice})
            value=eval_expr(QFAbvExpr(ctx,decode_sort(node.sort),node),state,interpretation)
        expected={'kind':node.sort.kind,'value':value.bits if isinstance(value,FPValue) else value.value if isinstance(value,RoundingMode) else value}
        request={'declarations':[],'values':[],'expression':node.to_data()};actual=oracle.evaluate(request)
        if actual!=expected:
            evidence={'request':request,'python':expected,'lean':actual};(args.artifacts/'counterexample.json').write_text(json.dumps(evidence,indent=2));raise AssertionError(evidence)
        counts[node.op]+=1
        format_counts[f"{eb}/{sb}:{node.op}"]+=1
    try:
        for eb,sb in [(3,4),(8,24),(11,53)]:
            sign=1<<(eb+sb-1);inf=((1<<eb)-1)<<(sb-1)
            samples=[0,sign,1,sign|1,(1<<(sb-1))-1,1<<(sb-1),inf-1,sign|(inf-1),inf,sign|inf,inf|1]
            if eb==11:samples += [0x3ff0000000000000,0x3ca0000000000000,0xbff0000000000000,0xbca0000000000000,0x3ff0000000000001]
            if eb==8:samples+=[0x3f800000,0x33800000,0xbf800000,0xb3800000,0x3f800001]
            # Guarantee the carrier equality / IEEE comparison distinction and
            # opposite-zero interpretation cases; random inputs cannot promise these.
            for op,a,b in [('eq',inf|1,inf|1),('fp_eq',inf|1,inf|1),
                           ('eq',0,sign),('fp_eq',0,sign),
                           ('fp_min',0,sign),('fp_min',sign,0),
                           ('fp_max',0,sign),('fp_max',sign,0)]:
                check(expression(op,eb,sb,a,b,0,RoundingMode.RNE));corners+=1
            bias=(1<<(eb-1))-1;one=bias<<(sb-1)
            half=(bias-sb)<<(sb-1) if bias-sb>0 else 1<<(bias-2)
            for mode in RoundingMode:
                for a,b in [(one,half),(sign|one,sign|half)]:
                    check(expression('fp_add',eb,sb,a,b,0,mode));corners+=1
                check(expression('fp_fma',eb,sb,one+1,one-2,sign|one,mode));corners+=1
            for op in OPS:
                for mode in RoundingMode:
                    for i,a in enumerate(samples):check(expression(op,eb,sb,a,samples[(i+3)%len(samples)],samples[(i+7)%len(samples)],mode))
                @settings(max_examples=args.examples,deadline=None,derandomize=True,database=None)
                @given(st.integers(0,(1<<(eb+sb))-1),st.integers(0,(1<<(eb+sb))-1),st.integers(0,(1<<(eb+sb))-1),st.sampled_from(list(RoundingMode)))
                def prop(a,b,c,mode):check(expression(op,eb,sb,a,b,c,mode))
                prop()
        report={'counts':dict(counts),'total':sum(counts.values()),'interpretation':'NaN canonical bits; invalid casts=0; oppositezero tie=left sign',
                'counts_by_format':dict(format_counts),'explicit_corner_comparisons':corners,
                'rounding_modes':[mode.value for mode in RoundingMode]};(args.artifacts/'coverage.json').write_text(json.dumps(report,indent=2));print(json.dumps(report))
    finally:oracle.close()

if __name__=='__main__':main()
