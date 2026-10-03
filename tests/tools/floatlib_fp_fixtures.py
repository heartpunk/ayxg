"""Emit Lean/FloatLib comparisons against the active pinned Z3 interpreter.
No machine FP arithmetic. Includes exceptional values, subnormal boundaries,
random bit patterns and a known RNA/RNE halfway difference.
"""
import argparse
import random
from pathlib import Path
import z3

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args(); rng=random.Random(20261002)
    out=['import FloatLib.Floats.Formats.BinaryInterchange.SMT.Proof', 'set_option maxRecDepth 4096',
         'open FloatLib.Floats.Formats.BinaryInterchange',
         'def check {f : FloatFormat} (name : String) (actual : Model f) (expected : Nat) (nan : Bool) : IO Unit := do',
         '  let good := if nan then actual.isNaN else actual.toNatBits == expected',
         '  unless good do throw <| IO.userError s!"{name}: got {actual.toNatBits}, expected {expected}, NaN={nan}"',
         'def checkInt {f : FloatFormat} (name : String) (mode : Model.SMT.RoundingMode) (x : Model f) (expected : Int) : IO Unit := do',
         '  let some dx := Model.toDyadic? x | throw <| IO.userError "integer fixture requires finite input"',
         '  let actual := Model.SMT.roundToInt mode dx',
         '  unless actual == expected do throw <| IO.userError s!"{name}: integer got {actual}, expected {expected}"',
         'def batch0 : IO Unit := do']
    count=0
    for eb,sb in [(3,4),(8,24)]:
        width=eb+sb;frac=sb-1;sign=1<<(width-1);inf=((1<<eb)-1)<<frac
        patterns=[0,sign,1,sign|1,(1<<frac)-1,1<<frac,inf-1,sign|inf-1,inf,sign|inf,inf|1]
        patterns += [rng.randrange(1<<width) for _ in range(5)]
        pairs=list(zip(patterns,patterns[3:]+patterns[:3]))
        if eb==8: pairs += [(0x3f800000,0x33800000),(0xbf800000,0xb3800000)]
        sort=z3.FPSort(eb,sb)
        def val(bits): return z3.fpBVToFP(z3.BitVecVal(bits,width),sort)
        def lean(bits): return f'(Model.ofNatBits (fmt := FloatFormat.ieee {eb} {frac}) {bits})'
        for name,rm in [('rne',z3.RNE()),('rna',z3.RNA()),('rtp',z3.RTP()),('rtn',z3.RTN()),('rtz',z3.RTZ())]:
            for i,(a,b) in enumerate(pairs):
                c=patterns[(i+7)%len(patterns)]
                for opname,expr,code in [
                    ('add',z3.fpAdd(rm,val(a),val(b)),f'Model.SMT.add .{name} {lean(a)} {lean(b)}'),
                    ('mul',z3.fpMul(rm,val(a),val(b)),f'Model.SMT.mul .{name} {lean(a)} {lean(b)}'),
                    ('div',z3.fpDiv(rm,val(a),val(b)),f'Model.SMT.div .{name} {lean(a)} {lean(b)}'),
                    ('fma',z3.fpFMA(rm,val(a),val(b),val(c)),f'Model.SMT.fma .{name} {lean(a)} {lean(b)} {lean(c)}'),
                    ('sqrt',z3.fpSqrt(rm,val(a)),f'Model.SMT.sqrt (by rfl) .{name} {lean(a)}'),
                    ('integral',z3.fpRoundToIntegral(rm,val(a)),f'Model.SMT.roundToIntegral .{name} {lean(a)}')]:
                    nan=z3.is_true(z3.simplify(z3.fpIsNaN(expr)))
                    bits=0 if nan else z3.simplify(z3.fpToIEEEBV(expr)).as_long()
                    label=f'{eb}/{sb}:{opname}:{name}:{a}:{b}'
                    if count and count % 40 == 0:
                        out.append(f'def batch{count // 40} : IO Unit := do')
                    out.append(f'  check "{label}" ({code}) {bits} {str(nan).lower()}');count+=1
            def append_check(label,expr,code):
                nonlocal count
                nan=z3.is_true(z3.simplify(z3.fpIsNaN(expr)))
                bits=0 if nan else z3.simplify(z3.fpToIEEEBV(expr)).as_long()
                if count and count % 40 == 0:out.append(f'def batch{count // 40} : IO Unit := do')
                out.append(f'  check "{label}" ({code}) {bits} {str(nan).lower()}');count+=1
            dst_eb,dst_sb=(8,24) if eb==3 else (3,4)
            for a in patterns:
                append_check(f'{eb}/{sb}:cast:{name}:{a}',z3.fpToFP(rm,val(a),z3.FPSort(dst_eb,dst_sb)),f'Model.SMT.cast (FloatFormat.ieee {eb} {frac}) (FloatFormat.ieee {dst_eb} {dst_sb-1}) .{name} {lean(a)}')
                integer=z3.simplify(z3.fpToSBV(rm,val(a),z3.BitVecSort(64)))
                if z3.is_bv_value(integer):
                    n=integer.as_long();n=n-(1<<64) if n>=(1<<63) else n
                    if count and count % 40==0:out.append(f'def batch{count // 40} : IO Unit := do')
                    out.append(f'  checkInt "{eb}/{sb}:roundInt:{name}:{a}" .{name} {lean(a)} ({n})');count+=1
            if eb==8:
                for a,b,c in [(0x3f800001,0x3f7ffffe,0xbf800000),(0x7f7fffff,0x40000000,0xff7fffff),(0x00800000,0x00800000,1)]:
                    append_check(f'FMA-targeted:{name}:{a}:{b}:{c}',z3.fpFMA(rm,val(a),val(b),val(c)),f'Model.SMT.fma .{name} {lean(a)} {lean(b)} {lean(c)}')
    out.append('def main : IO Unit := do')
    out.extend(f'  batch{n}' for n in range((count + 39) // 40))
    out.append(f'  IO.println "PASS {count} FloatLib/Z3 FP fixtures; Z3 {z3.get_version_string()}"')
    args.out.write_text('\n'.join(out)+'\n')
    print(f'generated {count} fixtures; reference Z3 {z3.get_version_string()}')

if __name__=='__main__':main()
