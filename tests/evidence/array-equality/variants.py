import z3
S=z3.BitVecSort(4);V=lambda i:z3.BitVecVal(i,1);I=lambda i:z3.BitVecVal(i,4)
a=z3.K(S,V(0));b=z3.Store(z3.Store(z3.K(S,V(1)),I(14),V(0)),I(15),V(0))
for settings in [{},{'auto_config':False},{'smt.array.extensional':True},{'smt.array.weak':False},{'smt.bv.solver':2}]:
 q=z3.Solver();q.set(timeout=10000,**settings);q.add(a==b)
 try:print(settings,q.check(),q.reason_unknown())
 except z3.Z3Exception as e:print(settings,str(e)[:120])
print('expanded minimal',z3.simplify(a==b,expand_store_eq=True))
s=z3.BitVecSort(2);a=z3.K(s,V(0));b=z3.K(s,V(1))
for i in [0,1]:a=z3.Store(a,z3.BitVecVal(i,2),V(1))
for i in [2,3]:b=z3.Store(b,z3.BitVecVal(i,2),V(0))
print('equal complementary full coverage:',[z3.simplify(z3.Select(a,z3.BitVecVal(i,2))==z3.Select(b,z3.BitVecVal(i,2))) for i in range(4)])
print('expanded full coverage',z3.simplify(a==b,expand_store_eq=True))
q=z3.Solver();q.add(a==b);print('default full coverage',q.check())
