#!/usr/bin/env python3
"""Propose the finite weight-eight data on Gamma0(6). Lean checks every identity by decide +kernel.
Usage: python3 scripts/theorem_a/gen_weight_eight.py RamanujanTau/TheoremA"""
import sys,re
from pathlib import Path
from fractions import Fraction as Fr
D=24
def mul(a,b):
    o=[0]*(D+1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b[:D+1-i]):o[i+j]+=x*y
    return o
def euler(d):
    o=[0]*(D+1);o[0]=1
    for n in range(1,D//d+1):
        new=o[:]
        for i in range(n*d,D+1):new[i]-=o[i-n*d]
        o=new
    return o
def pw(a,e):
    r=[1]+[0]*D
    for _ in range(e):r=mul(r,a)
    return r
def inv(a):
    o=[0]*(D+1);o[0]=1
    for n in range(1,D+1):o[n]=-sum(a[i]*o[n-i] for i in range(1,n+1))
    return o
num=[(2,12,3,2),(2,4,6,4),(1,2,6,12)];den=[(1,6,6,4),(1,2,3,2),(2,4,3,6)]
W=[]
for a in range(3):
    d,k,e,r=num[a];N=mul(pw(euler(d),k),pw(euler(e),r))
    d,k,e,r=den[a];Dn=mul(pw(euler(d),k),pw(euler(e),r))
    s=mul(N,inv(Dn));W.append(([0]*a+s)[:D+1])
known0=[1,6,15,24,33,36,33,48,69,78,90,72,51,84,120,144,141,108,87]
assert W[0][:19]==known0
n=4;dim=9
def basis(i):
    a=n-i//2-i%2;b=i%2;c=i//2
    return mul(mul(pw(W[0],a),pw(W[1],b)),pw(W[2],c))
B=[basis(i) for i in range(dim)]
def solve(v):
    # triangular: B[i] = q^i + ...
    v=v[:];c=[0]*dim
    for t in range(dim):
        c[t]=v[t]
        v=[x-c[t]*y for x,y in zip(v,B[t])]
    return c,v
def Umat(d):
    M=[[0]*dim for _ in range(dim)]
    for i in range(dim):
        u=[B[i][d*j] if d*j<=D else None for j in range(D//d+1)]
        v=u[:dim];c=[0]*dim
        for t in range(dim):
            c[t]=v[t];v=[x-c[t]*y for x,y in zip(v,B[t][:dim])]
        for t in range(dim):M[t][i]=c[t]
        for j in range(D//d+1):
            assert u[j]==sum(M[t][i]*B[t][j] for t in range(dim)),(d,i,j)
    return M
def matmul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(dim)) for j in range(dim)] for i in range(dim)]
def add(a,c):return [[a[i][j]+(c if i==j else 0) for j in range(dim)] for i in range(dim)]
A=Umat(2);Bm=Umat(3)
P=matmul(matmul(matmul(add(A,-1),add(A,-128)),add(A,8)),add(Bm,27))
# P should have rank one: P = h v^T
idx=next((i,j) for i in range(dim) for j in range(dim) if P[i][j])
piv=P[idx[0]][idx[1]]
from math import gcd
from functools import reduce
col=[P[i][idx[1]] for i in range(dim)];g=reduce(gcd,[abs(x) for x in col]);h=[x//g for x in col]
# normalize so the q^1 coefficient of the combination is 1
series=[sum(h[t]*B[t][j] for t in range(dim)) for j in range(D+1)]
assert series[0]==0
s=series[1]
assert all(x%abs(s)==0 for x in h) ,(h,s)
h=[x//s for x in h]
series=[sum(h[t]*B[t][j] for t in range(dim)) for j in range(D+1)]
print('h',h,'series',series[:8],file=sys.stderr)
v=[]
ref=next(i for i in range(dim) if h[i])
v=[Fr(P[ref][j],h[ref]) for j in range(dim)]
assert all(x.denominator==1 for x in v);v=[int(x) for x in v]
assert all(P[i][j]==h[i]*v[j] for i in range(dim) for j in range(dim))
print('v',v,'P(8,27)',(8-1)*(8-128)*(8+8)*(27+27),file=sys.stderr)
out=Path(sys.argv[1])
def mat(M):return '!!['+';\n    '.join(', '.join(str(x) for x in r) for r in M)+']'
root=Path(sys.argv[1])
src=(root/'ModularWeightSixData.lean').read_text()
# weight-two lists through q^24
def ren(t):
    t=t.replace('# Finite data for U₂ and U₃ on the full weight-six space','# Finite data for U₂ and U₃ on the full weight-eight space')
    t=t.replace('certified through q¹⁸','certified through q²⁴').replace('seven basis expansions','nine basis expansions')
    t=t.replace('Fin 7','Fin 9').replace('< 19','< 25').replace('π 19','π 25').replace('18','24')
    t=t.replace('evenSeries 3','evenSeries 4').replace('evenSeries_normalForm 3','evenSeries_normalForm 4').replace('normalExponentA 3','normalExponentA 4').replace('modularWeightSix','modularWeightEight')
    t=t.replace('evenForm 3','evenForm 4').replace('evenCombination 3','evenCombination 4').replace('evenFormCombination 3','evenFormCombination 4')
    t=t.replace('evenCombinationLinear (R := R) 3','evenCombinationLinear (R := R) 4').replace('modularExpansionLinear 6','modularExpansionLinear 8').replace('firstCoefficients_injective 6','firstCoefficients_injective 8').replace('ModularWeightSixData','ModularWeightEightData').replace('weight-six','weight-eight')
    return t
# cut the literal data out of the template first, rename, then insert data
t=src
a=t.index('def weightTwoCoefficients18');b=t.index('theorem weightTwo_list_certificate18')
t=t[:a]+'@@LISTS@@\n'+t[b:]
a=t.index('def modularWeightSixU2 :');b=t.index('theorem modularWeightSixU2_certificate')
t=t[:a]+'@@U2@@\n'+t[b:]
a=t.index('def modularWeightSixU3 :');b=t.index('theorem modularWeightSixU3_certificate')
t=t[:a]+'@@U3@@\n'+t[b:]
a=t.index('theorem modularWeightSix_matrix_identity');b=t.index('end RamanujanTau.TheoremA')
t=t[:a]+'@@ID@@\n'+t[b:]
t=ren(t)
t=t.replace('set_option autoImplicit false','set_option autoImplicit false\nset_option maxRecDepth 100000')
t=t.replace('@@LISTS@@',f'def weightTwoCoefficients24 (a : Fin 3) : List ℤ :=\n  match a.val with\n  | 0 => {W[0]}\n  | 1 => {W[1]}\n  | _ => {W[2]}\n')
t=t.replace('@@U2@@',f'def modularWeightEightU2 : Matrix (Fin 9) (Fin 9) ℤ :=\n  {mat(A)}\n')
t=t.replace('@@U3@@',f'def modularWeightEightU3 : Matrix (Fin 9) (Fin 9) ℤ :=\n  {mat(Bm)}\n')
t=t.replace('@@ID@@',f"""/-- The vector of the newform `6.8.a.a` in the normal basis. -/
def modularWeightEightH : Fin 9 → ℤ := ![{', '.join(map(str,h))}]

/-- The functional in the rank-one relation. -/
def modularWeightEightV : Fin 9 → ℤ := ![{', '.join(map(str,v))}]

/-- The polynomial that kills every other eigensystem has rank one. -/
theorem modularWeightEight_matrix_identity :
    (modularWeightEightU2 - 1) * (modularWeightEightU2 - 128) * (modularWeightEightU2 + 8) *
      (modularWeightEightU3 + 27) = Matrix.vecMulVec modularWeightEightH modularWeightEightV := by
  decide +kernel
""")
(root/'ModularWeightEightData.lean').write_text(t)
act=(root/'ModularWeightSixAction.lean').read_text()
(root/'ModularWeightEightAction.lean').write_text(ren(act))
