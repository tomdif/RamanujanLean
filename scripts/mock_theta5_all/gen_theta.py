# generate RamanujanTau/MockTheta5All/Theta.lean : the seven theta identities, certified by HM (1.4b) instances
import sys,os
os.environ['MOD']='80'
sys.argv=['x']
exec(open('small.py').read())
from fractions import Fraction as Fr
from collections import Counter
MODA=80
def Pv(r,M):
    v={}; poch(v,r,M,1,1); return (Fr(1),0,{r:n for r,n in v.items() if n})
# term spec: (coef, qpow, [(r,M,exp),...])
def tatoms(t):
    c,k,fs=t
    parts=[]
    for (r,M,e) in fs:
        p=Pv(r,M)
        parts.append(p if e>0 else inv(p)) if abs(e)==1 else None
        if abs(e)>1:
            for _ in range(abs(e)): parts.append(p if e>0 else inv(p))
    x=mul(*parts); return (x[0],x[1]+k,x[2])
def P(r,M): return f'ιN h1 (Pinf {r} {M})'
def tlean(t):
    c,k,fs=t
    num=[f for f in fs if f[2]>0]; den=[f for f in fs if f[2]<0]
    def pw(f): return P(f[0],f[1])+(f' ^ {abs(f[2])}' if abs(f[2])>1 else '')
    s=' * '.join(pw(f) for f in num) or '1'
    if den: s=f'({s}) * ({" * ".join(pw(f) for f in den)})⁻¹'
    if k: s=f'mono 1 1 ^ {k} * ({s})' if k>1 else f'mono 1 1 * ({s})'
    return s
th4=[(1,1,2),(2,2,-1)]; th45=[(5,10,2),(10,10,1)]
G=[(1,5,-1),(4,5,-1)]; H=[(2,5,-1),(3,5,-1)]
psi2=[(4,4,1),(2,4,-1)]; H4=[(8,20,-1),(12,20,-1)]; G4=[(4,20,-1),(16,20,-1)]
EF0_2=[(20,20,1),(8,20,-1),(10,20,-1),(12,20,-1)]
Ephi0_2=[(8,20,1),(10,20,1),(12,20,1),(20,20,1),(4,20,-2),(6,20,-1),(14,20,-1),(16,20,-2)]
Epsi0=[(1,10,1),(9,10,1),(10,10,1),(2,10,-1),(3,10,-1),(7,10,-1),(8,10,-1)]
Ephi1=[(2,10,1),(5,10,1),(8,10,1),(10,10,1),(1,10,-1),(4,10,-2),(6,10,-2),(9,10,-1)]
Ephi1_2=[(2*r,2*M,e) for r,M,e in Ephi1]
EF1=[(10,10,1),(2,10,-1),(5,10,-1),(8,10,-1)]
EF1_2=[(2*r,2*M,e) for r,M,e in EF1]
Epsi1=[(3,10,1),(7,10,1),(10,10,1),(1,10,-1),(4,10,-1),(6,10,-1),(9,10,-1)]
Echi1=[(1,5,1),(4,5,1),(5,5,1),(2,5,-2),(3,5,-2)]
IDS={
 'phi0':[(1,0,th45+G),(1,0,th4+G),(-2,0,Ephi0_2)],
 'F0':[(2,1,psi2+H4),(-1,0,th45+G),(1,0,th4+G),(2,2,EF0_2)],
 'psi0':[(1,0,psi2+H4),(-1,1,EF0_2),(-1,0,Epsi0)],
 'phi1':[(1,0,th45+H),(-1,0,th4+H),(-2,1,Ephi1_2)],
 'F1':[(2,0,psi2+G4),(-1,0,th45+H),(-1,0,th4+H),(-2,1,EF1_2)],
 'psi1':[(1,0,psi2+G4),(1,1,EF1_2),(-1,0,Epsi1)],
 'chi1':[(2,0,EF1),(-1,0,Ephi1),(-1,0,Echi1)],
}
rels=shapes([],mrel=True); rels=[r for r in rels if r[1][0]=='M']
def hname(N): return f'h{N}'
def thname(t):
    N,e,c=t; return f'θ {hname(N)} {e} {"1" if c==1 else "(-1)"}'
def lemname(t):
    N,e,c=t; return f'cv_{N}_{e}_{"p" if c==1 else "m"}'
def atoms_u(N,e):
    k=MODA//N; L=[]
    for j in range(k): L+=[e+N*j, N-e+N*j, N+N*j]
    return L
def prodA(L):
    c=Counter(L); return ' * '.join(f'Aw {r}'+(f' ^ {n}' if n>1 else '') for r,n in sorted(c.items())) or '1'
def atoms_b(N,e):
    num=[]; k=MODA//(2*N)
    for j in range(k): num+=[2*e+2*N*j, 2*N-2*e+2*N*j, 2*N+2*N*j]
    for j in range(k): num+=[N+2*N*j, 2*N-N+2*N*j, 2*N+2*N*j]
    return num, atoms_u(N,e)
def cvlemma(t):
    N,e,c=t
    if c==1:
        assert 0<e<N, t
        k=MODA//N
        return f'''lemma {lemname(t)} : {thname(t)} = {prodA(atoms_u(N,e))} := by
  rw [θu h1 {hname(N)} {N} {e} {k} (by norm_num) {e} (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring
'''
    if e==N or e==0:
        k=MODA//(8*N)
        num=[]
        for j in range(k): num+=[2*N+8*N*j, 8*N-2*N+8*N*j, 8*N+8*N*j]
        for j in range(k): num+=[4*N+8*N*j, 8*N-4*N+8*N*j, 8*N+8*N*j]
        den=[]
        for j in range(2*k): den+=[N+4*N*j, 4*N-N+4*N*j, 4*N+4*N*j]
        pre = f'''  have hr := θ_reflect {hname(N)} 0 (c := -1) (by norm_num)
  norm_num at hr
  rw [hr, θb0 h1 {hname(N)} {N} {k} (by norm_num) (by norm_num) (by norm_num)]''' if e==N else f'''  rw [θb0 h1 {hname(N)} {N} {k} (by norm_num) (by norm_num) (by norm_num)]'''
        return f'''lemma {lemname(t)} : {thname(t)} = 2 * ({prodA(num)}) / ({prodA(den)}) := by
{pre}
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring
'''
    assert 0<e<N, t
    k=MODA//(2*N); num,den=atoms_b(N,e)
    return f'''lemma {lemname(t)} : {thname(t)} = ({prodA(num)}) / ({prodA(den)}) := by
  rw [θb h1 {hname(N)} {N} {e} {k} (by norm_num) {e} (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, Aw, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring
'''
def lean_inst(N,e1,c1,e2,c2):
    A1=(N,e1,c1); A2=(N,e2,c2)
    B1=(2*N,e1+e2,-c1*c2); B2=(2*N,N+e1-e2,-c1*c2)  # -(c1/c2) = -c1*c2 for c=±1
    C1=(2*N,N+e1+e2,-c1*c2); C2=(2*N,2*N+e1-e2,-c1*c2)
    return A1,A2,B1,B2,C1,C2
def relname(sp):
    N,e1,c1,e2,c2=sp
    return f'M_{N}_{e1}{"p" if c1==1 else "m"}_{e2}{"p" if c2==1 else "m"}'
def monostr(e,c):
    return f'mono {e} {"1" if c==1 else "(-1)"}'
def rellemma(sp):
    N,e1,c1,e2,c2=sp
    A1,A2,B1,B2,C1,C2=lean_inst(*sp)
    cs1='1' if c1==1 else '(-1)'; cs2='1' if c2==1 else '(-1)'
    hc1='one_ne_zero' if c1==1 else '(by norm_num)'; hc2='one_ne_zero' if c2==1 else '(by norm_num)'
    sgn='' if c1==1 else '-'
    qp=f'mono 1 1 ^ {e1}'
    return f'''lemma {relname(sp)} : {thname(A1)} * {thname(A2)} = {thname(B1)} * {thname(B2)} - {sgn}({qp}) * ({thname(C1)} * {thname(C2)}) := by
  have h := θ_mul {hname(N)} {e1} {e2} (c1 := {cs1}) (c2 := {cs2}) {hc1} {hc2}
  have hm : ({monostr(e1,c1)} : L) = {sgn}({qp}) := by rw [monoPow]; simp [mono]
  rw [hm] at h
  generalize (mono 1 1 : L) = m at h ⊢
  norm_num at h
  linear_combination h
'''
out_head='''/-
# The seven theta-function identities behind the remaining fifth-order mock theta identities

Each identity is certified by a few instances of HM (1.4b) `θ_mul`, after writing every theta function and
every product `(q^r;q^M)_∞` as atoms `(q^r;q^{80})_∞`. Certificates were found numerically
(`scripts/mock_theta5_all/gen_theta.py`) and are checked here by `field_simp; ring`.

Notation: `P r M = ιN h1 (Pinf r M) = (q^r;q^M)_∞` in `ℂ((q))`, `q = mono 1 1`.
-/
import RamanujanTau.MTC.ProdId
import RamanujanTau.MTC.Final0

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace MockTheta5All.Theta
open ALz HahnSeries Finset RankProof MTC

lemma h1 : 1 ≤ 1 := le_rfl
lemma h5 : 1 ≤ 5 := by norm_num
lemma h10 : 1 ≤ 10 := by norm_num
lemma h20 : 1 ≤ 20 := by norm_num

/-- the atom `(q^r; q^{80})_∞` in `ℂ((q))`. -/
noncomputable def Aw (r : ℕ) : L := PA h1 r 80

lemma Aw_ne (r : ℕ) (hr : 1 ≤ r) : Aw r ≠ 0 := PA_ne h1 r 80 hr (by norm_num)

lemma monoPow (k : ℕ) : (mono 1 1 : L) ^ k = mono k 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, ih, mono_mul]; push_cast; ring_nf
'''
def run(which):
    blocks=[out_head]
    thetas=[]; relspecs=[]; pinfs=[]; results={}
    for nm in which:
        terms=[(c,tatoms((1,k,fs))) for c,k,fs in IDS[nm]]
        # sanity: tatoms coefficient 1
        sol=solve(terms,rels)
        assert sol, nm
        tt={key(t):t for c,t in terms}
        lc=[]
        for c,sp,kk,p in sol:
            spec=sp[1]
            rel=exact(sp); Ti=tt[kk]
            cp,(sp_,kp,vp)=rel[p]
            cf=Fr(1)/(cp*Fr(sp_)); sh=Ti[1]-kp
            d={r:Ti[2].get(r,0)-vp.get(r,0) for r in set(Ti[2])|set(vp)}
            num=' * '.join(f'Aw {r}'+(f' ^ {n}' if n>1 else '') for r,n in sorted(d.items()) if n>0) or '1'
            den=' * '.join(f'Aw {r}'+(f' ^ {-n}' if n<-1 else '') for r,n in sorted(d.items()) if n<0) or '1'
            co=Fr(c)*cf  # sympy rational * Fraction
            co=Fr(str(co))
            costr=f'({co.numerator} : L)' if co.denominator==1 else f'(({co.numerator} : L) / {co.denominator})'
            m=''
            if sh>0: m=' * '.join(['mono 1 1']*sh)+' * '
            elif sh<0: m=f'(1 / ({" * ".join(["mono 1 1"]*(-sh))})) * '
            lc.append(f'{costr} * {m}(({num}) / ({den})) * {relname(spec)}')
            if spec not in relspecs: relspecs.append(spec)
            for t in lean_inst(*spec):
                if t not in thetas: thetas.append(t)
        for c,k,fs in IDS[nm]:
            for (r,M,e) in fs:
                if (r,M) not in pinfs: pinfs.append((r,M))
        results[nm]=(lc,[s for s in relspecs])
    for t in thetas: blocks.append(cvlemma(t))
    for sp in relspecs: blocks.append(rellemma(sp))
    for (r,M) in pinfs:
        k=MODA//M
        blocks.append(f'''lemma ip_{r}_{M} : {P(r,M)} = {prodA([r+M*j for j in range(k)])} := by
  rw [ιN_Pinf_split h1 {r} {M} {k} (by norm_num) (by norm_num) (by norm_num)]
  simp only [Aw, prod_range_succ, prod_range_zero, one_mul]
''')
    nz='\n  '.join(f'have n{r} := Aw_ne {r} (by norm_num)' for r in range(1,81))
    cvs=', '.join(lemname(t) for t in thetas)
    for nm in which:
        lc,_=results[nm]
        target=' + '.join(f'({c} : L) * ({tlean((1,k,fs))})' for c,k,fs in IDS[nm])
        used=sorted(set(relname(s) for s in relspecs if any(relname(s) in x for x in lc)))
        ips=', '.join(f'ip_{r}_{M}' for (r,M) in pinfs if any((r,M)==(a,b) for (a,b,e) in sum([fs for c,k,fs in IDS[nm]],[])))
        haves='; '.join(f'have {u} := {u}' for u in used)
        blocks.append(f'''/-- theta identity `{nm}`. -/
theorem theta_{nm} : {target} = 0 := by
  {haves}
  simp only [{cvs}] at {' '.join(used)}
  rw [{ips}]
  have hm : (mono 1 1 : L) ≠ 0 := by simp [mono]
  {nz}
  linear_combination (norm := (field_simp; ring)) {' + '.join(lc)}
''')
    return '\n'.join(blocks)+'\nend MockTheta5All.Theta\n'
if __name__=='__main__':
    which=sys.argv_w if hasattr(sys,'argv_w') else os.environ.get('WHICH','phi0').split()
    out=os.environ.get('OUT','Theta.lean')
    s=run(which)

    open(out,'w').write(s)
    print('wrote',out,len(s))
