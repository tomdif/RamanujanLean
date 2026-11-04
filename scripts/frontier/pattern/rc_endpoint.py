# Endpoint test: overconvergent weight w=k' (positive), s=-1 lattice, slope j=k'-1 segment must have residual charpoly
#   T_l|S_k  *  T_l^{-1}|M_{k'}   with u=1 (k=l+1-k'): Bol images and critical stabilizations.
# Also intermediate weights w=4-k'+2i, j=1+i: u=prod_{m<j}(-1-m)/(k+m).
import sys
from fractions import Fraction as Fr
src=open("rc_weight_minus2.py").read().rsplit("\ntot=ok=0\n",1)[0]
exec(src)
tot=ok=0
for arg in sys.argv[1].split(','):
    p,PR,N=map(int,arg.split(':'))
    for kp in [int(x) for x in sys.argv[2].split(',')]:
        k=p+1-kp
        for i in range(0,kp-1):
            w=4-kp+2*i;j=1+i
            a=w+p-1
            if a<4 or dimM(a)==0: continue
            C,idx=run(p,a,-1,PR,N)
            S=segs_mod(C,p,PR)
            seg=[x for x in S if x[0]==j]
            u=Fr(1)
            for m in range(j):u*=Fr(-1-m,k+m)
            uu=u.numerator*pow(u.denominator,-1,p)%p
            A_=scale([x%p for x in cp(p,k)],uu,p)
            B_=scale(rev(predM(p,kp),p),uu,p)
            pred=pmul(A_,B_,p)
            if not seg:
                print(f'p={p} kp={kp} w={w} j={j}: no segment; slopes',[ (x[0],x[1]) for x in S],flush=True);continue
            _,m_,c=seg[0]
            tot+=1;good=(c==pred);ok+=good
            print(f'p={p} kp={kp} w={w} j={j} u={uu} m={m_} preddeg={len(pred)-1} {"OK" if good else "NO"}',flush=True)
print('TOTAL',ok,'/',tot)
