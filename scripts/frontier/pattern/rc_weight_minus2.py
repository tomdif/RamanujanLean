# Direct test of the law at negative weight, level 1: U on Katz lattice of weight w=a+s(p-1), s<0; truncated at index N.
import sys,re
from math import comb
from flint import fmpz_mat
src=open('rc_sharp_bound.py').read().split("p=int(sys.argv[1]);PR=int(sys.argv[2])")[0]
src=src.replace("    viol=[];att=tot=0;viol1=0\n","    viol=[];att=tot=0;viol1=0;COLS=[]\n")
src=src.replace("        for row in range(dN):\n            i=idx[row]","        COLS.append(co)\n        for row in range(dN):\n            i=idx[row]")
src=src.replace("    return tot,att,viol","    return COLS,idx")
exec(src)
exec(open('rc_slope_law_level1.py').read().split("tot=ok=0")[0])
def val_(x,p,PR):
    x%=p**PR
    if x==0:return PR
    c=0
    while x%p==0:x//=p;c+=1
    return c
def segs_mod(M,p,PR):
    m=p**PR;n=len(M)
    cp_=fmpz_mat([[M[c][r]%m for c in range(n)] for r in range(n)]).charpoly()
    co=[int(c)%m for c in cp_.coeffs()]
    e=[co[n-i] for i in range(n+1)]
    pts=[(i,val_(e[i],p,PR)) for i in range(n+1) if val_(e[i],p,PR)<PR]
    hull=[]
    for q in pts:
        while len(hull)>=2 and (hull[-1][1]-hull[-2][1])*(q[0]-hull[-1][0])>=(q[1]-hull[-1][1])*(hull[-1][0]-hull[-2][0]):hull.pop()
        hull.append(q)
    out=[]
    for a_,b_ in zip(hull,hull[1:]):
        k_=b_[0]-a_[0];d=b_[1]-a_[1]
        if d%k_:out.append((d/k_,k_,None));continue
        s_=d//k_;c=[]
        for i in range(k_+1):
            v=a_[1]+i*s_;x=e[a_[0]+i];c.append((x//p**v)%p if v<PR else 0)
        i0=pow(c[0],-1,p);out.append((s_,k_,[y*i0%p for y in c]))
    return out
def scale(T,u,p):return [pow(u,i,p)*T[i]%p for i in range(len(T))]
def rev(T,p):
    if len(T)==1:return T
    r=T[::-1];i=pow(r[0],-1,p);return [x*i%p for x in r]
def pmul(a,b,p):
    o=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):o[i+j]=(o[i+j]+x*y)%p
    return o
def predM(l,kp):
    P=[x%l for x in cp(l,kp)] if kp>=12 else [1]
    if kp>=4 and kp%2==0:P=pmul(P,[1,l-1],l)
    return P
tot=ok=0
for arg in sys.argv[1].split(','):
    p,PR,N=map(int,arg.split(':'))
    for w_ in (-2,-4,-6):
        a=w_+p-1;s=-1
        C,idx=run(p,a,s,PR,N)
        S=segs_mod(C,p,PR)
        line=[]
        for j,m_,c in S[:-1]:   # drop last (truncation) segment
            if c is None:line.append(f'{j:.2f}x{m_}');continue
            k=a-2*j
            while k<3:k+=p-1
            s_=(w_-k-2*j)//(p-1)
            num=1
            from fractions import Fraction as Fr
            u=Fr(1)
            for i in range(j):u*=Fr(s_-i,k+i)
            if u.numerator%p==0 or u.denominator%p==0:line.append(f'j{j}:binom0');continue
            uu=u.numerator*pow(u.denominator,-1,p)%p
            A_=scale(predM(p,k) if j==0 else [x%p for x in cp(p,k)],uu,p)
            h=predM(p,p+1-k)
            if h[-1]%p==0:line.append(f'j{j}:hnonord');continue
            B_=scale(rev(h,p),uu,p) if j>0 else [1]
            pred=pmul(A_,B_,p)
            tot+=1;good=pred==c;ok+=good
            line.append(f'j{j}[k{k},s{s_}]m{m_}:{"OK" if good else "NO pred"+str(len(pred)-1)}')
        print(p,'w',w_,' '.join(line),flush=True)
print('TOTAL',ok,'/',tot)
