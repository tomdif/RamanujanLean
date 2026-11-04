# Full law at level 1: for w = k+2j+s(l-1), 3<=k<=l+1, residual charpoly of slope-j part of T_l on S_w(1)
#  = charpoly(u T_l | S_k) * charpoly(u T_l^{-1} | M_{l+1-k}),  u = C(s,j)/C(k+j-1,j).
import sys
from math import comb
sys.argv_saved=sys.argv
from importlib import util
src=open('rc_slope_law_level1.py').read().split('tot=ok=0')[0]
exec(src)
def scale(T,u,p): return [pow(u,i,p)*T[i]%p for i in range(len(T))]
def rev(T,p):
    if len(T)==1:return T
    r=T[::-1];i=pow(r[0],-1,p);return [x*i%p for x in r]
def pmul(a,b,p):
    o=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):o[i+j]=(o[i+j]+x*y)%p
    return o
def predM(l,kp):
    # charpoly of T_l on M_kp mod l : cusp part times Eisenstein (x-1) when kp>=4
    P=[x%l for x in cp(l,kp)] if kp>=12 else [1]
    if kp>=4 and kp%2==0: P=pmul(P,[1,l-1],l)
    return P
stats={}
bad=[]
for l in map(int,sys.argv[1].split(',')):
  for w in range(l+3,int(sys.argv[2])*(l-1),2):
    co=cp(l,w)
    if len(co)==1: continue
    for j,m,c in segs(co,l):
        if c is None: stats['nonint']=stats.get('nonint',0)+1;bad.append((l,w,'nonint',j,m));continue
        if j==0: continue
        k=(w-2*j)%(l-1)
        while k<3:k+=l-1
        while k>l+1:k-=l-1
        s=(w-k-2*j)//(l-1)
        den=comb(k+j-1,j)
        if den%l==0 or comb(s,j)%l==0: stats['skip_binom0']=stats.get('skip_binom0',0)+1;continue
        u=comb(s,j)*pow(den,-1,l)%l
        A=scale([x%l for x in cp(l,k)],u,l)
        h=predM(l,l+1-k)
        if h[-1]%l==0: stats['h_nonord']=stats.get('h_nonord',0)+1;continue
        B=scale(rev(h,l),u,l)
        pred=pmul(A,B,l)
        key='j%d'%min(j,6)
        st=stats.setdefault(key,[0,0])
        st[1]+=1
        if pred==c: st[0]+=1
        else: bad.append((l,w,j,k,s,m,len(pred)-1))
print(stats)
print('mismatches',len(bad)); print(bad[:40])
