from ps import *
import itertools
g=lambda k,s=1: sub_q(mul(G1,fneg(1)),k,s)
h=lambda k,s=1: sub_q(mul(H1,fneg(1)),k,s)
L1=add(mul(g(3),g(7)),mul(mono(2),mul(h(3),h(7))))
L2=add(mul(g(21),h(1)),neg(mul(mono(4),mul(g(1),h(21)))))
targets={'L1/chi3chi7':div(L1,mul(chi(3,-1),chi(7,-1))),'L2/chi1chi21':div(L2,mul(chi(1,-1),chi(21,-1))),
 'L1*chi?':div(L1,mul(chi(3,-1),chi(21,-1))),'L2/chi1chi7':div(L2,mul(chi(1,-1),chi(7,-1))),
 'L1/chi1chi7':div(L1,mul(chi(1,-1),chi(7,-1))),'L2/chi3chi21':div(L2,mul(chi(3,-1),chi(21,-1))),
 'L1/chi3chi21':div(L1,mul(chi(3,-1),chi(21,-1))), 'L1/chi1chi21':div(L1,mul(chi(1,-1),chi(21,-1)))}
M=80
cache={}
def F(a,b,k,sa=1,sb=1):
    key=(a,b,k,sa,sb)
    if key not in cache: cache[key]=fab(a*k,b*k,sa,sb)
    return cache[key]
for name,T in targets.items():
  for K in (7,21,3):
    for Mo in range(2,25):
      for a in range(0,Mo//2+1):
        for a2 in range(0,Mo//2+1):
          for sg in [(1,1),(-1,-1)]:
            P1=mul(F(a,Mo-a,1,*sg),F(a2,Mo-a2,K,*sg))
            if P1[0]==0: continue
            # P1 must match T up to second term starting at some m
            diff=[T[n]*P1[0]-P1[n] for n in range(M)] if P1[0] in (1,2) else None
            if diff is None: continue
            # find first nonzero
            nz=[n for n in range(M) if diff[n]!=0]
            if not nz: print(name,"single",Mo,a,a2,K,sg); continue
            m=nz[0]
            for c in range(0,Mo//2+1):
              for c2 in range(0,Mo//2+1):
                P2=mul(F(c,Mo-c,1,*sg),F(c2,Mo-c2,K,*sg))
                for co in (1,-1,2,-2):
                  if all(T[n]*P1[0]==P1[n]+co*(P2[n-m] if n>=m else 0) for n in range(M)):
                    print(name,K,Mo,(a,a2),(c,c2),m,co,sg,P1[0])
