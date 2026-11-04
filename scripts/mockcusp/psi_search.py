import cmath, itertools
def poch(a,q,n):
    p=1
    for j in range(n): p*=1-a*q**j
    return p
def qq(q): return poch(q,q,400)
def psi(q): return sum(q**(n*n)/poch(q,q*q,n) for n in range(1,40))
pts=[0.3,0.45*cmath.exp(0.7j),0.5*cmath.exp(-2.1j)]
import sys; m=int(sys.argv[1]); T=[poch(q**m,q**m,400)*psi(q) for q in pts]
found=[]
for a2 in range(1,25):
 for b2 in range(-24,25):
  for c2 in range(-2,13):
   for al in [1,2,4,8]:
    for be in range(-5,6):
     for sg in [1,-1]:
      for sn in [1,-1]:
       vals=[]
       ok=True
       for q in pts:
        s=0
        for n in range(-25,26):
          D=al*n+be
          if D==0: ok=False;break
          s+=sn**n*q**((a2*n*n+b2*n+c2)/2)/(1-sg*q**D)
        if not ok: break
        vals.append(s)
       if ok:
        for coef in [1,-1,2,-2,0.5,-0.5]:
         if all(abs(coef*v-t)<1e-9 for v,t in zip(vals,T)): found.append((a2,b2,c2,al,be,sg,sn,coef))
print(found)
