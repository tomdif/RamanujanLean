N=40
import itertools
def mul(a,b):
    c=[0]*N
    for i,x in enumerate(a):
        if x:
            for j in range(N-i): c[i+j]+=x*b[j]
    return c
def geo(D,sg,e,c):  # c*q^e/(1 - sg q^D), D>0, as series
    a=[0]*N; k=0
    while e+D*k<N:
        if e+D*k>=0: a[e+D*k]+=c*sg**k
        k+=1
    return a
def add(a,b): return [x+y for x,y in zip(a,b)]
psiq=[0, 1, 0, -1, 0, -1, -1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0, -1, -1, 0, 1, 0, 0, 1, 0, 2, 1, 0, 0, 1]
found=[]
for a2 in range(1,13):
 for b2 in range(-12,13):
  if (a2+b2)%2: continue
  for c in range(-3,6):
   for al in [1,2,3,4]:
    for be in range(-4,5):
     for sg in [1,-1]:
      for sn in [1,-1]:
       for rng in ['Z','N0']:
        s=[0]*N; ok=True
        ns=range(-20,21) if rng=='Z' else range(0,30)
        for n in ns:
          e=(a2*n*n+b2*n)//2+c; D=al*n+be
          if D==0: ok=False;break
          if D>0: t=geo(D,sg,e,sn**n if n>=0 else sn**(-n))
          else: t=geo(-D,sg,e-D,-sg*(sn**n if n>=0 else sn**(-n)))
          if e<-60: ok=False;break
          s=add(s,t)
        if not ok: continue
        for co in [1,-1,2,-2]:
          if [co*x for x in s]==psiq: found.append((a2,b2,c,al,be,sg,sn,rng,co))
        # also half
        if [x for x in s]==[2*y for y in psiq]: found.append((a2,b2,c,al,be,sg,sn,rng,'1/2'))
print(found)
