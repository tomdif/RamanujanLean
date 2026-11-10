from ps import *
import itertools
A=mul(mul(chi(1),chi(3,-1)),mul(chi(7),chi(21,-1)))
Ep=[A[4*i] if 4*i<N else 0 for i in range(N)]
M=70
args=[1,2,3,6,7,14,21,42]
F={'G':G,'H':H}
for a,b in itertools.combinations_with_replacement(args,2):
  for s1 in (1,-1):
   for s2 in (1,-1):
    for (x,y),(xp,yp) in [(('G','G'),('H','H')),(('G','H'),('H','G')),(('H','G'),('G','H')),(('H','H'),('G','G'))]:
      P1=mul(F[x](a,s1),F[y](b,s2)); P2=mul(F[xp](a,s1),F[yp](b,s2))
      for k in range(0,12):
        for c in (1,-1):
          if all(Ep[n]==P1[n]+c*(P2[n-k] if n>=k else 0) for n in range(M)):
            print(a,b,s1,s2,x,y,xp,yp,k,c)
