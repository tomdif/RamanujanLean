"""round 11: degree-7 relation chi(q)chi(q^7) - chi(-q)chi(-q^7) = 2q and the reduced form
   L(q^2) = chi(-q^3)chi(-q^21) - q^2 chi(-q)chi(-q^7)."""
import sys
sys.argv=[sys.argv[0],'300']
exec(open(__file__.replace('m7.py','cramer.py')).read().split("g, h = G(), H()")[0])
def p(k): return Ng(chim(k))
def m(k): return chim(k)
g,h=G(),H()
def L(k): return add(mul(S(3*k,g),S(7*k,g)), sh(2*k, mul(S(3*k,h),S(7*k,h))))
d7 = add(mul(p(1),p(7)), sc(-1,mul(m(1),m(7))))
print('p1p7 - m1m7 =', [ (i,x) for i,x in enumerate(d7) if x][:5])
red = add(mul(m(3),m(21)), sc(-1, sh(2, mul(m(1),m(7)))))
print('L(q^2) == m3m21 - q^2 m1m7:', red == L(2))
u=mul(p(1),p(7)); v=mul(m(1),m(7))
lhs=mul(mul(u,v),add(u,sc(-1,v)))
print('uv(u-v) == 2q:', lhs == sc(2,sh(1,[1]+[0]*(N-1))))
# Cramer at L_2: G(q^42),H(q^42) from 3.8(q^7), 3.7(q^14); G(q^2),H(q^2) from 3.9, 3.10(q^2); det chi^2(q^7)
# L2(q^2) = G(q^42)H(q^2) - q^8 G(q^2)H(q^42)
a1=mul(m(7),inv(m(21))); b1=mul(m(42),inv(m(14))); c1=mul(m(14),inv(m(2))); d1=mul(m(1),inv(m(7)))
P7=mul(p(7),p(7)); target=mul(P7,L(2))
for e1 in range(0,10):
  for e2 in range(0,10):
    for s1 in (1,-1):
      for s2 in (1,-1):
        for (X,Y) in ((mul(a1,c1),mul(b1,d1)),(mul(b1,d1),mul(a1,c1)),(mul(a1,d1),mul(b1,c1)),(mul(b1,c1),mul(a1,d1))):
          r=add(sc(s1,sh(e1,X)),sc(s2,sh(e2,Y)))
          if r==target: print('chi^2(q^7) L(q^2) =',s1,'q^',e1,'*X +',s2,'q^',e2,'*Y')
