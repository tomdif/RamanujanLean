"""round 10, Entry 3.15(ii): with s^2 = q, A(s) = chi(s)chi(-s^3)chi(s^7)chi(-s^21), the entry is equivalent (round 7
uniqueness) to  (A(s)-A(-s))(A(s^2)-A(-s^2)) Pi(s^2) = 4 s^3 (chi^2(-s^2)chi^2(-s^42) + s^2 chi^2(-s^6)chi^2(-s^14)).
Question: is there ONE generalized eta quotient E such that E * (each of the six terms) is a product of two Jacobi
thetas f(+-s^a, +-s^b)?  Exponent vectors over (s^r; s^N)_inf, N = 336."""
import itertools, random
N=336
def P(b,a):            # (s^b; s^a)_inf, a | N
    v=[0]*N
    for r in range(b%a, N, a):
        if r==0: r=N
        v[r%N]+=1
    return v
def add(*vs): return [sum(x) for x in zip(*vs)]
def neg(v): return [-x for x in v]
def chim(k): return P(k,2*k)                      # chi(-s^k)
def chip(k): return add(P(2*k,4*k),neg(P(k,2*k)))  # chi(s^k)
def A(eps,k):  # A(eps s^k)
    # chi(eps s^k) chi(-eps... ) : chi(e s^k): e=+1 -> chip, e=-1 -> chim ; chi(-e s^{3k}) etc
    c=lambda e,m: chip(m) if e>0 else chim(m)
    e=eps                 # x = eps s^k, odd powers of x keep the sign
    return add(c(e,k),c(-e,3*k),c(e,7*k),c(-e,21*k))
terms=[add(A(e1,1),A(e2,2)) for e1 in (1,-1) for e2 in (1,-1)]
Pi2=add(chim(2),chim(6),chim(14),chim(42))
terms.append(add(chim(2),chim(2),chim(42),chim(42),neg(Pi2)))
terms.append(add(chim(6),chim(6),chim(14),chim(14),neg(Pi2)))
# thetas f(-s^a,-s^b) and f(s^a,s^b), modulus m = a+b, 2m | N or m | N
thetas=[]
for m in range(2,N+1):
    if N%m: continue
    for a in range(1,m//2+1):
        b=m-a
        t=add(P(a,m),P(b,m),P(m,m)) if a!=b else add(P(a,m),P(a,m),P(m,m))
        thetas.append(((m,a,'-'),t))
        if N%(2*m)==0:
            tb=add(P(2*a,2*m),P(2*b,2*m),P(m,m),neg(P(a,m)),neg(P(b,m)))
            thetas.append(((m,a,'+'),tb))
print(len(thetas),'thetas')
random.seed(1); W=[random.randrange(1,1<<61) for _ in range(N)]; MOD=(1<<61)-1
def h(v): return sum(w*x for w,x in zip(W,v))%MOD
th=[(n,h(t)) for n,t in thetas]
pair={}
for (n1,h1),(n2,h2) in itertools.combinations_with_replacement(th,2):
    pair.setdefault((h1+h2)%MOD,(n1,n2))
print(len(pair),'pair sums')
ht=[h(t) for t in terms]
found=0
for key,(n1,n2) in pair.items():
    E=(key-ht[0])%MOD
    ok=[(E+x)%MOD in pair for x in ht[1:]]
    if all(ok):
        found+=1
        if found<=5: print('E from',n1,n2,'->',[pair[(E+x)%MOD] for x in ht[1:]])
    elif sum(ok)>=4 and found==0:
        pass
print('common multipliers found:',found)
# weaker: the four A-terms only
f4=0
for key,(n1,n2) in pair.items():
    E=(key-ht[0])%MOD
    if all((E+x)%MOD in pair for x in ht[1:4]):
        f4+=1
        if f4<=3: print('A-terms only:',n1,n2,[pair[(E+x)%MOD] for x in ht[1:4]])
print('multipliers for the four A-terms:',f4)
