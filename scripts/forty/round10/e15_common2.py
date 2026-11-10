"""round 10, Entry 3.15(ii), second formulation: L(q) f(-q^6) f(-q^42) = Psi(q) (round-7 notes), i.e. with
Phi1 = L f(-q^3)f(-q^7) and Phi2 = L f(-q)f(-q^21) (two-term theta sums):
   Psi f(-q^3) f(-q^7) = Phi1 f(-q^6) f(-q^42),   Psi f(-q) f(-q^21) = Phi2 f(-q^6) f(-q^42).
Is there one generalized eta quotient E making all four terms products of two Jacobi thetas?"""
import itertools, random
N=1680
def P(b,a):
    v=[0]*N
    for r in range(b%a, N, a):
        v[r%N]+=1
    return v
def add(*vs): return [sum(x) for x in zip(*vs)]
def neg(v): return [-x for x in v]
def fm(a,b):  # f(-q^a,-q^b)
    m=a+b; return add(P(a,m),P(b,m),P(m,m))
def fp(a,b):  # f(q^a,q^b)
    m=a+b; return add(P(2*a,2*m),P(2*b,2*m),P(m,m),neg(P(a,m)),neg(P(b,m)))
def eta(k): return P(k,k)
Psi=[add(fp(2,10),fp(28,56)), add(fp(4,8),fp(14,70))]
Phi1=[add(fm(6,9),fm(14,21)), add(fm(3,12),fm(7,28))]
Phi2=[add(fm(42,63),fm(1,4)), add(fm(2,3),fm(21,84))]
sys1=[add(t,eta(3),eta(7)) for t in Psi]+[add(t,eta(6),eta(42)) for t in Phi1]
sys2=[add(t,eta(1),eta(21)) for t in Psi]+[add(t,eta(6),eta(42)) for t in Phi2]
mods=[m for m in range(2,421) if N%m==0]
thetas=[]
for m in mods:
    for a in range(1,m//2+1):
        thetas.append(((m,a,'-'),fm(a,m-a)))
        if N%(2*m)==0: thetas.append(((m,a,'+'),fp(a,m-a)))
print(len(thetas),'thetas')
random.seed(2); W=[random.randrange(1,1<<61) for _ in range(N)]; MOD=(1<<61)-1
def h(v): return sum(w*x for w,x in zip(W,v))%MOD
th=[(n,h(t)) for n,t in thetas]
pair={}
for (n1,h1),(n2,h2) in itertools.combinations_with_replacement(th,2):
    pair.setdefault((h1+h2)%MOD,(n1,n2))
print(len(pair),'pair sums')
for name,terms in (('Phi1',sys1),('Phi2',sys2)):
    ht=[h(t) for t in terms]; found=0
    for key,(n1,n2) in pair.items():
        E=(key-ht[0])%MOD
        if all((E+x)%MOD in pair for x in ht[1:]):
            found+=1
            if found<=3: print(name,(n1,n2),[pair[(E+x)%MOD] for x in ht[1:]])
    print(name,'common multipliers:',found)
