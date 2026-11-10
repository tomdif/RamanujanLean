"""round 11: the Cramer form chi^2(q) L(q^2) = bc + q ad (cramer.py) turns 3.15(ii) into the 2+2 product identity
   T1 + q^6 T2 = X1 + q X2,  T1 = f(q^4,q^20) f(q^56,q^112), T2 = f(q^8,q^16) f(q^28,q^140),
   X1 = e1 e4^3 e6 e7 e84/(e2^4 e14),  X2 = e1^3 e4 e6 e12 e28 e84/(e2^4 e3 e14)   (e_k = (q^k;q^k)).
Is there one generalized eta quotient E making all four terms products of two Jacobi thetas?"""
import itertools, random, sys
N=1680
def P(b,a):
    v=[0]*N
    for r in range(b%a, N, a): v[r%N]+=1
    return v
def add(*vs): return [sum(x) for x in zip(*vs)]
def neg(v): return [-x for x in v]
def sc(k,v): return [k*x for x in v]
def fm(a,b): m=a+b; return add(P(a,m),P(b,m),P(m,m))
def fp(a,b): m=a+b; return add(P(2*a,2*m),P(2*b,2*m),P(m,m),neg(P(a,m)),neg(P(b,m)))
def eta(k): return P(k,k)
def etaq(d): return add(*[sc(e,eta(k)) for k,e in d.items()])
X1=etaq({1:1,4:3,6:1,7:1,84:1,2:-4,14:-1})
X2=etaq({1:3,4:1,6:1,12:1,28:1,84:1,2:-4,3:-1,14:-1})
terms=[add(fp(4,20),fp(56,112)), add(fp(8,16),fp(28,140)), X1, X2]
LIM=int(sys.argv[1]) if len(sys.argv)>1 else 840
mods=[m for m in range(2,LIM+1) if N%m==0]
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
ht=[h(t) for t in terms]; found=0
for key,(n1,n2) in pair.items():
    E=(key-ht[0])%MOD
    if all((E+x)%MOD in pair for x in ht[1:]):
        found+=1
        if found<=10: print((n1,n2),[pair[(E+x)%MOD] for x in ht[1:]])
print('common multipliers:',found)
