import mpmath as mp, time
exec(open('xi3.py').read().split('t=time.time()')[0])
mp.mp.dps=70
def fd(vals,k): return sum((-1)**(k-j)*mp.binomial(k,j)*vals[j] for j in range(k+1))
KMAX=7
print("N | N^{k/2} Δ^k log B(N), k=2..7 | 2N δ² | Δ^k logγ/δ^k k=3..7")
for N in (25,50,100,200,400,800,1600):
    lB=[mp.log(B(N+j)) for j in range(KMAX+1)]
    lg=[lB[j]+mp.log(mp.factorial(N+j)/mp.factorial(2*N+2*j))-(2*(N+j)-1)*mp.log(2) for j in range(KMAX+1)]
    rB=[mp.nstr(fd(lB,k)*mp.mpf(N)**(mp.mpf(k)/2),4) for k in range(2,KMAX+1)]
    d2=-fd(lg,2)/2; dl=mp.sqrt(d2)
    rg=[mp.nstr(fd(lg,k)/dl**k,4) for k in range(3,KMAX+1)]
    print(N, rB, mp.nstr(2*N*d2,6), rg, flush=True)
