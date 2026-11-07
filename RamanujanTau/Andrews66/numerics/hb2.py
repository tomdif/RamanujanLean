import mpmath as mp, math, sys
DPS=int(sys.argv[1]) if len(sys.argv)>1 else 50
mp.mp.dps = DPS
def fq(q):
    s = mp.mpc(0); P = mp.mpc(1); n = 0; qn2 = mp.mpc(1); qn=mp.mpc(1)
    tol = mp.mpf(10)**(-DPS+5)
    while True:
        # q^{n^2}: q^{(n+1)^2} = q^{n^2} q^{2n+1}
        t = qn2/P**2
        s += t
        if n>5 and abs(qn2) < tol: break
        qn2 *= qn*qn*q
        n += 1
        qn *= q
        P *= (1+qn)
    return s, n
def poch(q):
    P = mp.mpc(1); qm=q
    while abs(qm) > mp.mpf(10)**(-DPS):
        P *= (1-qm); qm*=q
    return P
def bdirect(q): return poch(q)**3/poch(q*q)**2
def qp(h,K,z): return mp.exp(2j*mp.pi*(h+1j*z)/K)
def eps(K): return (-1)**(K//2) if K%2==0 else 0
def inv(h,K):  # h' with K | h h' + 1
    for x in range(K):
        if (h*x+1)%K==0: return x
omega_cache={}
def bvia(h,K,z):
    hp=inv(h,K)
    if (h,K) not in omega_cache:
        z0=mp.mpf(1)/K
        lhs=bdirect(qp(h,K,z0)); rhs=1/mp.sqrt(z0)*mp.exp(mp.pi*(1/z0-z0)/(12*K))*bdirect(qp(hp,K,1/z0))
        omega_cache[(h,K)]=lhs/rhs
    om=omega_cache[(h,K)]
    return om/mp.sqrt(z)*mp.exp(mp.pi*(1/z-z)/(12*K))*bdirect(qp(hp,K,1/z))
rows=[]
for K in [1,2,3,4,5,6,8,10]:
    for h in [h for h in range(K) if math.gcd(h,K)==1][:2]:
        for rw in [0.5,2.0,8.0]:
            for iv in [0,1,4,16,40,-40]:
                w=mp.mpc(rw*K, iv*K); z=1/w
                q=qp(h,K,z)
                f,nt=fq(q)
                d = f - (eps(K)*bvia(h,K,z) if K%2==0 else 0)
                rows.append((K,h,rw,iv,float(abs(z)),float(abs(d)),float(abs(f))))
                print(K,h,rw,iv,"|z|=%.3e |f-eb|=%.4e |f|=%.3e  |d||z|^.5=%.3e |d||z|=%.3e"%(abs(z),abs(d),abs(f),abs(d)*abs(z)**0.5,abs(d)*abs(z)),flush=True)
import pickle; pickle.dump(rows,open('hb2_%d.pkl'%DPS,'wb'))
