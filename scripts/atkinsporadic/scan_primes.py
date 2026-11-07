"""For each ell, compute T(Q^2) eigenvalues mod ell on the twisted partition series, flag sporadic Q."""
import sys
sys.path.insert(0, '/Users/thomasdifiore/RamanujanTau/scripts/atkinsporadic')
from eigen_mod import pmod, twisted, eigen, leg
from sympy import primerange
NMAX = int(sys.argv[1]); QMAX = int(sys.argv[2])
for ell in [int(x) for x in sys.argv[3].split(',')]:
    p = pmod(ell, NMAX); a, eps = twisted(ell, p); lam = (ell * ell - 3) // 2
    out = []
    for Q in primerange(5, QMAX):
        if Q == ell: continue
        mus, z = eigen(ell, a, Q, lam, NMAX)
        if len(mus) != 1 or not z:
            out.append((Q, 'NOT-EIGEN', mus)); continue
        mu = mus.pop(); c = pow(Q, lam - 1, ell); s = leg(-3, Q)
        tag = ''
        if mu == 0: tag = 'WEAVER(Q^3: mu=0)'
        elif (mu - s * c) % ell == 0: tag = 'ATKIN(m/Q)=+1'
        elif (mu + s * c) % ell == 0: tag = 'ATKIN(m/Q)=-1'
        out.append((Q, mu, tag))
    print("ell", ell, "eps", eps, [o for o in out if o[2]])
    print("   all:", out[:12])
