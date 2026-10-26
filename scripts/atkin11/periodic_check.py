"""Fully periodic form of the inductive step (no max(.,0)):  for all j, b in e_j, nu', t in J_b*J_nu':
   v11(c_jb) + v11(s) + B(lam-j,i,nu') >= B(lam,i,t).
B(lam+2,..) = B(lam,..)-1 and B(.,nu+10)=B(.,nu)+11 exactly, so it suffices to check lam in {0,1}, nu' in 0..9.
Also the final p(n) step in periodic form."""
from induct_check import E, prodJ, B, v11, DELTA
bad = []
for i in range(5):
    for lam in (0, 1):
        for j, e in E.items():
            for b, cb in e.items():
                for nu1 in range(0, 10):
                    for t, s in prodJ(b, nu1).items():
                        if v11(cb) + v11(s) + B(lam - j, i, nu1) < B(lam, i, t): bad.append((i, lam, j, b, nu1, t))
print("periodic inductive check (C-bound): violations =", len(bad), bad[:8])
# exactness of periodicity claims
assert all(B(l+2, i, n) == B(l, i, n) - 1 and B(l, i, n+10) == B(l, i, n) + 11 for l in range(-30, 30) for i in range(5) for n in range(-40, 40))
print("periodicity identities for B verified")
# final step: v(a_{r,nu}) >= r + floor((nu-1)/2), nu>=1, using v(C^lam_{mu,nu}) >= Bg = max(0, floor((11nu-mu-5lam+delta)/10))
# the max(0,.) here is essential (integrality) only for small nu; check box already done in partition_induct.py
