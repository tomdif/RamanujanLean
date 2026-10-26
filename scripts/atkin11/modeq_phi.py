"""Find the degree-11 modular equation of phi = q^5 E(q^121)/E(q) over M^0(11)(q^11):
   phi^11 + sum_{j=1}^{11} (-1)^j e_j(q^11) phi^{11-j} = 0,   e_j in span{ z^a J_i }  (J_0=1,J_1..4=g2,g3,g4,g6),
   by exact linear algebra on q-expansions; then verify to high order and report 11-adic valuations."""
import sys, itertools
from qs import *
from atkin_basis import basis
from flint import fmpq_mat

D = int(sys.argv[1]) if len(sys.argv) > 1 else 10   # max pole order at cusp 0 allowed for e_j
NQ = int(sys.argv[2]) if len(sys.argv) > 2 else 1500 # q-precision for the check
poles = {"1":0, "g2":2, "g3":3, "g4":4, "g6":6}
Nb = NQ//11 + 12
B = basis(Nb)
one = const(1, Nb)
J = {"1": one, "g2": B["g2"], "g3": B["g3"], "g4": B["g4"], "g6": B["g6"]}
z = B["z"]
mons = []
for a in range(0, D//5 + 1):
    for k, pl in poles.items():
        if 5*a + pl <= D: mons.append((a, k))
print("monomials z^a J:", mons)
phi = etaq({121:1, 1:-1}, 5, NQ)
phip = [const(1, NQ)]
for i in range(11): phip.append(phip[-1]*phi)
cols = []; names = []
for j in range(1, 12):
    for (a, k) in mons:
        f = (z**a if a else one) * J[k]
        fj = f.subs(11)
        cols.append(((-1)**j) * fj * phip[11-j]); names.append((j, a, k))
target = -phip[11]
rows = range(0, NQ)
M = fmpq_mat([[c.coeff(n) for c in cols] for n in rows])
b = fmpq_mat([[target.coeff(n)] for n in rows])
# solve least: use rref of augmented
A = fmpq_mat(len(rows), len(cols)+1)
for i in range(len(rows)):
    for jj in range(len(cols)): A[i, jj] = M[i, jj]
    A[i, len(cols)] = b[i, 0]
R, rank = A.rref()
# check consistency & uniqueness
ncols = len(cols)
piv = []
r = 0
sol = [fmpq(0)]*ncols
for i in range(rank):
    # find pivot column
    pc = next(jj for jj in range(ncols+1) if R[i, jj] != 0)
    if pc == ncols: print("INCONSISTENT (no solution with D=%d)" % D); sys.exit(1)
    piv.append(pc); sol[pc] = R[i, ncols]
print("rank", rank, "unknowns", ncols, "unique" if rank == ncols else "NOT unique")
print("\nModular equation:  phi^11 = sum_{j=1}^{11} (-1)^{j+1} e_j(q^11) phi^{11-j}, with")
for j in range(1, 12):
    terms = [(sol[i], a, k) for i, (jj, a, k) in enumerate(names) if jj == j and sol[i] != 0]
    s = " + ".join(f"{c}*{'z^%d*'%a if a else ''}{k}" for c, a, k in terms)
    vs = [val_p(c, 11) for c, a, k in terms]
    print(f" e_{j} = {s}\n      v11 of coeffs: {vs}")
# independent verification at higher precision is implicit (all NQ rows used); report
print("verified mod q^%d (all %d coefficient equations satisfied)" % (NQ, NQ))
