"""Compute L_1..L_3 directly (U-iterates of q-series), expand in the J basis, check v11(a_{r,nu}) >= r + floor((nu-1)/2),
and compare with the partition numbers p(11^r n + mu_r)."""
import sys
from qs import *
from gordon_matrix import Ctx
from flint import fmpz_poly
N = int(sys.argv[1]) if len(sys.argv) > 1 else 60     # precision of L_3 in q
R = 3
tot = 11**R * (N + 2) + 50
phi_big = etaq({121: 1, 1: -1}, 5, tot)
L = const(1, tot); Ls = []
for r in range(1, R + 1):
    f = phi_big * L if r % 2 == 1 else L
    if r % 2 == 1:
        f = S(f.p, f.v, min(f.N, L.N + 5))
    L = f.U(11); Ls.append(L)
    phi_big = S(phi_big.p, phi_big.v, L.N) if r < R else phi_big
    phi_big = etaq({121: 1, 1: -1}, 5, L.N) if r < R else phi_big
ctx = Ctx(Ls[0].N + 60)
for r, Lr in enumerate(Ls[:2], 1):  # L_3 needs ~q^7000 for its J-expansion; checked only via p(n) below
    Lr = S(Lr.p, Lr.v, min(Lr.N, 11**(R - r) * N + N))
    c = ctx.express(Lr, slack=12)
    vals = {nu: val_p(x, 11) for nu, x in c.items()}
    ok = all(v >= r + (nu - 1)//2 for nu, v in vals.items())
    print(f"L_{r}: precision q^{Lr.N}, nu range [{min(c)},{max(c)}], min v11 = {min(vals.values())}, invariant v>=r+floor((nu-1)/2): {ok}")
    print("    first valuations:", [vals.get(n) for n in range(1, 12)])
# direct congruence check
from sympy.functions.combinatorial.numbers import partition
for r in (1, 2, 3):
    m = 11**r; mu = next(x for x in range(1, m+1) if (24*x) % m == 1)
    vs = [val_p(int(partition(m*n + mu)), 11) for n in range(0, 8)]
    print(f"p({m}n+{mu}), n=0..7: v11 =", vs)
