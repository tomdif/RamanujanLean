"""Find K with  sum_{((24N-1)/13)=-1} p(N) q^N == q * prod(1-q^n)^23 * K(q)  (mod 13), K level one."""
import numpy as np
M = 13; L = 400
def mul(a, b):
    return np.convolve(a, b)[:L] % M
def powser(a, e):
    r = np.zeros(L, dtype=np.int64); r[0] = 1
    for _ in range(e): r = mul(r, a)
    return r
E = np.zeros(L, dtype=np.int64); E[0] = 1
for n in range(1, L):  # prod (1-q^n)
    f = np.zeros(L, dtype=np.int64); f[0] = 1; f[n] = -1 % M
    E = mul(E, f)
p = np.load('/private/tmp/claude-501/-Users-thomasdifiore/1baa43e0-9643-458b-8681-0a73f9f4e386/scratchpad/p_mod13.npy')[:L]
def leg(a):
    a %= M
    return 0 if a == 0 else (1 if pow(a, 6, M) == 1 else -1)
Pm = np.array([p[N] if leg(24 * N - 1) == -1 else 0 for N in range(L)], dtype=np.int64)
# divide by q*E^23 : E^{-1} = partition series
Pinv = p.copy() % M  # 1/E
lhs = Pm.copy()
X = mul(lhs, powser(Pinv, 23))  # = q*K
assert X[0] == 0
K = np.concatenate([X[1:], [0]])[:L-1]
print("K first 30:", list(K[:30]))
# Eisenstein series mod 13
def sigma(n, k): return sum(pow(d, k, M) for d in range(1, n + 1) if n % d == 0) % M
E4 = np.array([1] + [240 * sigma(n, 3) % M for n in range(1, L)], dtype=np.int64) % M
E6 = np.array([1] + [(-504 * sigma(n, 5)) % M for n in range(1, L)], dtype=np.int64) % M
Lk = L - 1
def basis(w):
    out = []
    for a in range(w // 4 + 1):
        for b in range(w // 6 + 1):
            if 4 * a + 6 * b == w:
                out.append(((a, b), mul(powser(E4, a), powser(E6, b))[:Lk]))
    return out
from sympy import Matrix
for w in range(0, 200, 12):
    B = basis(w)
    A = Matrix([[int(x) for x in v] for _, v in B]).T  # Lk x d
    rhs = Matrix([int(x) for x in K[:Lk]])
    # solve mod 13 using first d+5 rows then verify
    import itertools
    aug = A.row_join(rhs)
    # gaussian elimination mod 13
    R = [list(map(int, aug.row(i))) for i in range(Lk)]
    d = len(B)
    piv = []; r = 0
    for c in range(d + 1):
        pr = next((i for i in range(r, Lk) if R[i][c] % M), None)
        if pr is None: continue
        R[r], R[pr] = R[pr], R[r]
        inv = pow(R[r][c], -1, M)
        R[r] = [x * inv % M for x in R[r]]
        for i in range(Lk):
            if i != r and R[i][c] % M:
                f = R[i][c]; R[i] = [(x - f * y) % M for x, y in zip(R[i], R[r])]
        piv.append(c); r += 1
    if d in piv:
        continue
    sol = [0] * d
    for i, c in enumerate(piv): sol[c] = R[i][d]
    print("weight", w, "dim", d, "solution", [(B[i][0], sol[i]) for i in range(d) if sol[i]])
    break
