# Theta-invertibility and u0 != 0 sweep (logic of scripts/frontier/pattern/theta2.py, unchanged mathematics),
# with two speedups: X = D*U via nmod_mat instead of Python loops, and the idempotent e_Y = X^e with
#   e = l^(PR+2) * lcm_{f | charpoly(X mod l), f != x} (l^deg f - 1)
# (orders in GL_R(Z/l^PR): semisimple part divides the lcm, the l-part divides l^PR since R < l; the
# topologically nilpotent part dies after dN*PR < l^(PR+2) steps), instead of prod_{f<=d}(l^f - 1).
# Usage (system python3 / flint 0.6, imports katzmat from ../pattern):  python3 theta_sweep.py LO HI OUT.jsonl [PR N]
import sys, os, json, time, math, sympy
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'pattern'))
from katzmat import Katz
from flint import nmod_mat

def run(p, PR=3, N=6):
    T0 = time.time()
    K = Katz(p, PR, N); Um, Dm = K.matrices(); mod = K.mod
    U = [[int(x) for x in r] for r in Um.tolist()]; D = [[int(x) for x in r] for r in Dm.tolist()]
    n = K.dN; I1 = list(range(K.dims[0], K.dims[1])); d = len(I1)
    def mv(Mm, v):
        r = Mm * nmod_mat(n, 1, [x % mod for x in v], mod); return [int(r[i, 0]) for i in range(n)]
    sub = lambda Mx: [[Mx[i][j] % p for j in I1] for i in I1]
    U11 = nmod_mat(d, d, [x for r in sub(U) for x in r], p); D11 = nmod_mat(d, d, [x for r in sub(D) for x in r], p)
    X0, nul = D11.nullspace()
    Kb = [[int(X0[i, j]) for i in range(d)] for j in range(nul)]
    UV = U11 * D11
    cols = [[int(UV[i, j]) for i in range(d)] for j in range(d)]
    basisUV = []
    for c in cols:
        T = basisUV + [c]
        if nmod_mat(len(T), d, [x for r in T for x in r], p).rank() == len(T): basisUV = T
    Bfull = basisUV + Kb
    Bm = nmod_mat(d, d, [Bfull[j][i] for i in range(d) for j in range(d)], p)
    ok = (Bm.rank() == d); Binv = Bm.inv() if ok else None
    def projK(s):
        c = Binv * nmod_mat(d, 1, [x % p for x in s], p)
        return [int(c[len(basisUV) + i, 0]) for i in range(len(Kb))]
    def lift(svec):
        v = [0] * n
        for a, i in enumerate(I1): v[i] = svec[a]
        return v
    def theta(kvec):
        s = [sum(kvec[i] * Kb[i][a] for i in range(len(Kb))) % p for a in range(d)]
        w = mv(Dm, lift(s))
        assert all(x % p == 0 for x in w), 'D u~ not divisible by l'
        w = [x // p for x in w]
        u = mv(Um, w)
        return projK([u[i] % p for i in I1])
    k = len(Kb)
    Th = [theta([1 if i == j else 0 for i in range(k)]) for j in range(k)]
    Thm = nmod_mat(k, k, [Th[j][i] for i in range(k) for j in range(k)], p) if k else None
    Xm = Dm * Um
    Xp = nmod_mat(n, n, [int(x) % p for r in Xm.tolist() for x in r], p)
    degs = sorted(set(f.degree() for f, e in Xp.charpoly().factor()[1] if str(f) != 'x'))
    e = p ** (PR + 2)
    lc = 1
    for f in degs: lc = lc * (p ** f - 1) // math.gcd(lc, p ** f - 1)
    e *= lc
    Pm = nmod_mat(n, n, [1 if i == j else 0 for i in range(n) for j in range(n)], mod); B = Xm; ee = e
    while ee:
        if ee & 1: Pm = Pm * B
        ee >>= 1
        if ee: B = B * B
    L1 = mv(Dm, [1] + [0] * (n - 1))
    y = mv(Pm, L1)
    z = [(L1[i] - y[i]) % mod for i in range(n)]
    out = []; zk = z
    for kk in range(PR - 1):
        uk = mv(Um, zk)
        if not all(x % p ** (kk + 1) == 0 for x in uk): out.append(('notdiv', kk)); break
        red = [(uk[i] // p ** (kk + 1)) % p for i in I1]
        out.append(projK(red) if ok else red)
        zk = mv(Xm, zk)
    rk = Thm.rank() if k else 0
    u0nz = bool(out and isinstance(out[0], list) and any(out[0]))
    # Proposition check u1 = Theta u0
    prop = None
    if k and len(out) >= 2 and all(isinstance(o, list) for o in out[:2]):
        tu = Thm * nmod_mat(k, 1, out[0], p); prop = [int(tu[i, 0]) for i in range(k)] == out[1]
    cpf = Thm.charpoly().factor()[1] if k else []
    return dict(l=p, PR=PR, N=N, d=d, dimK=k, basis_ok=ok, rankTheta=rk, Theta_invertible=(rk == k),
                charpolyTheta=' * '.join(f'({f})^{e}' if e > 1 else f'({f})' for f, e in cpf),
                Theta_sqfree=all(e == 1 for _, e in cpf), u=out, u0_nonzero=u0nz, u1_eq_Theta_u0=prop,
                secs=round(time.time() - T0, 1))

if __name__ == '__main__':
    lo, hi, outf = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    PR = int(sys.argv[4]) if len(sys.argv) > 4 else 3; N = int(sys.argv[5]) if len(sys.argv) > 5 else 6
    done = set()
    if os.path.exists(outf):
        for line in open(outf):
            try: done.add(json.loads(line)['l'])
            except Exception: pass
    for p in sympy.primerange(lo, hi + 1):
        if p in done: continue
        o = run(p, PR, N)
        with open(outf, 'a') as fh: fh.write(json.dumps(o) + '\n')
        print(f"l={p} dimK={o['dimK']} rankTheta={o['rankTheta']} u0nz={o['u0_nonzero']} prop={o['u1_eq_Theta_u0']} {o['secs']}s", flush=True)
