# compute L(b) Katz vectors mod l^PR and analyze module stabilization b_l(m)
import sys, os, json, time
from katzmat import Katz
from zmod import smith, size, val
from flint import nmod_mat, fmpz_mat

def run(p, PR, N, B, mmax, out=None):
    t0 = time.time()
    K = Katz(p, PR, N); Um, Dm = K.matrices(); mod = K.mod
    vs = []
    v = nmod_mat(K.dN, 1, [1] + [0] * (K.dN - 1), mod)
    vs.append([int(v[i, 0]) for i in range(K.dN)])
    for b in range(1, B + 1):
        v = (Dm if b % 2 else Um) * v
        vs.append([int(v[i, 0]) for i in range(K.dN)])
    res = dict(p=p, PR=PR, N=N, B=B, dN=K.dN, d=K.dims[1], time_setup=time.time() - t0)
    # Katz-index valuation profile of L(b): min valuation over coordinates of each index i
    prof = {}
    for b in range(1, B + 1):
        pr = []
        for i in range(1, N + 1):
            pr.append(min([val(vs[b][t], p, PR) for t in range(K.dims[i - 1], K.dims[i])], default=PR))
        prof[b] = pr
    res['profile'] = prof
    tab = {}
    for m in range(1, mmax + 1):
        # tail module sizes s(b) = log_l |span{v_b, v_{b+2}, ...}| with Krylov-exact stopping
        s = {}; inv = {}; kryl = {}
        for b in range(1, B + 1):
            cols = []; last = -1; ok = False
            for j in range(b, B + 1, 2):
                cols.append(vs[j]); sz = size(cols, p, m)
                if sz == last: ok = True; break
                last = sz
            if ok:
                s[b] = last; inv[b] = smith(cols, p, m); kryl[b] = len(cols) - 1
        # b_mod: least b with s(b) == s(b+2)  (and both known)
        bmod = next((b for b in range(1, B - 1) if b in s and b + 2 in s and s[b] == s[b + 2]), None)
        # b_prop: least b such that v_{b'+2} ≡ c v_{b'} mod l^m for all b' >= b in range
        def prop(b):
            sz = size([vs[b]], p, m); return size([vs[b], vs[b + 2]], p, m) == sz and sz == m
        bprop = None
        for b in range(1, B - 1):
            if all(prop(bb) for bb in range(b, B - 1)): bprop = b; break
        stab = None
        if bmod is not None:
            stab = dict(invariants=[m - e for e in inv[bmod]], krylov_len=kryl[bmod])
        tab[m] = dict(bmod=bmod, bprop=bprop, stable=stab, s={b: s.get(b) for b in range(1, B + 1)})
        print(f'p={p} m={m}: b_mod={bmod} b_prop={bprop} stable module ≅ ⊕Z/p^{stab and stab["invariants"]}',
              ' s(b)=', [s.get(b) for b in range(1, B + 1)], flush=True)
    res['tab'] = tab
    # X = D*U (odd parity) char poly Newton polygon
    X = Dm * Um
    Xz = fmpz_mat([[int(x) for x in row] for row in X.tolist()])
    cp = Xz.charpoly()
    co = [int(c) % mod for c in cp.coeffs()]  # low to high
    n = len(co) - 1
    vals = [val(co[n - k], p, PR) for k in range(n + 1)]  # coefficient of x^{n-k}: e_k (elementary sym)
    res['X_charpoly_vals'] = vals
    print('val of e_k(X), k=0..:', vals[:40], flush=True)
    # also the reduced charpoly mod p of X (unit-root part)
    if out:
        json.dump(res, open(out, 'w'), default=str)
    return res, vs, K, Um, Dm

if __name__ == '__main__':
    p, PR, N, B, mmax = map(int, sys.argv[1:6])
    run(p, PR, N, B, mmax, sys.argv[6] if len(sys.argv) > 6 else None)
