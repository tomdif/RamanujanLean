"""Exact arithmetic in span{J_nu} (dense coefficient lists) and in span{J}[Y] modulo the modular equation P.
Checks the H2 identities I1-I4 and the Euler formula for the 55 seeds."""
import json, sys

ST = {(1, 1): {2: 1, 3: 1}, (1, 2): {3: 1, 5: 11}, (1, 3): {4: 1}, (1, 4): {5: 1, 6: 12, 7: 11},
      (2, 2): {4: 1, 5: -1}, (2, 3): {5: 1, 6: 11}, (2, 4): {6: 1, 7: 11, 8: 11},
      (3, 3): {6: 1, 7: 11}, (3, 4): {7: 1, 8: 12, 10: 121}, (4, 4): {8: 1, 9: 12, 10: 11, 11: 121}}
E = {1: {1: 121, 2: 2662, 3: 14641, 5: 161051}, 2: {1: -11, 2: 968, 3: 11979, 5: 161051},
     3: {2: 242, 3: 5324, 5: 73205}, 4: {2: 22, 3: 1452, 5: 14641}, 5: {3: 242, 5: -1331},
     6: {3: 22, 5: -1331}, 7: {5: -121}, 8: {5: 121}, 9: {5: 55}, 10: {5: 11}, 11: {5: 1}}
OPS = [0]

def trim(f):
    while f and f[-1] == 0: f = f[:-1]
    return f
def add(f, g, s=1):
    n = max(len(f), len(g)); out = [0] * n
    for i, x in enumerate(f): out[i] += x
    for i, x in enumerate(g): out[i] += s * x
    return trim(out)
def scale(c, f): return trim([c * x for x in f])
def gprod(i, r):
    if i == 0: return {r: 1}
    if r == 0: return {i: 1}
    return ST[(min(i, r), max(i, r))]
def mul_J(nu, f):
    """J_nu * f"""
    a, i = divmod(nu, 5)
    out = [0] * (len(f) + nu + 12)
    for mu, c in enumerate(f):
        if c == 0: continue
        b, r = divmod(mu, 5)
        for d, s in gprod(i, r).items():
            out[5 * (a + b) + d] += s * c; OPS[0] += 1
    return trim(out)
def mul(f, g):
    out = []
    for nu, c in enumerate(g):
        if c: out = add(out, scale(c, mul_J(nu, f)))
    return out
def dense(d):
    if not d: return []
    out = [0] * (max(d) + 1)
    for k, v in d.items(): out[k] += v
    return trim(out)
EL = {j: dense(E[j]) for j in E}

# polynomials in Y: list of dense J-lists
def padd(A, B, s=1):
    n = max(len(A), len(B)); return [add(A[k] if k < len(A) else [], B[k] if k < len(B) else [], s) for k in range(n)]
def pmul(A, B):
    out = [[] for _ in range(len(A) + len(B) - 1)]
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            if a and b: out[i + j] = add(out[i + j], mul(a, b))
    return out
def pshift(A, k): return [[] for _ in range(k)] + A
def pJ(nu, A): return [mul_J(nu, a) for a in A]
def reduce(A):
    """A mod P, where Y^11 = sum_{j=0}^{10} (-1)^j e_{j+1} Y^{10-j}"""
    A = [list(a) for a in A]
    for n in range(len(A) - 1, 10, -1):
        t = A[n]; A[n] = []
        if not t: continue
        for j in range(11):
            A[n - 1 - j] = add(A[n - 1 - j], mul(EL[j + 1], t), (-1) ** j)
    return (A + [[] for _ in range(11)])[:11]
def iszero(A): return all(not a for a in A)

Pd = [[] for _ in range(11)]
Pd[10] = [11]
for j in range(10):
    Pd[9 - j] = scale(-((-1) ** j) * (10 - j), EL[j + 1])

if __name__ == "__main__":
    Sraw = json.load(open('S.json'))
    S = {int(k): [trim(r) for r in v] for k, v in Sraw.items()}
    S[0] = Pd
    S2, S3, S4, S6 = S[1], S[2], S[3], S[4]
    Y12 = [[] for _ in range(12)] + [[1]]
    OPS[0] = 0
    S2S2 = pmul(S2, S2); S2S3 = pmul(S2, S3); S3P = pmul(S3, Pd); PP = pmul(Pd, Pd)
    I1 = padd(pJ(5, padd(padd(S2S2, S2S3, -1), S3P, -1)), [scale(11, a) for a in pmul(Y12, PP)])
    print("I1:", iszero(reduce(I1)), "ops", OPS[0]); OPS[0] = 0
    I2 = padd(pJ(5, padd(padd(pmul(pmul(S3, S3), Pd), pmul(S2S2, S2), -1), pmul(S2S3, Pd))), pmul(Y12, pmul(PP, Pd)))
    print("I2:", iszero(reduce(I2)), "ops", OPS[0]); OPS[0] = 0
    I3 = padd(pmul(Pd, S4), padd(S2S2, S3P, -1), -1)
    print("I3:", iszero(reduce(I3)), "ops", OPS[0]); OPS[0] = 0
    I4 = padd(pmul(Pd, S6), pmul(S2, S4), -1)
    print("I4:", iszero(reduce(I4)), "ops", OPS[0]); OPS[0] = 0
    base = {tuple(map(int, k.split(","))): {int(a): int(b) for a, b in v.items()} for k, v in json.load(open("base_C.json")).items()}
    ok = True
    for i in range(5):
        F = reduce(S[i])
        for lam in range(11):
            if F[10] != scale(11, dense(base[(lam, i)])):
                ok = False; print("seed mismatch", lam, i)
            F = reduce(pshift(F, 1))
    print("Euler seeds:", ok, "ops", OPS[0])
