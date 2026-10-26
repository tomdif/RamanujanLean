"""Compute Gordon's matrices C^lam_{mu,nu}:  U11(phi^lam J_mu) = sum_nu C^lam_{mu,nu} J_nu,
J_{5a+i} = z^a * (1, g2, g3, g4, g6)[i]  (Atkin basis; ord_inf J_nu = nu),
and check Gordon's 11-adic bound  v11(C^lam_{mu,nu}) >= floor((11 nu - mu - 5 lam + delta(mu,nu))/10)."""
import sys, json
from qs import *
from atkin_basis import basis

DELTA = [[-1, 8, 7, 6, 15], [0, 9, 8, 2, 11], [1, 10, 4, 13, 12], [2, 6, 5, 4, 13], [3, 7, 6, 5, 9]]

class Ctx:
    def __init__(self, N):
        self.N = N
        NB = N + 40
        B = basis(NB)
        self.z = B["z"]; self.zi = self.z.inv()
        self.g = [const(1, NB), B["g2"], B["g3"], B["g4"], B["g6"]]
        self.cache = {}
    def J(self, nu, N):
        a, i = divmod(nu, 5)
        key = (nu, N)
        if key in self.cache: return self.cache[key]
        zz = self.z if a >= 0 else self.zi
        r = self.g[i]
        for _ in range(abs(a)): r = r * zz
        r = S(r.p, r.v, min(r.N, N)); self.cache[key] = r
        return r
    def express(self, f, slack=25):
        """greedy reduction of f (in V) into J_nu basis; returns dict nu->coeff; asserts remainder 0 to precision."""
        out = {}
        r = f
        N = f.N
        while True:
            n, c = r.lead()
            if n is None: break
            if n > N - slack: raise RuntimeError("did not terminate within precision (n=%d,N=%d)" % (n, N))
            out[n] = c
            r = r - c * self.J(n, N)
            N = r.N
        return out

def phi_series(lam, N):
    # phi = q^5 E(q^121)/E(q) ; phi^lam to absolute precision N
    return etaq({121: lam, 1: -lam}, 5*lam, N)

def C(ctx, lam, mu, N):
    """U(phi^lam J_mu) expressed; N = precision of the result in q"""
    NN = 11*N + 11*abs(5*lam) + 60
    f = phi_series(lam, NN) * ctx.J(mu, NN)
    u = f.U(11)
    u = S(u.p, u.v, min(u.N, N))
    return ctx.express(u)

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 160
    lams = range(int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else range(-3, 14)
    ctx = Ctx(11*N + 400)
    worst = None; allok = True; data = {}
    for lam in lams:
        for mu in range(0, 5):
            c = C(ctx, lam, mu, N)
            data[f"{lam},{mu}"] = {str(k): str(v) for k, v in c.items()}
            for nu, v in c.items():
                b = (11*nu - mu - 5*lam + DELTA[mu % 5][nu % 5]) // 10
                vv = val_p(v, 11)
                slackv = vv - b
                if worst is None or slackv < worst[0]: worst = (slackv, lam, mu, nu, vv, b)
                if vv < b:
                    allok = False; print("VIOLATION lam=%d mu=%d nu=%d v=%d bound=%d" % (lam, mu, nu, vv, b))
            nus = sorted(c)
            print(f"lam={lam:3d} mu={mu}: nu in [{nus[0]},{nus[-1]}], #terms={len(nus)}, maxdigits={max(len(str(abs(int(x.p)))) for x in c.values())}")
    print("Gordon bound holds on all computed entries:", allok, "| tightest (slack,lam,mu,nu,v,bound):", worst)
    json.dump(data, open("gordon_C.json", "w"))
