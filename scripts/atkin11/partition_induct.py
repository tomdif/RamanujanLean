"""Final induction for p(n): L_r = sum_{nu>=1} a_{r,nu} J_nu with  v11(a_{r,nu}) >= r + floor((nu-1)/2).
Step: a_{r,nu} = sum_mu a_{r-1,mu} C^lam_{mu,nu}, lam = 1 (r odd) or 0 (r even), where (Gordon's form)
  v11(C^lam_{mu,nu}) >= max(0, floor((11nu - mu - 5lam + delta(mu%5,nu%5))/10)).
Check the inequality for all mu,nu in a box (periodic beyond)."""
from induct_check import DELTA
def Bg(lam, mu, nu): return max(0, (11*nu - mu - 5*lam + DELTA[mu % 5][nu % 5]) // 10)
def inv(nu): return (nu - 1)//2   # extra valuation beyond r
bad = []; tight = []
for lam in (0, 1):
    for mu in range(1, 400):
        for nu in range(1, 400):
            lhs = inv(mu) + Bg(lam, mu, nu)   # (r-1) + inv(mu) + bound  vs  r + inv(nu)
            rhs = 1 + inv(nu)
            if lhs < rhs: bad.append((lam, mu, nu, lhs, rhs))
            elif lhs == rhs and mu < 12 and nu < 12: tight.append((lam, mu, nu))
print("violations:", len(bad), bad[:10]); print("tight cases (small):", tight[:30])
# base: L1 = 11 g2 + 242 g3 + 1331 g4 + 14641 z  -> (nu: coeff) = {1:11, 2:242, 3:1331, 5:14641}
from qs import val_p
L1 = {1: 11, 2: 242, 3: 1331, 5: 14641}
print("L1 satisfies v >= 1 + floor((nu-1)/2):", all(val_p(c, 11) >= 1 + inv(n) for n, c in L1.items()))
