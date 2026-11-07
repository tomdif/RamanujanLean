/-
# Rankin–Selberg Mertens theorems for `λ(p)² = τ(p)²/p¹¹`: headlines

See `docs/SELBERG_COEFFS.md` §6.  All results are unconditional (no `DeligneBound`).

* `rsb_mul_log` — `λ(n)² log n = Σ_{dm=n} ΛR(d) λ(m)²`, `ΛR = vR − 2Λ(√·)1_□`
  (from `R(s) = exp(Σ cR n^{−s})/ζ(2s)` and L-series uniqueness);
* `cheb_LamR` — `Σ_{n≤N} |ΛR(n)| ≤ BN`;
* `summable_LamR_nonprime` — prime powers: `Σ_{n not prime} |ΛR(n)|/n < ∞`;
* `mertens1_LamR`, `mertens1_prime` — `Σ_{p≤N} λ(p)² log p/p = log N + O(1)`;
* `mertens2` — `Σ_{p≤N} λ(p)²/p − log log N → c_Δ` (`cMertens = 1 + Σ h_k`);
* `mertens2_bound` — `|Σ_{p≤N} λ(p)²/p − log log N| ≤ C` for all `N`.
-/
import RamanujanTau.SelbergCoeffs2.LogIdent
import RamanujanTau.SelbergCoeffs2.Cheb
import RamanujanTau.SelbergCoeffs2.Mertens1
import RamanujanTau.SelbergCoeffs2.Mertens2

#print axioms RamanujanTau.SelbergCoeffs2.logMul_rsB_eq
#print axioms RamanujanTau.SelbergCoeffs2.rsb_mul_log
#print axioms RamanujanTau.SelbergCoeffs2.abel_Ioc
#print axioms RamanujanTau.SelbergCoeffs2.cheb_LamR
#print axioms RamanujanTau.SelbergCoeffs2.summable_LamR_nonprime
#print axioms RamanujanTau.SelbergCoeffs2.LamR_prime
#print axioms RamanujanTau.SelbergCoeffs2.mertens1_LamR
#print axioms RamanujanTau.SelbergCoeffs2.mertens1_prime
#print axioms RamanujanTau.SelbergCoeffs2.mertens2
#print axioms RamanujanTau.SelbergCoeffs2.mertens2_bound
