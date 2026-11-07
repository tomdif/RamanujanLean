/-
# A real-variable Selberg–Delange theorem (logarithmic means), standalone

See `docs/SELBERG_DELANGE.md` §7. Build: `nice -n 10 lake build RamanujanTau.SelbergDelange2.Main`.

* `key_identity`: `(log x − c₀) S(x) = (1+κ) I(x) + R(x)` for `f log = Λ_f ∗ f`.
* `weight_bound`: `Σ_{n≤x} |f(n)|/n/(1+log(x/n)) ≪ (1+log(1+log x))(2+log x)^{σ−1}` from a
  density bound `Σ_{n≤y}|f(n)| ≤ K y (1+log y)^{σ−1}`.
* `limit_of_deriv_bound`: limit with rate from a right-derivative bound.
* `logmean_LSD`: `Σ_{n≤x} f(n)/n = C₁ (log x − c₀)^κ + O((1+log(1+log x))(log x)^{κ−1})`.
-/
import RamanujanTau.SelbergDelange2.LSD

#print axioms RamanujanTau.SelbergDelange2.key_identity
#print axioms RamanujanTau.SelbergDelange2.weight_bound
#print axioms RamanujanTau.SelbergDelange2.Ihat_hasDeriv
#print axioms RamanujanTau.SelbergDelange2.limit_of_deriv_bound
#print axioms RamanujanTau.SelbergDelange2.logmean_LSD
