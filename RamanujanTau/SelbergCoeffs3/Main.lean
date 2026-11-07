/-
# SelbergCoeffs3: Mertens rate, two-sided Selberg lemma, logarithmic mean-value theorems

See `docs/SELBERG_COEFFS.md` §7.

Level 1 (axiom-clean, unconditional):
* `mertens2_rate` — `|Σ_{p≤N} λ(p)²/p − log log N − c_Δ| ≤ C/log N` (`N ≥ 2`);
* `logmean_upper` — `f ≥ 0` multiplicative, `f(p^k) ≤ B`, `Σ_{p≤M} f(p)/p ≤ κ log log M + C`
  ⟹ `Σ_{n≤N} f(n)/n ≤ e^{C+2B}(log N)^κ`;
* `logmean_upper_abs` — the same for signed `f` with `|f|` in the hypotheses (no cancellation);
* `logmean_lower` — `f ≥ 0`, `κ ≥ 0`, `f(p) ≤ 2`, `Σ_{p≤M} f(p)log p/p ≤ A log M`,
  `Σ_{p≤M} f(p)/p ≥ κ log log M − C` ⟹ `Σ_{n≤N} f(n)/n ≥ c(log N)^κ`.

Level 2 (`[DeligneBound]`):
* `selberg_two_sided` — `c(log N)^{1/4} ≤ Σ_{n≤N} α(n)²/n ≤ C(log N)^{1/4}`.
-/
import RamanujanTau.SelbergCoeffs3.MertensRate
import RamanujanTau.SelbergCoeffs3.LogMean
import RamanujanTau.SelbergCoeffs3.SelbergTwoSided

#print axioms RamanujanTau.SelbergCoeffs3.mertens2_rate
#print axioms RamanujanTau.SelbergCoeffs3.tail_hh_le
#print axioms RamanujanTau.SelbergCoeffs3.logmean_upper
#print axioms RamanujanTau.SelbergCoeffs3.logmean_upper_abs
#print axioms RamanujanTau.SelbergCoeffs3.logmean_lower
#print axioms RamanujanTau.SelbergCoeffs3.selberg_two_sided
