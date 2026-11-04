import RamanujanTau.TauDensity.Analytic
import RamanujanTau.TauDensity.Proportion

/-! # Non-vanishing density of Ramanujan's `τ` — headline index

* `card_tau_ne_zero_ge_rpow` (Weil + Rankin–Selberg): `c_ε N^{1/2−ε} ≤ #{n ≤ N : τ(n) ≠ 0}`.
* `card_tau_ne_zero_ge_sqrt` (Lehmer + Hecke, elementary): `⌊√N⌋ ≤ #{n ≤ N : τ(n) ≠ 0}`.
* `card_tau_ne_zero_ge_proportion`: `N(1 − (1 + log N)/10 746 432 000) ≤ #{n ≤ N : τ(n) ≠ 0}`.
* `tau_eq_zero_iff`: `τ(n) = 0 ↔ ∃ p prime, v_p(n) odd ∧ τ(p) = 0`.
* `tau_ne_zero_of_mod691` / `tau_ne_zero_of_no_candidate`: structural non-vanishing.
-/

#print axioms RamanujanTau.TauDensity.card_tau_ne_zero_ge_rpow
#print axioms RamanujanTau.TauDensity.card_tau_ne_zero_ge_sqrt
#print axioms RamanujanTau.TauDensity.card_tau_ne_zero_ge
#print axioms RamanujanTau.TauDensity.card_tau_ne_zero_ge_proportion
#print axioms RamanujanTau.TauDensity.card_tau_ne_zero_ge_nine_tenths
#print axioms RamanujanTau.TauDensity.tau_eq_zero_iff
#print axioms RamanujanTau.TauDensity.tau_ne_zero_of_mod691
#print axioms RamanujanTau.TauDensity.tau_ne_zero_of_no_candidate
#print axioms RamanujanTau.TauDensity.tau_small_mul_sq_ne_zero
#print axioms RamanujanTau.TauDensity.tau_pointwise_weil
