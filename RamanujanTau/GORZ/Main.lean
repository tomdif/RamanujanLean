/-
# Griffin–Ono–Rolen–Zagier for the partition function (headline statements)

* `GORZ.H_alternating`, `GORZ.H_simple_roots`, `GORZ.H_hyperbolic` : Hermite sign alternation / simple real roots.
* `GORZ.tendsto_gam` : `Δ^k w(0)/δ^k → c_k` (GORZ Theorem 3, partition case).
* `GORZ.tendsto_Gn`, `GORZ.tendsto_coeff_Jhat` : renormalized `J^{d,n}` → `H_d(X/2)` pointwise and coefficientwise.
* `GORZ.jensen_eventually_hyperbolic` : `∀ d, ∀ᶠ n, J^{d,n}` hyperbolic.
-/
import RamanujanTau.GORZ.Coeff

set_option autoImplicit false

namespace GORZ

open Filter Polynomial JensenThreshold

/-- explicit-threshold form: for every `d` there is `N` with `J^{d,n}` hyperbolic for all `n ≥ N`. -/
theorem jensen_hyperbolic_from (d : ℕ) : ∃ N : ℕ, JensenTail d N :=
  (eventually_atTop.mp (jensen_eventually_hyperbolic d)).imp fun _ h n hn => h n hn

/-- sanity check against `docs/JENSEN_THRESHOLDS.md`: `H 6 = T_6 = x⁶ − 30x⁴ + 180x² − 120`. -/
example (x : ℝ) : (H 6).eval x = x ^ 6 - 30 * x ^ 4 + 180 * x ^ 2 - 120 := by
  simp [eval_H, Finset.sum_range_succ, cH, Nat.choose]
  ring

/-- and `H 7 = T_7 = x⁷ − 42x⁵ + 420x³ − 840x`. -/
example (x : ℝ) : (H 7).eval x = x ^ 7 - 42 * x ^ 5 + 420 * x ^ 3 - 840 * x := by
  simp [eval_H, Finset.sum_range_succ, cH, Nat.choose]
  ring

end GORZ

#print axioms GORZ.H_alternating
#print axioms GORZ.H_simple_roots
#print axioms GORZ.H_hyperbolic
#print axioms GORZ.newtonId
#print axioms GORZ.tendsto_gam
#print axioms GORZ.tendsto_Gn
#print axioms GORZ.tendsto_coeff_Jhat
#print axioms GORZ.jensen_eventually_hyperbolic
#print axioms GORZ.jensen_hyperbolic_from
