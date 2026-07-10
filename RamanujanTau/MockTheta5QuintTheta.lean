/-
# Quintuple product identity — stone 1: the right-hand series `Σ_{n∈ℤ}(z^{3n}−z^{−3n−1}) q^{n(3n+1)/2}`

Target (Watson's **quintuple product identity**), the named classical identity still absent from Mathlib
even after the Rogers–Ramanujan / JTP formalization (arXiv 2607.01544), and the exact missing key that turns
the repo's already-proven **sum**-form Rogers–Ramanujan/pentagonal Bailey identities into their celebrated
**product** forms:

  `∏_{n≥1}(1−qⁿ)(1−z qⁿ)(1−z⁻¹ qⁿ⁻¹)(1−z² q^{2n−1})(1−z⁻² q^{2n−1})`
    `= Σ_{n∈ℤ} (z^{3n} − z^{−3n−1}) q^{n(3n+1)/2}`.

Route (same as the pentagonal build — all in `PowerSeries (LaurentPolynomial ℤ)`, keeping `z = T` a **unit**,
so the bilateral `z⁻¹`/`z⁻²` products are legal and no `ℤ((q))` framework is needed): build the product side
via one-sided Cauchy/Durfee `zProj` machinery, prove equality to this series `zProj`-by-`zProj`. The `z²`
factors make the `z`-grading mixed (even and odd `z`-degrees), and the right side is a **difference** of two
theta families — both heavier than the single-theta pentagonal build, hence multi-session.

**This file (stone 1):** the right-hand *series* object `quintTheta`. The `q`-exponent `g(n)=n(3n+1)/2`
is the generalized-pentagonal set `0,1,2,5,7,12,…` (injective on `ℤ`), so `n` and `−n` carry distinct
exponents. Pairing `n = ±(m+1)` around the `n=0` base term `(1 − z⁻¹)`:
`g(−(m+1)) = (m+1)(3m+2)/2` (smaller, reuses `pentExp_ge`), `g(m+1) = (m+1)(3m+4)/2` (larger). Built by
coefficient stabilization (quadratic exponent growth). No `sorry`.

**Remaining stones (multi-session):** the two `z`-side one-sided products `∏(1+z qⁿ)`-type and the two
`z²`-side products `∏(1−z² q^{2n−1})`, `∏(1−z⁻² q^{2n−1})`; the mixed-grading convolution collapse; bilateral
assembly against `qfacInf`; and the `zProj`-by-`zProj` identification with `quintTheta`.
-/
import RamanujanTau.MockTheta5PentTheta

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-- The paired `n = ±(m+1)` term of the quintuple RHS, carrying the two *distinct* pentagonal exponents
`g(−(m+1)) = (m+1)(3m+2)/2` (smaller) and `g(m+1) = (m+1)(3m+4)/2` (larger), with the `z`-parts
`z^{−3(m+1)}−z^{3(m+1)−1}` and `z^{3(m+1)}−z^{−3(m+1)−1}` respectively. -/
noncomputable def quintTermP (m : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  X ^ ((m + 1) * (3 * m + 2) / 2)
      * (PowerSeries.C (T (-3 * (m : ℤ) - 3)) - PowerSeries.C (T (3 * (m : ℤ) + 2)))
    + X ^ ((m + 1) * (3 * m + 4) / 2)
      * (PowerSeries.C (T (3 * (m : ℤ) + 3)) - PowerSeries.C (T (-3 * (m : ℤ) - 4)))

/-- the `n = 0` term of the quintuple RHS: `z⁰ − z⁻¹ = 1 − z⁻¹`. -/
noncomputable def quintBase : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.C (T (0 : ℤ)) - PowerSeries.C (T (-1 : ℤ))

/-- finite truncation `quintBase + Σ_{m<M} quintTermP m`. -/
noncomputable def quintFiniteP (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  quintBase + ∑ m ∈ Finset.range M, quintTermP m

/-- **`Σ_{n∈ℤ} (z^{3n} − z^{−3n−1}) q^{n(3n+1)/2}`**, the RHS series of the quintuple product identity. -/
noncomputable def quintTheta : PowerSeries (LaurentPolynomial ℤ) :=
  mk fun k => coeff k (quintFiniteP (k + 1))

lemma coeff_quintTermP_zero {m k : ℕ} (h : k < (m + 1) * (3 * m + 2) / 2) :
    coeff k (quintTermP m) = 0 := by
  have hle : (m + 1) * (3 * m + 2) / 2 ≤ (m + 1) * (3 * m + 4) / 2 :=
    Nat.div_le_div_right (by nlinarith)
  rw [quintTermP, map_add, coeff_X_pow_mul', coeff_X_pow_mul',
      if_neg (Nat.not_le.mpr h), if_neg (Nat.not_le.mpr (lt_of_lt_of_le h hle)), add_zero]

lemma coeff_quintBase_zero {k : ℕ} (h : 0 < k) : coeff k quintBase = 0 := by
  rw [quintBase, map_sub, coeff_C, coeff_C, if_neg (by omega), if_neg (by omega), sub_zero]

lemma coeff_quintP_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (quintFiniteP N) = coeff k (quintFiniteP M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : quintFiniteP (N + 1) = quintFiniteP N + quintTermP N := by
          rw [quintFiniteP, quintFiniteP, Finset.sum_range_succ]; ring
        rw [hsucc, map_add, coeff_quintTermP_zero (by have := pentExp_ge N; omega), add_zero,
            ih (by omega)]
      · rw [show M = N + 1 from by omega]

lemma coeff_quintTheta {k M : ℕ} (hM : k + 1 ≤ M) :
    coeff k quintTheta = coeff k (quintFiniteP M) := by
  rw [quintTheta, coeff_mk, coeff_quintP_stable (Nat.lt_succ_self k) hM]

/-- Correctness: constant term is `1 − z⁻¹` (the `n = 0` term). -/
lemma coeff_zero_quintTheta : coeff 0 quintTheta = T 0 - T (-1) := by
  rw [coeff_quintTheta (le_refl 1), quintFiniteP, Finset.sum_range_one, map_add,
      coeff_quintTermP_zero (by norm_num), add_zero, quintBase, map_sub, coeff_C, coeff_C]
  simp

/-- Correctness: `q¹` coefficient is `z⁻³ − z²` (the `n = −1` term, `g(−1)=1`). -/
lemma coeff_one_quintTheta : coeff 1 quintTheta = T (-3) - T 2 := by
  rw [coeff_quintTheta (show 1 + 1 ≤ 2 from le_refl 2), quintFiniteP, Finset.sum_range_succ,
      Finset.sum_range_one, map_add, map_add, coeff_quintBase_zero (by norm_num), zero_add,
      coeff_quintTermP_zero (show (1 : ℕ) < (1 + 1) * (3 * 1 + 2) / 2 by norm_num), add_zero,
      quintTermP, map_add, coeff_X_pow_mul', coeff_X_pow_mul']
  norm_num [map_sub, coeff_C]

end MockTheta5.JTP
