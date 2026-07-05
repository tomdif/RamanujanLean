/-
# Euler pentagonal number theorem — stone 1: the shifted theta `Σ_{n∈ℤ} zⁿ q^{(3n²−n)/2}`

Target: **`(q;q)_∞ = Σ_{n∈ℤ} (−1)ⁿ q^{n(3n−1)/2}`** (Euler's pentagonal number theorem), the last classical
input for Ramanujan's `p(5n+4) ≡ 0 (mod 5)` (Jacobi's cube — the harder input — is already proven).

Route (avoids the non-unit `ℤ((q))` wall): build the **shifted base-`q³` triangular Jacobi triple product**

  `Σ_{n∈ℤ} zⁿ q^{(3n²−n)/2} = (q³;q³)_∞ · ∏_{i≥0}(1+z q^{3i+1}) · ∏_{i≥1}(1+z⁻¹ q^{3i−1})`,

then evaluate at `z = −1` (a **unit** — no `ℤ((q))` needed), giving `Σ(−1)ⁿq^{(3n²−n)/2} = (q;q)_∞` since the
three product families `∏(1−q^{3i})∏(1−q^{3i+1})∏(1−q^{3i+2})` reassemble to `∏_{k≥1}(1−qᵏ)`.

**This file (stone 1):** the right-hand-*series* object `pentTheta = Σ zⁿ q^{(3n²−n)/2}`. The exponent
`e(n)=(3n²−n)/2` is **injective** on `ℤ` (generalized pentagonal numbers `0,1,2,5,7,12,15,…`), so unlike the
triangular theta the `n` and `−n` terms carry *different* exponents: `e(m+1)=(m+1)(3m+2)/2`,
`e(−(m+1))=(m+1)(3m+4)/2`. Built by coefficient stabilization (exponents grow quadratically). No `sorry`.

**Remaining stones (multi-session):** shifted one-sided products `∏(1+zq^{3i+1})`, `∏(1+z⁻¹q^{3i−1})` (base-`q³`
Cauchy via `E3 = expand 3`); base-`q³` Durfee (`E3` of `durfee_rect_base`); the bilateral assembly; then the
`z=−1` evaluation and the `∏(1−q^{3i+a})` reassembly to `(q;q)_∞`.
-/
import RamanujanTau.MockTheta5JacobiBilateral

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-- the smaller exponent `e(m+1) = (m+1)(3m+2)/2` dominates `m+1` (fast quadratic growth). -/
lemma pentExp_ge (m : ℕ) : m + 1 ≤ (m + 1) * (3 * m + 2) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  nlinarith [Nat.zero_le m]

/-- the paired `n = ±(m+1)` term with the two *distinct* pentagonal exponents. -/
noncomputable def pentTermP (m : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  X ^ ((m + 1) * (3 * m + 2) / 2) * PowerSeries.C (T ((m : ℤ) + 1))
    + X ^ ((m + 1) * (3 * m + 4) / 2) * PowerSeries.C (T (-((m : ℤ) + 1)))

/-- finite truncation `1 + Σ_{m<M} pentTermP m` (the `1` is the `n=0` term). -/
noncomputable def pentFiniteP (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  1 + ∑ m ∈ Finset.range M, pentTermP m

/-- **`Σ_{n∈ℤ} zⁿ q^{(3n²−n)/2}`**, the RHS series of the shifted base-`q³` JTP. -/
noncomputable def pentTheta : PowerSeries (LaurentPolynomial ℤ) :=
  mk fun k => coeff k (pentFiniteP (k + 1))

lemma coeff_pentTermP_zero {m k : ℕ} (h : k < (m + 1) * (3 * m + 2) / 2) :
    coeff k (pentTermP m) = 0 := by
  have hle : (m + 1) * (3 * m + 2) / 2 ≤ (m + 1) * (3 * m + 4) / 2 :=
    Nat.div_le_div_right (by nlinarith)
  rw [pentTermP, map_add, coeff_X_pow_mul', coeff_X_pow_mul',
      if_neg (Nat.not_le.mpr h), if_neg (Nat.not_le.mpr (lt_of_lt_of_le h hle)), add_zero]

lemma coeff_pentP_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (pentFiniteP N) = coeff k (pentFiniteP M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : pentFiniteP (N + 1) = pentFiniteP N + pentTermP N := by
          rw [pentFiniteP, pentFiniteP, Finset.sum_range_succ]; ring
        rw [hsucc, map_add, coeff_pentTermP_zero (by have := pentExp_ge N; omega), add_zero,
            ih (by omega)]
      · rw [show M = N + 1 from by omega]

lemma coeff_pentTheta {k M : ℕ} (hM : k + 1 ≤ M) :
    coeff k pentTheta = coeff k (pentFiniteP M) := by
  rw [pentTheta, coeff_mk, coeff_pentP_stable (Nat.lt_succ_self k) hM]

/-- Correctness: constant term is `1` (the `n=0` term). -/
lemma coeff_zero_pentTheta : coeff 0 pentTheta = 1 := by
  rw [coeff_pentTheta (le_refl 1), pentFiniteP, Finset.sum_range_one, map_add,
      coeff_pentTermP_zero (by norm_num)]
  simp

/-- Correctness: `q¹` coefficient is `z` (the `n=1` term, `e(1)=1`). -/
lemma coeff_one_pentTheta : coeff 1 pentTheta = T 1 := by
  rw [coeff_pentTheta (show 1 + 1 ≤ 2 from le_refl 2), pentFiniteP, Finset.sum_range_succ,
      Finset.sum_range_one, map_add, map_add,
      show coeff 1 (1 : PowerSeries (LaurentPolynomial ℤ)) = 0 by
        rw [← map_one (PowerSeries.C (R := LaurentPolynomial ℤ)), coeff_C]; norm_num,
      coeff_pentTermP_zero (show (1 : ℕ) < (1 + 1) * (3 * 1 + 2) / 2 by norm_num), add_zero, zero_add,
      pentTermP, map_add, coeff_X_pow_mul', coeff_X_pow_mul']
  norm_num [coeff_C]
end MockTheta5.JTP
