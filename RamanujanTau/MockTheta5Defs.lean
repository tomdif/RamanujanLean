/-
# F₀, χ₀, φ₀ as formal power series (5th-order mock theta, rung-3 layer-1)

Builds on the q-Pochhammer foundation (`MockTheta5Series`) and the summable-family rung
(`MockTheta5Lemmas`: `mt_coeff_Xpow_mul_zero`, `mt_coeff_sum_eq`) to give three of the fifth-order mock theta
functions as genuine elements of `PowerSeries ℤ`:

  F₀(q) = Σ_n q^{2n²}/(q;q²)_n        χ₀(q) = Σ_n q^n/(q^{n+1};q)_n        φ₀(q) = Σ_n q^{n²}(−q;q²)_n

Each is defined by its coefficient function — coeff k is the FINITE sum over the first k+1 terms — and the
summable-family lemmas prove that finite sum equals the coefficient of *any* longer partial sum, so these are
the honest infinite sums (no `tsum`/topology needed). The denominators `(q;q²)_n`, `(q^{n+1};q)_n` are units
(constant term 1), so their `Ring.inverse` is a genuine power series.

No `sorry`. (Namespaced `MockTheta5.Formal` to avoid clashing with the truncated `List ℤ` versions in
`MockTheta5.lean`, which were the rung-2 native_decide objects.)
-/
import RamanujanTau.MockTheta5Lemmas
import Mathlib.RingTheory.PowerSeries.Inverse

namespace MockTheta5.Formal
open PowerSeries

/-- general two-parameter q-Pochhammer `(a;q)_n = ∏_{k<n} (1 - a·qᵏ)` over `ℤ`-power series. -/
noncomputable def qpochG (a q : PowerSeries ℤ) (n : ℕ) : PowerSeries ℤ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)

lemma constantCoeff_qpochG (a q : PowerSeries ℤ) (ha : constantCoeff a = 0) (n : ℕ) :
    constantCoeff (qpochG a q n) = 1 := by
  induction n with
  | zero => simp [qpochG]
  | succ k ih =>
      have h1 : constantCoeff (1 - a * q ^ k) = 1 := by
        rw [map_sub, map_one, map_mul, ha, zero_mul, sub_zero]
      rw [qpochG, Finset.prod_range_succ, ← qpochG, map_mul, ih, h1, mul_one]

/-- the `(q;q²)_n`, `(q^{n+1};q)_n` denominators are units, so `1/(…)` is a genuine power series. -/
lemma isUnit_qpochG (a q : PowerSeries ℤ) (ha : constantCoeff a = 0) (n : ℕ) :
    IsUnit (qpochG a q n) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_qpochG a q ha n]; exact isUnit_one

/-- summand of `F₀ = Σ q^{2n²}/(q;q²)_n`. -/
noncomputable def F0term (n : ℕ) : PowerSeries ℤ := X ^ (2 * (n * n)) * Ring.inverse (qpochG X (X ^ 2) n)
/-- summand of `χ₀ = Σ q^n/(q^{n+1};q)_n`. -/
noncomputable def chi0term (n : ℕ) : PowerSeries ℤ := X ^ n * Ring.inverse (qpochG (X ^ (n + 1)) X n)
/-- summand of `φ₀ = Σ q^{n²}(−q;q²)_n`. -/
noncomputable def phi0term (n : ℕ) : PowerSeries ℤ := X ^ (n * n) * qpochG (-X) (X ^ 2) n

/-- **F₀ as a formal power series.** -/
noncomputable def F0   : PowerSeries ℤ := mk fun k => coeff k (∑ n ∈ Finset.range (k + 1), F0term n)
/-- **χ₀ as a formal power series.** -/
noncomputable def chi0 : PowerSeries ℤ := mk fun k => coeff k (∑ n ∈ Finset.range (k + 1), chi0term n)
/-- **φ₀ as a formal power series.** -/
noncomputable def phi0 : PowerSeries ℤ := mk fun k => coeff k (∑ n ∈ Finset.range (k + 1), phi0term n)

-- term n lives in degree ≥ n, so it cannot affect coefficient k < n (the orders → ∞ condition).
lemma F0term_vanish {k n : ℕ} (h : k < n) : coeff k (F0term n) = 0 := by
  unfold F0term; apply mt_coeff_Xpow_mul_zero
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) h
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  omega

lemma chi0term_vanish {k n : ℕ} (h : k < n) : coeff k (chi0term n) = 0 := by
  unfold chi0term; exact mt_coeff_Xpow_mul_zero _ n k h

lemma phi0term_vanish {k n : ℕ} (h : k < n) : coeff k (phi0term n) = 0 := by
  unfold phi0term; apply mt_coeff_Xpow_mul_zero
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) h
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  omega

-- the definitions ARE the infinite sums: coeff k agrees with ANY partial sum of ≥ k+1 terms.
lemma coeff_F0 {k M : ℕ} (hM : k + 1 ≤ M) :
    coeff k F0 = coeff k (∑ n ∈ Finset.range M, F0term n) := by
  unfold F0
  rw [coeff_mk, mt_coeff_sum_eq F0term k (fun n hn => F0term_vanish hn) (k + 1) le_rfl,
      mt_coeff_sum_eq F0term k (fun n hn => F0term_vanish hn) M hM]

lemma coeff_chi0 {k M : ℕ} (hM : k + 1 ≤ M) :
    coeff k chi0 = coeff k (∑ n ∈ Finset.range M, chi0term n) := by
  unfold chi0
  rw [coeff_mk, mt_coeff_sum_eq chi0term k (fun n hn => chi0term_vanish hn) (k + 1) le_rfl,
      mt_coeff_sum_eq chi0term k (fun n hn => chi0term_vanish hn) M hM]

lemma coeff_phi0 {k M : ℕ} (hM : k + 1 ≤ M) :
    coeff k phi0 = coeff k (∑ n ∈ Finset.range M, phi0term n) := by
  unfold phi0
  rw [coeff_mk, mt_coeff_sum_eq phi0term k (fun n hn => phi0term_vanish hn) (k + 1) le_rfl,
      mt_coeff_sum_eq phi0term k (fun n hn => phi0term_vanish hn) M hM]

end MockTheta5.Formal
