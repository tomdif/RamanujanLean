/-
# Andrews' Bailey pair for the fifth-order mock theta function `f₁`

Relative to `a = q`,

  `βₙ = 1/(−q;q)ₙ`,   `αₙ = q^{(3n²+n)/2} (1 − q^{2n+1})/(1 − q) · Sₙ`,   `Sₙ = Σ_{|j|≤n} (−1)ʲ q^{−j²}`

is a Bailey pair (`isBaileyPairQ_f1`); with `q^{n²}Sₙ = V n` (`MockTheta5F0Pair`) the summand is
`F(n,r) = q^{T(r)} V r (1 − q^{2r+1}) / ((q;q)_{n−r} (q;q)_{n+r+1})`, and the creative-telescoping certificate

  `G(n,s) = q^{T(s)+n}/((q;q)_{n−s−1}(q;q)_{n+s+1}) · (−q^{2s+1}(1−qⁿ)(1+q^{s+1}) V s + 2(1 − q^{n+s+1})(−1)^s)`

satisfies `(1−qⁿ)((1+qⁿ)F(n,r) − F(n−1,r)) = G(n,r) − G(n,r−1)` (found by a sympy ansatz). The `a = q` Bailey
transform then gives Andrews' Hecke form
`(q;q)_∞ f₁(q) = Σ_{n≥0} Σ_{|j|≤n} (−1)ʲ q^{n(5n+3)/2 − j²}(1 − q^{2n+1})` (`qfacInf_mul_f1_hecke`).
-/
import RamanujanTau.MockTheta5F0Pair
import RamanujanTau.MockTheta5BaileyQTransform

set_option autoImplicit false

namespace MockTheta5.Bailey
open PowerSeries

/-- the working summand `q^{T(r)} V r (1 − q^{2r+1}) / ((q;q)_{n−r}(q;q)_{n+r+1})`. -/
noncomputable def F1term (n r : ℕ) : PowerSeries ℤ :=
  X ^ triF r * Vth r * (1 - X ^ (2 * r + 1)) * Ring.inverse (qfac (n - r)) * Ring.inverse (qfac (n + r + 1))

/-- the certificate. -/
noncomputable def G1term (n s : ℕ) : PowerSeries ℤ :=
  X ^ (triF s + n) * Ring.inverse (qfac (n - s - 1)) * Ring.inverse (qfac (n + s + 1)) *
    (-(X ^ (2 * s + 1) * (1 - X ^ n) * (1 + X ^ (s + 1)) * Vth s) + 2 * (1 - X ^ (n + s + 1)) * (-1) ^ s)

lemma lem0' (d : ℕ) :
    (1 - X ^ (d + 1)) * ((1 + X ^ (d + 1)) * F1term (d + 1) 0 - F1term d 0) = G1term (d + 1) 0 := by
  simp only [F1term, G1term, Vth, triF, Nat.sub_zero, Nat.add_zero, Nat.add_sub_cancel, mul_zero, zero_add]
  rw [inv_qfac_succ d, inv_qfac_succ (d + 1)]
  ring

lemma lemA1 (s d : ℕ) :
    (1 - X ^ (s + 2 + d)) * ((1 + X ^ (s + 2 + d)) * F1term (s + 2 + d) (s + 1) - F1term (s + 1 + d) (s + 1))
      = G1term (s + 2 + d) (s + 1) - G1term (s + 2 + d) s := by
  simp only [F1term, G1term, Vth, triF]
  simp only [show s + 2 + d - (s + 1) = d + 1 from by omega, show s + 2 + d + (s + 1) + 1 = 2 * s + 4 + d from by omega,
      show s + 1 + d - (s + 1) = d from by omega, show s + 1 + d + (s + 1) + 1 = 2 * s + 3 + d from by omega,
      show s + 2 + d - (s + 1) - 1 = d from by omega, show s + 2 + d - s - 1 = d + 1 from by omega,
      show s + 2 + d + s + 1 = 2 * s + 3 + d from by omega, Nat.add_sub_cancel]
  rw [inv_qfac_succ d, inv_qfac_succ (2 * s + 3 + d), show 2 * s + 3 + d + 1 = 2 * s + 4 + d from by omega]
  simp only [two_mul, pow_add, pow_succ]
  ring

lemma lemB1 (s : ℕ) :
    (1 - X ^ (s + 1)) * ((1 + X ^ (s + 1)) * F1term (s + 1) (s + 1)) = - G1term (s + 1) s := by
  simp only [F1term, G1term, Vth, triF]
  simp only [show s + 1 - (s + 1) = 0 from by omega, show s + 1 + (s + 1) + 1 = 2 * s + 2 + 1 from by omega,
      show s + 1 - s - 1 = 0 from by omega, show s + 1 + s + 1 = 2 * s + 2 from by omega]
  rw [inv_qfac_succ (2 * s + 2)]
  simp only [two_mul, pow_add, pow_succ, qfac_zero, Ring.inverse_one]
  ring

noncomputable def S1sum (n : ℕ) : PowerSeries ℤ := ∑ r ∈ Finset.range (n + 1), F1term n r

lemma S1sum_rec_mul (m : ℕ) :
    (1 - X ^ (m + 1)) * ((1 + X ^ (m + 1)) * S1sum (m + 1) - S1sum m) = 0 := by
  have hrow : ∀ r ∈ Finset.range (m + 1),
      (1 - X ^ (m + 1)) * ((1 + X ^ (m + 1)) * F1term (m + 1) r - F1term m r)
        = (if r = 0 then G1term (m + 1) 0 else G1term (m + 1) r - G1term (m + 1) (r - 1)) := by
    intro r hr
    rw [Finset.mem_range] at hr
    rcases r with _ | s
    · simpa using lem0' m
    · have h := lemA1 s (m - s - 1)
      rw [show s + 2 + (m - s - 1) = m + 1 from by omega,
          show s + 1 + (m - s - 1) = m from by omega] at h
      simpa using h
  have hsplit : (1 - X ^ (m + 1)) * ((1 + X ^ (m + 1)) * S1sum (m + 1) - S1sum m)
      = ∑ r ∈ Finset.range (m + 1),
          (1 - X ^ (m + 1)) * ((1 + X ^ (m + 1)) * F1term (m + 1) r - F1term m r)
        + (1 - X ^ (m + 1)) * ((1 + X ^ (m + 1)) * F1term (m + 1) (m + 1)) := by
    rw [S1sum, S1sum, Finset.sum_range_succ _ (m + 1)]
    simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  rw [hsplit, Finset.sum_congr rfl hrow, lemB1 m]
  have htel : ∀ k, k ≤ m → ∑ r ∈ Finset.range (k + 1),
      (if r = 0 then G1term (m + 1) 0 else G1term (m + 1) r - G1term (m + 1) (r - 1)) = G1term (m + 1) k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih (by omega), if_neg (by omega), Nat.add_sub_cancel]; ring
  rw [htel m le_rfl]; ring

lemma S1sum_rec (m : ℕ) : (1 + X ^ (m + 1)) * S1sum (m + 1) = S1sum m := by
  have h := S1sum_rec_mul m
  rcases mul_eq_zero.mp h with h0 | h1
  · exact absurd h0 (one_sub_X_pow_ne_zero m)
  · exact sub_eq_zero.mp h1

lemma S1sum_zero : S1sum 0 = 1 := by
  simp only [S1sum, F1term, Finset.sum_range_one, triF, Vth, pow_zero, one_mul, mul_zero, zero_add, pow_one,
    Nat.sub_zero, Nat.add_zero, qfac_zero, Ring.inverse_one, mul_one, zero_add]
  have h2 : (1 - X : PowerSeries ℤ) = qfac 1 := by simp [qfac]
  rw [h2]; exact Ring.mul_inverse_cancel _ (isUnit_qfac 1)

lemma S1sum_eq (n : ℕ) : S1sum n = Ring.inverse (mqfac n) := by
  induction n with
  | zero => rw [S1sum_zero]; simp [mqfac]
  | succ m ih =>
      have hrec := S1sum_rec m
      rw [ih] at hrec
      have hunit : mqfac (m + 1) * S1sum (m + 1) = 1 := by
        rw [mqfac_succ, mul_assoc, hrec, Ring.mul_inverse_cancel _ (isUnit_mqfac m)]
      calc S1sum (m + 1)
          = Ring.inverse (mqfac (m + 1)) * (mqfac (m + 1) * S1sum (m + 1)) := by
            rw [← mul_assoc, Ring.inverse_mul_cancel _ (isUnit_mqfac (m + 1)), one_mul]
        _ = Ring.inverse (mqfac (m + 1)) := by rw [hunit, mul_one]

/-- Andrews' `α` for `f₁` (relative to `a = q`). -/
noncomputable def alphaF1 (n : ℕ) : PowerSeries ℤ :=
  X ^ triF n * Vth n * (1 - X ^ (2 * n + 1)) * Ring.inverse (1 - X)

lemma isUnit_one_sub_X : IsUnit (1 - X : PowerSeries ℤ) := by
  rw [isUnit_iff_constantCoeff]; simp

lemma F1term_eq (n r : ℕ) :
    alphaF1 r * Ring.inverse (qfac (n - r)) * Ring.inverse (q2fac (n + r)) = F1term n r := by
  rw [alphaF1, F1term, inv_q2fac]
  have h := Ring.inverse_mul_cancel _ isUnit_one_sub_X
  linear_combination (X ^ triF r * Vth r * (1 - X ^ (2 * r + 1)) * Ring.inverse (qfac (n - r)) *
    Ring.inverse (qfac (n + r + 1))) * h

/-- **Andrews' Bailey pair for `f₁`** (relative to `a = q`). -/
theorem isBaileyPairQ_f1 : IsBaileyPairQ alphaF1 (fun n => Ring.inverse (mqfac n)) := by
  intro n
  show Ring.inverse (mqfac n) = _
  rw [← S1sum_eq n, S1sum]
  exact Finset.sum_congr rfl fun r _ => (F1term_eq n r).symm

/-- Andrews' `n`-th Hecke term for `f₁`: `q^{3T(n)} V n (1 − q^{2n+1})`. -/
noncomputable def heckeF1 (n : ℕ) : PowerSeries ℤ := X ^ (n ^ 2 + n + triF n) * Vth n * (1 - X ^ (2 * n + 1))

end MockTheta5.Bailey

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- Ramanujan's fifth-order mock theta function `f₁(q) = Σ_{n≥0} q^{n²+n}/(−q;q)ₙ`. -/
noncomputable def f1 : PowerSeries ℤ := tsumQsqQ fun n => Ring.inverse (mqfac n)

/-- Andrews' Hecke-type double sum `Σ_{n≥0} Σ_{|j|≤n} (−1)ʲ q^{n(5n+3)/2−j²}(1−q^{2n+1})`. -/
noncomputable def heckeSumF1 : PowerSeries ℤ :=
  mk fun k => coeff k (∑ n ∈ Finset.range (k + 1), heckeF1 n)

/-- **Andrews' Hecke-type identity for `f₁`**: `(q;q)_∞ f₁(q) = Σ_{n≥0} Σ_{|j|≤n} (−1)ʲ q^{n(5n+3)/2−j²}(1−q^{2n+1})`. -/
theorem qfacInf_mul_f1_hecke : qfacInf * f1 = heckeSumF1 := by
  have h := bailey_transform_q isBaileyPairQ_f1
  have h1 : qfacInf * f1 = (1 - X) * tsumQsqQ alphaF1 := by
    rw [f1, h, partitionGF, ← mul_assoc, ← mul_assoc, mul_comm qfacInf (1 - X), mul_assoc (1 - X),
      Ring.mul_inverse_cancel _ isUnit_qfacInf, mul_one]
  have hterm : ∀ j, (1 - X) * (X ^ (j ^ 2 + j) * alphaF1 j) = heckeF1 j := fun j => by
    rw [alphaF1, heckeF1, pow_add]
    have hu := Ring.mul_inverse_cancel _ isUnit_one_sub_X
    linear_combination (X ^ (j ^ 2 + j) * X ^ triF j * Vth j * (1 - X ^ (2 * j + 1))) * hu
  rw [h1]
  ext k
  rw [heckeSumF1, coeff_mk, coeff_prefactor_tsumQsqQ, map_sum]
  simp only [hterm]
  symm
  refine Finset.sum_subset (f := fun n => coeff k (heckeF1 n))
    (Finset.range_subset_range.mpr (show k + 1 ≤ 2 * k + 2 by omega)) fun n _ hn => ?_
  simp only [Finset.mem_range, not_lt] at hn
  show coeff k (heckeF1 n) = 0
  rw [heckeF1, mul_assoc, coeff_X_pow_mul', if_neg (by nlinarith)]

end MockTheta5.JTP
