/-
# Jacobi triple product campaign: the base-q Durfee rectangle identity (heart of L7)

Assembles the finite Durfee rectangle (`inner_inv_gen`) and inverse stabilization into the infinite identity

  **`durfee_rect_base`:**  `Σ_{j≥0} q^{j(j+n)} / ((q;q)_j·(q;q)_{n+j}) = 1/(q;q)_∞`   (for all `n ≥ 0`),

the base-`q` Durfee rectangle (its `n=0` case is the classical Durfee square identity). This is the heart of
the bilateralization step L7 of the Jacobi triple product; applying the base change `E2` (`q ↦ q²`) gives the
`Q = q²` form that L7 needs.

The proof is the `m → ∞` limit of `inner_inv_gen`, realized by coefficient stabilization (no analysis): for
each `coeff k`, take `inner_inv_gen` at `m = 2k+n+1`, replace every `(q;q)_{m-j}⁻¹ / (q;q)_m⁻¹ / (q;q)_{n+m}⁻¹`
by `(q;q)_∞⁻¹` (`coeff_mul_congr_left` + `inv_qfac_dvd`), and the `j`-sum truncates (`X^{j²+nj}`). The limit
naturally yields `(q;q)_∞⁻¹ · (rect sum) = (q;q)_∞⁻²`; multiplying through by `(q;q)_∞` gives the result. No `sorry`.
-/
import RamanujanTau.MockTheta5DurfeeInf

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

noncomputable def rectTerm (n j : ℕ) : PowerSeries ℤ :=
  X ^ (j ^ 2 + n * j) * Ring.inverse (qfac j) * Ring.inverse (qfac (n + j))
noncomputable def rectPartial (n M : ℕ) : PowerSeries ℤ := ∑ j ∈ Finset.range M, rectTerm n j
noncomputable def rectInf (n : ℕ) : PowerSeries ℤ := mk fun k => coeff k (rectPartial n (k + 1))

lemma rectTerm_coeff_zero (n j : ℕ) {k : ℕ} (h : k < j ^ 2 + n * j) : coeff k (rectTerm n j) = 0 := by
  rw [rectTerm, mul_assoc]
  exact MockTheta5.mt_coeff_Xpow_mul_zero _ (j ^ 2 + n * j) k h

lemma coeff_rectInf (n : ℕ) {k M : ℕ} (hM : k + 1 ≤ M) :
    coeff k (rectInf n) = coeff k (rectPartial n M) := by
  have hf : ∀ j, k < j → coeff k (rectTerm n j) = 0 := by
    intro j hj
    refine rectTerm_coeff_zero n j ?_
    have h2 : j ≤ j ^ 2 := Nat.le_self_pow (by norm_num) j
    omega
  rw [rectInf, coeff_mk, rectPartial, rectPartial,
      mt_coeff_sum_eq (rectTerm n) k hf (k + 1) (le_refl (k + 1)),
      mt_coeff_sum_eq (rectTerm n) k hf M hM]

lemma innerTerm_eq (n m j : ℕ) :
    X ^ (j ^ 2 + n * j) * Ring.inverse (qfac j) * Ring.inverse (qfac (m - j)) * Ring.inverse (qfac (n + j))
      = Ring.inverse (qfac (m - j)) * rectTerm n j := by
  rw [rectTerm]; ring

theorem durfee_rect_base (n : ℕ) : rectInf n = Ring.inverse qfacInf := by
  have key : Ring.inverse qfacInf * rectInf n = Ring.inverse qfacInf * Ring.inverse qfacInf := by
    ext k
    set mm := 2 * k + n + 1 with hmm
    have hdvd : (X : PowerSeries ℤ) ^ (k + 1) ∣ (rectInf n - rectPartial n (mm + 1)) := by
      rw [PowerSeries.X_pow_dvd_iff]; intro i hi
      rw [map_sub, coeff_rectInf n (show i + 1 ≤ mm + 1 by omega), sub_self]
    have step1 : coeff k (Ring.inverse qfacInf * rectInf n)
        = coeff k (Ring.inverse qfacInf * rectPartial n (mm + 1)) := by
      rw [mul_comm (Ring.inverse qfacInf) (rectInf n),
          mul_comm (Ring.inverse qfacInf) (rectPartial n (mm + 1))]
      exact coeff_mul_congr_left hdvd
    have hpert : ∀ j ∈ Finset.range (mm + 1),
        coeff k (X ^ (j ^ 2 + n * j) * Ring.inverse (qfac j) * Ring.inverse (qfac (mm - j))
            * Ring.inverse (qfac (n + j)))
          = coeff k (Ring.inverse qfacInf * rectTerm n j) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [innerTerm_eq n mm j]
      by_cases hjk : j ≤ k
      · exact coeff_mul_congr_left (inv_qfac_dvd (show k + 1 ≤ mm - j by omega))
      · have hjk' : k < j := Nat.lt_of_not_le hjk
        have hkj : k < j ^ 2 + n * j := by
          have h2 : j ≤ j ^ 2 := Nat.le_self_pow (by norm_num) j
          omega
        have e1 : Ring.inverse (qfac (mm - j)) * rectTerm n j
            = X ^ (j ^ 2 + n * j) * (Ring.inverse (qfac (mm - j)) * Ring.inverse (qfac j)
                * Ring.inverse (qfac (n + j))) := by rw [rectTerm]; ring
        have e2 : Ring.inverse qfacInf * rectTerm n j
            = X ^ (j ^ 2 + n * j) * (Ring.inverse qfacInf * Ring.inverse (qfac j)
                * Ring.inverse (qfac (n + j))) := by rw [rectTerm]; ring
        rw [e1, e2, MockTheta5.mt_coeff_Xpow_mul_zero _ _ k hkj,
            MockTheta5.mt_coeff_Xpow_mul_zero _ _ k hkj]
    have hLHS : coeff k (∑ j ∈ Finset.range (mm + 1),
        X ^ (j ^ 2 + n * j) * Ring.inverse (qfac j) * Ring.inverse (qfac (mm - j)) * Ring.inverse (qfac (n + j)))
          = coeff k (Ring.inverse qfacInf * rectPartial n (mm + 1)) := by
      rw [map_sum, Finset.sum_congr rfl hpert, ← map_sum, rectPartial, Finset.mul_sum]
    have hRHS : coeff k (Ring.inverse (qfac mm) * Ring.inverse (qfac (n + mm)))
        = coeff k (Ring.inverse qfacInf * Ring.inverse qfacInf) := by
      rw [coeff_mul_congr_left (inv_qfac_dvd (show k + 1 ≤ mm by omega)),
          mul_comm (Ring.inverse qfacInf) (Ring.inverse (qfac (n + mm))),
          coeff_mul_congr_left (inv_qfac_dvd (show k + 1 ≤ n + mm by omega)),
          mul_comm (Ring.inverse qfacInf) (Ring.inverse qfacInf)]
    rw [step1, ← hLHS, inner_inv_gen mm n, hRHS]
  calc rectInf n
      = qfacInf * (Ring.inverse qfacInf * rectInf n) := by
        rw [← mul_assoc, Ring.mul_inverse_cancel qfacInf isUnit_qfacInf, one_mul]
    _ = qfacInf * (Ring.inverse qfacInf * Ring.inverse qfacInf) := by rw [key]
    _ = Ring.inverse qfacInf := by
        rw [← mul_assoc, Ring.mul_inverse_cancel qfacInf isUnit_qfacInf, one_mul]
