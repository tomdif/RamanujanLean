/-
# Euler pentagonal — stone: the bilateral shifted base-`q³` Jacobi triple product

  **`bilateral_pent_JTP`:**  `(q³;q³)_∞ · ∏_{i≥0}(1+z q^{3i+1}) · ∏_{i≥1}(1+z⁻¹ q^{3i−1}) = Σ_{n∈ℤ} zⁿ q^{(3n²−n)/2}`.

Proved `zProj`-by-`zProj` (mirror of `bilateral_triangular_JTP`): the lifted prefactor `(q³;q³)_∞` factors out,
the z-Cauchy product collapses to `q^{e(N)}·E3(rectInf N) = q^{e(N)}/(q³;q³)_∞` (`zProj_PZ_PZ1inv` +
`durfee_rect_base_q3`, both signs), matching `zProj_pentTheta`. No `sorry`.
-/
import RamanujanTau.MockTheta5PentConv
import RamanujanTau.MockTheta5PentThetaProj

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- `n * n = n * (n-1) + n`. -/
private lemma sq_eq (n : ℕ) : n * n = n * (n - 1) + n := by
  rcases n with _ | k
  · rfl
  · rw [show k + 1 - 1 = k from rfl]; ring

/-- `2 ∣ n*(n-1)`. -/
private lemma two_dvd_mul_pred (n : ℕ) : 2 ∣ n * (n - 1) := by
  rcases n with _ | k
  · simp
  · rw [show k + 1 - 1 = k from rfl, Nat.mul_comm]; exact (Nat.even_mul_succ_self k).two_dvd

/-- exponent cast `3·C(N,2)+N = ⌊(3N²−N)/2⌋`. -/
lemma pent_toNat_pos (N : ℕ) : 3 * N.choose 2 + N = ((3 * (N : ℤ) ^ 2 - N) / 2).toNat := by
  have hr := sq_eq N
  have hae := two_dvd_mul_pred N
  have h : (N : ℤ) ^ 2 = ((N * N : ℕ) : ℤ) := by push_cast; ring
  rw [Nat.choose_two_right, h]; omega

/-- exponent cast `3·C(M,2)+2M = ⌊(3M²+M)/2⌋` (the `n = −M` case). -/
lemma pent_toNat_neg (M : ℕ) :
    3 * M.choose 2 + 2 * M = ((3 * (-(M : ℤ)) ^ 2 - -(M : ℤ)) / 2).toNat := by
  have hr := sq_eq M
  have hae := two_dvd_mul_pred M
  have h : 3 * (-(M : ℤ)) ^ 2 - -(M : ℤ) = ((3 * (M * M) + M : ℕ) : ℤ) := by push_cast; ring
  rw [Nat.choose_two_right, h]; omega

/-- lifted prefactor `(q³;q³)_∞`. -/
noncomputable def qfacInfL_q3 : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.map (LaurentPolynomial.C) (E3 qfacInf)

lemma zProj_qfacInfL_q3_mul (n : ℤ) (Y : PowerSeries (LaurentPolynomial ℤ)) :
    zProj n (qfacInfL_q3 * Y) = E3 qfacInf * zProj n Y := by
  ext m
  rw [coeff_zProj, PowerSeries.coeff_mul, laurentSum_apply, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [qfacInfL_q3, PowerSeries.coeff_map, C_mul_apply, coeff_zProj]

/-- **The bilateral shifted base-`q³` Jacobi triple product.** -/
theorem bilateral_pent_JTP :
    qfacInfL_q3 * pentProdAInf * (PowerSeries.map invertHom pentProdBInf) = pentTheta := by
  rw [← PZ_eq, ← PZ1inv_eq]
  refine zProj_ext (fun n => ?_)
  rw [mul_assoc, zProj_qfacInfL_q3_mul, zProj_pentTheta]
  have hu : IsUnit (E3 qfacInf) := isUnit_qfacInf.map E3
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn with N
    rw [zProj_PZ_PZ1inv, durfee_rect_base_q3, ← pent_toNat_pos, ← mul_assoc,
        mul_comm (E3 qfacInf) (X ^ (3 * N.choose 2 + N)), mul_assoc,
        Ring.mul_inverse_cancel _ hu, mul_one]
  · obtain ⟨M, rfl⟩ : ∃ M : ℕ, n = -(M : ℤ) := ⟨n.natAbs, by omega⟩
    rw [zProj_PZ_PZ1inv_neg, durfee_rect_base_q3, ← pent_toNat_neg, ← mul_assoc,
        mul_comm (E3 qfacInf) (X ^ (3 * M.choose 2 + 2 * M)), mul_assoc,
        Ring.mul_inverse_cancel _ hu, mul_one]

end MockTheta5.JTP
