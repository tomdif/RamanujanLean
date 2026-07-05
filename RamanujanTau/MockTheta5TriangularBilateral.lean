/-
# Triangular JTP, stone 3 capstone: the bilateral triangular Jacobi triple product

  **`bilateral_triangular_JTP`:**  `(q;q)_∞ · ∏_{i≥0}(1+z qⁱ) · ∏_{i≥1}(1+z⁻¹ qⁱ) = Σ_{n∈ℤ} zⁿ q^{n(n−1)/2}`.

Proved `zProj`-by-`zProj` (mirror of `bilateral_jacobi_triple_product`): the lifted prefactor `(q;q)_∞`
factors out (z-degree 0), the z-Cauchy product collapses to `q^{C(N,2)}·rectInf N = q^{C(N,2)}/(q;q)_∞`
(`zProj_TZ_TZ1inv` + `durfee_rect_base`, both signs of `N`), leaving `q^{C(N,2)}` which matches
`zProj_triTheta`. The `q^{1/2}`-free base-`q` route; `z = ±1` are units so no `ℤ((q))` wall. No `sorry`.
-/
import RamanujanTau.MockTheta5TriangularConv
import RamanujanTau.MockTheta5TriangularJTP

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- the lifted prefactor `(q;q)_∞` in the z-outer ring (z-degree 0). -/
noncomputable def qfacInfL : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.map (LaurentPolynomial.C) qfacInf

/-- prefactor law: `qfacInfL` is z-degree-0, so it factors out of any z-projection. -/
lemma zProj_qfacInfL_mul (n : ℤ) (Y : PowerSeries (LaurentPolynomial ℤ)) :
    zProj n (qfacInfL * Y) = qfacInf * zProj n Y := by
  ext m
  rw [coeff_zProj, PowerSeries.coeff_mul, laurentSum_apply, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [qfacInfL, PowerSeries.coeff_map, C_mul_apply, coeff_zProj]

/-- `C(n,2)` as the triangular exponent `⌊n(n−1)/2⌋` (`n ≥ 0`). -/
lemma choose_two_toNat (n : ℕ) : n.choose 2 = ((n : ℤ) * ((n : ℤ) - 1) / 2).toNat := by
  rw [Nat.choose_two_right]
  have h : (n : ℤ) * ((n : ℤ) - 1) = ((n * (n - 1) : ℕ) : ℤ) := by
    rcases n with _ | n
    · simp
    · push_cast; ring
  rw [h]; omega

/-- `C(M+1,2)` as the triangular exponent for `n = −M`. -/
lemma choose_two_toNat_neg (M : ℕ) :
    (M + 1).choose 2 = ((-(M : ℤ)) * ((-(M : ℤ)) - 1) / 2).toNat := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  have h : (-(M : ℤ)) * ((-(M : ℤ)) - 1) = (((M + 1) * M : ℕ) : ℤ) := by push_cast; ring
  rw [h]; omega

/-- **The bilateral triangular Jacobi triple product.**
`(q;q)_∞ · ∏_{i≥0}(1+z qⁱ) · ∏_{i≥1}(1+z⁻¹ qⁱ) = Σ_{n∈ℤ} zⁿ q^{n(n−1)/2}`. -/
theorem bilateral_triangular_JTP :
    qfacInfL * triProdQInf * (PowerSeries.map invertHom triProdQ1Inf) = triTheta := by
  rw [← TZ_eq, ← TZ1inv_eq]
  refine zProj_ext (fun n => ?_)
  rw [mul_assoc, zProj_qfacInfL_mul, zProj_triTheta]
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn with N
    rw [zProj_TZ_TZ1inv, durfee_rect_base, ← choose_two_toNat, ← mul_assoc,
        mul_comm qfacInf (X ^ N.choose 2), mul_assoc,
        Ring.mul_inverse_cancel qfacInf isUnit_qfacInf, mul_one]
  · obtain ⟨M, rfl⟩ : ∃ M : ℕ, n = -(M : ℤ) := ⟨n.natAbs, by omega⟩
    rw [zProj_TZ_TZ1inv_neg, durfee_rect_base, ← choose_two_toNat_neg, ← mul_assoc,
        mul_comm qfacInf (X ^ (M + 1).choose 2), mul_assoc,
        Ring.mul_inverse_cancel qfacInf isUnit_qfacInf, mul_one]

end MockTheta5.JTP
