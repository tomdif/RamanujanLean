import RamanujanTau.TheoremA.HasseSeparation

/-!
# Theta and Hasse divisibility in the binary model

The homogeneous numerator A·δP + k·B·P has complete expansion 12θ(P).
On each affine chart, its Hasse divisibility is unchanged when k is nonzero
in the coefficient field. When k vanishes, the numerator has a Hasse factor.
These are polynomial statements; `BinaryFiltration` and `BinaryFiltrationCycle`
assemble them into the minimum-weight filtration and its cycle laws.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open MvPolynomial

variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]

noncomputable def binaryThetaNumerator (hp5 : 5 ≤ p) (n : ℕ)
    (P : MvPolynomial (Fin 2) F) : MvPolynomial (Fin 2) F :=
  binaryHasse F p hp5 * binarySerre n P +
    C (2 * n : F) * binaryHasseCompanion F p hp5 * P

theorem binaryThetaNumerator_homogeneous (hp5 : 5 ≤ p) (n : ℕ)
    (P : MvPolynomial (Fin 2) F) (hP : BinaryHomogeneous P (2 * n)) :
    BinaryHomogeneous (binaryThetaNumerator hp5 n P) (2 * n + p + 1) := by
  have h1 : BinaryHomogeneous (binaryHasse F p hp5 * binarySerre n P)
      (2 * n + p + 1) := by
    convert (binaryHasse_homogeneous (F := F) hp5).mul (binarySerre_homogeneous n P) using 1
    omega
  have h2 : BinaryHomogeneous (C (2 * n : F) * binaryHasseCompanion F p hp5 * P)
      (2 * n + p + 1) := by
    convert ((binaryHasseCompanion_homogeneous (F := F) hp5).C_mul (2 * n : F)).mul hP using 1
    omega
  exact h1.add h2

theorem binaryEv_thetaNumerator (hp5 : 5 ≤ p) (n : ℕ)
    (P : MvPolynomial (Fin 2) F) (hP : BinaryHomogeneous P (2 * n)) :
    binaryEv F (binaryThetaNumerator hp5 n P) = 12 * Igusa.theta (binaryEv F P) := by
  rw [binaryThetaNumerator, map_add, map_mul, map_mul, map_mul, binaryEv_hasse,
    binaryEv_hasseCompanion, binaryEv_binarySerre n P hP, one_mul]
  have hc : binaryEv F (C (2 * n : F)) = (2 * n : PowerSeries F) := by
    simp only [binaryEv, map_mul, map_ofNat, map_natCast]
  rw [hc, serreSeries]
  push_cast
  ring

private theorem chart_theta_dvd_iff (A B S P : Polynomial F) (k : F)
    (hAB : IsCoprime A B) (hk : k ≠ 0) :
    A ∣ A * S + Polynomial.C k * B * P ↔ A ∣ P := by
  have hC : IsCoprime A (Polynomial.C k) := by
    refine ⟨0, Polynomial.C k⁻¹, ?_⟩
    simp [← map_mul, hk]
  rw [dvd_add_right (dvd_mul_right _ _)]
  exact ⟨(hC.mul_right hAB).dvd_of_dvd_mul_left, fun h => h.mul_left _⟩

/-- Away from weight zero mod p, theta introduces no new Hasse factor in this chart. -/
theorem chartT_hasse_dvd_theta_iff (hp5 : 5 ≤ p) (n : ℕ)
    (P : MvPolynomial (Fin 2) F) (hk : (2 * n : F) ≠ 0) :
    Igusa.chartT (binaryHasse F p hp5) ∣ Igusa.chartT (binaryThetaNumerator hp5 n P) ↔
      Igusa.chartT (binaryHasse F p hp5) ∣ Igusa.chartT P := by
  simpa only [binaryThetaNumerator, map_add, map_mul, Igusa.chartT, aeval_C,
    Polynomial.algebraMap_eq] using
    chart_theta_dvd_iff (Igusa.chartT (binaryHasse F p hp5))
      (Igusa.chartT (binaryHasseCompanion F p hp5)) (Igusa.chartT (binarySerre n P))
      (Igusa.chartT P) (2 * n : F) (binaryHasse_chartT_coprime hp5) hk

/-- The same criterion on the second chart also covers the point at infinity. -/
theorem chartS_hasse_dvd_theta_iff (hp5 : 5 ≤ p) (n : ℕ)
    (P : MvPolynomial (Fin 2) F) (hk : (2 * n : F) ≠ 0) :
    Igusa.chartS (binaryHasse F p hp5) ∣ Igusa.chartS (binaryThetaNumerator hp5 n P) ↔
      Igusa.chartS (binaryHasse F p hp5) ∣ Igusa.chartS P := by
  simpa only [binaryThetaNumerator, map_add, map_mul, Igusa.chartS, aeval_C,
    Polynomial.algebraMap_eq] using
    chart_theta_dvd_iff (Igusa.chartS (binaryHasse F p hp5))
      (Igusa.chartS (binaryHasseCompanion F p hp5)) (Igusa.chartS (binarySerre n P))
      (Igusa.chartS P) (2 * n : F) (binaryHasse_chartS_coprime hp5) hk

/-- At weight zero mod p, the homogeneous theta numerator has a Hasse factor. -/
theorem hasse_dvd_theta_of_weight_zero (hp5 : 5 ≤ p) (n : ℕ)
    (P : MvPolynomial (Fin 2) F) (hk : (2 * n : F) = 0) :
    binaryHasse F p hp5 ∣ binaryThetaNumerator hp5 n P := by
  simp only [binaryThetaNumerator, hk, map_zero, zero_mul, add_zero]
  exact dvd_mul_right _ _

end RamanujanTau.TheoremA
