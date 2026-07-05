/-
# Ramanujan's partition congruence `p(5n+4) ≡ 0 (mod 5)` — the full power-series proof

`p(n) = coeff n (1/(q;q)_∞)`.  Over `ZMod 5`, writing `g = Ψ₅(q;q)_∞` (a unit) and using the Frobenius
`g⁵ = expand₅ g`, the reduced generating function satisfies

  **`P_eq`:**  `Ψ₅ partitionGF = Ψ₅((q;q)_∞⁴) · expand₅ (Ψ₅ partitionGF)`.

The right factor `expand₅(·)` is supported on multiples of `5`, so the coefficient of `q^{5n+4}` is a sum of
terms each hitting `coeff_{≡4}((q;q)_∞⁴) = 0` (the arithmetic heart). Hence

  **`five_dvd_coeff_partitionGF`:**  `5 ∣ p(5n+4)`.

No induction, no `sorry`.
-/
import RamanujanTau.MockTheta5Qfac4

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- dilation `q ↦ q⁵` over `ZMod 5`. -/
noncomputable def expand5 : PowerSeries (ZMod 5) →+* PowerSeries (ZMod 5) :=
  (PowerSeries.expand 5 (by norm_num)).toRingHom

lemma coeff_expand5 (n : ℕ) (f : PowerSeries (ZMod 5)) :
    coeff n (expand5 f) = if 5 ∣ n then coeff (n / 5) f else 0 := by
  have h : expand5 f = PowerSeries.expand 5 (by norm_num) f := rfl
  rw [h, PowerSeries.coeff_expand]

private lemma coeff_Ψ5 (n : ℕ) (f : PowerSeries ℤ) :
    coeff n (Ψ5 f) = (Int.castRingHom (ZMod 5)) (coeff n f) := PowerSeries.coeff_map _ _ _

/-- `Ψ₅` commutes with the `q ↦ q⁵` dilation. -/
lemma Ψ5_E5 (f : PowerSeries ℤ) : Ψ5 (E5 f) = expand5 (Ψ5 f) := by
  ext n
  rw [coeff_Ψ5, coeff_expand5]
  have h : E5 f = PowerSeries.expand 5 (by norm_num) f := rfl
  rw [h, PowerSeries.coeff_expand]
  split_ifs with hd
  · rw [coeff_Ψ5]
  · simp

lemma g_unit : IsUnit (Ψ5 qfacInf) := isUnit_qfacInf.map Ψ5

/-- Frobenius, packaged as `g⁵ = expand₅ g`. -/
lemma g_pow5 : (Ψ5 qfacInf) ^ 5 = expand5 (Ψ5 qfacInf) := by rw [frobenius_qfacInf, Ψ5_E5]

lemma Ψ5_partitionGF_mul : Ψ5 partitionGF * Ψ5 qfacInf = 1 := by
  rw [← map_mul, partitionGF, Ring.inverse_mul_cancel _ isUnit_qfacInf, map_one]

/-- **The key relation** `Ψ₅ partitionGF = Ψ₅((q;q)_∞⁴) · expand₅(Ψ₅ partitionGF)`. -/
lemma P_eq : Ψ5 partitionGF = Ψ5 (qfacInf ^ 4) * expand5 (Ψ5 partitionGF) := by
  set g := Ψ5 qfacInf with hg
  set P := Ψ5 partitionGF with hP
  have hu : IsUnit g := g_unit
  have hPg : P * g = 1 := Ψ5_partitionGF_mul
  have hgP : g * P = 1 := by rw [mul_comm]; exact hPg
  have hgexp : g ^ 5 * expand5 P = 1 := by rw [g_pow5, ← map_mul, hgP, map_one]
  have hgx : g * (g ^ 4 * expand5 P) = 1 := by
    rw [← mul_assoc, show g * g ^ 4 = g ^ 5 from by ring]; exact hgexp
  have hPinv : P = Ring.inverse g := by
    calc P = P * 1 := (mul_one _).symm
      _ = P * (g * Ring.inverse g) := by rw [Ring.mul_inverse_cancel g hu]
      _ = (P * g) * Ring.inverse g := by ring
      _ = Ring.inverse g := by rw [hPg, one_mul]
  rw [show Ψ5 (qfacInf ^ 4) = g ^ 4 from by rw [map_pow]]
  conv_lhs => rw [hPinv]
  symm
  calc g ^ 4 * expand5 P = 1 * (g ^ 4 * expand5 P) := (one_mul _).symm
    _ = (Ring.inverse g * g) * (g ^ 4 * expand5 P) := by rw [Ring.inverse_mul_cancel g hu]
    _ = Ring.inverse g * (g * (g ^ 4 * expand5 P)) := by ring
    _ = Ring.inverse g := by rw [hgx, mul_one]

/-- **Ramanujan's congruence, reduced form:** every `q^{5n+4}` coefficient of `1/(q;q)_∞` is `0` mod 5. -/
theorem partition_congruence_mod5 (n : ℕ) : coeff (5 * n + 4) (Ψ5 partitionGF) = 0 := by
  rw [P_eq, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  obtain ⟨a, b⟩ := p
  have hab : a + b = 5 * n + 4 := Finset.mem_antidiagonal.mp hp
  by_cases hb : 5 ∣ b
  · obtain ⟨j, rfl⟩ := hb
    rw [coeff_qfac4_mod5 (show a % 5 = 4 by omega), zero_mul]
  · rw [coeff_expand5, if_neg hb, mul_zero]

/-- **Ramanujan's partition congruence** `5 ∣ p(5n+4)`, where `p(n) = coeff n (1/(q;q)_∞)`. -/
theorem five_dvd_coeff_partitionGF (n : ℕ) : (5 : ℤ) ∣ coeff (5 * n + 4) partitionGF := by
  have h : ((coeff (5 * n + 4) partitionGF : ℤ) : ZMod 5) = 0 := by
    have hh := partition_congruence_mod5 n; rwa [coeff_Ψ5] at hh
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h

end MockTheta5.JTP
