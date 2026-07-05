/-
# The char-5 Frobenius step: `(q;q)_∞⁵ ≡ (q⁵;q⁵)_∞  (mod 5)`

Over `ZMod 5`, freshman's dream `(1−x)⁵ = 1−x⁵` applied to each factor of `(q;q)_∞` gives, after the
`q ↦ q⁵` dilation `E5`,

  **`frobenius_qfacInf`:**  `(Ψ₅ (q;q)_∞)⁵ = Ψ₅ (E5 (q;q)_∞)`,   `Ψ₅ = map (·: ℤ → ZMod 5)`.

The finite identity is per-factor; the infinite one lifts by coefficient stabilization. No `sorry`.
-/
import RamanujanTau.MockTheta5EulerPentagonal
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.ZMod.Basic

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- reduction of coefficients mod 5. -/
noncomputable def Ψ5 : PowerSeries ℤ →+* PowerSeries (ZMod 5) := PowerSeries.map (Int.castRingHom (ZMod 5))

/-- dilation `q ↦ q⁵`. -/
noncomputable def E5 : PowerSeries ℤ →+* PowerSeries ℤ := (PowerSeries.expand 5 (by norm_num)).toRingHom

lemma E5_X : E5 X = X ^ 5 := PowerSeries.expand_X 5 (by norm_num)

lemma E5_qfac (n : ℕ) : E5 (qfac n) = ∏ i ∈ Finset.range n, (1 - X ^ (5 * i + 5)) := by
  rw [qfac, map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [map_sub, map_one, map_pow, E5_X, ← pow_mul, show 5 * (i + 1) = 5 * i + 5 from by ring]

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : CharP (PowerSeries (ZMod 5)) 5 :=
  charP_of_injective_ringHom (PowerSeries.C_injective (R := ZMod 5)) 5

/-- freshman's dream on one factor, over `ZMod 5`. -/
lemma frob_factor (e : ℕ) : ((1 : PowerSeries (ZMod 5)) - X ^ e) ^ 5 = 1 - X ^ (5 * e) := by
  rw [sub_pow_char_of_commute _ (Commute.all _ _), one_pow, ← pow_mul, Nat.mul_comm e 5]

/-- `E5 (q;q)_∞` agrees with `E5 (q;q)_N` up to degree `5N − 1`. -/
lemma coeff_E5_qfacInf {i N : ℕ} (h : i + 1 ≤ 5 * N) :
    coeff i (E5 qfacInf) = coeff i (E5 (qfac N)) := by
  have hdvd : (X : PowerSeries ℤ) ^ (i + 1) ∣ (E5 qfacInf - E5 (qfac N)) := by
    obtain ⟨g, hg⟩ : (X : PowerSeries ℤ) ^ N ∣ (qfacInf - qfac N) := by
      rw [PowerSeries.X_pow_dvd_iff]; intro j hj
      rw [map_sub, coeff_qfacInf (show j + 1 ≤ N by omega), sub_self]
    rw [← map_sub, hg, map_mul, map_pow, E5_X, ← pow_mul]
    exact dvd_mul_of_dvd_left (pow_dvd_pow X (by omega)) _
  obtain ⟨c, hc⟩ := hdvd
  have hz : coeff i (E5 qfacInf) - coeff i (E5 (qfac N)) = 0 := by
    rw [← map_sub, hc]; exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ i (by omega)
  exact sub_eq_zero.mp hz

/-- finite Frobenius: `(Ψ₅ (q;q)_N)⁵ = Ψ₅ (E5 (q;q)_N)`. -/
lemma frobenius_qfac (N : ℕ) : (Ψ5 (qfac N)) ^ 5 = Ψ5 (E5 (qfac N)) := by
  rw [E5_qfac, Ψ5, qfac, map_prod, map_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [map_sub, map_one, map_pow, PowerSeries.map_X]
  rw [frob_factor (i + 1), show 5 * (i + 1) = 5 * i + 5 from by ring]

/-- coefficient equality from a high divisibility of the difference. -/
lemma coeff_congr_of_dvd {f g : PowerSeries (ZMod 5)} {m : ℕ}
    (h : (X : PowerSeries (ZMod 5)) ^ (m + 1) ∣ (f - g)) : coeff m f = coeff m g := by
  obtain ⟨c, hc⟩ := h
  have hz : coeff m f - coeff m g = 0 := by
    rw [← map_sub, hc, coeff_X_pow_mul']
    simp
  exact sub_eq_zero.mp hz

/-- **the char-5 Frobenius step** `(q;q)_∞⁵ ≡ (q⁵;q⁵)_∞  (mod 5)`. -/
lemma frobenius_qfacInf : (Ψ5 qfacInf) ^ 5 = Ψ5 (E5 qfacInf) := by
  ext m
  have hqf : (X : PowerSeries (ZMod 5)) ^ (m + 1) ∣ (Ψ5 qfacInf - Ψ5 (qfac (m + 1))) := by
    rw [PowerSeries.X_pow_dvd_iff]; intro i hi
    rw [map_sub, Ψ5, PowerSeries.coeff_map, PowerSeries.coeff_map,
        coeff_qfacInf (show i + 1 ≤ m + 1 by omega), sub_self]
  have h5 : (X : PowerSeries (ZMod 5)) ^ (m + 1) ∣ ((Ψ5 qfacInf) ^ 5 - (Ψ5 (qfac (m + 1))) ^ 5) :=
    dvd_trans hqf (sub_dvd_pow_sub_pow _ _ 5)
  have hE5 : (X : PowerSeries (ZMod 5)) ^ (m + 1) ∣ (Ψ5 (E5 qfacInf) - Ψ5 (E5 (qfac (m + 1)))) := by
    rw [PowerSeries.X_pow_dvd_iff]; intro i hi
    rw [map_sub, Ψ5, PowerSeries.coeff_map, PowerSeries.coeff_map,
        coeff_E5_qfacInf (show i + 1 ≤ 5 * (m + 1) by omega), sub_self]
  rw [coeff_congr_of_dvd h5, frobenius_qfac, coeff_congr_of_dvd hE5]

end MockTheta5.JTP
