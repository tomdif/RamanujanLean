/-
# Quadratic Riesz mean with the `η = 1/21` parameters (weight-`k` copy of `SCSSharp2.Rmean21`)

`RmeanT_bound21`: `|RmeanT h x (x^{1−2/39})| ≤ C h^{1/21} x^{k − 1/21}` from the weight-`k`
pointwise bound with `h^{1/21}` and saving `99/1000` (`GeoPoint21.pointwise_GF21`).
-/
import RamanujanTau.SubconvexGeneral2.TauRiesz
import RamanujanTau.SCSSharp2.Rmean21

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral3

open MeasureTheory Complex Filter
open RamanujanTau.HeckeConvexGeneral RamanujanTau.SubconvexGeneral RamanujanTau.SubconvexGeneral2
open RamanujanTau.RankinError RamanujanTau.SCSProof RamanujanTau.SCSSharp RamanujanTau.SCSSharp2
open scoped MatrixGroups Real

variable {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ))

set_option maxHeartbeats 2000000 in
/-- **Bound for the quadratic exponential-Riesz mean**, weight `k`. -/
theorem RmeanT_le21 (hreal : ∀ n, (coef f n).im = 0) (K : ℝ) (hK : 0 ≤ K)
    (hpt : ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 → (h : ℝ) * σ ≤ 1 →
      ‖GhF f h ((σ : ℂ) + v * I)‖ ≤
        K * (h : ℝ) ^ (1 / 21 : ℝ) * (|2 * v / σ| + 3) * σ ^ (-(k : ℝ) + 99 / 1000))
    (h : ℕ) (hh : 1 ≤ h) {x : ℝ} (hx : 1 ≤ x) (hhx : (h : ℝ) ≤ x) {σ₀ : ℝ} (hσ0 : 0 < σ₀) :
    2 * π * |RmeanT f h x (x * σ₀)| ≤
      Real.exp 1 * (48 / σ₀) * I2 * (K * (h : ℝ) ^ (1 / 21 : ℝ) * x ^ ((k : ℝ) - 99 / 1000)) := by
  have hx0 : 0 < x := by linarith
  set L := x * σ₀ with hLdef
  have hL : 0 < L := by positivity
  have hLx : L / x = σ₀ := by rw [hLdef]; field_simp
  have hsum := summable_aabsT f h (σ := 1 / x) (by positivity)
  have hR := laplace_rieszT f hreal (j := 2) (by norm_num) h hx0 hL hsum
  rw [hLx] at hR
  set Gm := K * (h : ℝ) ^ (1 / 21 : ℝ) * x ^ ((k : ℝ) - 99 / 1000)
  have hGm0 : 0 ≤ Gm := by positivity
  have hbound : ∀ y : ℝ, ‖cexp (x * ((σ₀ : ℂ) + y * I) / L) * Pk 2 ((σ₀ : ℂ) + y * I) *
      GhF f h (((σ₀ : ℂ) + y * I) / L)‖ ≤
        Real.exp 1 * Gm * (48 / σ₀ * (1 + ‖y‖) ^ (-(2 : ℝ))) := by
    intro y
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have hre : (x * ((σ₀ : ℂ) + y * I) / L).re = 1 := by
      rw [hLdef]; simp [Complex.div_re]; field_simp
    rw [hre]
    have hW : ((σ₀ : ℂ) + y * I) / L = ((1 / x : ℝ) : ℂ) + ((y / L : ℝ) : ℂ) * I := by
      have hσC : (σ₀ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
      have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
      rw [hLdef]; push_cast; field_simp
    rw [hW]
    have hG := hpt h hh (1 / x) (y / L) (by positivity) (by rw [div_le_one hx0]; exact hx)
      (by rw [mul_one_div, div_le_one hx0]; exact hhx)
    have hθ : 2 * (y / L) / (1 / x) = 2 * y / σ₀ := by rw [hLdef]; field_simp
    have hxp : (1 / x) ^ (-(k : ℝ) + 99 / 1000) = x ^ ((k : ℝ) - 99 / 1000) := by
      rw [one_div, Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le]
      congr 1; ring
    rw [hxp, hθ] at hG
    have hk := Pk2_mul_le hσ0 y
    calc Real.exp 1 * ‖Pk 2 ((σ₀ : ℂ) + y * I)‖ *
          ‖GhF f h (((1 / x : ℝ) : ℂ) + ((y / L : ℝ) : ℂ) * I)‖
        ≤ Real.exp 1 * ‖Pk 2 ((σ₀ : ℂ) + y * I)‖ *
            (K * (h : ℝ) ^ (1 / 21 : ℝ) * (|2 * y / σ₀| + 3) * x ^ ((k : ℝ) - 99 / 1000)) := by gcongr
      _ = Real.exp 1 * Gm * (‖Pk 2 ((σ₀ : ℂ) + y * I)‖ * (|2 * y / σ₀| + 3)) := by ring
      _ ≤ _ := by gcongr
  have hint : Integrable fun y : ℝ => Real.exp 1 * Gm * (48 / σ₀ * (1 + ‖y‖) ^ (-(2 : ℝ))) :=
    (int2.const_mul _).const_mul _
  have hnorm := norm_integral_le_of_norm_le hint (Eventually.of_forall hbound)
  rw [← hR] at hnorm
  rw [integral_const_mul, integral_const_mul] at hnorm
  have hRe : ‖(2 * π : ℂ) * ∑' n : ℕ, (aT f h n : ℂ) * (phi 2 (Real.exp ((n - x) / L)) : ℂ)‖ =
      2 * π * |RmeanT f h x L| := by
    unfold RmeanT
    rw [norm_mul]
    have : (∑' n : ℕ, (aT f h n : ℂ) * (phi 2 (Real.exp ((n - x) / L)) : ℂ)) =
        ((∑' n : ℕ, aT f h n * phi 2 (Real.exp ((n - x) / L)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]; push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    congr 1
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [hRe] at hnorm
  refine hnorm.trans (le_of_eq ?_)
  unfold I2
  ring

set_option maxHeartbeats 2000000 in
/-- `|RmeanT h x (x^{19/20})| ≤ C √h x^{k − 1/22}` for `1 ≤ h ≤ x`. -/
theorem RmeanT_bound21 (hreal : ∀ n, (coef f n).im = 0)
    (hpw : ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 → (h : ℝ) * σ ≤ 1 →
      ‖GhF f h ((σ : ℂ) + v * I)‖ ≤
        K * (h : ℝ) ^ (1 / 21 : ℝ) * (|2 * v / σ| + 3) * σ ^ (-(k : ℝ) + 99 / 1000)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℕ, 1 ≤ h → ∀ x : ℝ, 1 ≤ x → (h : ℝ) ≤ x →
      |RmeanT f h x (x * x ^ (-(2 / 39 : ℝ)))| ≤ C * (h : ℝ) ^ (1 / 21 : ℝ) * x ^ ((k : ℝ) - ηt) := by
  obtain ⟨K, hK0, hK⟩ := hpw
  refine ⟨Real.exp 1 * 48 * I2 * K, by have := I2_nonneg; positivity, fun h hh x hx hhx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hσ0 : 0 < x ^ (-(2 / 39 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hR := RmeanT_le21 f hreal K hK0 hK h hh hx hhx hσ0
  have hI2 := I2_nonneg
  have e : 48 / x ^ (-(2 / 39 : ℝ)) * x ^ ((k : ℝ) - 99 / 1000) =
      48 * x ^ ((k : ℝ) - 99 / 1000 + 2 / 39) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hx0.le, neg_neg, mul_assoc, ← Real.rpow_add hx0]
    rw [show (2 / 39 : ℝ) + ((k : ℝ) - 99 / 1000) = (k : ℝ) - 99 / 1000 + 2 / 39 by ring]
  have hpow : x ^ ((k : ℝ) - 99 / 1000 + 2 / 39) ≤ x ^ ((k : ℝ) - ηt) :=
    Real.rpow_le_rpow_of_exponent_le hx (by unfold ηt; linarith)
  have h2π : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
  have hRn : 0 ≤ |RmeanT f h x (x * x ^ (-(2 / 39 : ℝ)))| := abs_nonneg _
  have hfin : Real.exp 1 * (48 / x ^ (-(2 / 39 : ℝ))) * I2 *
      (K * (h : ℝ) ^ (1 / 21 : ℝ) * x ^ ((k : ℝ) - 99 / 1000))
      ≤ Real.exp 1 * 48 * I2 * K * (h : ℝ) ^ (1 / 21 : ℝ) * x ^ ((k : ℝ) - ηt) := by
    have : Real.exp 1 * (48 / x ^ (-(2 / 39 : ℝ))) * I2 *
        (K * (h : ℝ) ^ (1 / 21 : ℝ) * x ^ ((k : ℝ) - 99 / 1000))
        = Real.exp 1 * I2 * K * (h : ℝ) ^ (1 / 21 : ℝ) *
          (48 / x ^ (-(2 / 39 : ℝ)) * x ^ ((k : ℝ) - 99 / 1000)) := by
      ring
    rw [this, e]
    have h0 : 0 ≤ Real.exp 1 * I2 * K * (h : ℝ) ^ (1 / 21 : ℝ) := by positivity
    calc Real.exp 1 * I2 * K * (h : ℝ) ^ (1 / 21 : ℝ) * (48 * x ^ ((k : ℝ) - 99 / 1000 + 2 / 39))
        ≤ Real.exp 1 * I2 * K * (h : ℝ) ^ (1 / 21 : ℝ) * (48 * x ^ ((k : ℝ) - ηt)) := by gcongr
      _ = _ := by ring
  have := hR.trans hfin
  nlinarith

end RamanujanTau.SubconvexGeneral3
