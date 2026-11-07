/-
# The quadratic exponential-Riesz mean with `h`-exponent `1/22`

Copies of `SCSSharp.Rmean2_le`/`Rmean2_bound` with `√h` replaced by `h^{1/22}`
(input `pointwise_G2`): `|Rmean2 h x (x^{19/20})| ≤ C h^{1/22} x^{12 − 1/22}` for `1 ≤ h ≤ x`.
-/
import RamanujanTau.SCSSharp.Rmean
import RamanujanTau.SCSSharp2.Point

set_option autoImplicit false

namespace RamanujanTau.SCSSharp2

open MeasureTheory Complex Filter
open RamanujanTau.RankinError RamanujanTau.SCSProof RamanujanTau.SCSSharp
open scoped Real

set_option maxHeartbeats 2000000 in
/-- **Bound for the quadratic exponential-Riesz mean.** -/
theorem Rmean2_leG (K C₀ : ℝ) (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hpt : ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 → (h : ℝ) * σ ≤ 1 →
      ‖Gh h ((σ : ℂ) + v * I)‖ ≤ K * (h : ℝ) ^ (1 / 22 : ℝ) * (|2 * v / σ| + 3) * σ ^ (-(1488 / 125 : ℝ)))
    (hlap : ∀ (h : ℕ) (σ : ℝ), 0 < σ →
      Summable (fun n : ℕ => aabs h n * Real.exp (-n * σ)) ∧
        ∑' n : ℕ, aabs h n * Real.exp (-n * σ) ≤ (1 + Real.exp (h * σ)) / 2 * (C₀ * σ ^ (-(12 : ℝ))))
    (h : ℕ) (hh : 1 ≤ h) {x : ℝ} (hx : 1 ≤ x) (hhx : (h : ℝ) ≤ x) {σ₀ : ℝ} (hσ0 : 0 < σ₀) :
    2 * π * |Rmean2 h x (x * σ₀)| ≤
      Real.exp 1 * (48 / σ₀) * I2 * (K * (h : ℝ) ^ (1 / 22 : ℝ) * x ^ (1488 / 125 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  set L := x * σ₀ with hLdef
  have hL : 0 < L := by positivity
  have hLx : L / x = σ₀ := by rw [hLdef]; field_simp
  obtain ⟨hsum, -⟩ := hlap h (1 / x) (by positivity)
  have hR := laplace_rieszK (k := 2) (by norm_num) h hx0 hL hsum
  rw [hLx] at hR
  set Gm := K * (h : ℝ) ^ (1 / 22 : ℝ) * x ^ (1488 / 125 : ℝ)
  have hGm0 : 0 ≤ Gm := by positivity
  have hbound : ∀ y : ℝ, ‖cexp (x * ((σ₀ : ℂ) + y * I) / L) * Pk 2 ((σ₀ : ℂ) + y * I) *
      Gh h (((σ₀ : ℂ) + y * I) / L)‖ ≤
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
    have hxp : (1 / x) ^ (-(1488 / 125 : ℝ)) = x ^ (1488 / 125 : ℝ) := by
      rw [one_div, Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le, neg_neg]
    rw [hxp, hθ] at hG
    have hk := Pk2_mul_le hσ0 y
    calc Real.exp 1 * ‖Pk 2 ((σ₀ : ℂ) + y * I)‖ * ‖Gh h (((1 / x : ℝ) : ℂ) + ((y / L : ℝ) : ℂ) * I)‖
        ≤ Real.exp 1 * ‖Pk 2 ((σ₀ : ℂ) + y * I)‖ *
            (K * (h : ℝ) ^ (1 / 22 : ℝ) * (|2 * y / σ₀| + 3) * x ^ (1488 / 125 : ℝ)) := by gcongr
      _ = Real.exp 1 * Gm * (‖Pk 2 ((σ₀ : ℂ) + y * I)‖ * (|2 * y / σ₀| + 3)) := by ring
      _ ≤ _ := by gcongr
  have hint : Integrable fun y : ℝ => Real.exp 1 * Gm * (48 / σ₀ * (1 + ‖y‖) ^ (-(2 : ℝ))) :=
    (int2.const_mul _).const_mul _
  have hnorm := norm_integral_le_of_norm_le hint (Eventually.of_forall hbound)
  rw [← hR] at hnorm
  rw [integral_const_mul, integral_const_mul] at hnorm
  have hRe : ‖(2 * π : ℂ) * ∑' n : ℕ, (aR h n : ℂ) * (phi 2 (Real.exp ((n - x) / L)) : ℂ)‖ =
      2 * π * |Rmean2 h x L| := by
    unfold Rmean2
    rw [norm_mul]
    have : (∑' n : ℕ, (aR h n : ℂ) * (phi 2 (Real.exp ((n - x) / L)) : ℂ)) =
        ((∑' n : ℕ, aR h n * phi 2 (Real.exp ((n - x) / L)) : ℝ) : ℂ) := by
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
/-- `|Rmean2 h x (x^{19/20})| ≤ C √h x^{12 − 1/22}` for `1 ≤ h ≤ x`. -/
theorem Rmean2_boundG : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℕ, 1 ≤ h → ∀ x : ℝ, 1 ≤ x → (h : ℝ) ≤ x →
    |Rmean2 h x (x * x ^ (-(1 / 20 : ℝ)))| ≤ C * (h : ℝ) ^ (1 / 22 : ℝ) * x ^ (12 - ηs) := by
  obtain ⟨K, hK0, hK⟩ := pointwise_G2
  obtain ⟨C₀, hC₀, hT⟩ := abs_laplace_le
  refine ⟨Real.exp 1 * 48 * I2 * K, by have := I2_nonneg; positivity, fun h hh x hx hhx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hσ0 : 0 < x ^ (-(1 / 20 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hR := Rmean2_leG K C₀ hK0 hC₀ hK hT h hh hx hhx hσ0
  have hI2 := I2_nonneg
  have e : 48 / x ^ (-(1 / 20 : ℝ)) * x ^ (1488 / 125 : ℝ) = 48 * x ^ (5977 / 500 : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hx0.le, neg_neg, mul_assoc, ← Real.rpow_add hx0]
    norm_num
  have hpow : x ^ (5977 / 500 : ℝ) ≤ x ^ (12 - ηs) :=
    Real.rpow_le_rpow_of_exponent_le hx (by unfold ηs; norm_num)
  have h2π : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
  have hRn : 0 ≤ |Rmean2 h x (x * x ^ (-(1 / 20 : ℝ)))| := abs_nonneg _
  have hfin : Real.exp 1 * (48 / x ^ (-(1 / 20 : ℝ))) * I2 * (K * (h : ℝ) ^ (1 / 22 : ℝ) * x ^ (1488 / 125 : ℝ))
      ≤ Real.exp 1 * 48 * I2 * K * (h : ℝ) ^ (1 / 22 : ℝ) * x ^ (12 - ηs) := by
    have : Real.exp 1 * (48 / x ^ (-(1 / 20 : ℝ))) * I2 * (K * (h : ℝ) ^ (1 / 22 : ℝ) * x ^ (1488 / 125 : ℝ))
        = Real.exp 1 * I2 * K * (h : ℝ) ^ (1 / 22 : ℝ) * (48 / x ^ (-(1 / 20 : ℝ)) * x ^ (1488 / 125 : ℝ)) := by
      ring
    rw [this, e]
    have h0 : 0 ≤ Real.exp 1 * I2 * K * (h : ℝ) ^ (1 / 22 : ℝ) := by positivity
    calc Real.exp 1 * I2 * K * (h : ℝ) ^ (1 / 22 : ℝ) * (48 * x ^ (5977 / 500 : ℝ))
        ≤ Real.exp 1 * I2 * K * (h : ℝ) ^ (1 / 22 : ℝ) * (48 * x ^ (12 - ηs)) := by gcongr
      _ = _ := by ring
  have := hR.trans hfin
  nlinarith

end RamanujanTau.SCSSharp2
