/-
# Tauberian step 2: bounding the exponential-Riesz mean
-/
import RamanujanTau.SCSProof.Tauber1

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Complex Filter
open RamanujanTau.RankinError
open scoped Real

/-- The exponential-Riesz mean `R(x) = Σ_n a_n (1 − e^{(n−x)/L})₊`. -/
noncomputable def Rmean (h : ℕ) (x L : ℝ) : ℝ := ∑' n : ℕ, aR h n * phi 1 (Real.exp ((n - x) / L))

/-- `I₂ = ∫ (1+|y|)^{−2}` and `I₃₂ = ∫ (1+|y|)^{−3/2}`. -/
noncomputable def I2 : ℝ := ∫ y : ℝ, (1 + ‖y‖) ^ (-(2 : ℝ))
noncomputable def I32 : ℝ := ∫ y : ℝ, (1 + ‖y‖) ^ (-(3 / 2 : ℝ))

lemma int2 : Integrable fun y : ℝ => (1 + ‖y‖) ^ (-(2 : ℝ)) := integrable_one_add_norm (by simp)
lemma int32 : Integrable fun y : ℝ => (1 + ‖y‖) ^ (-(3 / 2 : ℝ)) :=
  integrable_one_add_norm (by simp; norm_num)

lemma Pk1_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ ≤ 1) (y : ℝ) :
    ‖Pk 1 ((σ₀ : ℂ) + y * I)‖ ≤ (2 / σ₀) ^ 2 * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  have := Pk_line_le 1 h0 y
  rw [min_eq_left h1] at this
  refine this.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  simp [div_eq_mul_inv]

set_option maxHeartbeats 2000000 in
/-- **Bound for the exponential-Riesz mean.** -/
theorem Rmean_le (K C₀ : ℝ) (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hpt : ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 → (h : ℝ) * σ ≤ 1 →
      ‖Gh h ((σ : ℂ) + v * I)‖ ≤ K * h * (|2 * v / σ| + 3) ^ 32 * σ ^ (-(477 / 40 : ℝ)))
    (hlap : ∀ (h : ℕ) (σ : ℝ), 0 < σ →
      Summable (fun n : ℕ => aabs h n * Real.exp (-n * σ)) ∧
        ∑' n : ℕ, aabs h n * Real.exp (-n * σ) ≤ (1 + Real.exp (h * σ)) / 2 * (C₀ * σ ^ (-(12 : ℝ))))
    (h : ℕ) (hh : 1 ≤ h) {x : ℝ} (hx : 1 ≤ x) (hhx : (h : ℝ) ≤ x) {σ₀ Y₀ : ℝ} (hσ0 : 0 < σ₀)
    (hσ1 : σ₀ ≤ 1) (hY0 : 1 ≤ Y₀) :
    2 * π * |Rmean h x (x * σ₀)| ≤ Real.exp 1 * (2 / σ₀) ^ 2 *
      (I2 * (K * h * (2 * Y₀ / σ₀ + 3) ^ 32 * x ^ (477 / 40 : ℝ)) +
        I32 * Y₀ ^ (-(1 / 2 : ℝ)) * (2 * C₀ * x ^ 12)) := by
  have hx0 : 0 < x := by linarith
  set L := x * σ₀ with hLdef
  have hL : 0 < L := by positivity
  have hLx : L / x = σ₀ := by rw [hLdef]; field_simp
  obtain ⟨hsum, hbd⟩ := hlap h (1 / x) (by positivity)
  have hR := laplace_riesz h hx0 hL hsum
  rw [hLx] at hR
  have hT : ∑' n : ℕ, aabs h n * Real.exp (-n * (1 / x)) ≤ 2 * C₀ * x ^ 12 := by
    have := laplace_le_of hC₀ h (s := 1 / x) (by positivity) (by
      rw [mul_one_div, div_le_one hx0]; exact hhx) hbd
    simpa using this
  -- pointwise bound on the integrand
  set Gm := K * h * (2 * Y₀ / σ₀ + 3) ^ 32 * x ^ (477 / 40 : ℝ)
  set Gt := 2 * C₀ * x ^ 12
  have hGm0 : 0 ≤ Gm := by positivity
  have hGt0 : 0 ≤ Gt := by positivity
  have hbound : ∀ y : ℝ, ‖cexp (x * ((σ₀ : ℂ) + y * I) / L) * Pk 1 ((σ₀ : ℂ) + y * I) *
      Gh h (((σ₀ : ℂ) + y * I) / L)‖ ≤ Real.exp 1 * (2 / σ₀) ^ 2 *
        ((1 + ‖y‖) ^ (-(2 : ℝ)) * Gm + (1 + ‖y‖) ^ (-(3 / 2 : ℝ)) * Y₀ ^ (-(1 / 2 : ℝ)) * Gt) := by
    intro y
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have hre : (x * ((σ₀ : ℂ) + y * I) / L).re = 1 := by
      rw [hLdef]; simp [Complex.div_re]; field_simp
    rw [hre]
    have hP := Pk1_le hσ0 hσ1 y
    have hW : ((σ₀ : ℂ) + y * I) / L = ((1 / x : ℝ) : ℂ) + ((y / L : ℝ) : ℂ) * I := by
      have hσC : (σ₀ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
      have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
      rw [hLdef]; push_cast; field_simp
    rw [hW]
    have hGtriv : ‖Gh h (((1 / x : ℝ) : ℂ) + ((y / L : ℝ) : ℂ) * I)‖ ≤ Gt := by
      refine (norm_Gh_le h _ ?_).trans ?_
      · simpa using hsum
      · simpa using hT
    have hp0 : 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) := by positivity
    have hp1 : 0 ≤ (1 + ‖y‖) ^ (-(3 / 2 : ℝ)) * Y₀ ^ (-(1 / 2 : ℝ)) := by positivity
    by_cases hy : |y| ≤ Y₀
    · have hG := hpt h hh (1 / x) (y / L) (by positivity) (by rw [div_le_one hx0]; exact hx)
        (by rw [mul_one_div, div_le_one hx0]; exact hhx)
      have hθ : |2 * (y / L) / (1 / x)| ≤ 2 * Y₀ / σ₀ := by
        rw [hLdef]
        have : 2 * (y / (x * σ₀)) / (1 / x) = 2 * y / σ₀ := by field_simp
        rw [this, abs_div, abs_mul, abs_of_pos hσ0, abs_two]
        gcongr
      have hxp : (1 / x) ^ (-(477 / 40 : ℝ)) = x ^ (477 / 40 : ℝ) := by
        rw [one_div, Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le, neg_neg]
      rw [hxp] at hG
      have hG' : ‖Gh h (((1 / x : ℝ) : ℂ) + ((y / L : ℝ) : ℂ) * I)‖ ≤ Gm := by
        refine hG.trans ?_
        show _ ≤ K * h * (2 * Y₀ / σ₀ + 3) ^ 32 * x ^ (477 / 40 : ℝ)
        gcongr
      calc Real.exp 1 * ‖Pk 1 ((σ₀ : ℂ) + y * I)‖ * ‖Gh h _‖
          ≤ Real.exp 1 * ((2 / σ₀) ^ 2 * (1 + ‖y‖) ^ (-(2 : ℝ))) * Gm := by gcongr
        _ ≤ Real.exp 1 * (2 / σ₀) ^ 2 * ((1 + ‖y‖) ^ (-(2 : ℝ)) * Gm +
            (1 + ‖y‖) ^ (-(3 / 2 : ℝ)) * Y₀ ^ (-(1 / 2 : ℝ)) * Gt) := by
          have : 0 ≤ (1 + ‖y‖) ^ (-(3 / 2 : ℝ)) * Y₀ ^ (-(1 / 2 : ℝ)) * Gt := by positivity
          have : 0 ≤ Real.exp 1 * (2 / σ₀) ^ 2 := by positivity
          nlinarith
    · push Not at hy
      have hsplit : (1 + ‖y‖) ^ (-(2 : ℝ)) ≤ (1 + ‖y‖) ^ (-(3 / 2 : ℝ)) * Y₀ ^ (-(1 / 2 : ℝ)) := by
        have hy1 : Y₀ ≤ 1 + ‖y‖ := by rw [Real.norm_eq_abs]; linarith
        have e : (1 + ‖y‖) ^ (-(2 : ℝ)) = (1 + ‖y‖) ^ (-(3 / 2 : ℝ)) * (1 + ‖y‖) ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_add (by positivity)]; norm_num
        rw [e]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by linarith) hy1 (by norm_num : (-(1 / 2 : ℝ)) ≤ 0))
          (by positivity)
      calc Real.exp 1 * ‖Pk 1 ((σ₀ : ℂ) + y * I)‖ * ‖Gh h _‖
          ≤ Real.exp 1 * ((2 / σ₀) ^ 2 * (1 + ‖y‖) ^ (-(2 : ℝ))) * Gt := by gcongr
        _ ≤ Real.exp 1 * ((2 / σ₀) ^ 2 * ((1 + ‖y‖) ^ (-(3 / 2 : ℝ)) * Y₀ ^ (-(1 / 2 : ℝ)))) * Gt := by
          gcongr
        _ ≤ Real.exp 1 * (2 / σ₀) ^ 2 * ((1 + ‖y‖) ^ (-(2 : ℝ)) * Gm +
            (1 + ‖y‖) ^ (-(3 / 2 : ℝ)) * Y₀ ^ (-(1 / 2 : ℝ)) * Gt) := by
          have : 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) * Gm := by positivity
          have : 0 ≤ Real.exp 1 * (2 / σ₀) ^ 2 := by positivity
          nlinarith
  have hint : Integrable fun y : ℝ => Real.exp 1 * (2 / σ₀) ^ 2 *
      ((1 + ‖y‖) ^ (-(2 : ℝ)) * Gm + (1 + ‖y‖) ^ (-(3 / 2 : ℝ)) * Y₀ ^ (-(1 / 2 : ℝ)) * Gt) :=
    ((int2.mul_const _).add ((int32.mul_const _).mul_const _)).const_mul _
  have hnorm := norm_integral_le_of_norm_le hint (Eventually.of_forall hbound)
  rw [← hR] at hnorm
  rw [integral_const_mul, integral_add (int2.mul_const _) ((int32.mul_const _).mul_const _),
    integral_mul_const, integral_mul_const, integral_mul_const] at hnorm
  have hRe : ‖(2 * π : ℂ) * ∑' n : ℕ, (aR h n : ℂ) * (phi 1 (Real.exp ((n - x) / L)) : ℂ)‖ =
      2 * π * |Rmean h x L| := by
    unfold Rmean
    rw [norm_mul]
    have : (∑' n : ℕ, (aR h n : ℂ) * (phi 1 (Real.exp ((n - x) / L)) : ℂ)) =
        ((∑' n : ℕ, aR h n * phi 1 (Real.exp ((n - x) / L)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]; push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    congr 1
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [hRe] at hnorm
  refine hnorm.trans (le_of_eq ?_)
  unfold I2 I32
  ring

end RamanujanTau.SCSProof
