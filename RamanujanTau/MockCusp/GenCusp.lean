/-
# The key lemma with the optimal shift and the pole geometry

`den_lower`: if `ω = e^{iθ}` with `|θ − 2πk| ≥ δ` for all `k`, then on the strip `|Im U| ≤ Y₀` the denominator
`1 − ω e^{−α(DU+E)}` is `≥ min(1, |α| Re(1/α) (δ − D Y₀/Re(1/α)))/3`: its zeros lie at heights
`(θ+2πk) Re(1/α)/D`.

`al_sum_cusp`: `al_sum_le` with `Y₀ = π Re(1/α)/(2TA)` (the optimal shift for the frequency `1/(2T)`), assuming
`δ > πD/(2TA)`:

  `|S| ≤ 3/min(1, |α|Re(1/α)(δ − πD/(2TA))) · e^{c₀ + B² Re α/(4A)} √(π/(A Re α)) / sinh(2c₀)`,
  `c₀ = π² Re(1/α)/(4AT²)`.
-/
import RamanujanTau.MockCusp.ALSum
import RamanujanTau.MockCusp.Denom

set_option autoImplicit false

namespace MockCusp
open Complex Filter MeasureTheory Set
open scoped Topology Real

noncomputable section

lemma re_inv_pos' {α : ℂ} (hα : 0 < α.re) : 0 < (1 / α).re := by
  rw [one_div, inv_re]
  exact div_pos hα (normSq_pos.mpr fun h => by rw [h] at hα; simp at hα)

lemma im_I_mul_div (t : ℝ) (α : ℂ) : (I * t / α).im = t * (1 / α).re := by
  rw [one_div, inv_re, div_eq_mul_inv, mul_im, inv_re, inv_im]
  simp only [mul_re, I_re, ofReal_re, I_im, ofReal_im, mul_im]
  ring

lemma den_lower {α : ℂ} (hα : 0 < α.re) {D E δ Y0 θ : ℝ} (hD : 0 < D)
    (hθ : ∀ k : ℤ, δ ≤ |θ - 2 * π * k|) (x y : ℝ) (hy : |y| ≤ Y0) :
    min 1 (‖α‖ * ((1 / α).re * δ - D * Y0)) / 3 ≤
      ‖1 - cexp (I * θ) * cexp (-(α * (D * ((x : ℂ) + y * I) + E)))‖ := by
  have hα0 : α ≠ 0 := fun h => by rw [h] at hα; simp at hα
  have hR := re_inv_pos' hα
  rw [← Complex.exp_add]
  apply norm_one_sub_exp_ge
  intro k
  set v := I * θ + -(α * (D * ((x : ℂ) + y * I) + E))
  have hdiv : v - 2 * π * I * k = α * ((I * ((θ - 2 * π * k : ℝ) : ℂ)) / α - (D * ((x : ℂ) + y * I) + E)) := by
    simp only [v]; field_simp; push_cast; ring
  rw [hdiv, norm_mul]
  gcongr
  refine le_trans ?_ (abs_im_le_norm _)
  rw [sub_im, im_I_mul_div]
  simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, add_re, mul_re]
  have h1 := hθ k
  have h2 : (1 / α).re * δ ≤ (1 / α).re * |θ - 2 * π * k| := by gcongr
  have h3 : D * y ≤ D * Y0 := by
    have := (le_abs_self y).trans hy; nlinarith
  have h4 : -(D * Y0) ≤ D * y := by
    have := neg_abs_le y; nlinarith
  simp only [zero_mul, mul_zero, add_zero, zero_add, mul_one, sub_zero]
  rcases le_total 0 (θ - 2 * π * k) with hs | hs
  · rw [abs_of_nonneg hs] at h2
    calc (1 / α).re * δ - D * Y0 ≤ (θ - 2 * π * k) * (1 / α).re - D * y := by nlinarith
      _ ≤ _ := le_abs_self _
  · rw [abs_of_nonpos hs] at h2
    calc (1 / α).re * δ - D * Y0 ≤ -((θ - 2 * π * k) * (1 / α).re - D * y) := by nlinarith
      _ ≤ _ := neg_le_abs _

/-- **the key lemma at the optimal shift**. -/
theorem al_sum_cusp {α : ℂ} (hα : 0 < α.re) {A B D E δ : ℝ} (hA : 0 < A) (hD : 0 < D) {T : ℕ} (hT : 0 < T)
    {c : ℤ → ℂ} (hc : ∀ n, c (n + T) = -c n) (hc1 : ∀ n, ‖c n‖ ≤ 1)
    {θ : ℤ → ℝ} (hθp : ∀ n, θ (n + T) = θ n) (hθ : ∀ n : ℤ, ∀ k : ℤ, δ ≤ |θ n - 2 * π * k|)
    (hgap : π * D / (2 * T * A) < δ) :
    Summable (alTerm α A B D E c (fun n => cexp (I * θ n))) ∧
    ‖∑' n, alTerm α A B D E c (fun n => cexp (I * θ n)) n‖ ≤
      (3 / min 1 (‖α‖ * ((1 / α).re * (δ - π * D / (2 * T * A))))) *
        (Real.exp (π ^ 2 * (1 / α).re / (4 * A * T ^ 2) + B ^ 2 * α.re / (4 * A)) * √(π / (A * α.re))) *
        (1 / Real.sinh (π ^ 2 * (1 / α).re / (2 * A * T ^ 2))) := by
  have hR := re_inv_pos' hα
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  set Y0 := π * (1 / α).re / (2 * T * A)
  have hY0 : 0 < Y0 := by positivity
  have hDY : D * Y0 = (1 / α).re * (π * D / (2 * T * A)) := by simp only [Y0]; ring
  have hmin : 0 < min 1 (‖α‖ * ((1 / α).re * (δ - π * D / (2 * T * A)))) := by
    have : 0 < ‖α‖ := norm_pos_iff.mpr fun h => by rw [h] at hα; simp at hα
    have : 0 < δ - π * D / (2 * T * A) := by linarith
    positivity
  set m := min 1 (‖α‖ * ((1 / α).re * (δ - π * D / (2 * T * A)))) / 3
  have hm : 0 < m := by positivity
  have hden : ∀ n : ℤ, ∀ x y : ℝ, |y| ≤ Y0 →
      m ≤ ‖1 - (fun n => cexp (I * θ n)) n * cexp (-(α * (D * ((x : ℂ) + y * I) + E)))‖ := by
    intro n x y hy
    have := den_lower (E := E) hα hD (hθ n) x y hy
    simp only [m]
    convert this using 3
    rw [mul_sub, ← hDY]
  have hω : ∀ n, (fun n => cexp (I * θ n)) (n + T) = (fun n => cexp (I * θ n)) n := fun n => by
    simp only [hθp]
  obtain ⟨hs, hb⟩ := al_sum_le (B := B) (E := E) hα hA hT hc hc1 hω hm hY0 hden
  refine ⟨hs, hb.trans (le_of_eq ?_)⟩
  have hn2 : α.re ^ 2 + α.im ^ 2 = α.re / (1 / α).re := by
    rw [one_div, inv_re, normSq_apply]
    have : α.re * α.re + α.im * α.im ≠ 0 := by
      have := normSq_pos.mpr (fun h : α = 0 => by rw [h] at hα; simp at hα)
      rw [normSq_apply] at this; linarith
    field_simp
  have hαr : α.re ≠ 0 := hα.ne'
  have hRr : (1 / α).re ≠ 0 := hR.ne'
  have e1 : A * Y0 ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re = π ^ 2 * (1 / α).re / (4 * A * T ^ 2) := by
    rw [hn2]; simp only [Y0]; field_simp; ring
  have e2 : π * Y0 / T = π ^ 2 * (1 / α).re / (2 * A * T ^ 2) := by
    simp only [Y0]; field_simp
  have e3 : 1 / m = 3 / min 1 (‖α‖ * ((1 / α).re * (δ - π * D / (2 * T * A)))) := by
    simp only [m]; rw [one_div_div]
  rw [e1, e2, e3]

end

end MockCusp
