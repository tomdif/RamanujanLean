/-
# The shifted-contour identity with the residue normalised away

For `6 ≤ σ < 7`, `0 < δ < 1`, `X ≥ 1` and real `t`, Perron (`perron_c`) plus the
contour shift (`shift_identity`) give

    λ_δ(X) L(Δ, σ+it) − ∑_{n ≤ X} τ(n)(1 − n/X)³ n^{-σ-it} = −(1/2π) Ig(t),

    λ_δ(X) = φ₃(1/X) − (1/2π) ∫ X^{−δ+iy} P₃(−δ+iy) dy        (independent of `t`, `→ 1`),
    Ig(t)  = ∫ X^{−δ+iy} P₃(−δ+iy) L(Δ, σ−δ + i(t+y)) dy.

So `λ_δ(X) L − P` is controlled by the values of `L` on the line `Re = σ − δ` only (no pointwise
`L(Δ,σ+it)` term), and `‖Ig(t)‖ ≤ A X^{−δ} ∫ (1+|y|)^{-4} |L(Δ,σ−δ+i(t+y))| dy`.
-/
import RamanujanTau.MeanSquareFull.Remainder

set_option autoImplicit false

namespace RamanujanTau.MeanSquareFull

open Complex Real MeasureTheory Set Filter Topology Finset LSeries
open RamanujanTau.RankinError RamanujanTau.HeckeL RamanujanTau.MeanSquare

/-- `∫ X^{−δ+iy} P₃(−δ+iy) dy`. -/
noncomputable def IX (δ X : ℝ) : ℂ := ∫ y : ℝ, (X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y)

/-- The normalising constant `λ_δ(X) = φ₃(1/X) − IX/(2π)`. -/
noncomputable def lam (δ X : ℝ) : ℂ := (phi 3 (1 / X) : ℂ) - IX δ X / (2 * π)

/-- The left-line integral. -/
noncomputable def Ig (σ δ X t : ℝ) : ℂ :=
  ∫ y : ℝ, (X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y) *
    tauL (((σ - δ : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I)

/-- The constant `A = 6 (2/min(δ,1−δ))⁴` of `norm_Pk3_le_left`. -/
noncomputable def Acst (δ : ℝ) : ℝ := 6 * (2 / min (-(-δ)) (1 + -δ)) ^ 4

lemma Acst_nonneg {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) : 0 ≤ Acst δ := by
  have : 0 < min (-(-δ)) (1 + -δ) := lt_min (by linarith) (by linarith)
  unfold Acst; positivity

lemma norm_XPk_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {X : ℝ} (hX0 : 0 < X) (y : ℝ) :
    ‖(X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y)‖ ≤ X ^ (-δ) * Acst δ * wt y := by
  rw [norm_mul, norm_X_cpow hX0]
  have hre : (ln (-δ) y).re = -δ := by simp [ln]
  rw [hre]
  have := norm_Pk3_le_left (σ := -δ) (by linarith) (by linarith) y
  have e : Acst δ * wt y = 6 * (2 / min (-(-δ)) (1 + -δ)) ^ 4 / (1 + |y|) ^ 4 := by
    unfold Acst wt; ring
  rw [mul_assoc, e]
  gcongr

lemma norm_IX_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {X : ℝ} (hX0 : 0 < X) :
    ‖IX δ X‖ ≤ X ^ (-δ) * Acst δ * ∫ y, wt y := by
  unfold IX
  refine (norm_integral_le_of_norm_le (integrable_wt.const_mul (X ^ (-δ) * Acst δ))
    (ae_of_all _ fun y => norm_XPk_le hδ0 hδ1 hX0 y)).trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]

/-- `λ_δ(X) → 1` as `X → ∞`. -/
lemma tendsto_lam {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Tendsto (fun X => lam δ X) atTop (𝓝 1) := by
  have hb : Tendsto (fun X : ℝ => 3 * X⁻¹ + X ^ (-δ) * (Acst δ * (∫ y, wt y) / (2 * π)))
      atTop (𝓝 0) := by
    have h1 := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul 3
    have h2 := (tendsto_rpow_neg_atTop hδ0).mul_const (Acst δ * (∫ y, wt y) / (2 * π))
    simpa using h1.add h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have hX0 : 0 < X := by linarith
  have hπ : 0 < π := Real.pi_pos
  have hnorm2π : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]
  have e : lam δ X - 1 = ((phi 3 (1 / X) - 1 : ℝ) : ℂ) - IX δ X / (2 * π) := by
    unfold lam; push_cast; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, norm_div, hnorm2π]
  have h1 := one_sub_phi_le hX
  have h2 := norm_IX_le hδ0 hδ1 hX0
  have h3 : ‖IX δ X‖ / (2 * π) ≤ X ^ (-δ) * (Acst δ * (∫ y, wt y) / (2 * π)) := by
    rw [div_le_iff₀ (by positivity)]
    calc ‖IX δ X‖ ≤ X ^ (-δ) * Acst δ * ∫ y, wt y := h2
      _ = _ := by field_simp
  have : 3 / X = 3 * X⁻¹ := by ring
  linarith

/-- **The identity.** -/
theorem tauL_identity {σ δ : ℝ} (hσ1 : 6 ≤ σ) (hσ2 : σ < 7) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {X : ℝ} (hX : 1 ≤ X) (t : ℝ) :
    lam δ X * tauL ((σ : ℂ) + t * I) - dpoly (bsm σ X) ⌊X⌋₊ t = -(Ig σ δ X t / (2 * π)) := by
  obtain ⟨K0, hK00, hK0⟩ := tauL_growth
  have hX0 : 0 < X := by linarith
  set s : ℂ := (σ : ℂ) + t * I with hs
  set c : ℝ := 7 - σ with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  set F : ℂ → ℂ := fun w => tauL (s + w) with hF
  have hFd : Differentiable ℂ F := tauLSeries_entire.comp (differentiable_const _ |>.add
    differentiable_id)
  have hK : ∀ w : ℂ, -δ ≤ w.re → w.re ≤ c → ‖F w‖ ≤ (K0 * (1 + |t|) ^ 2) * (1 + |w.im|) ^ 2 := by
    intro w h1 h2
    have hre : (s + w).re = σ + w.re := by simp [hsre]
    have him : (s + w).im = t + w.im := by simp [hsim]
    have := hK0 (s + w) (by rw [hre]; linarith) (by rw [hre]; linarith)
    rw [him] at this
    refine this.trans ?_
    have h3 := one_add_abs_add_le t w.im
    calc K0 * (1 + |t + w.im|) ^ 2 ≤ K0 * ((1 + |t|) * (1 + |w.im|)) ^ 2 := by
          gcongr
      _ = _ := by ring
  have hP := perron_c (aS s) (aS_zero s) (k := 3) (by norm_num) hc0 hX0
    (summable_aS (by rw [hsre, hc]; ring))
  have hLS : (fun y : ℝ => (X : ℂ) ^ ln c y * Pk 3 (ln c y) * LSeries (aS s) (ln c y)) =
      fun y : ℝ => (X : ℂ) ^ ln c y * Pk 3 (ln c y) * F (ln c y) := by
    funext y
    rw [LSeries_aS (by simp [hsre, ln, hc]; norm_num)]
  rw [hLS, shift_identity hFd hX hc0 hδ0 hδ1 hK, tsum_eq_dpoly hX0 t] at hP
  have hIg : (∫ y : ℝ, (X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y) * F (ln (-δ) y)) = Ig σ δ X t := by
    unfold Ig; congr 1; funext y
    have e : s + ln (-δ) y = ((σ - δ : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I := by
      simp only [hs, ln]; push_cast; ring
    simp only [hF]; rw [e]
  have hIX : (∫ y : ℝ, (X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y)) = IX δ X := rfl
  rw [hIg, hIX] at hP
  have hF0 : F 0 = tauL s := by simp [hF]
  rw [hF0] at hP
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  unfold lam
  field_simp
  linear_combination (-1 : ℂ) * hP

/-- `‖Ig(t)‖ ≤ A X^{−δ} ∫ wt(y) |L(σ−δ+i(t+y))| dy`, given integrability of the right side. -/
lemma norm_Ig_le {σ δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {X : ℝ} (hX0 : 0 < X) (t : ℝ)
    (hint : Integrable fun y => wt y * ‖tauL (((σ - δ : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I)‖) :
    ‖Ig σ δ X t‖ ≤ X ^ (-δ) * Acst δ *
      ∫ y, wt y * ‖tauL (((σ - δ : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I)‖ := by
  unfold Ig
  refine (norm_integral_le_of_norm_le (hint.const_mul (X ^ (-δ) * Acst δ))
    (ae_of_all _ fun y => ?_)).trans (le_of_eq ?_)
  · rw [norm_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_XPk_le hδ0 hδ1 hX0 y) (norm_nonneg _)
  · rw [MeasureTheory.integral_const_mul]

end RamanujanTau.MeanSquareFull
