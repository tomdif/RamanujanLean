/-
# Averaged horizontal sides: `∫_T^{2T} ∫_{p+1}^{σ₁} |L(f,σ+it)| dσ dt ≪ T`

From the uniform mean square (`MeanSquare.mean_square_uniform`,
`∫_T^{2T}|L(f,p+1+x+it)|² ≤ CT/x`), exactly as in `HardyCountHafner.Horizontal`:

* for `p+1 < σ ≤ p+2` (`x = σ − p − 1`), `|L| ≤ √x |L|² + 1/√x`, hence
  `∫_T^{2T} |L(σ+it)| dt ≤ (C+1) T x^{−1/2}`;
* for `p+2 ≤ σ ≤ σ₁`, `|L(f,σ+it)| ≤ D` (absolute convergence, `σ > (k+1)/2 = p + 3/2`);
* Fubini, and `∫_0^1 x^{−1/2} dx = 2`.

The horizontal integrand `Fh g a b t = ∫_a^b |g(σ+it)| dσ` is defined for any continuous `g`.
-/
import RamanujanTau.HafnerGeneral.MeanSquare

set_option autoImplicit false

namespace RamanujanTau.HafnerGeneral

open Complex MeasureTheory Set Filter Topology ModularForm
open RamanujanTau.HeckeConvexGeneral
open scoped Real MatrixGroups

/-- The horizontal-side integrand `F(t) = ∫_a^b |g(σ+it)| dσ`. -/
noncomputable def Fh (g : ℂ → ℂ) (a b t : ℝ) : ℝ := ∫ σ in a..b, ‖g ((σ : ℂ) + t * I)‖

lemma continuous_normg {g : ℂ → ℂ} (hg : Continuous g) :
    Continuous fun q : ℝ × ℝ => ‖g ((q.1 : ℂ) + q.2 * I)‖ :=
  (hg.comp (by fun_prop)).norm

lemma continuous_Fh {g : ℂ → ℂ} (hg : Continuous g) (a b : ℝ) : Continuous (Fh g a b) := by
  have h : Continuous (Function.uncurry fun t σ : ℝ => ‖g ((σ : ℂ) + t * I)‖) := by
    have h1 : Continuous fun q : ℝ × ℝ => ‖g ((q.2 : ℂ) + q.1 * I)‖ :=
      (hg.comp (by fun_prop)).norm
    exact h1
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h a b

lemma Fh_nonneg (g : ℂ → ℂ) {a b : ℝ} (h : a ≤ b) (t : ℝ) : 0 ≤ Fh g a b t :=
  intervalIntegral.integral_nonneg h fun _ _ => norm_nonneg _

/-- Comparison of horizontal integrands. -/
lemma Fh_le_of_le {g L : ℂ → ℂ} (hg : Continuous g) (hL : Continuous L) {a b B : ℝ}
    (hab : a ≤ b) (hle : ∀ σ ∈ Icc a b, ∀ t : ℝ, ‖g ((σ : ℂ) + t * I)‖ ≤ B * ‖L ((σ : ℂ) + t * I)‖)
    (t : ℝ) : Fh g a b t ≤ B * Fh L a b t := by
  unfold Fh
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hab ?_ ?_ fun σ hσ => hle σ hσ t
  · exact ((hg.comp (by fun_prop)).norm).intervalIntegrable _ _
  · exact (((hL.comp (by fun_prop)).norm).const_mul B).intervalIntegrable _ _

variable {p : ℕ}

/-- Mean of `|L(f,σ+it)|` for `p+1 < σ ≤ p+2`. -/
lemma mean_abs_near (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (C : ℝ)
    (hC : ∀ x : ℝ, 0 < x → x ≤ 1 → ∀ T : ℝ, 1 ≤ T →
      ∫ t in Icc T (2 * T), ‖fL f ((((p : ℝ) + 1 + x : ℝ) : ℂ) + t * I)‖ ^ 2 ≤ C * T / x)
    {σ T : ℝ} (hσ : (p : ℝ) + 1 < σ) (hσ7 : σ ≤ (p : ℝ) + 2) (hT : 1 ≤ T) :
    ∫ t in Icc T (2 * T), ‖fL f ((σ : ℂ) + t * I)‖ ≤
      (C + 1) * T * (σ - ((p : ℝ) + 1)) ^ (-(1 / 2) : ℝ) := by
  set x : ℝ := σ - ((p : ℝ) + 1) with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  have hx1 : x ≤ 1 := by rw [hx]; linarith
  have hσx : σ = (p : ℝ) + 1 + x := by rw [hx]; ring
  have hTpos : 0 < T := by linarith
  set s : ℝ := Real.sqrt x with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hx0
  have hss : s * s = x := Real.mul_self_sqrt hx0.le
  have hsx : x ^ (-(1 / 2) : ℝ) = s⁻¹ := by
    rw [hs, Real.sqrt_eq_rpow, Real.rpow_neg hx0.le]
  have hm := hC x hx0 hx1 T hT
  rw [← hσx] at hm
  have hcont : Continuous fun t : ℝ => ‖fL f ((σ : ℂ) + t * I)‖ :=
    ((fL_entire f (by omega)).continuous.comp (by fun_prop)).norm
  have hpt : ∀ t ∈ Icc T (2 * T), ‖fL f ((σ : ℂ) + t * I)‖ ≤
      s * ‖fL f ((σ : ℂ) + t * I)‖ ^ 2 + s⁻¹ := by
    intro t _
    set a := ‖fL f ((σ : ℂ) + t * I)‖
    have h1 : 0 ≤ (s * a - 1) ^ 2 := sq_nonneg _
    have : a * s ≤ s * s * a ^ 2 + 1 := by nlinarith
    rw [show s * a ^ 2 + s⁻¹ = (s * s * a ^ 2 + 1) / s by field_simp]
    rw [le_div_iff₀ hspos]; linarith
  have hvol : volume.real (Icc T (2 * T)) = T := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  calc ∫ t in Icc T (2 * T), ‖fL f ((σ : ℂ) + t * I)‖
      ≤ ∫ t in Icc T (2 * T), (s * ‖fL f ((σ : ℂ) + t * I)‖ ^ 2 + s⁻¹) :=
        setIntegral_mono_on hcont.integrableOn_Icc
          (((hcont.pow 2).const_mul s).add continuous_const).integrableOn_Icc measurableSet_Icc hpt
    _ = s * (∫ t in Icc T (2 * T), ‖fL f ((σ : ℂ) + t * I)‖ ^ 2) + s⁻¹ * T := by
        rw [integral_add ((hcont.pow 2).const_mul s).integrableOn_Icc
          (continuous_const.integrableOn_Icc), integral_const_mul, setIntegral_const, hvol,
          smul_eq_mul]
        ring
    _ ≤ s * (C * T / x) + s⁻¹ * T := by
        have := mul_le_mul_of_nonneg_left hm hspos.le; linarith
    _ = (C + 1) * T * s⁻¹ - (s⁻¹ * T) * (1 - 1) := by
        rw [← hss]; field_simp; ring
    _ = (C + 1) * T * x ^ (-(1 / 2) : ℝ) := by rw [hsx]; ring

/-- **Averaged horizontal sides**: `∫_T^{2T} F ≤ C T`, `F(t) = ∫_{p+1}^{σ₁} |L(f,σ+it)| dσ`. -/
theorem horizontal_mean (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2)
    {σ₁ : ℝ} (h7 : (p : ℝ) + 2 ≤ σ₁) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      ∫ t in Icc T (2 * T), Fh (fL f) ((p : ℝ) + 1) σ₁ t ≤ C * T := by
  obtain ⟨C, hC0, hC⟩ := mean_square_uniform f hk
  have hk1 : 1 ≤ 2 * p + 2 := by omega
  obtain ⟨D, hD0, hD⟩ := fL_bounded_of_gt f hk1 (σ := (p : ℝ) + 2) (by push_cast; linarith)
  have hcL : Continuous (fL f) := (fL_entire f hk1).continuous
  have hnL := continuous_normg hcL
  refine ⟨2 * (C + 1) + D * (σ₁ - ((p : ℝ) + 2)), by nlinarith, fun T hT => ?_⟩
  have hTpos : 0 < T := by linarith
  set μ : Measure ℝ := volume.restrict (Icc T (2 * T)) with hμ
  have hvol : volume.real (Icc T (2 * T)) = T := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have hint : Integrable (Function.uncurry fun (σ t : ℝ) => ‖fL f ((σ : ℂ) + t * I)‖)
      ((volume.restrict (uIoc ((p : ℝ) + 1) σ₁)).prod μ) := by
    rw [hμ, Measure.prod_restrict]
    have hc : ContinuousOn (Function.uncurry fun (σ t : ℝ) => ‖fL f ((σ : ℂ) + t * I)‖)
        (Icc ((p : ℝ) + 1) σ₁ ×ˢ Icc T (2 * T)) := hnL.continuousOn
    refine (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set ?_
    rw [uIoc_of_le (by linarith)]
    exact prod_mono Ioc_subset_Icc_self le_rfl
  have hswap := intervalIntegral_integral_swap hint
  have hF : ∫ t in Icc T (2 * T), Fh (fL f) ((p : ℝ) + 1) σ₁ t =
      ∫ σ in ((p : ℝ) + 1)..σ₁, ∫ t in Icc T (2 * T), ‖fL f ((σ : ℂ) + t * I)‖ := by
    rw [hswap]; rfl
  rw [hF]
  have hG : Continuous fun σ : ℝ => ∫ t in Icc T (2 * T), ‖fL f ((σ : ℂ) + t * I)‖ := by
    exact continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (p : ℝ) + 2)
    (hG.intervalIntegrable _ _) (hG.intervalIntegrable _ _)]
  have h2 : ∫ σ in ((p : ℝ) + 2)..σ₁, ∫ t in Icc T (2 * T), ‖fL f ((σ : ℂ) + t * I)‖ ≤
      D * (σ₁ - ((p : ℝ) + 2)) * T := by
    have hb : ∀ σ ∈ Icc ((p : ℝ) + 2) σ₁,
        ∫ t in Icc T (2 * T), ‖fL f ((σ : ℂ) + t * I)‖ ≤ D * T := by
      intro σ hσ
      have hbd : ∀ t ∈ Icc T (2 * T), ‖fL f ((σ : ℂ) + t * I)‖ ≤ D := fun t _ =>
        hD _ (by simp; linarith [hσ.1])
      calc ∫ t in Icc T (2 * T), ‖fL f ((σ : ℂ) + t * I)‖ ≤ ∫ t in Icc T (2 * T), D :=
            setIntegral_mono_on
              ((hcL.comp (by fun_prop)).norm.integrableOn_Icc)
              continuous_const.integrableOn_Icc measurableSet_Icc hbd
        _ = D * T := by rw [setIntegral_const, hvol, smul_eq_mul, mul_comm]
    calc ∫ σ in ((p : ℝ) + 2)..σ₁, ∫ t in Icc T (2 * T), ‖fL f ((σ : ℂ) + t * I)‖
        ≤ ∫ σ in ((p : ℝ) + 2)..σ₁, D * T :=
          intervalIntegral.integral_mono_on h7 (hG.intervalIntegrable _ _)
            intervalIntegrable_const hb
      _ = D * (σ₁ - ((p : ℝ) + 2)) * T := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have h1 : ∫ σ in ((p : ℝ) + 1)..((p : ℝ) + 2),
      ∫ t in Icc T (2 * T), ‖fL f ((σ : ℂ) + t * I)‖ ≤ 2 * (C + 1) * T := by
    have hri : IntervalIntegrable
        (fun σ : ℝ => (C + 1) * T * (σ - ((p : ℝ) + 1)) ^ (-(1 / 2) : ℝ))
        volume ((p : ℝ) + 1) ((p : ℝ) + 2) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (r := (-(1 / 2) : ℝ)) (by norm_num)).comp_sub_right ((p : ℝ) + 1)
      simp only [show (0 : ℝ) + ((p : ℝ) + 1) = (p : ℝ) + 1 by ring,
        show (1 : ℝ) + ((p : ℝ) + 1) = (p : ℝ) + 2 by ring] at this
      exact this.const_mul _
    have hval : ∫ σ in ((p : ℝ) + 1)..((p : ℝ) + 2),
        (C + 1) * T * (σ - ((p : ℝ) + 1)) ^ (-(1 / 2) : ℝ) = 2 * (C + 1) * T := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right
        (fun σ : ℝ => σ ^ (-(1 / 2) : ℝ)), integral_rpow (Or.inl (by norm_num))]
      rw [show (p : ℝ) + 2 - ((p : ℝ) + 1) = 1 by ring, sub_self]
      norm_num
      ring
    rw [← hval]
    refine intervalIntegral.integral_mono_on_of_le_Ioo (by linarith)
      (hG.intervalIntegrable _ _) hri fun σ hσ => ?_
    exact mean_abs_near f C hC hσ.1 hσ.2.le hT
  have hDT : 0 ≤ D * (σ₁ - ((p : ℝ) + 2)) * T := by
    have : 0 ≤ σ₁ - ((p : ℝ) + 2) := by linarith
    positivity
  nlinarith

end RamanujanTau.HafnerGeneral
