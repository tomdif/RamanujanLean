/-
# The contour identity behind the approximate functional equation

For an entire, even `F` with `‖F(x+iy)‖ ≤ K e^{y²/2}` on the strip `|x| ≤ c`,

    π F(0) = ∫_ℝ F(c+iy) e^{(c+iy)²} / (c+iy) dy.

Proof: `h(z) = (F(z) − F(0)) e^{z²}/z` (via `dslope`) is entire and odd off `0`, so Cauchy's theorem on
the rectangle `[−c,c] × [−Y,Y]` and `Y → ∞` give `∫_{(c)} h = 0`; and `∫_{(c)} e^{z²}/z = π`
(`line_gauss_zero`).
-/
import RamanujanTau.ZetaAFE.Gauss

set_option autoImplicit false

namespace RamanujanTau.ZetaAFE

open Complex MeasureTheory Set Filter Topology

lemma norm_line_ge (c y : ℝ) : |c| ≤ ‖(c : ℂ) + y * I‖ ∧ |y| ≤ ‖(c : ℂ) + y * I‖ := by
  constructor
  · have := Complex.abs_re_le_norm ((c : ℂ) + y * I); simpa using this
  · have := Complex.abs_im_le_norm ((c : ℂ) + y * I); simpa using this

lemma line_ne_zero {c : ℝ} (hc : c ≠ 0) (y : ℝ) : (c : ℂ) + y * I ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this; exact hc this

lemma norm_cexp_sq_line (x y : ℝ) : ‖cexp (((x : ℂ) + y * I) ^ 2)‖ = Real.exp (x ^ 2 - y ^ 2) := by
  rw [Complex.norm_exp]; congr 1; simp [sq]

/-- Integrability of `G(c+iy) e^{(c+iy)²}/(c+iy)` for `‖G‖ ≤ K e^{y²/2}`. -/
lemma integrable_line_gauss {c : ℝ} (hc : 0 < c) {G : ℝ → ℂ} (hG : Continuous G) {K : ℝ}
    (hK : ∀ y, ‖G y‖ ≤ K * Real.exp (y ^ 2 / 2)) :
    Integrable (fun y : ℝ => G y * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)) := by
  have hint : Integrable (fun y : ℝ => K * Real.exp (c ^ 2) / c * Real.exp (-(1 / 2) * y ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num)).const_mul _
  refine hint.mono' ?_ (Eventually.of_forall fun y => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    refine (hG.mul (by fun_prop)).div (by fun_prop) fun y => line_ne_zero hc.ne' y
  · have hK0 : 0 ≤ K := by
      have := (norm_nonneg _).trans (hK 0); simpa using this
    rw [norm_div, norm_mul, norm_cexp_sq_line]
    have hz : c ≤ ‖(c : ℂ) + y * I‖ := by
      have := (norm_line_ge c y).1; rwa [abs_of_pos hc] at this
    rw [div_le_iff₀ (hc.trans_le hz)]
    calc ‖G y‖ * Real.exp (c ^ 2 - y ^ 2)
        ≤ K * Real.exp (y ^ 2 / 2) * Real.exp (c ^ 2 - y ^ 2) := by gcongr; exact hK y
      _ = K * Real.exp (c ^ 2) / c * Real.exp (-(1 / 2) * y ^ 2) * c := by
          rw [mul_assoc, ← Real.exp_add]
          field_simp
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ _ := by gcongr

/-- **Contour identity.** -/
theorem afe_line {F : ℂ → ℂ} (hF : Differentiable ℂ F) (heven : ∀ z, F (-z) = F z) {c : ℝ}
    (hc : 0 < c) {K : ℝ} (hK : ∀ x y : ℝ, |x| ≤ c → ‖F (x + y * I)‖ ≤ K * Real.exp (y ^ 2 / 2)) :
    ∫ y : ℝ, F (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I) =
      (Real.pi : ℂ) * F 0 := by
  set h : ℂ → ℂ := fun z => dslope F 0 z * cexp (z ^ 2) with hh
  have hdiff : Differentiable ℂ h := by
    have : Differentiable ℂ (dslope F 0) :=
      differentiableOn_univ.mp ((differentiableOn_dslope Filter.univ_mem).mpr hF.differentiableOn)
    exact this.mul (by fun_prop)
  have hval : ∀ z : ℂ, z ≠ 0 → h z = (F z - F 0) * cexp (z ^ 2) / z := by
    intro z hz
    simp only [hh, dslope_of_ne _ hz, slope, sub_zero, smul_eq_mul, vsub_eq_sub]
    field_simp
  have hK0 : 0 ≤ K := by
    have := (norm_nonneg _).trans (hK 0 0 (by simp [hc.le])); simpa using this
  -- the line integrals
  set IR : ℝ → ℂ := fun Y => ∫ y in -Y..Y, h (c + y * I) with hIR
  have hodd : ∀ Y : ℝ, (∫ y in -Y..Y, h ((-c : ℝ) + y * I)) = -IR Y := by
    intro Y
    have : ∀ y : ℝ, h ((-c : ℝ) + y * I) = -h ((c : ℝ) + (-y : ℝ) * I) := by
      intro y
      have h1 : ((-c : ℝ) : ℂ) + y * I ≠ 0 := line_ne_zero (by linarith) y
      have h2 : ((c : ℝ) : ℂ) + (-y : ℝ) * I ≠ 0 := line_ne_zero hc.ne' _
      rw [hval _ h1, hval _ h2]
      have h3 : ((-c : ℝ) : ℂ) + y * I = -(((c : ℝ) : ℂ) + (-y : ℝ) * I) := by push_cast; ring
      rw [h3, heven, neg_sq]
      field_simp
    simp_rw [this]
    rw [intervalIntegral.integral_neg]
    congr 1
    rw [hIR]
    simp only
    rw [intervalIntegral.integral_comp_neg (fun y : ℝ => h ((c : ℝ) + y * I)), neg_neg]
  -- Cauchy on the rectangle
  have hrect : ∀ Y : ℝ, (∫ x in -c..c, h (x + (-Y) * I)) - (∫ x in -c..c, h (x + Y * I)) +
      I • IR Y - I • (-IR Y) = 0 := by
    intro Y
    have := integral_boundary_rect_eq_zero_of_differentiableOn h (⟨-c, -Y⟩ : ℂ) (⟨c, Y⟩ : ℂ)
      hdiff.differentiableOn
    rw [← hodd Y]
    simpa using this
  -- horizontal edges vanish
  have hbound : ∀ Y : ℝ, 1 ≤ Y → ∀ x : ℝ, |x| ≤ c → ∀ s : ℝ, |s| = Y →
      ‖h (x + s * I)‖ ≤ (K + ‖F 0‖) * Real.exp (c ^ 2) * Real.exp (-(Y ^ 2 / 2)) := by
    intro Y hY x hx s hs
    have hz0 : (x : ℂ) + s * I ≠ 0 := by
      intro h0; have := congrArg Complex.im h0; simp at this; rw [this] at hs; simp at hs; linarith
    rw [hval _ hz0, norm_div, norm_mul, norm_cexp_sq_line]
    have hzY : Y ≤ ‖(x : ℂ) + s * I‖ := by rw [← hs]; exact (norm_line_ge x s).2
    rw [div_le_iff₀ (by linarith)]
    have hFb : ‖F (x + s * I) - F 0‖ ≤ K * Real.exp (Y ^ 2 / 2) + ‖F 0‖ := by
      refine (norm_sub_le _ _).trans ?_
      have := hK x s hx
      rw [show s ^ 2 = Y ^ 2 by rw [← hs, sq_abs]] at this
      linarith
    have hx2 : x ^ 2 ≤ c ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    have hs2 : s ^ 2 = Y ^ 2 := by rw [← hs, sq_abs]
    have e1 : Real.exp (x ^ 2 - s ^ 2) ≤ Real.exp (c ^ 2) * Real.exp (-(Y ^ 2)) := by
      rw [← Real.exp_add]; gcongr; linarith
    have e2 : Real.exp (Y ^ 2 / 2) * Real.exp (-(Y ^ 2)) = Real.exp (-(Y ^ 2 / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e3 : Real.exp (-(Y ^ 2)) ≤ Real.exp (-(Y ^ 2 / 2)) := by
      gcongr; nlinarith
    calc ‖F (x + s * I) - F 0‖ * Real.exp (x ^ 2 - s ^ 2)
        ≤ (K * Real.exp (Y ^ 2 / 2) + ‖F 0‖) * (Real.exp (c ^ 2) * Real.exp (-(Y ^ 2))) := by
          gcongr
      _ = Real.exp (c ^ 2) * (K * (Real.exp (Y ^ 2 / 2) * Real.exp (-(Y ^ 2))) +
            ‖F 0‖ * Real.exp (-(Y ^ 2))) := by ring
      _ ≤ Real.exp (c ^ 2) * (K * Real.exp (-(Y ^ 2 / 2)) + ‖F 0‖ * Real.exp (-(Y ^ 2 / 2))) := by
          rw [e2]; gcongr
      _ = (K + ‖F 0‖) * Real.exp (c ^ 2) * Real.exp (-(Y ^ 2 / 2)) * 1 := by ring
      _ ≤ _ := by gcongr; linarith
  have hexp0 : Tendsto (fun Y : ℝ => Real.exp (-(Y ^ 2 / 2))) atTop (𝓝 0) := by
    refine Real.tendsto_exp_neg_atTop_nhds_zero.comp ?_
    refine Filter.tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with Y hY
    simp only [id]; nlinarith
  have hedge : ∀ sY : ℝ → ℝ, (∀ Y, |sY Y| = Y ∨ Y < 1) →
      Tendsto (fun Y : ℝ => ∫ x in -c..c, h (x + ((sY Y : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    intro sY hsY
    have hlim : Tendsto (fun Y : ℝ => (K + ‖F 0‖) * Real.exp (c ^ 2) * Real.exp (-(Y ^ 2 / 2)) *
        |c - -c|) atTop (𝓝 0) := by
      simpa using ((hexp0.const_mul ((K + ‖F 0‖) * Real.exp (c ^ 2))).mul_const |c - -c|)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with Y hY
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    have hx' : |x| ≤ c := by
      rw [Set.uIoc_of_le (by linarith)] at hx; exact abs_le.mpr ⟨hx.1.le, hx.2⟩
    refine hbound Y hY x hx' _ ?_
    rcases hsY Y with h1 | h1
    · exact h1
    · linarith
  have hIR0 : Tendsto IR atTop (𝓝 0) := by
    have hT := hedge id (fun Y => by
      rcases lt_or_ge Y 1 with h1 | h1
      · exact Or.inr h1
      · left; simp only [id]; exact abs_of_pos (by linarith))
    have hB := hedge (fun Y => -Y) (fun Y => by
      rcases lt_or_ge Y 1 with h1 | h1
      · exact Or.inr h1
      · left; rw [abs_neg]; exact abs_of_pos (by linarith))
    simp only [id, Complex.ofReal_neg] at hT hB
    have heq : ∀ Y : ℝ, IR Y = ((∫ x in -c..c, h (x + (Y : ℂ) * I)) -
        (∫ x in -c..c, h (x + -(Y : ℂ) * I))) / (2 * I) := by
      intro Y
      have := hrect Y
      simp only [smul_eq_mul] at this
      have hI : (2 : ℂ) * I ≠ 0 := by simp
      rw [eq_div_iff hI]
      linear_combination this
    rw [show IR = _ from funext heq]
    simpa using (hT.sub hB).div_const (2 * I)
  -- the improper integral
  have hgi : Integrable (fun y : ℝ => F (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2) /
      ((c : ℂ) + y * I)) :=
    integrable_line_gauss hc (hF.continuous.comp (by fun_prop)) (fun y => hK c y (abs_of_pos hc).le)
  have hg0 : Integrable (fun y : ℝ => F 0 * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)) :=
    integrable_line_gauss hc continuous_const (K := ‖F 0‖) (fun y => by
      have : 1 ≤ Real.exp (y ^ 2 / 2) := Real.one_le_exp (by positivity)
      nlinarith [norm_nonneg (F 0)])
  have hhint : Integrable (fun y : ℝ => h (c + y * I)) := by
    refine (hgi.sub hg0).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    rw [hval _ (line_ne_zero hc.ne' y)]
    ring
  have hlim2 : Tendsto IR atTop (𝓝 (∫ y : ℝ, h (c + y * I))) :=
    intervalIntegral_tendsto_integral hhint tendsto_neg_atTop_atBot tendsto_id
  have hzero : ∫ y : ℝ, h (c + y * I) = 0 := tendsto_nhds_unique hlim2 hIR0
  have hsplit : ∫ y : ℝ, h (c + y * I) =
      (∫ y : ℝ, F (c + y * I) * cexp (((c : ℂ) + y * I) ^ 2) / ((c : ℂ) + y * I)) -
      F 0 * (Real.pi : ℂ) := by
    rw [← line_gauss_zero hc, ← integral_const_mul, ← integral_sub hgi]
    · congr 1; funext y; rw [hval _ (line_ne_zero hc.ne' y)]; ring
    · simpa [mul_div_assoc] using hg0
  rw [hsplit] at hzero
  linear_combination hzero

end RamanujanTau.ZetaAFE
