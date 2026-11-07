/-
# `L²` bound for a weighted vertical average, from a mean-square bound on the line

Weight `wt(y) = (1+|y|)^{-4}` (the decay of the Riesz kernel `P₃` on a vertical line).

`L2_remainder`: let `g ≥ 0` be continuous with `g(u) ≤ K(1+|u|)` and
`∫_{−U}^{U} g² ≤ C (1+U)^a` for all `U ≥ 0` (`0 ≤ a ≤ 2`).  If `E` is continuous and
`‖E(t)‖ ≤ B ∫ wt(y) g(t+y) dy` for all `t`, then for `T ≥ 0`

    ∫₀ᵀ ‖E‖² ≤ B² W · C J (1+T)^a,        W = ∫ wt,  J = ∫ (1+|y|)^{-2}.

Proof: weighted Cauchy–Schwarz `(∫ w G)² ≤ (∫ w)(∫ w G²)` pointwise in `t`, then Fubini–Tonelli
in `(t, y)`, the translation `∫₀ᵀ g(t+y)² dt ≤ ∫_{−(T+|y|)}^{T+|y|} g²`, and
`(1+T+|y|)^a ≤ (1+T)^a (1+|y|)^a`.
-/
import RamanujanTau.MeanSquareFull.LeftLine

set_option autoImplicit false

namespace RamanujanTau.MeanSquareFull

open Real MeasureTheory intervalIntegral Filter Topology Set

/-- The kernel weight `(1+|y|)^{-4}`. -/
noncomputable def wt (y : ℝ) : ℝ := 1 / (1 + |y|) ^ 4

lemma wt_nonneg (y : ℝ) : 0 ≤ wt y := by unfold wt; positivity

lemma continuous_wt : Continuous wt := by
  unfold wt
  exact continuous_const.div (by fun_prop) fun y => by positivity

lemma wt_le_div_sq (y : ℝ) : wt y ≤ 1 / (1 + |y|) ^ 2 := by
  unfold wt
  have h1 : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
  have : (1 + |y|) ^ 2 ≤ (1 + |y|) ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
  gcongr

lemma integrable_wt : Integrable wt :=
  (RamanujanTau.MeanSquare.integrable_div_sq 1).mono' continuous_wt.aestronglyMeasurable
    (ae_of_all _ fun y => by rw [Real.norm_of_nonneg (wt_nonneg y)]; exact wt_le_div_sq y)

lemma integral_wt_pos : 0 < ∫ y, wt y := by
  have hpos : ∀ y, 0 < wt y := fun y => by unfold wt; positivity
  exact integral_pos_iff_support_of_nonneg wt_nonneg integrable_wt |>.2 (by
    rw [Function.support_eq_univ (fun y => (hpos y).ne')]; simp)

lemma one_add_abs_add_le' (a b : ℝ) : 1 + |a + b| ≤ (1 + |a|) * (1 + |b|) := by
  have := abs_add_le a b
  nlinarith [abs_nonneg a, abs_nonneg b, mul_nonneg (abs_nonneg a) (abs_nonneg b)]

/-- Weighted Cauchy–Schwarz. -/
lemma cs_weighted {w G : ℝ → ℝ} (hw0 : ∀ y, 0 ≤ w y) (hw : Integrable w)
    (hwG : Integrable fun y => w y * G y) (hwG2 : Integrable fun y => w y * G y ^ 2)
    (hW : 0 < ∫ y, w y) :
    (∫ y, w y * G y) ^ 2 ≤ (∫ y, w y) * ∫ y, w y * G y ^ 2 := by
  set W := ∫ y, w y
  set P := ∫ y, w y * G y
  set Q := ∫ y, w y * G y ^ 2
  set c := P / W
  have hnn : 0 ≤ ∫ y, (w y * G y ^ 2 - 2 * c * (w y * G y) + c ^ 2 * w y) := by
    refine integral_nonneg fun y => ?_
    have : w y * G y ^ 2 - 2 * c * (w y * G y) + c ^ 2 * w y = w y * (G y - c) ^ 2 := by ring
    rw [this]; exact mul_nonneg (hw0 y) (sq_nonneg _)
  have hsum : ∫ y, (w y * G y ^ 2 - 2 * c * (w y * G y) + c ^ 2 * w y) =
      Q - 2 * c * P + c ^ 2 * W := by
    rw [MeasureTheory.integral_add (f := fun y => w y * G y ^ 2 - 2 * c * (w y * G y))
      (g := fun y => c ^ 2 * w y) (hwG2.sub (hwG.const_mul _)) (hw.const_mul _),
      MeasureTheory.integral_sub (f := fun y => w y * G y ^ 2)
      (g := fun y => 2 * c * (w y * G y)) hwG2 (hwG.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hsum] at hnn
  have e : Q - 2 * c * P + c ^ 2 * W = Q - P ^ 2 / W := by
    simp only [c]; field_simp; ring
  rw [e, sub_nonneg, div_le_iff₀ hW] at hnn
  linarith

section

variable {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ u, 0 ≤ g u) {K : ℝ}
  (hgK : ∀ u, g u ≤ K * (1 + |u|))

include hg hg0 hgK

lemma K_nonneg : 0 ≤ K := by
  have := (hg0 0).trans (hgK 0); simpa using this

lemma g_le (t y : ℝ) : g (t + y) ≤ K * (1 + |t|) * (1 + |y|) := by
  have hK := K_nonneg hg hg0 hgK
  calc g (t + y) ≤ K * (1 + |t + y|) := hgK _
    _ ≤ K * ((1 + |t|) * (1 + |y|)) := by gcongr; exact one_add_abs_add_le' t y
    _ = _ := by ring

lemma integrable_wt_mul (t : ℝ) : Integrable fun y => wt y * g (t + y) := by
  have hK := K_nonneg hg hg0 hgK
  refine (RamanujanTau.MeanSquare.integrable_div_sq (K * (1 + |t|))).mono'
    ((continuous_wt.mul (hg.comp (continuous_const.add continuous_id))).aestronglyMeasurable)
    (ae_of_all _ fun y => ?_)
  have h1 : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
  rw [Real.norm_of_nonneg (mul_nonneg (wt_nonneg y) (hg0 _))]
  unfold wt
  have hgy := g_le hg hg0 hgK t y
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  calc g (t + y) * (1 + |y|) ^ 2 ≤ (K * (1 + |t|) * (1 + |y|)) * (1 + |y|) ^ 2 := by
        gcongr
    _ = K * (1 + |t|) * (1 + |y|) ^ 3 := by ring
    _ ≤ K * (1 + |t|) * (1 + |y|) ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by norm_num)) (by positivity)

lemma wt_mul_sq_le (t y : ℝ) :
    wt y * g (t + y) ^ 2 ≤ (K ^ 2 * (1 + |t|) ^ 2) * (1 / (1 + |y|) ^ 2) := by
  have hgy := g_le hg hg0 hgK t y
  have hK := K_nonneg hg hg0 hgK
  have hsq : g (t + y) ^ 2 ≤ (K * (1 + |t|) * (1 + |y|)) ^ 2 :=
    pow_le_pow_left₀ (hg0 _) hgy 2
  unfold wt
  have hy : (0 : ℝ) < 1 + |y| := by positivity
  calc 1 / (1 + |y|) ^ 4 * g (t + y) ^ 2 ≤ 1 / (1 + |y|) ^ 4 * (K * (1 + |t|) * (1 + |y|)) ^ 2 := by
        gcongr
    _ = _ := by field_simp

lemma integrable_wt_mul_sq (t : ℝ) : Integrable fun y => wt y * g (t + y) ^ 2 := by
  refine (RamanujanTau.MeanSquare.integrable_div_sq (K ^ 2 * (1 + |t|) ^ 2)).mono'
    ((continuous_wt.mul ((hg.comp (continuous_const.add continuous_id)).pow 2)).aestronglyMeasurable)
    (ae_of_all _ fun y => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (wt_nonneg y) (sq_nonneg _))]
  refine (wt_mul_sq_le hg hg0 hgK t y).trans (le_of_eq ?_)
  ring

/-- **The `L²` remainder bound.** -/
theorem L2_remainder {a C : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 2)
    (hG : ∀ U : ℝ, 0 ≤ U → ∫ u in (-U)..U, g u ^ 2 ≤ C * (1 + U) ^ a)
    {E : ℝ → ℂ} (hE : Continuous E) {B : ℝ} (hB0 : 0 ≤ B)
    (hEB : ∀ t, ‖E t‖ ≤ B * ∫ y, wt y * g (t + y)) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, ‖E t‖ ^ 2 ≤
      B ^ 2 * (∫ y, wt y) * (C * (∫ y : ℝ, 1 / (1 + |y|) ^ 2) * (1 + T) ^ a) := by
  have hC0 : 0 ≤ C := by
    have := hG 0 le_rfl; simpa using this
  set W := ∫ y, wt y with hW
  have hW0 : 0 < W := integral_wt_pos
  set J := ∫ y : ℝ, 1 / (1 + |y|) ^ 2 with hJ
  set F : ℝ → ℝ → ℝ := fun t y => wt y * g (t + y) ^ 2 with hF
  set Φ : ℝ → ℝ := fun t => ∫ y, F t y with hΦ
  -- pointwise
  have hpt : ∀ t, ‖E t‖ ^ 2 ≤ B ^ 2 * W * Φ t := by
    intro t
    have hP0 : 0 ≤ ∫ y, wt y * g (t + y) :=
      integral_nonneg fun y => mul_nonneg (wt_nonneg y) (hg0 _)
    have h1 : ‖E t‖ ^ 2 ≤ (B * ∫ y, wt y * g (t + y)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hEB t) 2
    have h2 := cs_weighted (w := wt) (G := fun y => g (t + y)) wt_nonneg integrable_wt
      (integrable_wt_mul hg hg0 hgK t) (integrable_wt_mul_sq hg hg0 hgK t) hW0
    calc ‖E t‖ ^ 2 ≤ (B * ∫ y, wt y * g (t + y)) ^ 2 := h1
      _ = B ^ 2 * (∫ y, wt y * g (t + y)) ^ 2 := by ring
      _ ≤ B ^ 2 * (W * Φ t) := by gcongr
      _ = _ := by ring
  -- product integrability
  set μ : Measure ℝ := volume.restrict (Ioc 0 T) with hμ
  have hprod : Integrable (Function.uncurry F) (μ.prod volume) := by
    have h1 : Integrable (fun t : ℝ => K ^ 2 * (1 + |t|) ^ 2) μ :=
      (show Continuous fun t : ℝ => K ^ 2 * (1 + |t|) ^ 2 by fun_prop).integrableOn_Ioc
    have h2 := h1.mul_prod (RamanujanTau.MeanSquare.integrable_div_sq 1)
    refine h2.mono' ?_ (ae_of_all _ fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hF]
      exact (continuous_wt.comp continuous_snd).mul
        ((hg.comp (continuous_fst.add continuous_snd)).pow 2)
    · simp only [Function.uncurry, hF]
      rw [Real.norm_of_nonneg (mul_nonneg (wt_nonneg _) (sq_nonneg _))]
      exact wt_mul_sq_le hg hg0 hgK p.1 p.2
  have hΦint : IntegrableOn Φ (Ioc 0 T) := hprod.integral_prod_left
  -- step 1
  have hstep1 : ∫ t in (0 : ℝ)..T, ‖E t‖ ^ 2 ≤ B ^ 2 * W * ∫ t in (0 : ℝ)..T, Φ t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hT
      ((hE.norm.pow 2).intervalIntegrable _ _) ?_ fun t _ => hpt t
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact hΦint.const_mul _
  -- step 2: Fubini
  have hswap : ∫ t in (0 : ℝ)..T, Φ t = ∫ y, ∫ t in Ioc 0 T, F t y := by
    rw [intervalIntegral.integral_of_le hT]
    exact integral_integral_swap hprod
  -- step 3: inner bound
  have hinner : ∀ y, ∫ t in Ioc 0 T, F t y ≤ C * (1 + T) ^ a * (1 / (1 + |y|) ^ 2) := by
    intro y
    simp only [hF]
    rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le hT]
    have hc2 : Continuous fun u => g u ^ 2 := hg.pow 2
    have e := intervalIntegral.integral_comp_add_right (a := 0) (b := T) (fun u => g u ^ 2) y
    simp only [zero_add] at e
    rw [e]
    have hU : 0 ≤ T + |y| := by positivity
    have hmono : ∫ u in y..T + y, g u ^ 2 ≤ ∫ u in (-(T + |y|))..T + |y|, g u ^ 2 :=
      intervalIntegral.integral_mono_interval (by linarith [neg_abs_le y]) (by linarith)
        (by linarith [le_abs_self y]) (ae_of_all _ fun u => sq_nonneg (g u))
        (hc2.intervalIntegrable _ _)
    have hb := hG (T + |y|) hU
    have hpow : (1 + (T + |y|)) ^ a ≤ (1 + T) ^ a * (1 + |y|) ^ a := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg y]) ha0
    have hya : (1 + |y|) ^ a ≤ (1 + |y|) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) ha
    rw [Real.rpow_two] at hya
    have hy : (0 : ℝ) < 1 + |y| := by positivity
    calc wt y * ∫ u in y..T + y, g u ^ 2
        ≤ wt y * (C * ((1 + T) ^ a * (1 + |y|) ^ a)) := by
          gcongr
          · exact wt_nonneg y
          · exact hmono.trans (hb.trans (by gcongr))
      _ ≤ wt y * (C * ((1 + T) ^ a * (1 + |y|) ^ 2)) := by
          have := wt_nonneg y; gcongr
      _ = C * (1 + T) ^ a * (1 / (1 + |y|) ^ 2) := by
          unfold wt; field_simp
  have hstep3 : ∫ y, ∫ t in Ioc 0 T, F t y ≤ C * J * (1 + T) ^ a := by
    have hr : Integrable (fun y => ∫ t in Ioc 0 T, F t y) :=
      hprod.integral_prod_right
    refine (integral_mono hr ((RamanujanTau.MeanSquare.integrable_div_sq 1).const_mul
      (C * (1 + T) ^ a)) hinner).trans (le_of_eq ?_)
    rw [MeasureTheory.integral_const_mul, hJ]; ring
  rw [hswap] at hstep1
  refine hstep1.trans ?_
  have : 0 ≤ B ^ 2 * W := by positivity
  gcongr

end

end RamanujanTau.MeanSquareFull
