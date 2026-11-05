/-
# From the weighted asymptotic to the Laplace transform of `t¹¹ |L(6+it)|²`

With `λ = π − 2β`:

    ∫_ℝ |Λ(6+it)|² e^{2βt} dt = N(β) + ∫_0^∞ kΓ(t) e^{−λt} |L|² dt,   0 ≤ N(β) ≤ N₀,

and `t¹¹/(2π)¹¹ ≤ kΓ(t) ≤ (1+η) t¹¹/(2π)¹¹ + C_η 1_{t ≤ T_η}` (`Gamma`).  Together with
`weighted_asymptotic` (`κ = cot β = tan(λ/2) ~ λ/2`) this gives

    λ¹² ∫_0^∞ t¹¹ e^{−λt} |L(6+it)|² dt / log(1/λ) → Kc = (2π)¹¹ 2¹² · 12‖Δ‖².
-/
import RamanujanTau.CriticalMeanSquareAsymp.Weighted
import RamanujanTau.CriticalMeanSquareAsymp.Gamma
import RamanujanTau.CriticalMeanSquareAsymp.KarC

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquareAsymp

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.HeckeL RamanujanTau.CriticalMeanSquare RamanujanTau.CriticalMeanSquareLower
open scoped Real

/-- The weighted integrand `|Λ(6+it)|² e^{2βt}`. -/
noncomputable def fW (β t : ℝ) : ℝ := ‖heckeLambda (6 + t * I)‖ ^ 2 * Real.exp (2 * β * t)

lemma continuous_fW (β : ℝ) : Continuous (fW β) :=
  ((heckeLambda_entire.continuous.comp (by fun_prop : Continuous fun t : ℝ => (6 : ℂ) + t * I)).norm.pow
    2).mul (by fun_prop)

lemma fW_nonneg (β t : ℝ) : 0 ≤ fW β t := by unfold fW; positivity

lemma integrable_fW {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 2) : Integrable (fW β) := by
  obtain ⟨CΓ, hCΓ, hw⟩ := exists_weight_bound
  refine ((integrable_major (δ := π / 2 - β) (by linarith)).const_mul CΓ).mono'
    (continuous_fW β).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (fW_nonneg β t)]
  exact hw β hβ0 t

lemma fW_eq {t : ℝ} (ht : t ≠ 0) (l : ℝ) :
    fW ((π - l) / 2) t = kG t * Real.exp (-(l * t)) * Lsq t := by
  unfold fW; rw [weight_eq ht]; congr 3; ring

/-- The Laplace transform `∫_0^∞ t¹¹ |L(6+it)|² e^{−λt} dt`. -/
noncomputable def Lap (l : ℝ) : ℝ := ∫ x in Ioi 0, x ^ 11 * Lsq x * Real.exp (-(x * l))

/-- The Gamma-weighted transform `∫_0^∞ kΓ(t) e^{−λt} |L|² dt`. -/
noncomputable def KGL (l : ℝ) : ℝ := ∫ x in Ioi 0, kG x * Real.exp (-(l * x)) * Lsq x

lemma integrableOn_Lap {l : ℝ} (hl : 0 < l) :
    IntegrableOn (fun x => x ^ 11 * Lsq x * Real.exp (-(x * l))) (Ioi 0) := by
  have hc : Continuous fun x : ℝ => x ^ 11 * Lsq x * Real.exp (-(x * l)) :=
    ((continuous_pow 11).mul continuous_Lsq).mul (by fun_prop)
  refine ((integrable_major (δ := l / 2) (by positivity)).integrableOn).mono' hc.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
  have hx0 : 0 < x := hx
  have hL := Lsq_nonneg x
  rw [Real.norm_of_nonneg (by positivity), abs_of_pos hx0]
  have h1 : x ^ 11 ≤ (1 + x) ^ 11 := pow_le_pow_left₀ hx0.le (by linarith) 11
  have h2 : Real.exp (-(x * l)) = Real.exp (-2 * (l / 2) * x) := by congr 1; ring
  rw [h2]
  have := Real.exp_pos (-2 * (l / 2) * x)
  calc x ^ 11 * Lsq x * Real.exp (-2 * (l / 2) * x) ≤ (1 + x) ^ 11 * Lsq x * Real.exp (-2 * (l / 2) * x) := by
        gcongr
    _ = _ := by ring

lemma integrableOn_KGL {l : ℝ} (hl0 : 0 < l) (hl : l < π) :
    IntegrableOn (fun x => kG x * Real.exp (-(l * x)) * Lsq x) (Ioi 0) := by
  have hi := (integrable_fW (β := (π - l) / 2) (by linarith) (by linarith)).integrableOn (s := Ioi 0)
  refine hi.congr_fun (fun x hx => fW_eq (ne_of_gt hx) l) measurableSet_Ioi

lemma Lap_nonneg (l : ℝ) : 0 ≤ Lap l :=
  setIntegral_nonneg measurableSet_Ioi fun x hx => by
    have := Lsq_nonneg x; have : (0 : ℝ) < x := hx; positivity

/-- `W = N + KGL`. -/
lemma W_split {l : ℝ} (hl0 : 0 < l) (hl : l < π) :
    ∫ t, fW ((π - l) / 2) t = (∫ t in Iic 0, fW ((π - l) / 2) t) + KGL l := by
  have hi := integrable_fW (β := (π - l) / 2) (by linarith) (by linarith)
  rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := 0),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hi.integrableOn hi.integrableOn]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => fW_eq (ne_of_gt hx) l

lemma N_bounds {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 2) :
    0 ≤ ∫ t in Iic 0, fW β t ∧ ∫ t in Iic 0, fW β t ≤ ∫ t in Iic 0, fW 0 t := by
  refine ⟨setIntegral_nonneg measurableSet_Iic fun t _ => fW_nonneg β t, ?_⟩
  refine setIntegral_mono_on (integrable_fW hβ0 hβ).integrableOn
    (integrable_fW le_rfl (by positivity)).integrableOn measurableSet_Iic fun t ht => ?_
  unfold fW
  have ht' : t ≤ 0 := ht
  have hbt := mul_nonpos_of_nonneg_of_nonpos hβ0 ht'
  have : Real.exp (2 * β * t) ≤ Real.exp (2 * 0 * t) := Real.exp_le_exp.mpr (by nlinarith)
  exact mul_le_mul_of_nonneg_left this (sq_nonneg _)

lemma Lap_le_KGL {l : ℝ} (hl0 : 0 < l) (hl : l < π) : Lap l / (2 * π) ^ 11 ≤ KGL l := by
  unfold Lap KGL
  rw [← integral_div]
  refine setIntegral_mono_on ((integrableOn_Lap hl0).div_const _) (integrableOn_KGL hl0 hl)
    measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  have hk := kG_ge hx0
  have hL := Lsq_nonneg x
  have e : Real.exp (-(x * l)) = Real.exp (-(l * x)) := by ring_nf
  rw [e]
  calc x ^ 11 * Lsq x * Real.exp (-(l * x)) / (2 * π) ^ 11 =
      x ^ 11 / (2 * π) ^ 11 * Real.exp (-(l * x)) * Lsq x := by ring
    _ ≤ _ := by gcongr

lemma KGL_le {η : ℝ} (hη : 0 < η) : ∃ C : ℝ, ∀ l : ℝ, 0 < l → l < π →
    KGL l ≤ (1 + η) * (Lap l / (2 * π) ^ 11) + C := by
  have hev := (tendsto_order.1 tendsto_kG_ratio).2 (1 + η) (by linarith)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hev
  set T := max T₀ 1 with hT
  have hT1 : 1 ≤ T := le_max_right _ _
  set Ck := Pq T * Real.exp (π * T) / (2 * π) ^ 12 with hCk
  refine ⟨Ck * ∫ x in Ioc 0 T, Lsq x, fun l hl0 hl => ?_⟩
  have hiK := integrableOn_KGL hl0 hl
  have hiL := integrableOn_Lap hl0
  unfold KGL
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ T by linarith),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi (hiK.mono_set Ioc_subset_Ioi_self)
      (hiK.mono_set (Ioi_subset_Ioi (by linarith)))]
  have hLsqi : IntegrableOn Lsq (Ioc 0 T) :=
    (continuous_Lsq.integrableOn_Icc (a := 0) (b := T)).mono_set Ioc_subset_Icc_self
  have h1 : ∫ x in Ioc 0 T, kG x * Real.exp (-(l * x)) * Lsq x ≤ Ck * ∫ x in Ioc 0 T, Lsq x := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hiK.mono_set Ioc_subset_Ioi_self) (hLsqi.const_mul _)
      measurableSet_Ioc fun x hx => ?_
    have hk := kG_le hx.1 hx.2
    have hL := Lsq_nonneg x
    have he : Real.exp (-(l * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := mul_pos hl0 hx.1; linarith)
    have hk0 : 0 ≤ kG x := le_trans (by have := hx.1; positivity) (kG_ge hx.1)
    calc kG x * Real.exp (-(l * x)) * Lsq x ≤ kG x * 1 * Lsq x := by gcongr
      _ ≤ Ck * Lsq x := by rw [mul_one]; exact mul_le_mul_of_nonneg_right hk hL
  have h2 : ∫ x in Ioi T, kG x * Real.exp (-(l * x)) * Lsq x ≤ (1 + η) * (Lap l / (2 * π) ^ 11) := by
    have hsub : ∫ x in Ioi T, x ^ 11 * Lsq x * Real.exp (-(x * l)) ≤ Lap l := by
      unfold Lap
      refine setIntegral_mono_set hiL (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
        (Eventually.of_forall (Ioi_subset_Ioi (by linarith)))
      have : (0 : ℝ) < x := hx
      have := Lsq_nonneg x
      positivity
    calc ∫ x in Ioi T, kG x * Real.exp (-(l * x)) * Lsq x
        ≤ ∫ x in Ioi T, (1 + η) / (2 * π) ^ 11 * (x ^ 11 * Lsq x * Real.exp (-(x * l))) := by
          refine setIntegral_mono_on (hiK.mono_set (Ioi_subset_Ioi (by linarith)))
            ((hiL.mono_set (Ioi_subset_Ioi (by linarith))).const_mul _) measurableSet_Ioi
            fun x hx => ?_
          have hxT : T < x := hx
          have hx0 : 0 < x := by linarith
          have hr := hT₀ x (by linarith [le_max_left T₀ 1])
          rw [div_lt_iff₀ (by positivity)] at hr
          have hk : kG x ≤ (1 + η) / (2 * π) ^ 11 * x ^ 11 := by
            rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
          have hL := Lsq_nonneg x
          have e : Real.exp (-(x * l)) = Real.exp (-(l * x)) := by ring_nf
          rw [e]
          calc kG x * Real.exp (-(l * x)) * Lsq x ≤
              (1 + η) / (2 * π) ^ 11 * x ^ 11 * Real.exp (-(l * x)) * Lsq x := by gcongr
            _ = _ := by ring
      _ = (1 + η) / (2 * π) ^ 11 * ∫ x in Ioi T, x ^ 11 * Lsq x * Real.exp (-(x * l)) :=
          integral_const_mul _ _
      _ ≤ (1 + η) / (2 * π) ^ 11 * Lap l := by gcongr
      _ = _ := by ring
  linarith

/-! ### The weighted asymptotic in the variable `λ = π − 2β` -/

lemma tendsto_beta_of_l :
    Tendsto (fun l : ℝ => (π - l) / 2) (𝓝[>] 0) (𝓝[<] (π / 2)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun l : ℝ => (π - l) / 2) (𝓝 0) (𝓝 ((π - 0) / 2)) :=
      ((continuous_const.sub continuous_id).div_const 2).tendsto 0
    rw [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with l hl
    show (π - l) / 2 < π / 2
    have : (0 : ℝ) < l := hl
    linarith

lemma cot_of_l (l : ℝ) : Real.cos ((π - l) / 2) / Real.sin ((π - l) / 2) =
    Real.sin (l / 2) / Real.cos (l / 2) := by
  rw [show (π - l) / 2 = π / 2 - l / 2 by ring, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]

lemma tendsto_l_div_kappa : Tendsto (fun l : ℝ => l / (Real.sin (l / 2) / Real.cos (l / 2)))
    (𝓝[>] 0) (𝓝 2) := by
  have hs : Tendsto (fun l : ℝ => Real.sinc (l / 2)) (𝓝[>] 0) (𝓝 1) := by
    have hcont : Continuous (fun l : ℝ => Real.sinc (l / 2)) :=
      Real.continuous_sinc.comp (by fun_prop)
    have := hcont.tendsto 0
    simp only [zero_div, Real.sinc_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun l : ℝ => Real.cos (l / 2)) (𝓝[>] 0) (𝓝 1) := by
    have hcont : Continuous (fun l : ℝ => Real.cos (l / 2)) :=
      Real.continuous_cos.comp (by fun_prop)
    have := hcont.tendsto 0
    simp only [zero_div, Real.cos_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h := (hc.const_mul 2).div hs one_ne_zero
  rw [mul_one, div_one] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π by positivity)] with l hl
  have hl0 : 0 < l := hl.1
  have hs0 : 0 < Real.sin (l / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [hl.2])
  show 2 * Real.cos (l / 2) / Real.sinc (l / 2) = _
  rw [Real.sinc_of_ne_zero (by positivity : l / 2 ≠ 0)]
  field_simp

lemma alg2 {l κ W A B : ℝ} (hl : l ≠ 0) (hκ : κ ≠ 0) (hA : A ≠ 0) (hAB : A + B ≠ 0) :
    l ^ 12 / A * W = κ ^ 12 * W / (A + B) * (l / κ) ^ 12 * (1 + B * A⁻¹) := by
  field_simp

lemma Xnn {l : ℝ} (h0 : 0 < l) (h1 : l < 1) : 0 ≤ l ^ 12 / Real.log (1 / l) :=
  div_nonneg (by positivity) (Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith))

/-- **(B′)** The weighted asymptotic in `λ`. -/
theorem weighted_lambda :
    Tendsto (fun l : ℝ => l ^ 12 / Real.log (1 / l) * ∫ t, fW ((π - l) / 2) t) (𝓝[>] 0)
      (𝓝 (2 ^ 12 * (12 * EisensteinReal.petNormSq))) := by
  have hB := weighted_asymptotic.comp tendsto_beta_of_l
  have h2 := tendsto_l_div_kappa
  have hL : Tendsto (fun l : ℝ => Real.log (1 / l)) (𝓝[>] 0) atTop := by
    have := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    refine this.congr fun t => ?_
    simp [one_div]
  have hr : Tendsto (fun l : ℝ => 1 + Real.log (l / (Real.sin (l / 2) / Real.cos (l / 2))) *
      (Real.log (1 / l))⁻¹) (𝓝[>] 0) (𝓝 1) := by
    have hlog := (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp h2
    have := (hlog.mul hL.inv_tendsto_atTop).const_add 1
    simpa using this
  have hlim := (hB.mul (h2.pow 12)).mul hr
  rw [mul_one, mul_comm (12 * EisensteinReal.petNormSq)] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num), hL.eventually_gt_atTop 0]
    with l hl hLl
  have hl0 : 0 < l := hl.1
  have hlπ : l < π := by linarith [hl.2, Real.pi_gt_three]
  have hs0 : 0 < Real.sin (l / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hc0 : 0 < Real.cos (l / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  set κ := Real.sin (l / 2) / Real.cos (l / 2) with hκ
  have hκ0 : 0 < κ := div_pos hs0 hc0
  have hlogκ : Real.log (1 / κ) = Real.log (1 / l) + Real.log (l / κ) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  have hκ1 : κ < 1 := by
    have h1 : Real.sin (l / 2) < l / 2 := Real.sin_lt (by positivity)
    have h2 : 1 - (l / 2) ^ 2 / 2 ≤ Real.cos (l / 2) := Real.one_sub_sq_div_two_le_cos
    rw [hκ, div_lt_one hc0]
    nlinarith [hl.2]
  have hLκ : 0 < Real.log (1 / l) + Real.log (l / κ) := by
    rw [← hlogκ]; exact Real.log_pos (by rw [lt_div_iff₀ hκ0, one_mul]; exact hκ1)
  simp only [Function.comp, cot_of_l]
  rw [← hκ, hlogκ]
  exact (alg2 hl0.ne' hκ0.ne' hLl.ne' hLκ.ne').symm

/-- **The Laplace asymptotic**: `λ¹² ∫_0^∞ t¹¹ |L|² e^{−λt} dt / log(1/λ) → Kc`. -/
noncomputable def Kc : ℝ := (2 * π) ^ 11 * (2 ^ 12 * (12 * EisensteinReal.petNormSq))

theorem laplace_asymptotic :
    Tendsto (fun l : ℝ => l ^ 12 / Real.log (1 / l) * Lap l) (𝓝[>] 0) (𝓝 Kc) := by
  set A₁ := 2 ^ 12 * (12 * EisensteinReal.petNormSq) with hA₁
  set X : ℝ → ℝ := fun l => l ^ 12 / Real.log (1 / l) with hX
  have hL : Tendsto (fun l : ℝ => Real.log (1 / l)) (𝓝[>] 0) atTop := by
    have := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    refine this.congr fun t => ?_
    simp [one_div]
  have hX0 : Tendsto X (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun l : ℝ => l ^ 12) (𝓝[>] 0) (𝓝 0) := by
      have := ((continuous_pow 12).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    have := h1.mul hL.inv_tendsto_atTop
    rw [mul_zero] at this
    refine this.congr fun l => ?_
    simp only [hX, div_eq_mul_inv, Pi.inv_apply]
  have hW := weighted_lambda
  set N₀ := ∫ t in Iic 0, fW 0 t
  -- `X · KGL → A₁`
  have hK : Tendsto (fun l => X l * KGL l) (𝓝[>] 0) (𝓝 A₁) := by
    have hN : Tendsto (fun l => X l * ∫ t in Iic 0, fW ((π - l) / 2) t) (𝓝[>] 0) (𝓝 0) := by
      have hb : Tendsto (fun l => X l * N₀) (𝓝[>] 0) (𝓝 0) := by
        simpa using hX0.mul_const N₀
      refine squeeze_zero' ?_ ?_ hb
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l hl
        exact mul_nonneg (Xnn hl.1 hl.2) (N_bounds (by linarith [hl.2, Real.pi_gt_three])
            (by linarith [hl.1, Real.pi_pos])).1
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l hl
        have hX0' : 0 ≤ X l :=
          Xnn hl.1 hl.2
        exact mul_le_mul_of_nonneg_left (N_bounds (by linarith [hl.2, Real.pi_gt_three])
            (by linarith [hl.1, Real.pi_pos])).2 hX0'
    have := hW.sub hN
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l hl
    have hlπ : l < π := by linarith [hl.2, Real.pi_gt_three]
    simp only [hX]
    rw [W_split hl.1 hlπ]; ring
  -- squeeze `X · Lap/(2π)¹¹`
  have hY : Tendsto (fun l => X l * (Lap l / (2 * π) ^ 11)) (𝓝[>] 0) (𝓝 A₁) := by
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · -- lower bound
      by_cases hb0 : b < 0
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l hl
        have hX0' : 0 ≤ X l :=
          Xnn hl.1 hl.2
        have := Lap_nonneg l
        have : 0 ≤ X l * (Lap l / (2 * π) ^ 11) := by positivity
        linarith
      push Not at hb0
      -- choose `η` with `b < A₁/(1+η)`
      set η : ℝ := (A₁ - b) / (2 * (b + 1)) with hη
      have hη0 : 0 < η := by rw [hη]; apply div_pos <;> linarith
      have hbη : b * (1 + η) < A₁ := by
        rw [hη]
        have h1 : b * (1 + (A₁ - b) / (2 * (b + 1))) = b + b * (A₁ - b) / (2 * (b + 1)) := by ring
        rw [h1]
        have h2 : b * (A₁ - b) / (2 * (b + 1)) < A₁ - b := by
          rw [div_lt_iff₀ (by linarith)]; nlinarith
        linarith
      obtain ⟨C, hC⟩ := KGL_le hη0
      have hconv : Tendsto (fun l => X l * KGL l - X l * C) (𝓝[>] 0) (𝓝 A₁) := by
        have := hK.sub (hX0.mul_const C)
        rwa [zero_mul, sub_zero] at this
      filter_upwards [(tendsto_order.1 hconv).1 (b * (1 + η)) hbη,
        Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l h1 hl
      have hlπ : l < π := by linarith [hl.2, Real.pi_gt_three]
      have hX0' : 0 ≤ X l :=
        Xnn hl.1 hl.2
      have h2 := mul_le_mul_of_nonneg_left (hC l hl.1 hlπ) hX0'
      have h3 : b * (1 + η) < (1 + η) * (X l * (Lap l / (2 * π) ^ 11)) := by nlinarith
      nlinarith
    · filter_upwards [(tendsto_order.1 hK).2 b hb,
        Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l h1 hl
      have hlπ : l < π := by linarith [hl.2, Real.pi_gt_three]
      have hX0' : 0 ≤ X l :=
        Xnn hl.1 hl.2
      exact (mul_le_mul_of_nonneg_left (Lap_le_KGL hl.1 hlπ) hX0').trans_lt h1
  have := hY.const_mul ((2 * π) ^ 11)
  rw [show (2 * π) ^ 11 * A₁ = Kc by rw [hA₁]; rfl] at this
  refine this.congr fun l => ?_
  simp only [hX]
  field_simp

end RamanujanTau.CriticalMeanSquareAsymp
