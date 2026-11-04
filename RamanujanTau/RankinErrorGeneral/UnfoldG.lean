/-
# The unfolding identity and the real Mellin transform of `Φ − ‖G‖` for an `RSFn`

Generalizes `RankinError/UnfoldTheta.lean` and `RankinError/RSMellin.lean`. For every `t > 0`,
in `[0,∞]` (`unfold_thetaG`):

    ∫_𝓕 G(z)(Θ_z(t) − 1) dμ = 2 ∫₀^∞ I(v) h_t(v) dv/v²,

and for real `σ > 0` (`lintegral_mellin_PhiG`):

    ∫₀^∞ t^{σ−1}(Φ(t) − ‖G‖) dt = 2Γ(σ)π^{−σ} ζ(2σ) ∑ₙ cₙ Γ(σ+m)(4πn)^{−σ−m}.
-/
import RamanujanTau.RankinErrorGeneral.ThetaG

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.RankinErrorGeneral

open Real Filter Topology MeasureTheory Set ModularGroup
open RamanujanTau.RankinSelberg hiding G G_smul continuous_G G_pos
open RamanujanTau.RankinError
open RamanujanTau.RankinSelbergGeneral RamanujanTau.RankinSelbergGeneral.Horo
open HoroFn RSFn
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal

variable [RSFn]

lemma toH_gptG {p : ℝ × ℝ} (h : 1 / 4 ≤ p.2) : toH p = gpt p.1 p.2 := by
  apply UpperHalfPlane.ext
  rw [coe_toH (by linarith)]
  have h' : (4:ℝ)⁻¹ ≤ p.2 := by norm_num; linarith
  simp [gpt, h', max_eq_left h]

/-- `Ψ_t(w) = 1_{strip}(w) G(w) h_t(Im w)`. -/
noncomputable def PsiG (t : ℝ) (w : ℍ) : ℝ≥0∞ :=
  strip.indicator (1 : ℍ → ℝ≥0∞) w * (ENNReal.ofReal (G w) * hfun t w.im)

lemma measurable_PsiG (t : ℝ) : Measurable (PsiG t) := by
  unfold PsiG
  exact (measurable_one.indicator measurableSet_strip).mul
    ((ENNReal.measurable_ofReal.comp continuous_G.measurable).mul
      ((measurable_hfun t).comp measurable_im_H))

/-- The pointwise identity on `𝓕`. -/
lemma ofReal_gR_thetaG {p : ℝ × ℝ} (hp : p ∈ Freg) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal (gR p * (theta p.1 p.2 t - 1)) =
      ENNReal.ofReal (1 / p.2 ^ 2) * ∑' γ : SL(2, ℤ), PsiG t (γ • toH p) := by
  have hy := Freg_im hp
  have hy0 : 0 < p.2 := by linarith
  set z := toH p with hz
  have hzre : z.re = p.1 := toH_re hy0
  have hzim : z.im = p.2 := toH_im hy0
  set R : ℝ≥0∞ := ∑' γ : SL(2, ℤ), strip.indicator (1 : ℍ → ℝ≥0∞) (γ • z) * hfun t (γ • z).im
    with hR
  have hsum := summable_theta p.1 hy0 ht
  have hc := theta_coset z t
  rw [hzre, hzim] at hc
  have hfin : (1 : ℝ≥0∞) + R = ENNReal.ofReal (theta p.1 p.2 t) := by
    rw [← hc, theta, ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) hsum]
  have hRtop : R ≠ ⊤ := by
    intro h; rw [h] at hfin; simp at hfin
  have hθ : theta p.1 p.2 t - 1 = R.toReal := by
    have := congrArg ENNReal.toReal hfin
    rw [ENNReal.toReal_add ENNReal.one_ne_top hRtop, ENNReal.toReal_ofReal (theta_nonneg _ _ _),
      ENNReal.toReal_one] at this
    linarith
  have hG : gR p = G z * (1 / p.2 ^ 2) := by
    rw [gR, hz, toH_gptG (by linarith)]; ring
  have hPsi : ∑' γ : SL(2, ℤ), PsiG t (γ • z) = ENNReal.ofReal (G z) * R := by
    rw [hR, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun γ => ?_
    unfold PsiG
    rw [G_smul]; ring
  rw [hPsi, hθ, hG, mul_comm (G z), mul_assoc, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (G_nonneg z), ENNReal.ofReal_toReal hRtop]

lemma Freg'_ae_eqG : (Freg' : Set (ℝ × ℝ)) =ᵐ[volume] Freg := by
  have hsub : Freg' ⊆ Freg := fun p hp => ⟨hp.1, abs_le.2 ⟨hp.2.1, hp.2.2.1.le⟩, hp.2.2.2⟩
  have hline : volume ({(1 / 2 : ℝ)} ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  refine (ae_eq_set).2 ⟨?_, ?_⟩
  · rw [diff_eq_empty.2 hsub]; simp
  · refine measure_mono_null (fun p hp => ?_) hline
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hp
    refine ⟨?_, mem_univ _⟩
    simp only [Freg', mem_setOf_eq, not_and] at h4
    have := abs_le.1 h2
    simp only [mem_singleton_iff]
    by_contra hne
    exact h4 h1 this.1 (lt_of_le_of_ne this.2 hne) h3

lemma measurable_tsum_PsiG (t : ℝ) : Measurable fun w : ℍ => ∑' γ : SL(2, ℤ), PsiG t (γ • w) :=
  Measurable.ennreal_tsum fun γ => (measurable_PsiG t).comp (measurePreserving_sl γ).measurable

/-- The strip side: `∫_ℍ Ψ_t dμ = ∫₀^∞ I(v) h_t(v) dv / v²`. -/
lemma lintegral_PsiG (t : ℝ) :
    ∫⁻ w, PsiG t w = ∫⁻ v in Ioi 0, ENNReal.ofReal (Aint v) * hfun t v * ENNReal.ofReal (1 / v ^ 2) := by
  rw [lintegral_H _ (measurable_PsiG t)]
  set F : ℝ × ℝ → ℝ≥0∞ := fun p => PsiG t (toH p) * ENNReal.ofReal (1 / p.2 ^ 2) with hF
  have hFm : Measurable F :=
    ((measurable_PsiG t).comp measurable_toH).mul
      (ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_snd.pow_const 2)))
  have hset : {p : ℝ × ℝ | 0 < p.2} = (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
    ext p; simp
  rw [hset, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod_symm _ hFm.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have e : ∀ x : ℝ, F (x, y) = (Ico (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (G (hp hy0 x))) x *
      (hfun t y * ENNReal.ofReal (1 / y ^ 2)) := by
    intro x
    simp only [hF, PsiG, toH_hp hy0, hp_im]
    by_cases hx : x ∈ Ico (0 : ℝ) 1
    · have hs : hp hy0 x ∈ strip := by
        simp only [strip, mem_setOf_eq, hp_re']; exact ⟨hx.1, hx.2⟩
      rw [indicator_of_mem hs, indicator_of_mem hx]; simp only [Pi.one_apply, one_mul]; ring
    · have hs : hp hy0 x ∉ strip := by
        simp only [strip, mem_setOf_eq, hp_re']; exact fun h => hx ⟨h.1, h.2⟩
      rw [indicator_of_notMem hs, indicator_of_notMem hx]; simp
  simp_rw [e]
  have hmx : Measurable fun x => ENNReal.ofReal (G (hp hy0 x)) :=
    ENNReal.measurable_ofReal.comp (continuous_G_hp hy0).measurable
  rw [lintegral_mul_const _ (hmx.indicator measurableSet_Ico),
    lintegral_indicator measurableSet_Ico, setLIntegral_congr Ico_ae_eq_Ioc, ← mul_assoc]
  congr 1
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [Aint, dif_pos hy0, intervalIntegral.integral_of_le zero_le_one]
  · exact ((continuous_G_hp hy0).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · exact Eventually.of_forall fun x => (G_nonneg _)

/-- **The unfolding identity (U)**, for every `t > 0`, in `[0, ∞]`. -/
theorem unfold_thetaG {t : ℝ} (ht : 0 < t) :
    ∫⁻ p in Freg, ENNReal.ofReal (gR p * (theta p.1 p.2 t - 1)) =
      2 * ∫⁻ v in Ioi 0, ENNReal.ofReal (Aint v) * hfun t v * ENNReal.ofReal (1 / v ^ 2) := by
  rw [← lintegral_PsiG, ← lintegral_unfold_U _ (measurable_PsiG t),
    lintegral_H _ ((measurable_one.indicator measurableSet_Uset).mul (measurable_tsum_PsiG t))]
  rw [setLIntegral_congr_fun measurableSet_Freg (fun p hp => ofReal_gR_thetaG hp t ht),
    ← setLIntegral_congr Freg'_ae_eqG, ← lintegral_indicator measurableSet_Freg',
    ← lintegral_indicator (measurableSet_lt measurable_const measurable_snd)]
  congr 1; funext p
  by_cases hy : 0 < p.2
  · rw [indicator_of_mem (show p ∈ {p : ℝ × ℝ | 0 < p.2} from hy)]
    by_cases hF : p ∈ Freg'
    · rw [indicator_of_mem hF, indicator_of_mem ((toH_mem_Uset hy).2 hF)]
      simp only [Pi.one_apply, one_mul]; ring
    · rw [indicator_of_notMem hF, indicator_of_notMem (fun h => hF ((toH_mem_Uset hy).1 h))]
      simp
  · rw [indicator_of_notMem (show p ∉ {p : ℝ × ℝ | 0 < p.2} from hy),
      indicator_of_notMem (fun h : p ∈ Freg' => hy h.1)]

lemma integrableOn_gR_theta_subG {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun p : ℝ × ℝ => gR p * (theta p.1 p.2 t - 1)) Freg :=
  ((integrableOn_gR_thetaG ht).sub (by simpa using integrableOn_gR_mul_powG 0)).congr_fun
    (fun p _ => by simp only [Pi.sub_apply]; ring) measurableSet_Freg

lemma PhiG_sub_eq {t : ℝ} (ht : 0 < t) :
    PhiG t - petNormSq = ∫ p in Freg, gR p * (theta p.1 p.2 t - 1) := by
  unfold PhiG
  rw [petNormSq_eq, ← integral_sub (integrableOn_gR_thetaG ht)
    (by simpa using integrableOn_gR_mul_powG 0)]
  congr 1; funext p; ring

lemma gR_theta_sub_nonnegG {t : ℝ} (ht : 0 < t) {p : ℝ × ℝ} (hp : p ∈ Freg) :
    0 ≤ gR p * (theta p.1 p.2 t - 1) := by
  have hy0 : 0 < p.2 := by linarith [Freg_im hp]
  exact mul_nonneg (div_nonneg (G_nonneg _) (by positivity))
    (sub_nonneg.2 (one_le_theta _ hy0 ht))

lemma PhiG_sub_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ PhiG t - petNormSq := by
  rw [PhiG_sub_eq ht]
  exact setIntegral_nonneg measurableSet_Freg fun p hp => gR_theta_sub_nonnegG ht hp

lemma ofReal_PhiG_sub {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (PhiG t - petNormSq) =
      ∫⁻ p in Freg, ENNReal.ofReal (gR p * (theta p.1 p.2 t - 1)) := by
  rw [PhiG_sub_eq ht, ofReal_integral_eq_lintegral_ofReal (integrableOn_gR_theta_subG ht)
    ((ae_restrict_iff' measurableSet_Freg).2 (Eventually.of_forall fun p hp =>
      gR_theta_sub_nonnegG ht hp))]

/-- The horocycle mean as a series of measurable terms. -/
noncomputable def JfunG (v : ℝ) : ℝ≥0∞ := ∑' n : ℕ, ENNReal.ofReal (mtermG 2 n v)

lemma measurable_JfunG : Measurable JfunG :=
  Measurable.ennreal_tsum fun n => ENNReal.measurable_ofReal.comp (by unfold mtermG; fun_prop)

lemma ofReal_AintG {v : ℝ} (hv : 0 < v) : ENNReal.ofReal (Aint v) = JfunG v := by
  have h := hasSum_mtermG 2 hv
  rw [sub_self, Real.rpow_zero, mul_one] at h
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => mtermG_nonneg 2 n hv) h.summable]
  rfl

/-- **The Mellin transform of `Φ − ‖Δ‖²` at real `σ > 0`**, in `[0, ∞]`. -/
theorem lintegral_mellin_PhiG {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (σ - 1)) * ENNReal.ofReal (PhiG t - petNormSq) =
      2 * ENNReal.ofReal (Real.Gamma σ * π ^ (-σ)) * Zfun σ *
        ∑' n : ℕ, ENNReal.ofReal (cf n * Real.Gamma (σ + m) /
          (4 * π * n) ^ (σ + m)) := by
  set ρ : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal (1 / v ^ 2) with hρ
  have hρm : Measurable ρ :=
    ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_id.pow_const 2))
  -- step 1: unfold for each `t`
  have s1 : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (t ^ (σ - 1)) * ENNReal.ofReal (PhiG t - petNormSq) =
      2 * ∫⁻ v in Ioi 0, ENNReal.ofReal (t ^ (σ - 1)) * (JfunG v * hfun t v * ρ v) := by
    intro t ht
    rw [ofReal_PhiG_sub ht, unfold_thetaG ht, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [setLIntegral_congr_fun measurableSet_Ioi (fun v (hv : 0 < v) => by rw [ofReal_AintG hv])]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi s1, lintegral_const_mul' _ _ (by simp)]
  -- step 2: Tonelli
  have hjoint : Measurable (Function.uncurry fun (t v : ℝ) =>
      ENNReal.ofReal (t ^ (σ - 1)) * (JfunG v * hfun t v * ρ v)) := by
    refine (ENNReal.measurable_ofReal.comp ?_).mul
      (((measurable_JfunG.comp measurable_snd).mul measurable_hfun_uncurry).mul
        (hρm.comp measurable_snd))
    exact measurable_fst.pow_const _
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  -- step 3: Euler's integral in `t`
  have s3 : ∀ v ∈ Ioi (0 : ℝ), ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (σ - 1)) * (JfunG v * hfun t v * ρ v) =
      JfunG v * ENNReal.ofReal (v ^ (σ - 2)) * (ENNReal.ofReal (Real.Gamma σ * π ^ (-σ)) * Zfun σ) := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    have e : ∀ t, ENNReal.ofReal (t ^ (σ - 1)) * (JfunG v * hfun t v * ρ v) =
        ENNReal.ofReal (t ^ (σ - 1)) * hfun t v * (JfunG v * ρ v) := fun t => by ring
    simp_rw [e]
    have hm : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (σ - 1)) * hfun t v :=
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
        (measurable_hfun_uncurry.comp (measurable_id.prodMk measurable_const))
    rw [lintegral_mul_const _ hm, lintegral_hfun hσ hv0]
    have e2 : ENNReal.ofReal (Real.Gamma σ * π ^ (-σ) * v ^ σ) * ρ v =
        ENNReal.ofReal (Real.Gamma σ * π ^ (-σ)) * ENNReal.ofReal (v ^ (σ - 2)) := by
      rw [hρ, ← ENNReal.ofReal_mul (by have := Real.Gamma_pos_of_pos hσ; positivity),
        ← ENNReal.ofReal_mul (by have := Real.Gamma_pos_of_pos hσ; positivity)]
      congr 1
      rw [Real.rpow_sub hv0, Real.rpow_two]
      ring
    calc ENNReal.ofReal (Real.Gamma σ * π ^ (-σ) * v ^ σ) * Zfun σ * (JfunG v * ρ v)
        = JfunG v * (ENNReal.ofReal (Real.Gamma σ * π ^ (-σ) * v ^ σ) * ρ v) * Zfun σ := by ring
      _ = _ := by rw [e2]; ring
  have hm4 : Measurable fun v : ℝ => JfunG v * ENNReal.ofReal (v ^ (σ - 2)) :=
    measurable_JfunG.mul (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
  rw [setLIntegral_congr_fun measurableSet_Ioi s3, lintegral_mul_const _ hm4]
  -- step 4: the strip side (E3a)
  have s4 : ∫⁻ v in Ioi 0, JfunG v * ENNReal.ofReal (v ^ (σ - 2)) =
      ∫⁻ v in Ioi 0, ENNReal.ofReal (Aint v * v ^ (σ - 2)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
    rw [← ofReal_AintG hv, ← ENNReal.ofReal_mul]
    unfold Aint; rw [dif_pos hv]
    exact intervalIntegral.integral_nonneg zero_le_one fun x _ => (G_nonneg _)
  rw [s4, lintegral_mellin_horocycleG (by linarith)]
  ring

end RamanujanTau.RankinErrorGeneral

#print axioms RamanujanTau.RankinErrorGeneral.unfold_thetaG
#print axioms RamanujanTau.RankinErrorGeneral.lintegral_mellin_PhiG
