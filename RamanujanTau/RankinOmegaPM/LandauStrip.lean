/-
# Landau's theorem with only a *local* continuation along the real axis

`TauOmegaPM.landau_mellin` asks for a continuation `F` of `G(s) = ∫ g(t) t^{−s−1} dt` to a whole
half-plane `Re s > β`. Landau's argument only uses analyticity in a neighbourhood of the real
segment: here `F` is holomorphic on the thin strip `{β < Re s < σ₀ + η, |Im s| < r}` and agrees
with `G` on its part `Re s > σ₀` (where `G` converges). Conclusion as before: `G` converges for
every `σ > β`. (Taylor expansion at `a = σ_c + ρ` with `ρ = min((σ_c−β)/3, r/3, η/6)`, so the
disc of radius `3ρ` stays inside the strip.)
-/
import RamanujanTau.TauOmegaPM.Landau

set_option autoImplicit false

namespace RamanujanTau.RankinOmegaPM

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.TauOmegaPM
open scoped Nat

/-- **Landau's theorem, strip version.** -/
theorem landau_mellin_strip {g : ℝ → ℝ} (hg0 : ∀ t, 0 ≤ g t) (hg1 : ∀ t < 1, g t = 0)
    (hgm : Measurable g) {σ0 β η r : ℝ} (hβ : β < σ0) (hη : 0 < η) (hr : 0 < r)
    (hconv : ∀ σ : ℝ, σ0 < σ → MellinConvergent (fun t => (g t : ℂ)) (-((σ : ℝ) : ℂ)))
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {s | β < s.re ∧ s.re < σ0 + η ∧ |s.im| < r})
    (hFG : ∀ s : ℂ, σ0 < s.re → s.re < σ0 + η → |s.im| < r →
      mellin (fun t => (g t : ℂ)) (-s) = F s) :
    ∀ σ : ℝ, β < σ → MellinConvergent (fun t => (g t : ℂ)) (-((σ : ℝ) : ℂ)) := by
  set ψ : ℝ → ℂ := fun t => (g t : ℂ) with hψdef
  have h0 : ∀ t < 1, ψ t = 0 := fun t ht => by simp [hψdef, hg1 t ht]
  have hψ : Measurable ψ := Complex.measurable_ofReal.comp hgm
  have hmono : ∀ s s' : ℂ, s'.re ≤ s.re → MellinConvergent ψ s → MellinConvergent ψ s' :=
    fun s s' h hc => mc_mono h0 hψ hc h
  by_contra hcon
  push Not at hcon
  obtain ⟨σs, hσsβ, hns⟩ := hcon
  set S : Set ℝ := {σ : ℝ | MellinConvergent ψ (-((σ : ℝ) : ℂ))} with hS
  have hlow : ∀ σ ∈ S, σs < σ := by
    intro σ hσ
    by_contra h
    push Not at h
    exact hns (hmono _ _ (by simp; linarith) hσ)
  have hσ0S : σ0 + 1 ∈ S := hconv _ (by linarith)
  have hne : S.Nonempty := ⟨σ0 + 1, hσ0S⟩
  have hbdd : BddBelow S := ⟨σs, fun σ hσ => (hlow σ hσ).le⟩
  set σc : ℝ := sInf S with hσc
  have hσsc : σs ≤ σc := le_csInf hne fun σ hσ => (hlow σ hσ).le
  have hσcle : σc ≤ σ0 := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have h1 : σ0 + ε / 2 ∈ S := hconv _ (by linarith)
    have := csInf_le hbdd h1
    linarith
  have habove : ∀ σ : ℝ, σc < σ → σ ∈ S := by
    intro σ hσ
    obtain ⟨b, hb, hbσ⟩ := exists_lt_of_csInf_lt hne hσ
    exact hmono _ _ (by simp; linarith) hb
  have hconvc : ∀ s : ℂ, σc < s.re → MellinConvergent ψ (-s) := by
    intro s hs
    exact hmono _ _ (by simp) (habove s.re hs)
  set M : ℂ → ℂ := fun s => mellin ψ (-s) with hM
  -- the identity `M = F` on the convex set `V`
  set V : Set ℂ := ({s : ℂ | σc < s.re} ∩ {s : ℂ | s.re < σ0 + η}) ∩
    ({s : ℂ | s.im < r} ∩ {s : ℂ | -r < s.im}) with hV
  have hVo : IsOpen V :=
    ((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)).inter
      ((isOpen_lt continuous_im continuous_const).inter (isOpen_lt continuous_const continuous_im))
  have hVc : IsPreconnected V :=
    (((convex_halfSpace_re_gt σc).inter (convex_halfSpace_re_lt _)).inter
      ((convex_halfSpace_im_lt r).inter (convex_halfSpace_im_gt _))).isPreconnected
  have hMd : DifferentiableOn ℂ M V :=
    (differentiableOn_mellin_neg h0 hψ hconvc).mono fun s hs => hs.1.1
  have hFV : DifferentiableOn ℂ F V := hF.mono fun s hs =>
    ⟨by linarith [hs.1.1, show σc < s.re from hs.1.1], hs.1.2, abs_lt.2 ⟨hs.2.2, hs.2.1⟩⟩
  set p0 : ℂ := ((σ0 + η / 2 : ℝ) : ℂ) with hp0
  have hp0V : p0 ∈ V := by
    simp only [hV, hp0, mem_inter_iff, mem_setOf_eq, ofReal_re, ofReal_im]
    refine ⟨⟨by linarith, by linarith⟩, hr, by linarith⟩
  have hev : M =ᶠ[𝓝 p0] F := by
    set W : Set ℂ := ({s : ℂ | σ0 < s.re} ∩ {s : ℂ | s.re < σ0 + η}) ∩
      ({s : ℂ | s.im < r} ∩ {s : ℂ | -r < s.im}) with hW
    have hWo : IsOpen W :=
      ((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)).inter
        ((isOpen_lt continuous_im continuous_const).inter (isOpen_lt continuous_const continuous_im))
    have hp0W : p0 ∈ W := by
      simp only [hW, hp0, mem_inter_iff, mem_setOf_eq, ofReal_re, ofReal_im]
      refine ⟨⟨by linarith, by linarith⟩, hr, by linarith⟩
    filter_upwards [hWo.mem_nhds hp0W] with s hs
    exact hFG s hs.1.1 hs.1.2 (abs_lt.2 ⟨hs.2.2, hs.2.1⟩)
  have hEqV : EqOn M F V :=
    (hMd.analyticOnNhd hVo).eqOn_of_preconnected_of_eventuallyEq (hFV.analyticOnNhd hVo) hVc hp0V hev
  have hσcβ : β < σc := lt_of_lt_of_le hσsβ hσsc
  set ρ : ℝ := min ((σc - β) / 3) (min (r / 3) (η / 6)) with hρ
  have hρ0 : 0 < ρ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hρ1 : ρ ≤ (σc - β) / 3 := min_le_left _ _
  have hρ2 : ρ ≤ r / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ3 : ρ ≤ η / 6 := (min_le_right _ _).trans (min_le_right _ _)
  set a : ℝ := σc + ρ with ha
  set z : ℝ := σc - ρ with hz
  have haU : ((a : ℝ) : ℂ) ∈ {s : ℂ | σc < s.re} := by
    show σc < ((a : ℝ) : ℂ).re; simp [ha]; linarith
  have haV : ((a : ℝ) : ℂ) ∈ V := by
    simp only [hV, mem_inter_iff, mem_setOf_eq, ofReal_re, ofReal_im]
    refine ⟨⟨by linarith, by linarith⟩, hr, by linarith⟩
  have hFa : F =ᶠ[𝓝 ((a : ℝ) : ℂ)] M := by
    filter_upwards [hVo.mem_nhds haV] with s hs using (hEqV hs).symm
  have hball : DifferentiableOn ℂ F (Metric.ball ((a : ℝ) : ℂ) (3 * ρ)) := by
    refine hF.mono fun s hs => ?_
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have h1 := abs_re_le_norm (s - ((a : ℝ) : ℂ))
    have h2 : |(s - ((a : ℝ) : ℂ)).re| < 3 * ρ := lt_of_le_of_lt h1 hs
    have h3 := abs_im_le_norm (s - ((a : ℝ) : ℂ))
    have h4 : |(s - ((a : ℝ) : ℂ)).im| < 3 * ρ := lt_of_le_of_lt h3 hs
    rw [sub_re, ofReal_re, abs_lt] at h2
    rw [sub_im, ofReal_im, sub_zero] at h4
    refine ⟨?_, ?_, ?_⟩
    · rw [ha] at h2; linarith
    · rw [ha] at h2; linarith
    · linarith
  have hzb : ((z : ℝ) : ℂ) ∈ Metric.ball ((a : ℝ) : ℂ) (3 * ρ) := by
    rw [Metric.mem_ball, dist_eq_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [show z - a = -(2 * ρ) by rw [hz, ha]; ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  have htay := Complex.hasSum_taylorSeries_on_ball hball hzb
  -- the real terms
  set b : ℕ → ℝ → ℝ := fun n t =>
    t ^ (-a - 1) * ((2 * ρ * Real.log t) ^ n / (n ! : ℝ)) * g t with hb
  have hb0 : ∀ n t, 0 ≤ b n t := by
    intro n t
    rcases lt_or_ge t 1 with h1 | h1
    · simp [hb, hg1 t h1]
    · have : 0 ≤ Real.log t := Real.log_nonneg h1
      have ht0 : 0 ≤ t := by linarith
      simp only [hb]
      have := hg0 t
      positivity
  have hpt : ∀ n : ℕ, ∀ t ∈ Ioi (0 : ℝ),
      (t : ℂ) ^ (-((a : ℝ) : ℂ) - 1) •
        (((n ! : ℂ)⁻¹ * (((z : ℝ) : ℂ) - ((a : ℝ) : ℂ)) ^ n) • logPow ψ n t) =
        ((b n t : ℝ) : ℂ) := by
    intro n t ht
    have ht0 : (0 : ℝ) < t := ht
    obtain ⟨X, hX⟩ : ∃ X : ℝ, X = t ^ (-a - 1) := ⟨_, rfl⟩
    have e1 : (t : ℂ) ^ (-((a : ℝ) : ℂ) - 1) = ((X : ℝ) : ℂ) := by
      rw [hX, Complex.ofReal_cpow ht0.le]; push_cast; ring_nf
    have e2 : ((z : ℝ) : ℂ) - ((a : ℝ) : ℂ) = ((-(2 * ρ) : ℝ) : ℂ) := by
      rw [← ofReal_sub]; congr 1; rw [hz, ha]; ring
    have e3 : b n t = X * ((2 * ρ * Real.log t) ^ n / (n ! : ℝ)) * g t := by
      simp only [hb, hX]
    rw [e1, e2, e3]
    simp only [logPow, smul_eq_mul, hψdef]
    push_cast
    have : ((-(2 * (ρ : ℂ))) ^ n * (-(Real.log t : ℂ)) ^ n) = (2 * ρ * Real.log t) ^ n := by
      rw [← mul_pow]; ring
    rw [div_eq_mul_inv]
    linear_combination ((n ! : ℂ)⁻¹ * (X : ℂ) * (g t : ℂ)) * this
  have hconva : MellinConvergent ψ (-((a : ℝ) : ℂ)) := hconvc _ (by simp [ha]; linarith)
  have hint : ∀ n : ℕ, IntegrableOn (fun t => ((b n t : ℝ) : ℂ)) (Ioi 0) := by
    intro n
    have hmc : MellinConvergent (logPow ψ n) (-((a : ℝ) : ℂ)) :=
      conv_logPow h0 hψ hconvc n _ (by simp [ha]; linarith)
    have := hmc.const_smul ((n ! : ℂ)⁻¹ * (((z : ℝ) : ℂ) - ((a : ℝ) : ℂ)) ^ n)
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    exact hpt n t ht
  have hintR : ∀ n : ℕ, IntegrableOn (b n) (Ioi 0) := fun n => by
    simpa using (hint n).re
  have hterm : ∀ n : ℕ, (n ! : ℂ)⁻¹ • (((z : ℝ) : ℂ) - ((a : ℝ) : ℂ)) ^ n •
      iteratedDeriv n F ((a : ℝ) : ℂ) = (((∫ t in Ioi 0, b n t) : ℝ) : ℂ) := by
    intro n
    rw [hFa.iteratedDeriv_eq n, iteratedDeriv_mellin_neg h0 hψ hconvc n _ haU, mellin,
      ← integral_complex_ofReal, smul_smul, ← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [← hpt n t ht, smul_comm]
  simp_rw [hterm] at htay
  have hsumR : Summable (fun n => ∫ t in Ioi 0, b n t) :=
    Complex.summable_ofReal.1 htay.summable
  -- pointwise series
  set T : ℝ → ℝ := fun t => t ^ (-z - 1) * g t with hT
  have hTsum : ∀ t, HasSum (fun n => b n t) (T t) := by
    intro t
    rcases le_or_gt t 0 with h1 | h1
    · have hg : g t = 0 := hg1 t (by linarith)
      simp [hb, hT, hg, hasSum_zero]
    have he := NormedSpace.expSeries_div_hasSum_exp (2 * ρ * Real.log t)
    rw [← Real.exp_eq_exp_ℝ] at he
    have := (he.mul_left (t ^ (-a - 1))).mul_right (g t)
    convert this using 1
    simp only [hT]
    congr 1
    rw [mul_comm (2 * ρ) (Real.log t), ← Real.rpow_def_of_pos h1, ← Real.rpow_add h1]
    congr 1; rw [hz, ha]; ring
  have hT0 : ∀ t, 0 ≤ T t := fun t => (hTsum t).nonneg fun n => hb0 n t
  have hTm : Measurable T := by
    simp only [hT]
    exact (measurable_id.pow_const _).mul hgm
  -- monotone convergence
  have hlin : ∫⁻ t in Ioi 0, ENNReal.ofReal (T t) =
      ENNReal.ofReal (∑' n, ∫ t in Ioi 0, b n t) := by
    have e1 : ∀ t, ENNReal.ofReal (T t) = ∑' n, ENNReal.ofReal (b n t) := by
      intro t
      rw [← (hTsum t).tsum_eq]
      exact ENNReal.ofReal_tsum_of_nonneg (fun n => hb0 n t) (hTsum t).summable
    simp_rw [e1]
    have hbm : ∀ n, Measurable (b n) := by
      intro n
      simp only [hb]
      exact ((measurable_id.pow_const _).mul
        ((measurable_const.mul Real.measurable_log).pow_const n |>.div_const _)).mul hgm
    rw [lintegral_tsum fun n => (hbm n).ennreal_ofReal.aemeasurable,
      ENNReal.ofReal_tsum_of_nonneg (fun n => setIntegral_nonneg measurableSet_Ioi
        fun t _ => hb0 n t) hsumR]
    congr 1; funext n
    exact (ofReal_integral_eq_lintegral_ofReal (hintR n)
      (Eventually.of_forall fun t => hb0 n t)).symm
  have hTint : IntegrableOn T (Ioi 0) := by
    refine ⟨hTm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hT0), hlin]
    exact ENNReal.ofReal_lt_top
  have hzS : z ∈ S := by
    show MellinConvergent ψ (-((z : ℝ) : ℂ))
    unfold MellinConvergent
    refine (show IntegrableOn (fun t => ((T t : ℝ) : ℂ)) (Ioi (0 : ℝ)) volume from hTint.ofReal (𝕜 := ℂ)).congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    simp only [hT, hψdef, smul_eq_mul]
    push_cast
    rw [Complex.ofReal_cpow ht0.le]; push_cast; ring_nf
  have := csInf_le hbdd hzS
  rw [← hσc] at this
  rw [hz] at this
  linarith

end RamanujanTau.RankinOmegaPM
