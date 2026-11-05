/-
# Landau's theorem for Mellin transforms of nonnegative functions

Let `g ≥ 0` be measurable, `g = 0` on `(0,1)`, and suppose `∫₁^∞ g(t) t^{−σ₀−1} dt < ∞`. If
`G(s) = ∫ g(t) t^{−s−1} dt` (for `Re s > σ₀`) agrees with a function `F` holomorphic on
`Re s > β`, then `∫ g(t) t^{−σ−1} dt < ∞` for every `σ > β` (`landau_mellin`).

Proof. Let `σ_c` be the abscissa of convergence and suppose `σ_c > β`.

* `s ↦ ∫ ψ(t) t^{−s−1} dt` is holomorphic on `Re s > σ_c`, with `n`-th derivative
  `∫ (−log t)^n ψ(t) t^{−s−1} dt` (`hasDerivAt_mellin_neg`, `iteratedDeriv_mellin_neg`;
  differentiation under the integral sign, dominated by `log t ≤ t^ε/ε`).
* By the identity theorem `F = G` on `Re s > σ_c`.
* Taylor-expand `F` at `a = σ_c + ρ` (`Complex.hasSum_taylorSeries_on_ball`) and evaluate at the
  real point `z = σ_c − ρ`: all terms `(2ρ)^n/n! ∫ (log t)^n g(t) t^{−a−1} dt` are nonnegative,
  so by monotone convergence `∫ g(t) t^{−z−1} dt = ∑ (…) < ∞`, contradicting `z < σ_c`.

Everything is about `mellin ψ (−s) = ∫_{t>0} t^{−s−1} ψ(t) dt`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.TauOmegaPM

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Nat

/-- `(−log t)^n ψ(t)`. -/
noncomputable def logPow (ψ : ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (((-Real.log t : ℝ)) : ℂ) ^ n * ψ t

lemma logPow_zero (ψ : ℝ → ℂ) : logPow ψ 0 = ψ := by
  funext t; simp [logPow]

lemma logPow_logPow_one (ψ : ℝ → ℂ) (n : ℕ) : logPow (logPow ψ n) 1 = logPow ψ (n + 1) := by
  funext t; simp only [logPow, pow_succ]; ring

lemma measurable_logPow {ψ : ℝ → ℂ} (hψ : Measurable ψ) (n : ℕ) : Measurable (logPow ψ n) := by
  unfold logPow
  exact ((Complex.measurable_ofReal.comp Real.measurable_log.neg).pow_const n).mul hψ

lemma logPow_of_lt_one {ψ : ℝ → ℂ} (h0 : ∀ t < 1, ψ t = 0) (n : ℕ) :
    ∀ t < 1, logPow ψ n t = 0 := fun t ht => by simp [logPow, h0 t ht]

lemma norm_logPow (ψ : ℝ → ℂ) (n : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    ‖logPow ψ n t‖ = Real.log t ^ n * ‖ψ t‖ := by
  rw [logPow, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (Real.log_nonneg ht)]

lemma norm_integrand {t : ℝ} (ht : 0 < t) (s : ℂ) (v : ℂ) :
    ‖(t : ℂ) ^ (s - 1) • v‖ = t ^ (s.re - 1) * ‖v‖ := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]; simp

lemma aesm_integrand {ψ : ℝ → ℂ} (hψ : Measurable ψ) (s : ℂ) (μ : Measure ℝ) :
    AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (s - 1) • ψ t) μ :=
  ((Complex.measurable_ofReal.pow_const (s - 1)).smul hψ).aestronglyMeasurable

/-- Mellin convergence moves to the left half (`ψ = 0` on `(0,1)`). -/
lemma mc_mono {ψ : ℝ → ℂ} (h0 : ∀ t < 1, ψ t = 0) (hψ : Measurable ψ) {s s' : ℂ}
    (hc : MellinConvergent ψ s) (hss : s'.re ≤ s.re) : MellinConvergent ψ s' := by
  unfold MellinConvergent at *
  refine hc.norm.mono' (aesm_integrand hψ s' _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_integrand ht0 s', norm_integrand ht0 s]
  rcases lt_or_ge t 1 with h1 | h1
  · rw [h0 t h1]; simp
  · gcongr

/-- Mellin convergence of `(−log t)^n ψ(t)` strictly to the right. -/
lemma mc_logPow {ψ : ℝ → ℂ} (h0 : ∀ t < 1, ψ t = 0) (hψ : Measurable ψ) {s s' : ℂ}
    (hc : MellinConvergent ψ s) (hss : s'.re < s.re) (n : ℕ) :
    MellinConvergent (logPow ψ n) s' := by
  unfold MellinConvergent at *
  set ε : ℝ := s.re - s'.re with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set e : ℝ := ε / (n + 1) with he
  have he0 : 0 < e := by positivity
  refine (hc.norm.const_mul (1 / e ^ n)).mono' (aesm_integrand (measurable_logPow hψ n) s' _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_integrand ht0 s', norm_integrand ht0 s]
  rcases lt_or_ge t 1 with h1 | h1
  · rw [logPow_of_lt_one h0 n t h1, h0 t h1]; simp
  rw [norm_logPow ψ n h1]
  have hlog : Real.log t ^ n ≤ t ^ ε / e ^ n := by
    have h1' : Real.log t ^ n ≤ (t ^ e / e) ^ n :=
      pow_le_pow_left₀ (Real.log_nonneg h1) (Real.log_le_rpow_div ht0.le he0) n
    have h2 : (t ^ e / e) ^ n = t ^ (e * n) / e ^ n := by
      rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    have h3 : t ^ (e * n) ≤ t ^ ε := by
      apply Real.rpow_le_rpow_of_exponent_le h1
      rw [he]
      have : (n : ℝ) ≤ n + 1 := by linarith
      calc ε / (n + 1) * n ≤ ε / (n + 1) * (n + 1) := by gcongr
        _ = ε := by field_simp
    calc Real.log t ^ n ≤ (t ^ e / e) ^ n := h1'
      _ = t ^ (e * n) / e ^ n := h2
      _ ≤ t ^ ε / e ^ n := by gcongr
  have hpow : t ^ (s'.re - 1) * t ^ ε = t ^ (s.re - 1) := by
    rw [← Real.rpow_add ht0]; congr 1; rw [hε]; ring
  calc t ^ (s'.re - 1) * (Real.log t ^ n * ‖ψ t‖)
      ≤ t ^ (s'.re - 1) * (t ^ ε / e ^ n * ‖ψ t‖) := by gcongr
    _ = 1 / e ^ n * (t ^ (s.re - 1) * ‖ψ t‖) := by rw [← hpow]; field_simp

/-- Convergence on `Re s > σ₁` is inherited by every `(−log t)^n ψ`. -/
lemma conv_logPow {ψ : ℝ → ℂ} (h0 : ∀ t < 1, ψ t = 0) (hψ : Measurable ψ) {σ1 : ℝ}
    (hc : ∀ s : ℂ, σ1 < s.re → MellinConvergent ψ (-s)) (n : ℕ) :
    ∀ s : ℂ, σ1 < s.re → MellinConvergent (logPow ψ n) (-s) := by
  intro s hs
  have hw : σ1 < (((σ1 + s.re) / 2 : ℝ) : ℂ).re := by simp; linarith
  refine mc_logPow h0 hψ (hc _ hw) ?_ n
  simp; linarith

/-- **Differentiation under the integral sign**:
`d/ds ∫ ψ(t) t^{−s−1} dt = ∫ (−log t) ψ(t) t^{−s−1} dt` on `Re s > σ₁`. -/
lemma hasDerivAt_mellin_neg {ψ : ℝ → ℂ} (h0 : ∀ t < 1, ψ t = 0) (hψ : Measurable ψ) {σ1 : ℝ}
    (hc : ∀ s : ℂ, σ1 < s.re → MellinConvergent ψ (-s)) {s0 : ℂ} (hs0 : σ1 < s0.re) :
    HasDerivAt (fun s => mellin ψ (-s)) (mellin (logPow ψ 1) (-s0)) s0 := by
  set η : ℝ := (s0.re - σ1) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  set w : ℂ := (((σ1 + η / 2) : ℝ) : ℂ) with hw
  have hwc : MellinConvergent ψ (-w) := hc w (by rw [hw]; simp; linarith)
  set s1 : ℂ := s0 - (η : ℂ) with hs1
  have hs1re : s1.re = s0.re - η := by simp [hs1]
  have hbd : MellinConvergent (logPow ψ 1) (-s1) :=
    mc_logPow h0 hψ hwc (by rw [neg_re, neg_re, hs1re, hw]; simp; linarith) 1
  unfold mellin
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (s : ℂ) (t : ℝ) => (t : ℂ) ^ (-s - 1) • ψ t)
    (F' := fun (s : ℂ) (t : ℝ) => (t : ℂ) ^ (-s - 1) • logPow ψ 1 t)
    (x₀ := s0) (bound := fun t => ‖(t : ℂ) ^ (-s1 - 1) • logPow ψ 1 t‖) (s := Metric.ball s0 η)
    (Metric.ball_mem_nhds s0 hη0)
    (Eventually.of_forall fun s => aesm_integrand hψ (-s) _)
    (hc s0 hs0) (aesm_integrand (measurable_logPow hψ 1) (-s0) _) ?_ hbd.norm ?_
  · exact key.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs
    have ht0 : (0 : ℝ) < t := ht
    have e1 : -s - 1 = -s - 1 := rfl
    rw [show (-s - 1 : ℂ) = (-s) - 1 by ring, norm_integrand ht0,
      show (-s1 - 1 : ℂ) = (-s1) - 1 by ring, norm_integrand ht0]
    rcases lt_or_ge t 1 with h1 | h1
    · rw [logPow_of_lt_one h0 1 t h1]; simp
    · have hre : s0.re - η ≤ s.re := by
        have := abs_re_le_norm (s - s0)
        rw [Metric.mem_ball, dist_eq_norm] at hs
        have h2 : |(s - s0).re| < η := lt_of_le_of_lt this hs
        rw [sub_re, abs_lt] at h2; linarith
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1
        (by rw [neg_re, neg_re, hs1re]; linarith)) (norm_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s _hs
    have ht0 : (0 : ℝ) < t := ht
    have hd : HasDerivAt (fun s : ℂ => (t : ℂ) ^ (-s - 1))
        ((t : ℂ) ^ (-s - 1) * Complex.log t * (-1)) s := by
      have := ((hasDerivAt_id s).neg.sub_const (1 : ℂ)).const_cpow
        (c := (t : ℂ)) (Or.inl (ofReal_ne_zero.2 ht0.ne'))
      simpa using this
    have := hd.smul_const (ψ t)
    convert this using 1
    simp only [logPow, pow_one, smul_eq_mul]
    rw [← Complex.ofReal_log ht0.le]; push_cast; ring

lemma differentiableOn_mellin_neg {ψ : ℝ → ℂ} (h0 : ∀ t < 1, ψ t = 0) (hψ : Measurable ψ)
    {σ1 : ℝ} (hc : ∀ s : ℂ, σ1 < s.re → MellinConvergent ψ (-s)) :
    DifferentiableOn ℂ (fun s => mellin ψ (-s)) {s | σ1 < s.re} := fun s hs =>
  (hasDerivAt_mellin_neg h0 hψ hc hs).differentiableAt.differentiableWithinAt

/-- The `n`-th derivative of `s ↦ ∫ ψ(t) t^{−s−1} dt` on `Re s > σ₁`. -/
lemma iteratedDeriv_mellin_neg {ψ : ℝ → ℂ} (h0 : ∀ t < 1, ψ t = 0) (hψ : Measurable ψ)
    {σ1 : ℝ} (hc : ∀ s : ℂ, σ1 < s.re → MellinConvergent ψ (-s)) (n : ℕ) :
    ∀ s : ℂ, σ1 < s.re →
      iteratedDeriv n (fun s => mellin ψ (-s)) s = mellin (logPow ψ n) (-s) := by
  induction n with
  | zero => intro s _; simp [logPow_zero]
  | succ n ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    have hopen : IsOpen {s : ℂ | σ1 < s.re} := isOpen_lt continuous_const continuous_re
    have hev : iteratedDeriv n (fun s => mellin ψ (-s)) =ᶠ[𝓝 s]
        (fun s => mellin (logPow ψ n) (-s)) := by
      filter_upwards [hopen.mem_nhds hs] with u hu using ih u hu
    rw [hev.deriv_eq]
    have := hasDerivAt_mellin_neg (logPow_of_lt_one h0 n) (measurable_logPow hψ n)
      (conv_logPow h0 hψ hc n) hs
    rw [this.deriv, logPow_logPow_one]

/-- **Identity principle**: an identity `∫ ψ t^{−s−1} = H(s)` for `Re s > σ₀` extends to the whole
half-plane of convergence `Re s > σ₁` if `H` is holomorphic there. -/
lemma mellin_eq_of_eventually {ψ : ℝ → ℂ} (h0 : ∀ t < 1, ψ t = 0) (hψ : Measurable ψ)
    {σ1 : ℝ} (hc : ∀ s : ℂ, σ1 < s.re → MellinConvergent ψ (-s)) {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H {s | σ1 < s.re}) {σ0 : ℝ}
    (heq : ∀ s : ℂ, σ0 < s.re → mellin ψ (-s) = H s) :
    ∀ s : ℂ, σ1 < s.re → mellin ψ (-s) = H s := by
  set U : Set ℂ := {s | σ1 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt σ1).isPreconnected
  set r : ℝ := max σ0 σ1 + 1 with hr
  have hz0 : ((r : ℝ) : ℂ) ∈ U := by
    show σ1 < ((r : ℝ) : ℂ).re
    rw [Complex.ofReal_re, hr]; linarith [le_max_right σ0 σ1]
  have hev : (fun s => mellin ψ (-s)) =ᶠ[𝓝 ((r : ℝ) : ℂ)] H := by
    have hVo : IsOpen {s : ℂ | σ0 < s.re} := isOpen_lt continuous_const continuous_re
    have hz : ((r : ℝ) : ℂ) ∈ {s : ℂ | σ0 < s.re} := by
      show σ0 < ((r : ℝ) : ℂ).re
      rw [Complex.ofReal_re, hr]; linarith [le_max_left σ0 σ1]
    filter_upwards [hVo.mem_nhds hz] with s hs using heq s hs
  intro s hs
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    ((differentiableOn_mellin_neg h0 hψ hc).analyticOnNhd hUo) (hH.analyticOnNhd hUo) hUc hz0 hev hs

/-- **Landau's theorem for Mellin transforms of nonnegative functions.** -/
theorem landau_mellin {g : ℝ → ℝ} (hg0 : ∀ t, 0 ≤ g t) (hg1 : ∀ t < 1, g t = 0)
    (hgm : Measurable g) {σ0 β : ℝ}
    (hconv : MellinConvergent (fun t => (g t : ℂ)) (-((σ0 : ℝ) : ℂ))) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {s | β < s.re})
    (hFG : ∀ s : ℂ, σ0 < s.re → mellin (fun t => (g t : ℂ)) (-s) = F s) :
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
  have hσ0S : σ0 ∈ S := hconv
  have hne : S.Nonempty := ⟨σ0, hσ0S⟩
  have hbdd : BddBelow S := ⟨σs, fun σ hσ => (hlow σ hσ).le⟩
  set σc : ℝ := sInf S with hσc
  have hσsc : σs ≤ σc := le_csInf hne fun σ hσ => (hlow σ hσ).le
  have habove : ∀ σ : ℝ, σc < σ → σ ∈ S := by
    intro σ hσ
    obtain ⟨b, hb, hbσ⟩ := exists_lt_of_csInf_lt hne hσ
    exact hmono _ _ (by simp; linarith) hb
  have hconvc : ∀ s : ℂ, σc < s.re → MellinConvergent ψ (-s) := by
    intro s hs
    exact hmono _ _ (by simp) (habove s.re hs)
  set M : ℂ → ℂ := fun s => mellin ψ (-s) with hM
  have hEq : ∀ s : ℂ, σc < s.re → M s = F s :=
    mellin_eq_of_eventually h0 hψ hconvc
      (hF.mono fun s (hs : σc < s.re) => (show β < s.re by linarith)) hFG
  set ρ : ℝ := (σc - β) / 3 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  set a : ℝ := σc + ρ with ha
  set z : ℝ := σc - ρ with hz
  have hopen : IsOpen {s : ℂ | σc < s.re} := isOpen_lt continuous_const continuous_re
  have haU : ((a : ℝ) : ℂ) ∈ {s : ℂ | σc < s.re} := by
    show σc < ((a : ℝ) : ℂ).re; simp [ha]; linarith
  have hFa : F =ᶠ[𝓝 ((a : ℝ) : ℂ)] M := by
    filter_upwards [hopen.mem_nhds haU] with s hs using (hEq s hs).symm
  have hball : DifferentiableOn ℂ F (Metric.ball ((a : ℝ) : ℂ) (3 * ρ)) := by
    refine hF.mono fun s hs => ?_
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have h1 := abs_re_le_norm (s - ((a : ℝ) : ℂ))
    have h2 : |(s - ((a : ℝ) : ℂ)).re| < 3 * ρ := lt_of_le_of_lt h1 hs
    rw [sub_re, ofReal_re, abs_lt] at h2
    show β < s.re
    rw [ha] at h2; linarith
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

end RamanujanTau.TauOmegaPM
