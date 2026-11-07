/-
# `∫₁^∞ A(x)² x^{−2σ−1} dx < ∞` for every `σ > 23/4` (Landau, unconditional)

`A(x) = ∑_{n≤x} τ(n)`, `g(x) = |A(x)|²`.

1. `|A(x)| ≪ x^θ`, `θ = 237/40 = 11/2 + 2/5 + 1/40` (`TauPartialSumsSharp`), so the Mellin
   transform `M(s) = ∫ g(x) x^{−s−1} dx` converges and is holomorphic on `Re s > 2θ`.
2. For real `σ > θ`, Plancherel (`TauOmegaPartial`) gives `M(2σ) = ∫ |L(σ−2πiξ)/(σ−2πiξ)|² dξ
   = P(σ)` (`mellin_g_real`).
3. `P` is holomorphic on `23/4 < Re w < 6` (`Holo.differentiableOn_P`), so by the identity
   theorem `M(s) = P(s/2)` on `2θ < Re s < 12` (`mellin_eq_P_strip`).
4. `F(s) = M(s)` for `Re s > 119/10`, `P(s/2)` otherwise, is holomorphic on `Re s > 23/2`.
   Landau's theorem (`TauOmegaPM.landau_mellin`; `g ≥ 0`) gives convergence of `M` on
   `Re s > 23/2` and `M(2σ) = P(σ)` for `23/4 < σ < 6` (`mellin_sq`).
-/
import RamanujanTau.Voronoi.Holo
import RamanujanTau.TauOmegaPM.OmegaPM
import RamanujanTau.TauOmegaPartial.Omega
import RamanujanTau.TauPartialSumsSharp.Main
import RamanujanTau.HardyZerosGeneral.Main

set_option autoImplicit false

namespace RamanujanTau.Voronoi

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.HeckeL RamanujanTau.HeckeConvexGeneral RamanujanTau.TauOmegaPartial
  RamanujanTau.TauOmegaPM
open scoped ComplexConjugate Real MatrixGroups FourierTransform

/-- `Δ` as a level-one cusp form of weight `12`. -/
noncomputable abbrev Dl : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ) := CuspForm.discriminant

lemma fL_Dl : fL Dl = tauL := by
  have h1 : AnalyticOnNhd ℂ (fL Dl) univ :=
    (fL_entire Dl (by norm_num)).differentiableOn.analyticOnNhd isOpen_univ
  have h2 : AnalyticOnNhd ℂ tauL univ :=
    tauLSeries_entire.differentiableOn.analyticOnNhd isOpen_univ
  have hev : fL Dl =ᶠ[𝓝 (8 : ℂ)] tauL := by
    have hVo : IsOpen {s : ℂ | 7 < s.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hVo.mem_nhds (show (7 : ℝ) < (8 : ℂ).re by norm_num)] with s hs
    have hs' : (7 : ℝ) < s.re := hs
    rw [fL_eq_LSeries Dl (by norm_num) (by norm_num; linarith), tauL_eq_LSeries hs']
    congr 1; funext n; exact coef_discriminant n
  funext s
  exact h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_univ (mem_univ _) hev
    (mem_univ s)

lemma Fs_eq (σ ξ : ℝ) : Fs Dl σ ξ = Gt ((σ : ℂ) - 2 * π * ξ * I) := by
  rw [Fs, fL_Dl]; rfl

lemma Gt_conj (s : ℂ) : Gt (conj s) = conj (Gt s) := by
  unfold Gt; rw [RamanujanTau.HeckeZeros.tauL_conj, map_div₀]

/-- On the real axis `P(σ) = ∫ |F_σ|²`. -/
lemma P_real (σ : ℝ) : P σ = ((∫ ξ : ℝ, ‖Fs Dl σ ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [P, ← integral_complex_ofReal]
  congr 1; funext ξ
  unfold Qd
  have e : (σ : ℂ) + 2 * π * ξ * I = conj ((σ : ℂ) - 2 * π * ξ * I) := by
    apply Complex.ext <;> simp
  rw [e, Gt_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Fs_eq]

/-! ### The sharp sup bound and Mellin convergence on `Re s > 2θ` -/

/-- `θ = 237/40`. -/
noncomputable def θs : ℝ := 237 / 40

lemma sharp_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖A Dl x‖ ≤ C * x ^ θs := by
  obtain ⟨C, hC⟩ := RamanujanTau.TauPartialSumsSharp.cuspForm_partial_sum_sharp Dl
    (ε := 1 / 40) (by norm_num)
  have e : (((12 : ℕ) : ℝ) - 1) / 2 + 2 / 5 + 1 / 40 = θs := by unfold θs; norm_num
  have hC0 : 0 ≤ C := by
    have h := hC 1 le_rfl
    rw [Real.one_rpow, mul_one] at h
    exact le_trans (norm_nonneg _) h
  refine ⟨C, hC0, fun x hx => ?_⟩
  have h := hC x hx
  rw [e] at h
  exact h

/-- `g(x) = |A(x)|²`. -/
noncomputable def gsq (x : ℝ) : ℝ := ‖A Dl x‖ ^ 2

/-- `g` as a complex-valued function. -/
noncomputable def gC (x : ℝ) : ℂ := (gsq x : ℂ)

lemma gsq_nonneg (x : ℝ) : 0 ≤ gsq x := by unfold gsq; positivity

lemma gsq_of_lt_one {x : ℝ} (hx : x < 1) : gsq x = 0 := by
  simp [gsq, A_of_lt_one Dl hx]

lemma gC_of_lt_one {x : ℝ} (hx : x < 1) : gC x = 0 := by
  simp [gC, gsq_of_lt_one hx]

lemma measurable_gsq : Measurable gsq := ((measurable_A Dl).norm.pow_const 2)

lemma measurable_gC : Measurable gC := Complex.measurable_ofReal.comp measurable_gsq

lemma mc_large : ∀ s : ℂ, 2 * θs < s.re → MellinConvergent gC (-s) := by
  obtain ⟨C, hC0, hC⟩ := sharp_bound
  refine mc_of_bound (fun t ht => gC_of_lt_one ht) measurable_gC (K := C ^ 2) (θ := 2 * θs) ?_
  intro t ht
  have ht0 : 0 < t := by linarith
  rw [gC, Complex.norm_real, Real.norm_of_nonneg (gsq_nonneg t), gsq]
  have h := pow_le_pow_left₀ (norm_nonneg _) (hC t ht) 2
  calc ‖A Dl t‖ ^ 2 ≤ (C * t ^ θs) ^ 2 := h
    _ = C ^ 2 * t ^ (2 * θs) := by
        rw [mul_pow, ← Real.rpow_natCast (t ^ θs), ← Real.rpow_mul ht0.le]; push_cast; ring_nf

/-- **Plancherel on the real axis**: `M(2σ) = P(σ)` for `σ > θ`. -/
theorem mellin_g_real {σ : ℝ} (hσ : θs < σ) :
    mellin gC (-(((2 * σ : ℝ)) : ℂ)) = P σ := by
  obtain ⟨C, hC0, hC⟩ := sharp_bound
  have hθ0 : (0 : ℝ) ≤ θs := by unfold θs; norm_num
  have hX : ∀ x ≥ (1 : ℝ), ‖A Dl x‖ ≤ C * x ^ θs := fun x hx => hC x hx
  obtain ⟨hi, hmem, _⟩ := hfun_L1L2 Dl hθ0 hC0 le_rfl hX hσ
  obtain ⟨_, hpl⟩ := plancherel_of_integrable hi hmem
  have hF : 𝓕 (hfun Dl σ) = Fs Dl σ := by
    funext ξ; exact fourier_hfun Dl (by norm_num) hθ0 hX hσ ξ
  rw [hF] at hpl
  rw [P_real, hpl, mellin_eq_fourier, Real.fourier_real_eq]
  have hre : (-(((2 * σ : ℝ)) : ℂ)).re = -(2 * σ) := by simp
  have him : (-(((2 * σ : ℝ)) : ℂ)).im = 0 := by simp
  rw [hre, him, zero_div, ← integral_complex_ofReal]
  congr 1; funext v
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]
  rw [hfun, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, gC, gsq]
  rw [Complex.real_smul]
  push_cast
  rw [mul_pow, ← Complex.exp_nat_mul]
  congr 2; push_cast; ring

/-! ### Identity theorem on the strip `2θ < Re s < 12` -/

lemma differentiableOn_M : DifferentiableOn ℂ (fun s => mellin gC (-s)) {s | 2 * θs < s.re} :=
  differentiableOn_mellin_neg (fun t ht => gC_of_lt_one ht) measurable_gC mc_large

lemma differentiableOn_Phalf {U : Set ℂ} (hU : ∀ s ∈ U, 23 / 2 < s.re ∧ s.re < 12) :
    DifferentiableOn ℂ (fun s => P (s / 2)) U := by
  refine differentiableOn_P.comp (differentiableOn_id.div_const 2) fun s hs => ?_
  obtain ⟨h1, h2⟩ := hU s hs
  show 23 / 4 < (id s / 2).re ∧ (id s / 2).re < 6
  simp only [id, Complex.div_ofNat_re]
  constructor <;> linarith

lemma θs_val : θs = 237 / 40 := rfl

/-- **`M(s) = P(s/2)` on `2θ < Re s < 12`.** -/
theorem mellin_eq_P_strip {s : ℂ} (h1 : 2 * θs < s.re) (h2 : s.re < 12) :
    mellin gC (-s) = P (s / 2) := by
  set U : Set ℂ := {s : ℂ | 2 * θs < s.re ∧ s.re < 12} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt (2 * θs)).inter (convex_halfSpace_re_lt 12)).isPreconnected
  have hf : AnalyticOnNhd ℂ (fun s => mellin gC (-s)) U :=
    (differentiableOn_M.mono fun s hs => hs.1).analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ (fun s => P (s / 2)) U :=
    (differentiableOn_Phalf fun s (hs : 2 * θs < s.re ∧ s.re < 12) =>
      ⟨by rw [θs_val] at hs; linarith [hs.1], hs.2⟩).analyticOnNhd
      hUo
  set z0 : ℂ := ((119 / 10 : ℝ) : ℂ) with hz0
  have hz0U : z0 ∈ U := by
    show 2 * θs < z0.re ∧ z0.re < 12
    rw [hz0, Complex.ofReal_re, θs_val]; norm_num
  have hfreq : ∃ᶠ z in 𝓝[≠] z0, mellin gC (-z) = P (z / 2) := by
    rw [Filter.frequently_iff]
    intro W hW
    obtain ⟨V, hV, hVW⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hW
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
    set r : ℝ := min (ε / 2) (1 / 40) with hr
    have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
    have hr1 : r ≤ 1 / 40 := min_le_right _ _
    have hr2 : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine ⟨((119 / 10 + r : ℝ) : ℂ), hVW ⟨hball ?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, hz0, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      rw [show (119 / 10 + r - 119 / 10 : ℝ) = r by ring, abs_of_pos hr0]; exact hr2
    · intro h
      have := congrArg Complex.re (show ((119 / 10 + r : ℝ) : ℂ) = z0 from h)
      rw [hz0, Complex.ofReal_re, Complex.ofReal_re] at this; linarith
    · have hσ : θs < (119 / 10 + r) / 2 := by rw [θs_val]; linarith
      have h := mellin_g_real hσ
      have e1 : (((2 * ((119 / 10 + r) / 2) : ℝ)) : ℂ) = ((119 / 10 + r : ℝ) : ℂ) := by
        congr 1; ring
      have e2 : (((119 / 10 + r : ℝ) : ℂ)) / 2 = (((119 / 10 + r) / 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [e1] at h; rw [e2]; exact h
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hUc hz0U hfreq ⟨h1, h2⟩

/-! ### The glued function and Landau -/

/-- `F(s) = M(s)` for `Re s > 119/10`, `P(s/2)` otherwise. -/
noncomputable def FL (s : ℂ) : ℂ := if 119 / 10 < s.re then mellin gC (-s) else P (s / 2)

lemma FL_eq_P {s : ℂ} (h1 : 23 / 2 < s.re) (h2 : s.re < 12) : FL s = P (s / 2) := by
  unfold FL
  split_ifs with h
  · exact mellin_eq_P_strip (by rw [θs_val]; linarith) h2
  · rfl

lemma differentiableOn_FL : DifferentiableOn ℂ FL {s | 23 / 2 < s.re} := by
  intro s0 hs0
  have hs0' : 23 / 2 < s0.re := hs0
  refine DifferentiableAt.differentiableWithinAt ?_
  rcases lt_or_ge (119 / 10 : ℝ) s0.re with h | h
  · have hO : IsOpen {s : ℂ | 119 / 10 < s.re} := isOpen_lt continuous_const continuous_re
    have hev : (fun s => mellin gC (-s)) =ᶠ[𝓝 s0] FL := by
      filter_upwards [hO.mem_nhds h] with s hs
      unfold FL; rw [if_pos hs]
    have hd : DifferentiableAt ℂ (fun s => mellin gC (-s)) s0 :=
      (differentiableOn_M s0 (by show 2 * θs < s0.re; rw [θs_val]; linarith)).differentiableAt
        ((isOpen_lt continuous_const continuous_re).mem_nhds
          (by show 2 * θs < s0.re; rw [θs_val]; linarith))
    exact hd.congr_of_eventuallyEq hev.symm
  · set U : Set ℂ := {s : ℂ | 23 / 2 < s.re ∧ s.re < 12} with hU
    have hUo : IsOpen U :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
    have hs0U : s0 ∈ U := ⟨hs0', by linarith⟩
    have hev : (fun s => P (s / 2)) =ᶠ[𝓝 s0] FL := by
      filter_upwards [hUo.mem_nhds hs0U] with s hs
      exact (FL_eq_P hs.1 hs.2).symm
    have hd : DifferentiableAt ℂ (fun s => P (s / 2)) s0 :=
      ((differentiableOn_Phalf fun s hs => hs) s0 hs0U).differentiableAt (hUo.mem_nhds hs0U)
    exact hd.congr_of_eventuallyEq hev.symm

/-- **Landau**: `M(s)` converges on `Re s > 23/2`. -/
theorem mc_all : ∀ σ : ℝ, 23 / 2 < σ → MellinConvergent gC (-((σ : ℝ) : ℂ)) := by
  have hconv : MellinConvergent (fun t => (gsq t : ℂ)) (-(((119 / 10 + 1 : ℝ)) : ℂ)) :=
    mc_large _ (by rw [Complex.ofReal_re, θs_val]; norm_num)
  exact landau_mellin gsq_nonneg (fun t ht => gsq_of_lt_one ht) measurable_gsq hconv
    differentiableOn_FL (fun s hs => by
      unfold FL; rw [if_pos (by linarith)]; rfl)

lemma mc_all' : ∀ s : ℂ, 23 / 2 < s.re → MellinConvergent gC (-s) := by
  intro s hs
  exact mc_mono (fun t ht => gC_of_lt_one ht) measurable_gC (mc_all s.re hs) (by simp)

/-- **Mean square identity**: for `23/4 < σ < 6`, `∫ |A(x)|² x^{−2σ−1} dx` converges and equals
`∫ |L(Δ,σ−2πiξ)/(σ−2πiξ)|² dξ`. -/
theorem mellin_sq {σ : ℝ} (h1 : 23 / 4 < σ) (h2 : σ < 6) :
    MellinConvergent gC (-(((2 * σ : ℝ)) : ℂ)) ∧
      mellin gC (-(((2 * σ : ℝ)) : ℂ)) = ((∫ ξ : ℝ, ‖Fs Dl σ ξ‖ ^ 2 : ℝ) : ℂ) := by
  refine ⟨mc_all _ (by linarith), ?_⟩
  have heq := mellin_eq_of_eventually (fun t ht => gC_of_lt_one ht) measurable_gC mc_all'
    differentiableOn_FL (σ0 := 119 / 10 + 1) (fun s hs => by
      unfold FL; rw [if_pos (by linarith)])
  rw [heq _ (by rw [Complex.ofReal_re]; linarith), FL_eq_P (by rw [Complex.ofReal_re]; linarith)
    (by rw [Complex.ofReal_re]; linarith), ← P_real]
  congr 1; push_cast; ring

end RamanujanTau.Voronoi
