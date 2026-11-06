/-
# The Mellin transform of the Rankin–Selberg error term, and its log-scale Fourier transform

`A(x) = ∑_{n ≤ x} aₙ`, `R(x) = A(x) − c x` for `x > 1`, `R(x) = 0` for `x < 1` (`Rf a c`).

* `mellin_Rf_large`: `∫₀^∞ R(x) x^{−s−1} dx = D(s)/s − c/(s−1)` for `Re s > 2`;
* `Lam_eq_mellin`: if `‖R(x)‖ ≤ c₀ x^θ` for `x ≥ X₀`, then on `{Re s > θ} ∩ {Im s < 0}`
  `Lam(s) γₘ(s)⁻¹ = ζ(2s) (s M(s) + c s/(s−1))`, `M(s) = mellin R (−s)` (identity principle; the
  half-plane cut along `Im s < 0` avoids the poles `s = 1/2, 1` of `ζ(2s)` and `Lam`);
* `fourier_hfun`, `hfun_L1L2`: `h_σ(u) = e^{σu} R(e^{−u})` has `𝓕h_σ(ξ) = M(σ − 2πiξ)`, lies in
  `L¹ ∩ L²`, and `∫|h_σ|² ≤ c₀²/(2(σ−θ)) + S² log X₀`.
-/
import RamanujanTau.RankinOmega.FirstMoment
import RamanujanTau.TauOmegaPartial.Fourier

set_option autoImplicit false

namespace RamanujanTau.RankinOmega

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open scoped Real FourierTransform

section Mellin

variable (a : ℕ → ℝ) (c : ℝ)

/-- `A(x) = ∑_{1 ≤ n ≤ x} aₙ`. -/
noncomputable def Asum (x : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (a n : ℂ)

/-- The main-term indicator `1_{x > 1} c x`. -/
noncomputable def Ind (x : ℝ) : ℂ := (Ioi (1 : ℝ)).indicator (fun x => ((c * x : ℝ) : ℂ)) x

/-- The error term `R(x) = A(x) − 1_{x>1} c x`. -/
noncomputable def Rf (x : ℝ) : ℂ := Asum a x - Ind c x

variable {a}

lemma Asum_of_lt_one {x : ℝ} (hx : x < 1) : Asum a x = 0 := by
  have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx
  simp [Asum, this]

lemma Rf_of_lt_one {x : ℝ} (hx : x < 1) : Rf a c x = 0 := by
  have h : Ind c x = 0 := indicator_of_notMem (by simp only [mem_Ioi, not_lt]; linarith) _
  rw [Rf, Asum_of_lt_one hx, h, sub_zero]

lemma Rf_of_one_lt {x : ℝ} (hx : 1 < x) : Rf a c x = Asum a x - ((c * x : ℝ) : ℂ) := by
  rw [Rf, Ind, indicator_of_mem (show x ∈ Ioi (1 : ℝ) from hx)]

lemma measurable_Asum : Measurable (Asum a) := by
  have h : Asum a = (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (a n : ℂ)) ∘ (fun x : ℝ => ⌊x⌋₊) := rfl
  rw [h]
  exact (measurable_from_nat).comp Nat.measurable_floor

lemma measurable_Ind : Measurable (Ind c) :=
  (measurable_ofReal.comp (measurable_const.mul measurable_id)).indicator measurableSet_Ioi

lemma measurable_Rf : Measurable (Rf a c) := measurable_Asum.sub (measurable_Ind c)

lemma norm_Asum_le {x X : ℝ} (hx : x ≤ X) :
    ‖Asum a x‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ‖(a n : ℂ)‖ := by
  refine (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hx)) (fun _ _ _ => norm_nonneg _)

lemma norm_Ind_le {x : ℝ} (hx : 0 ≤ x) : ‖Ind c x‖ ≤ |c| * x := by
  unfold Ind
  by_cases h : x ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem h, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hx]
  · rw [indicator_of_notMem h, norm_zero]; positivity

lemma norm_Rf_le {x X : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ X) :
    ‖Rf a c x‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ‖(a n : ℂ)‖ + |c| * X := by
  refine (norm_sub_le _ _).trans ?_
  have := norm_Ind_le c hx0
  have : |c| * x ≤ |c| * X := by gcongr
  linarith [norm_Asum_le (a := a) hx]

lemma locallyIntegrableOn_Rf : LocallyIntegrableOn (Rf a c) (Ioi 0) := by
  refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun K hK hKc => ?_
  obtain ⟨R, hR⟩ := hKc.bddAbove
  exact Measure.integrableOn_of_bounded hKc.measure_lt_top.ne (measurable_Rf c).aestronglyMeasurable
    ((ae_restrict_iff' hKc.measurableSet).2 (Eventually.of_forall fun x hx =>
      norm_Rf_le c (le_of_lt (hK hx)) (hR hx)))

lemma locallyIntegrableOn_Asum : LocallyIntegrableOn (Asum a) (Ioi 0) := by
  refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun K _ hKc => ?_
  obtain ⟨R, hR⟩ := hKc.bddAbove
  exact Measure.integrableOn_of_bounded hKc.measure_lt_top.ne measurable_Asum.aestronglyMeasurable
    ((ae_restrict_iff' hKc.measurableSet).2 (Eventually.of_forall fun x hx =>
      norm_Asum_le (a := a) (hR hx)))

variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

include habs in
lemma sum_norm_le_sq : ∃ S2 : ℝ, 0 ≤ S2 ∧ ∀ N : ℕ,
    ∑ k ∈ Finset.Icc 1 N, ‖(a k : ℂ)‖ ≤ S2 * (N : ℝ) ^ 2 := by
  have hs := summable_a2 habs
  refine ⟨∑' n : ℕ, ‖(a n : ℂ)‖ / (n : ℝ) ^ (2 : ℝ), tsum_nonneg fun n =>
    div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _), fun N => ?_⟩
  calc ∑ k ∈ Finset.Icc 1 N, ‖(a k : ℂ)‖
      ≤ ∑ k ∈ Finset.Icc 1 N, ‖(a k : ℂ)‖ / (k : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun k hk => ?_
        simp only [Finset.mem_Icc] at hk
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
        have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk.2
        rw [Real.rpow_two, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have := norm_nonneg (a k : ℂ)
        have : (k : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by gcongr
        nlinarith
    _ = (∑ k ∈ Finset.Icc 1 N, ‖(a k : ℂ)‖ / (k : ℝ) ^ (2 : ℝ)) * (N : ℝ) ^ 2 := by
        rw [Finset.sum_mul]
    _ ≤ _ := by
        gcongr
        exact hs.sum_le_tsum _ fun n _ => div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

include habs in
lemma mellin_Asum_large {s : ℂ} (hs : 2 < s.re) :
    MellinConvergent (Asum a) (-s) ∧ mellin (Asum a) (-s) = LSeries (fun n => (a n : ℂ)) s / s := by
  obtain ⟨S2, hS20, hS2⟩ := sum_norm_le_sq habs
  have hO : (fun n : ℕ ↦ ∑ j ∈ Finset.Icc 1 n, ‖(a j : ℂ)‖) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (2 : ℝ) := by
    refine IsBigO.of_bound S2 (Eventually.of_forall fun N => ?_)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
      Real.norm_of_nonneg (by positivity), Real.rpow_two]
    exact hS2 N
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  constructor
  · refine mellinConvergent_of_isBigO_rpow (a := -2) (b := -s.re - 1)
      locallyIntegrableOn_Asum ?_
      (by simp; linarith) ?_ (by simp)
    · refine IsBigO.of_bound S2 ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [neg_neg, Real.norm_of_nonneg (by positivity)]
      refine (norm_Asum_le (a := a) le_rfl).trans ((hS2 _).trans ?_)
      rw [Real.rpow_two]
      gcongr
      exact Nat.floor_le hx
    · have : Asum a =ᶠ[𝓝[>] 0] 0 := by
        filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx using Asum_of_lt_one hx.2
      exact this.trans_isBigO (isBigO_zero _ _)
  have hL := LSeries_eq_mul_integral' (fun n => (a n : ℂ)) (r := 2) (by norm_num) hs hO
  rw [hL, mul_div_cancel_left₀ _ hs0, mellin]
  rw [← setIntegral_eq_of_subset_of_ae_diff_eq_zero measurableSet_Ioi.nullMeasurableSet
    (Ioi_subset_Ioi zero_le_one)]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [Asum, smul_eq_mul]
    rw [mul_comm]; congr 2; ring
  · have h1 : ∀ᵐ x : ℝ ∂volume, x ∈ ({1} : Set ℝ)ᶜ :=
      compl_mem_ae_iff.mpr (measure_singleton 1)
    filter_upwards [h1] with x hx1 hx
    have hx1' : x ≠ 1 := hx1
    rcases hx with ⟨h0, h1⟩
    simp only [mem_Ioi, not_lt] at h1 h0
    have : x < 1 := lt_of_le_of_ne h1 hx1'
    have h2 := Asum_of_lt_one (a := a) this
    simp only [Asum] at h2
    rw [h2, zero_mul]

lemma mellin_Ind_large {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (Ind c) (-s) ∧ mellin (Ind c) (-s) = c / (s - 1) := by
  have hs1 : s - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; rw [h] at hs; simp at hs
  have e : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • Ind c t =
      (Ioi (1 : ℝ)).indicator (fun t : ℝ => (c : ℂ) * (t : ℂ) ^ (-s)) t := by
    intro t
    by_cases h : t ∈ Ioi (1 : ℝ)
    · have ht0 : (t : ℂ) ≠ 0 := by
        have : (0 : ℝ) < t := lt_trans zero_lt_one h
        exact_mod_cast this.ne'
      rw [Ind, indicator_of_mem h, indicator_of_mem h, smul_eq_mul]
      have : (t : ℂ) ^ (-s) = (t : ℂ) ^ (-s - 1) * t := by
        rw [show -s = (-s - 1) + 1 by ring, Complex.cpow_add _ _ ht0, Complex.cpow_one]; ring_nf
      rw [this]; push_cast; ring
    · rw [Ind, indicator_of_notMem h, indicator_of_notMem h, smul_zero]
  have hI : IntegrableOn (fun t : ℝ => (c : ℂ) * (t : ℂ) ^ (-s)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one).const_mul _
  constructor
  · unfold MellinConvergent
    rw [show (fun t : ℝ => (t : ℂ) ^ (-s - 1) • Ind c t) =
      (Ioi (1 : ℝ)).indicator (fun t : ℝ => (c : ℂ) * (t : ℂ) ^ (-s)) from funext e]
    exact (hI.integrable_indicator measurableSet_Ioi).integrableOn
  · unfold mellin
    rw [show (fun t : ℝ => (t : ℂ) ^ (-s - 1) • Ind c t) =
      (Ioi (1 : ℝ)).indicator (fun t : ℝ => (c : ℂ) * (t : ℂ) ^ (-s)) from funext e,
      setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one,
      integral_const_mul, integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
    have hs1' : -s + 1 ≠ 0 := by intro h; apply hs1; linear_combination -h
    push_cast
    rw [Complex.one_cpow]
    field_simp
    ring

include habs in
/-- **Mellin transform of the error term**, `Re s > 2`. -/
theorem mellin_Rf_large {s : ℂ} (hs : 2 < s.re) :
    mellin (Rf a c) (-s) = LSeries (fun n => (a n : ℂ)) s / s - c / (s - 1) := by
  obtain ⟨h1, e1⟩ := mellin_Asum_large habs hs
  obtain ⟨h2, e2⟩ := mellin_Ind_large c (s := s) (by linarith)
  have := (hasMellin_sub h1 h2).2
  rw [e1, e2] at this
  exact this

/-- `M(s) = mellin R (−s)` is holomorphic on `Re s > θ` under `‖R(x)‖ ≤ c₀ x^θ`. -/
lemma differentiableAt_mellin_Rf {θ c0 X0 : ℝ} (hX : ∀ x ≥ X0, ‖Rf a c x‖ ≤ c0 * x ^ θ)
    {s : ℂ} (hs : θ < s.re) : DifferentiableAt ℂ (fun s => mellin (Rf a c) (-s)) s := by
  have htop : Rf a c =O[atTop] (· ^ (-(-θ))) := by
    simp only [neg_neg]
    refine IsBigO.of_bound c0 ?_
    filter_upwards [eventually_ge_atTop X0, eventually_gt_atTop 0] with x hx hx0
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]; exact hX x hx
  have hbot : Rf a c =O[𝓝[>] 0] (· ^ (-(-s.re - 1))) := by
    have : Rf a c =ᶠ[𝓝[>] 0] 0 := by
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx using Rf_of_lt_one c hx.2
    exact this.trans_isBigO (isBigO_zero _ _)
  have hd := mellin_differentiableAt_of_isBigO_rpow (locallyIntegrableOn_Rf c) htop
    (s := -s) (by simp; exact hs) hbot (by simp)
  exact hd.comp s differentiableAt_id.neg

include habs in
/-- **The completed function in terms of `M`**, on `{Re s > θ} ∩ {Im s < 0}`. -/
theorem Lam_eq_mellin {m : ℕ} {κ : ℝ} (d : RSDataM m a κ) {θ c0 X0 : ℝ} (hθ : 0 ≤ θ)
    (hX : ∀ x ≥ X0, ‖Rf a c x‖ ≤ c0 * x ^ θ) {s : ℂ} (hs : θ < s.re) (him : s.im < 0) :
    Lam d s * invGamM m s =
      riemannZeta (2 * s) * (s * mellin (Rf a c) (-s) + c * s / (s - 1)) := by
  set U : Set ℂ := {z : ℂ | θ < z.re} ∩ {z : ℂ | z.im < 0} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_im continuous_const)
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hnr : ∀ z ∈ U, ∀ r : ℝ, z ≠ r := by
    intro z hz r h; have := hz.2; rw [h] at this; simp at this
  have hF : DifferentiableOn ℂ (fun z => Lam d z * invGamM m z) U := by
    intro z hz
    have h0 : z ≠ 0 := by simpa using hnr z hz 0
    have h1 : z ≠ 1 := by simpa using hnr z hz 1
    exact ((differentiableAt_Lam d h0 h1).mul (differentiable_invGamM m z)).differentiableWithinAt
  have hG : DifferentiableOn ℂ
      (fun z => riemannZeta (2 * z) * (z * mellin (Rf a c) (-z) + c * z / (z - 1))) U := by
    intro z hz
    have h1 : z - 1 ≠ 0 := sub_ne_zero.2 (by simpa using hnr z hz 1)
    have h2 : 2 * z ≠ 1 := by
      intro h; apply hnr z hz (1 / 2); push_cast; linear_combination h / 2
    have hζ : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) z :=
      (differentiableAt_riemannZeta h2).comp z (differentiableAt_id.const_mul 2)
    refine (hζ.mul ((differentiableAt_id.mul (differentiableAt_mellin_Rf c hX hz.1)).add
      ((differentiableAt_id.const_mul (c : ℂ)).div (differentiableAt_id.sub_const 1) h1))).differentiableWithinAt
  set z0 : ℂ := (max θ 2 + 1 : ℝ) - I with hz0
  have hz0re : z0.re = max θ 2 + 1 := by simp [hz0]
  have hz0U : z0 ∈ U := by
    refine ⟨?_, by simp [hz0]⟩
    show θ < z0.re
    rw [hz0re]; linarith [le_max_left θ 2]
  have hev : (fun z => Lam d z * invGamM m z) =ᶠ[𝓝 z0]
      (fun z => riemannZeta (2 * z) * (z * mellin (Rf a c) (-z) + c * z / (z - 1))) := by
    have hV : {z : ℂ | 2 < z.re} ∈ 𝓝 z0 :=
      (isOpen_lt continuous_const continuous_re).mem_nhds
        (by show 2 < z0.re; rw [hz0re]; linarith [le_max_right θ 2])
    filter_upwards [hV] with z hz
    have hz : 2 < z.re := hz
    have e1 : Lam d z * invGamM m z = Zf d z := rfl
    rw [e1, Zf_eq d habs (by linarith), mellin_Rf_large c habs hz]
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz; linarith
    have hz1 : z - 1 ≠ 0 := by
      intro h; rw [sub_eq_zero] at h; rw [h] at hz; norm_num at hz
    field_simp
    ring
  exact (hF.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hUo) hUc
    hz0U hev ⟨hs, him⟩

end Mellin

/-! ### The log-scale function `h_σ(u) = e^{σu} R(e^{−u})` -/

section Fourier

variable (a : ℕ → ℝ) (c : ℝ)

noncomputable def hfun (σ : ℝ) (u : ℝ) : ℂ := Real.exp (σ * u) • Rf a c (Real.exp (-u))

lemma fourier_hfun (σ ξ : ℝ) :
    𝓕 (hfun a c σ) ξ = mellin (Rf a c) (-((σ : ℂ) - 2 * π * ξ * I)) := by
  set w : ℂ := (σ : ℂ) - 2 * π * ξ * I with hw
  have hre : (-w).re = -σ := by simp [hw]
  have him : (-w).im = 2 * π * ξ := by simp [hw]
  have h := mellin_eq_fourier (Rf a c) (s := -w)
  rw [hre, him] at h
  have e1 : (2 * π * ξ) / (2 * π) = ξ := by field_simp
  rw [e1] at h
  have e2 : (fun u : ℝ => Real.exp (-(-σ) * u) • Rf a c (Real.exp (-u))) = hfun a c σ := by
    funext u; simp [hfun]
  rw [e2] at h
  exact h.symm

lemma measurable_hfun (σ : ℝ) : Measurable (hfun a c σ) := by
  unfold hfun
  exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).smul
    ((measurable_Rf c).comp (Real.measurable_exp.comp measurable_neg))

/-- The near-range bound `S = ∑_{n ≤ X₀} |aₙ| + |c| X₀`. -/
noncomputable def Sb (a : ℕ → ℝ) (c X0 : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X0⌋₊, ‖(a n : ℂ)‖ + |c| * X0

lemma norm_hfun_le {θ c0 X0 σ : ℝ} (hθ : 0 ≤ θ) (hc0 : 0 ≤ c0) (hX0 : 1 ≤ X0)
    (hX : ∀ x ≥ X0, ‖Rf a c x‖ ≤ c0 * x ^ θ) (hσ : θ ≤ σ) (u : ℝ) :
    ‖hfun a c σ u‖ ≤ TauOmegaPartial.G1 c0 (σ - θ) (Real.log X0) (Sb a c X0) u ∧
    ‖hfun a c σ u‖ ^ 2 ≤ TauOmegaPartial.G2 c0 (σ - θ) (Real.log X0) (Sb a c X0) u := by
  set S := Sb a c X0 with hS
  have hS0 : 0 ≤ S := by
    rw [hS, Sb]; have := Finset.sum_nonneg fun n (_ : n ∈ Finset.Icc 1 ⌊X0⌋₊) => norm_nonneg (a n : ℂ)
    have : 0 ≤ |c| * X0 := by have := abs_nonneg c; nlinarith
    linarith
  have hn : ‖hfun a c σ u‖ = Real.exp (σ * u) * ‖Rf a c (Real.exp (-u))‖ := by
    rw [hfun, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hI1 : 0 ≤ (Iic (0 : ℝ)).indicator (fun u => c0 * Real.exp ((σ - θ) * u)) u :=
    Set.indicator_nonneg (fun _ _ => by positivity) _
  have hI2 : 0 ≤ (Icc (-Real.log X0) 0).indicator (fun _ => S) u :=
    Set.indicator_nonneg (fun _ _ => hS0) _
  have hJ1 : 0 ≤ (Iic (0 : ℝ)).indicator (fun u => c0 ^ 2 * Real.exp ((2 * (σ - θ)) * u)) u :=
    Set.indicator_nonneg (fun _ _ => by positivity) _
  have hJ2 : 0 ≤ (Icc (-Real.log X0) 0).indicator (fun _ => S ^ 2) u :=
    Set.indicator_nonneg (fun _ _ => by positivity) _
  unfold TauOmegaPartial.G1 TauOmegaPartial.G2
  rcases lt_or_ge 0 u with hu | hu
  · have h0 : hfun a c σ u = 0 := by
      rw [hfun, Rf_of_lt_one c ((Real.exp_lt_exp.2 (by linarith : -u < 0)).trans_eq Real.exp_zero),
        smul_zero]
    rw [h0, norm_zero]
    exact ⟨by linarith, by nlinarith⟩
  rcases le_or_gt u (-Real.log X0) with hL | hL
  · have hx : X0 ≤ Real.exp (-u) := by
      rw [← Real.exp_log (by linarith : (0:ℝ) < X0)]; exact Real.exp_le_exp.2 (by linarith)
    have hA := hX _ hx
    rw [← Real.exp_mul] at hA
    have hb : ‖hfun a c σ u‖ ≤ c0 * Real.exp ((σ - θ) * u) := by
      rw [hn]
      calc Real.exp (σ * u) * ‖Rf a c (Real.exp (-u))‖ ≤ Real.exp (σ * u) * (c0 * Real.exp (-u * θ)) :=
            by gcongr
        _ = c0 * (Real.exp (σ * u) * Real.exp (-u * θ)) := by ring
        _ = c0 * Real.exp ((σ - θ) * u) := by rw [← Real.exp_add]; congr 2; ring
    have hmem : u ∈ Iic (0 : ℝ) := hu
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    refine ⟨by linarith, ?_⟩
    have h2 : ‖hfun a c σ u‖ ^ 2 ≤ (c0 * Real.exp ((σ - θ) * u)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    have e : (c0 * Real.exp ((σ - θ) * u)) ^ 2 = c0 ^ 2 * Real.exp (2 * (σ - θ) * u) := by
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    rw [e] at h2; linarith
  · have hx : Real.exp (-u) ≤ X0 := by
      rw [← Real.exp_log (by linarith : (0:ℝ) < X0)]; exact Real.exp_le_exp.2 (by linarith)
    have hA := norm_Rf_le (a := a) c (Real.exp_pos (-u)).le hx
    have hb : ‖hfun a c σ u‖ ≤ S := by
      rw [hn]
      have he : Real.exp (σ * u) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ σ := le_trans hθ hσ
        nlinarith
      calc Real.exp (σ * u) * ‖Rf a c (Real.exp (-u))‖ ≤ 1 * S := by
            gcongr; exact hA
        _ = S := one_mul S
    have hmem : u ∈ Icc (-Real.log X0) 0 := ⟨hL.le, hu⟩
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    refine ⟨by linarith, ?_⟩
    have h2 : ‖hfun a c σ u‖ ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    linarith

/-- **`h_σ ∈ L¹ ∩ L²` with the explicit `L²` bound.** -/
theorem hfun_L1L2 {θ c0 X0 σ : ℝ} (hθ : 0 ≤ θ) (hc0 : 0 ≤ c0) (hX0 : 1 ≤ X0)
    (hX : ∀ x ≥ X0, ‖Rf a c x‖ ≤ c0 * x ^ θ) (hσ : θ < σ) :
    Integrable (hfun a c σ) ∧ MemLp (hfun a c σ) 2 ∧
      ∫ u, ‖hfun a c σ u‖ ^ 2 ≤ c0 ^ 2 / (2 * (σ - θ)) + (Sb a c X0) ^ 2 * Real.log X0 := by
  have hδ : 0 < σ - θ := by linarith
  have hb := norm_hfun_le a c hθ hc0 hX0 hX hσ.le
  have hm := (measurable_hfun a c σ).aestronglyMeasurable (μ := volume)
  have hi : Integrable (hfun a c σ) :=
    (TauOmegaPartial.integrable_G1 hδ).mono' hm (Eventually.of_forall fun u => (hb u).1)
  have hsq : Integrable (fun u => ‖hfun a c σ u‖ ^ 2) :=
    (TauOmegaPartial.integrable_G2 hδ).mono' (hm.norm.pow 2) (Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (by positivity)]; exact (hb u).2)
  refine ⟨hi, (memLp_two_iff_integrable_sq_norm hm).2 hsq, ?_⟩
  rw [← TauOmegaPartial.integral_G2 hδ (Real.log_nonneg hX0)]
  exact integral_mono hsq (TauOmegaPartial.integrable_G2 hδ) fun u => (hb u).2

end Fourier

end RamanujanTau.RankinOmega
