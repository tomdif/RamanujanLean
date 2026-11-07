/-
# `R(x) = Ω±(x^β)` for every `β < 3/20`

Let `R(x) = ∑_{n≤x} aₙ − c x` for Rankin–Selberg data with `|R(x)| ≤ C x^{3/5}` (`RankinExact`).

1. **One-sided bound ⇒ Mellin convergence on `Re s > β`** (`conv_of_one_sided`, `0 < β < 3/5`).
   If `ε R(x) ≥ −c₁ x^β` for `x ≥ X₀` (`ε = ±1`), then `g = ε R + c' 1_{t≥1} t^β ≥ 0` and
   `∫ g t^{−s−1} = ε M(s) + c'/(s−β)` for `Re s > 3/5`. On the strip `3/5 < Re s < 1`,
   `M(s) = Λ(s)γ(s)⁻¹ Q(2s)/s − c/(s−1)` (`M_eq_cont`, `Q = 1/ζ` holomorphic, `ZetaReal`), and the
   right side is holomorphic on a thin strip `{β < Re s < 4/5, |Im s| < r}` around the real axis,
   because `ζ(w) ≠ 0` near real `w ∈ [2β, 8/5]` (`exists_strip`). Landau's theorem in strip form
   (`landau_mellin_strip`) gives convergence of `∫ g t^{−σ−1}` for all `σ > β`, hence of
   `∫ |R| t^{−σ−1}`.
2. **Mellin convergence on `Re s > β`, `β < 3/20` ⇒ False** (`false_of_conv`). Put
   `σ₁ = (β + 3/20)/2`. For `σ ≥ 3/8`, `|h_σ|² ≤ C |h_{σ₁}|` pointwise (from `|R| ≤ C x^{3/5}` and
   `2σ − 3/5 ≥ 3/20 > σ₁`), so `∫|h_σ|² ≤ C‖h_{σ₁}‖₁` uniformly, against `≥ K₂/(8δ)` (`core_lower`).
3. `rs_omega_pm`: both one-sided bounds fail, for every real `c₁`.

The exponent is `2·(3/8) − 3/5 = 3/20`: the `L¹ → L²` conversion costs the pointwise exponent.
-/
import RamanujanTau.RankinOmegaPM.Core
import RamanujanTau.RankinOmegaPM.ZetaReal
import RamanujanTau.RankinOmegaPM.LandauStrip

set_option autoImplicit false

namespace RamanujanTau.RankinOmegaPM

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open RamanujanTau.RankinOmega
open scoped Real Interval FourierTransform

section Real

variable {a : ℕ → ℝ}

lemma Rf_im (c x : ℝ) : (Rf a c x).im = 0 := by
  unfold Rf Asum Ind
  rw [sub_im, Complex.im_sum]
  simp only [ofReal_im, Finset.sum_const_zero, zero_sub, neg_eq_zero]
  by_cases h : x ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem h]; simp
  · rw [indicator_of_notMem h]; simp

lemma Rf_eq_re (c x : ℝ) : Rf a c x = (((Rf a c x).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [Rf_im])

lemma Rf_re_of_one_lt (c : ℝ) {x : ℝ} (hx : 1 < x) :
    (Rf a c x).re = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - c * x := by
  rw [Rf_of_one_lt c hx, Asum]; simp

/-- `1_{t ≥ 1} t^β`. -/
noncomputable def Pw (β t : ℝ) : ℝ := (Ici (1 : ℝ)).indicator (fun t => t ^ β) t

lemma measurable_Pw (β : ℝ) : Measurable (Pw β) :=
  (measurable_id.pow_const β).indicator measurableSet_Ici

lemma Pw_nonneg (β t : ℝ) : 0 ≤ Pw β t := by
  unfold Pw
  exact Set.indicator_nonneg (fun t (ht : 1 ≤ t) => Real.rpow_nonneg (by linarith) β) t

lemma mellin_Pw {β : ℝ} {s : ℂ} (hs : β < s.re) :
    MellinConvergent (fun t => (Pw β t : ℂ)) (-s) ∧
      mellin (fun t => (Pw β t : ℂ)) (-s) = 1 / (s - β) := by
  have hsβ : s - β ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  set e : ℂ := (β : ℂ) - s - 1 with he
  have hre : e.re < -1 := by simp [he]; linarith
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (-s - 1) • (Pw β t : ℂ) =
      (Ici (1 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ e) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    by_cases h1 : t ∈ Ici (1 : ℝ)
    · rw [indicator_of_mem h1, Pw, indicator_of_mem h1, smul_eq_mul, Complex.ofReal_cpow ht0.le,
        ← Complex.cpow_add _ _ (by exact_mod_cast ht0.ne')]
      congr 1; rw [he]; ring
    · rw [indicator_of_notMem h1, Pw, indicator_of_notMem h1]; simp
  have hI : IntegrableOn (fun t : ℝ => (t : ℂ) ^ e) (Ici 1) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (b := (1 : ℝ)) (f := fun t : ℝ => (t : ℂ) ^ e)).2
      (integrableOn_Ioi_cpow_of_lt hre zero_lt_one)
  have hI' : IntegrableOn ((Ici (1 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ e)) (Ioi 0) :=
    (hI.integrable_indicator measurableSet_Ici).integrableOn
  constructor
  · unfold MellinConvergent
    exact hI'.congr_fun (fun t ht => (hpt t ht).symm) measurableSet_Ioi
  · rw [mellin, setIntegral_congr_fun measurableSet_Ioi hpt, setIntegral_indicator measurableSet_Ici,
      show Ioi (0 : ℝ) ∩ Ici 1 = Ici 1 from inter_eq_right.2
        (fun t (ht : t ∈ Ici (1 : ℝ)) => show (0 : ℝ) < t from lt_of_lt_of_le zero_lt_one ht),
      integral_Ici_eq_integral_Ioi,
      integral_Ioi_cpow_of_lt hre zero_lt_one]
    rw [show e + 1 = (β : ℂ) - s by rw [he]; ring]
    push_cast
    rw [Complex.one_cpow]
    have : (β : ℂ) - s ≠ 0 := by
      intro h; apply hsβ; linear_combination -h
    field_simp
    ring

end Real

section Data

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ)
variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

include habs in
/-- **The continuation of `M` in the strip `θ < Re s < 1`** (`θ ≥ 1/2`). -/
lemma M_eq_cont (c : ℝ) {θ : ℝ} (hθ : 1 / 2 ≤ θ)
    (hconv : ∀ s : ℂ, θ < s.re → MellinConvergent (Rf a c) (-s)) {s : ℂ} (hs : θ < s.re)
    (hs1 : s.re < 1) :
    mellin (Rf a c) (-s) = Lam d s * invGamM m s * Qz (2 * s) / s - c / (s - 1) := by
  set U : Set ℂ := {z : ℂ | θ < z.re} ∩ {z : ℂ | z.re < 1} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hne0 : ∀ z ∈ U, z ≠ 0 := by
    intro z hz h; have := hz.1; rw [h] at this; simp at this; linarith
  have hne1 : ∀ z ∈ U, z ≠ 1 := by
    intro z hz h; have := hz.2; rw [h] at this; simp at this
  have h2re : ∀ z ∈ U, 1 < (2 * z).re := by
    intro z hz; have : θ < z.re := hz.1; simp; linarith
  have hF : DifferentiableOn ℂ (fun z => Lam d z * invGamM m z) U := fun z hz =>
    ((differentiableAt_Lam d (hne0 z hz) (hne1 z hz)).mul
      (differentiable_invGamM m z)).differentiableWithinAt
  have hG : DifferentiableOn ℂ
      (fun z => riemannZeta (2 * z) * (z * mellin (Rf a c) (-z) + c * z / (z - 1))) U := by
    intro z hz
    have h1 : z - 1 ≠ 0 := sub_ne_zero.2 (hne1 z hz)
    have h2 : 2 * z ≠ 1 := by
      intro h; have := h2re z hz; rw [h] at this; simp at this
    have hζ : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) z :=
      (differentiableAt_riemannZeta h2).comp z (differentiableAt_id.const_mul 2)
    exact (hζ.mul ((differentiableAt_id.mul (differentiableAt_M hconv hz.1)).add
      ((differentiableAt_id.const_mul (c : ℂ)).div (differentiableAt_id.sub_const 1)
        h1))).differentiableWithinAt
  set p0 : ℂ := (((θ + 1) / 2 : ℝ) : ℂ) - I with hp0
  have hp0U : p0 ∈ U := by
    simp only [hU, hp0, mem_inter_iff, mem_setOf_eq, sub_re, ofReal_re, I_re, sub_zero]
    constructor <;> linarith
  have hev : (fun z => Lam d z * invGamM m z) =ᶠ[𝓝 p0]
      (fun z => riemannZeta (2 * z) * (z * mellin (Rf a c) (-z) + c * z / (z - 1))) := by
    have hW : U ∩ {z : ℂ | z.im < 0} ∈ 𝓝 p0 :=
      (hUo.inter (isOpen_lt continuous_im continuous_const)).mem_nhds
        ⟨hp0U, by simp [hp0]⟩
    filter_upwards [hW] with z hz
    exact Lam_eq_mellin_conv d habs c hconv hz.1.1 hz.2
  have hid := (hF.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hUo)
    hUc hp0U hev ⟨hs, hs1⟩
  simp only at hid
  have hsU : s ∈ U := ⟨hs, hs1⟩
  have hs0 := hne0 s hsU
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 (hne1 s hsU)
  have hQ := Qz_mul_zeta (h2re s hsU)
  set Mv := mellin (Rf a c) (-s) with hMv
  rw [hid]
  rw [show riemannZeta (2 * s) * (s * Mv + c * s / (s - 1)) * Qz (2 * s) =
      (Qz (2 * s) * riemannZeta (2 * s)) * (s * Mv + c * s / (s - 1)) by ring, hQ, one_mul]
  field_simp
  ring

/-- The nonnegative function `g = ε R + c' 1_{t ≥ 1} t^β`. -/
noncomputable def gfun (a : ℕ → ℝ) (c ε c' β : ℝ) (t : ℝ) : ℝ := ε * (Rf a c t).re + c' * Pw β t

lemma gfun_cast (c ε c' β t : ℝ) :
    ((gfun a c ε c' β t : ℝ) : ℂ) = (ε : ℂ) • Rf a c t + (c' : ℂ) • (Pw β t : ℂ) := by
  rw [gfun, smul_eq_mul, smul_eq_mul, Rf_eq_re c t]; push_cast; simp

lemma measurable_gfun (c ε c' β : ℝ) : Measurable (gfun a c ε c' β) :=
  (measurable_const.mul (Complex.measurable_re.comp (measurable_Rf c))).add
    (measurable_const.mul (measurable_Pw β))

include d habs in
/-- **A one-sided bound forces Mellin convergence on `Re s > β`.** -/
theorem conv_of_one_sided {C c : ℝ} (hR : ∀ x : ℝ, 1 ≤ x → ‖Rf a c x‖ ≤ C * x ^ ((3 : ℝ) / 5))
    {β : ℝ} (hβ0 : 0 < β) (hβ : β < 3 / 5) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {c1 X0 : ℝ}
    (h : ∀ x ≥ X0, -c1 * x ^ β ≤ ε * (Rf a c x).re) :
    ∀ s : ℂ, β < s.re → MellinConvergent (Rf a c) (-s) := by
  have hε1 : |ε| = 1 := by rcases hε with h | h <;> simp [h]
  have hRc : ∀ s : ℂ, 3 / 5 < s.re → MellinConvergent (Rf a c) (-s) :=
    TauOmegaPM.mc_of_bound (Rf_zero_lt_one c) (measurable_Rf c) hR
  set X1 : ℝ := max X0 1 with hX1
  have hX11 : 1 ≤ X1 := le_max_right _ _
  set c' : ℝ := |c1| + Sb a c X1 with hc'
  have hSb0 : 0 ≤ Sb a c X1 := by
    unfold Sb
    have := Finset.sum_nonneg fun n (_ : n ∈ Finset.Icc 1 ⌊X1⌋₊) => norm_nonneg (a n : ℂ)
    have : 0 ≤ |c| * X1 := by have := abs_nonneg c; nlinarith
    linarith
  have hc'0 : 0 ≤ c' := by rw [hc']; positivity
  set g : ℝ → ℝ := gfun a c ε c' β with hg
  have hreR : ∀ t, |(Rf a c t).re| ≤ ‖Rf a c t‖ := fun t => abs_re_le_norm _
  have hg0 : ∀ t, 0 ≤ g t := by
    intro t
    simp only [hg, gfun, Pw]
    rcases lt_or_ge t 1 with h1 | h1
    · rw [Rf_of_lt_one c h1, indicator_of_notMem (show t ∉ Ici (1 : ℝ) by simpa using h1)]; simp
    · rw [indicator_of_mem (show t ∈ Ici (1 : ℝ) from h1)]
      have htβ : 1 ≤ t ^ β := Real.one_le_rpow h1 hβ0.le
      have hεR : -‖Rf a c t‖ ≤ ε * (Rf a c t).re := by
        have : |ε * (Rf a c t).re| ≤ ‖Rf a c t‖ := by rw [abs_mul, hε1, one_mul]; exact hreR t
        linarith [neg_abs_le (ε * (Rf a c t).re)]
      rcases le_or_gt X0 t with hX | hX
      · have := h t hX
        have : -c1 * t ^ β ≥ -|c1| * t ^ β := by
          have := neg_abs_le c1
          have : 0 ≤ t ^ β := by linarith
          nlinarith [le_abs_self c1]
        have : |c1| * t ^ β ≤ c' * t ^ β := by
          have : 0 ≤ t ^ β := by linarith
          exact mul_le_mul_of_nonneg_right (by rw [hc']; linarith) this
        linarith
      · have htX : t ≤ X1 := le_trans hX.le (le_max_left _ _)
        have hb := norm_Rf_le (a := a) c (by linarith) htX
        have hb' : ‖Rf a c t‖ ≤ Sb a c X1 := hb
        have : Sb a c X1 * 1 ≤ c' * t ^ β := by
          refine mul_le_mul (by rw [hc']; linarith [abs_nonneg c1]) htβ (by norm_num) hc'0
        linarith
  have hg1 : ∀ t < 1, g t = 0 := by
    intro t ht
    simp only [hg, gfun, Pw, Rf_of_lt_one c ht,
      indicator_of_notMem (show t ∉ Ici (1 : ℝ) by simpa using ht)]
    simp
  have hgm : Measurable g := measurable_gfun c ε c' β
  -- convergence of `g` far right
  have hgb : ∀ t, 1 ≤ t → ‖((g t : ℝ) : ℂ)‖ ≤ (C + c') * t ^ ((3 : ℝ) / 5) := by
    intro t ht
    rw [Complex.norm_real, Real.norm_eq_abs]
    simp only [hg, gfun, Pw, indicator_of_mem (show t ∈ Ici (1 : ℝ) from ht)]
    have h1 : t ^ β ≤ t ^ ((3 : ℝ) / 5) := Real.rpow_le_rpow_of_exponent_le ht hβ.le
    have h2 := hR t ht
    have h3 : |ε * (Rf a c t).re| ≤ ‖Rf a c t‖ := by rw [abs_mul, hε1, one_mul]; exact hreR t
    have h4 : 0 ≤ t ^ β := Real.rpow_nonneg (by linarith) β
    calc |ε * (Rf a c t).re + c' * t ^ β| ≤ |ε * (Rf a c t).re| + |c' * t ^ β| := abs_add_le _ _
      _ ≤ C * t ^ ((3 : ℝ) / 5) + c' * t ^ ((3 : ℝ) / 5) := by
          rw [abs_of_nonneg (mul_nonneg hc'0 h4)]
          have : c' * t ^ β ≤ c' * t ^ ((3 : ℝ) / 5) := mul_le_mul_of_nonneg_left h1 hc'0
          linarith
      _ = (C + c') * t ^ ((3 : ℝ) / 5) := by ring
  have hg0' : ∀ t < 1, ((g t : ℝ) : ℂ) = 0 := fun t ht => by simp [hg1 t ht]
  have hgconv : ∀ s : ℂ, 3 / 5 < s.re → MellinConvergent (fun t => ((g t : ℝ) : ℂ)) (-s) :=
    TauOmegaPM.mc_of_bound hg0' (Complex.measurable_ofReal.comp hgm) hgb
  -- the Mellin transform of `g` for `Re s > 3/5`
  have hmg : ∀ s : ℂ, 3 / 5 < s.re → mellin (fun t => ((g t : ℝ) : ℂ)) (-s) =
      (ε : ℂ) * mellin (Rf a c) (-s) + (c' : ℂ) * (1 / (s - β)) := by
    intro s hs
    obtain ⟨hP, eP⟩ := mellin_Pw (β := β) (s := s) (by linarith)
    have h1 := (hRc s hs).const_smul (ε : ℂ)
    have h2 := hP.const_smul (c' : ℂ)
    have hadd := (hasMellin_add h1 h2).2
    rw [mellin_const_smul, mellin_const_smul, eP, smul_eq_mul, smul_eq_mul] at hadd
    rw [← hadd]
    congr 1; funext t; exact gfun_cast c ε c' β t
  -- the strip
  obtain ⟨r', hr', hstrip⟩ := exists_strip (β0 := 2 * β) (B := 8 / 5) (by linarith)
  set F : ℂ → ℂ := fun s => (ε : ℂ) * (Lam d s * invGamM m s * Qz (2 * s) / s - c / (s - 1)) +
    (c' : ℂ) * (1 / (s - β)) with hF
  have hFd : DifferentiableOn ℂ F {s | β < s.re ∧ s.re < 3 / 5 + 1 / 5 ∧ |s.im| < r' / 2} := by
    rintro s ⟨h1, h2, h3⟩
    have hs0 : s ≠ 0 := by intro h; rw [h] at h1; simp at h1; linarith
    have hs1 : s ≠ 1 := by intro h; rw [h] at h2; simp at h2; linarith
    have hsβ : s - β ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h2s : (2 * s).re = 2 * s.re := by simp
    have h2i : (2 * s).im = 2 * s.im := by simp
    obtain ⟨hw0, hwz⟩ := hstrip (2 * s) (by rw [h2s]; linarith) (by rw [h2s]; linarith)
      (by rw [h2i, abs_mul]; norm_num; linarith)
    have hQ : DifferentiableAt ℂ (fun s : ℂ => Qz (2 * s)) s :=
      (differentiableAt_Qz hw0 hwz).comp s (differentiableAt_id.const_mul 2)
    refine DifferentiableAt.differentiableWithinAt ?_
    have e1 : DifferentiableAt ℂ (fun s : ℂ => Lam d s * invGamM m s * Qz (2 * s) / s) s :=
      (((differentiableAt_Lam d hs0 hs1).mul (differentiable_invGamM m s)).mul hQ).div
        differentiableAt_id hs0
    have e2 : DifferentiableAt ℂ (fun s : ℂ => (c : ℂ) / (s - 1)) s :=
      (differentiableAt_const (c : ℂ)).div (differentiableAt_id.sub_const 1) (sub_ne_zero.2 hs1)
    have e3 : DifferentiableAt ℂ (fun s : ℂ => (1 : ℂ) / (s - β)) s :=
      (differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const _) hsβ
    exact ((e1.sub e2).const_mul (ε : ℂ)).add (e3.const_mul (c' : ℂ))
  have hFG : ∀ s : ℂ, 3 / 5 < s.re → s.re < 3 / 5 + 1 / 5 → |s.im| < r' / 2 →
      mellin (fun t => ((g t : ℝ) : ℂ)) (-s) = F s := by
    intro s h1 h2 _
    rw [hmg s h1, M_eq_cont d habs c (θ := 3 / 5) (by norm_num) hRc h1 (by linarith)]
  have hgσ := landau_mellin_strip hg0 hg1 hgm (σ0 := 3 / 5) (η := 1 / 5) (r := r' / 2) hβ
    (by norm_num) (by positivity) (fun σ hσ => hgconv _ (by simpa using hσ)) hFd hFG
  -- back to `R`
  intro s hs
  have hgs := hgσ s.re hs
  obtain ⟨hP, -⟩ := mellin_Pw (β := β) (s := (s.re : ℂ)) (by simpa using hs)
  have hdom := (hgs.norm.add (hP.norm.const_mul c'))
  unfold MellinConvergent
  refine hdom.mono' (TauOmegaPM.aesm_integrand (measurable_Rf c) (-s) _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [TauOmegaPM.norm_integrand ht0]
  simp only [Pi.add_apply]
  rw [TauOmegaPM.norm_integrand ht0,
    TauOmegaPM.norm_integrand ht0, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (hg0 t), Real.norm_of_nonneg (Pw_nonneg β t)]
  simp only [neg_re, ofReal_re]
  have hRle : ‖Rf a c t‖ ≤ g t + c' * Pw β t := by
    rw [Rf_eq_re c t, Complex.norm_real, Real.norm_eq_abs]
    have e : (Rf a c t).re = ε * (g t - c' * Pw β t) := by
      simp only [hg, gfun]
      rcases hε with h | h <;> rw [h] <;> ring
    rw [e, abs_mul, hε1, one_mul]
    have := hg0 t
    have := Pw_nonneg β t
    rw [abs_le]; constructor <;> nlinarith
  have hp : 0 ≤ t ^ (-s.re - 1) := Real.rpow_nonneg ht0.le _
  calc t ^ (-s.re - 1) * ‖Rf a c t‖ ≤ t ^ (-s.re - 1) * (g t + c' * Pw β t) :=
        mul_le_mul_of_nonneg_left hRle hp
    _ = t ^ (-s.re - 1) * g t + c' * (t ^ (-s.re - 1) * Pw β t) := by ring

include d habs in
/-- **Mellin convergence on `Re s > β` with `β < 3/20` is impossible.** -/
theorem false_of_conv (hm : 1 ≤ m) (hne : ∃ n, 0 < n ∧ a n ≠ 0) {C c : ℝ}
    (hR : ∀ x : ℝ, 1 ≤ x → ‖Rf a c x‖ ≤ C * x ^ ((3 : ℝ) / 5)) {β : ℝ} (hβ : β < 3 / 20)
    (hconv : ∀ s : ℂ, β < s.re → MellinConvergent (Rf a c) (-s)) : False := by
  obtain ⟨n0, hn0, hlow, ha0⟩ := exists_first hne
  obtain ⟨K2, hK2, hcore⟩ := core_lower d habs hm hn0 hlow ha0 c
  have hC : 0 ≤ C := by
    have h1 := hR 1 le_rfl
    rw [Real.one_rpow, mul_one] at h1
    exact le_trans (norm_nonneg _) h1
  set σ1 : ℝ := (β + 3 / 20) / 2 with hσ1
  have hβσ1 : β < σ1 := by rw [hσ1]; linarith
  have hi1 : Integrable (RankinOmega.hfun a c σ1) :=
    integrable_hfun_of_mc (hconv _ (by simpa using hβσ1))
  set L : ℝ := C * ∫ u, ‖RankinOmega.hfun a c σ1 u‖ with hL
  have hL0 : 0 ≤ L := by rw [hL]; exact mul_nonneg hC (integral_nonneg fun _ => norm_nonneg _)
  have hpt : ∀ σ : ℝ, 3 / 8 ≤ σ → ∀ u : ℝ,
      ‖RankinOmega.hfun a c σ u‖ ^ 2 ≤ C * ‖RankinOmega.hfun a c σ1 u‖ := by
    intro σ hσ u
    have hn : ∀ q : ℝ, ‖RankinOmega.hfun a c q u‖ = Real.exp (q * u) * ‖Rf a c (Real.exp (-u))‖ :=
      fun q => by rw [RankinOmega.hfun, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [hn, hn]
    rcases lt_or_ge 0 u with hu | hu
    · rw [Rf_of_lt_one c ((Real.exp_lt_exp.2 (by linarith : -u < 0)).trans_eq Real.exp_zero)]
      simp
    · have hx : 1 ≤ Real.exp (-u) := Real.one_le_exp (by linarith)
      have hb := hR _ hx
      rw [← Real.exp_mul] at hb
      set r := ‖Rf a c (Real.exp (-u))‖ with hr
      have hr0 : 0 ≤ r := norm_nonneg _
      have he : Real.exp (2 * σ * u) * Real.exp (-u * (3 / 5)) ≤ Real.exp (σ1 * u) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
      calc (Real.exp (σ * u) * r) ^ 2 = Real.exp (2 * σ * u) * r * r := by
            rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
        _ ≤ Real.exp (2 * σ * u) * (C * Real.exp (-u * (3 / 5))) * r := by gcongr
        _ = C * (Real.exp (2 * σ * u) * Real.exp (-u * (3 / 5))) * r := by ring
        _ ≤ C * Real.exp (σ1 * u) * r := by gcongr
        _ = C * (Real.exp (σ1 * u) * r) := by ring
  set δ : ℝ := min (1 / 16) (K2 / (16 * (L + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 16 := min_le_left _ _
  have hδ2 : δ ≤ K2 / (16 * (L + 1)) := min_le_right _ _
  have hσ : 3 / 8 ≤ 3 / 8 + δ := by linarith
  have hsqi : Integrable (fun u => ‖RankinOmega.hfun a c (3 / 8 + δ) u‖ ^ 2) :=
    (hi1.norm.const_mul C).mono' ((measurable_hfun a c _).norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hpt _ hσ u)
  have hmem : MemLp (RankinOmega.hfun a c (3 / 8 + δ)) 2 :=
    (memLp_two_iff_integrable_sq_norm (measurable_hfun a c _).aestronglyMeasurable).2 hsqi
  have hup : ∫ u, ‖RankinOmega.hfun a c (3 / 8 + δ) u‖ ^ 2 ≤ L := by
    rw [hL, ← integral_const_mul]
    exact integral_mono hsqi (hi1.norm.const_mul C) (hpt _ hσ)
  have hlowb := hcore δ hδ0 hδ1 (fun s hs => hconv s (by linarith)) hmem
  have h2 : 2 * (L + 1) ≤ K2 / (8 * δ) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hδ2 (show (0 : ℝ) ≤ 16 * (L + 1) by positivity)
    have e : 16 * (L + 1) * (K2 / (16 * (L + 1))) = K2 := by field_simp
    nlinarith
  linarith

include d habs in
/-- **`R = Ω±(x^β)` for every `β < 3/20`**, abstract Rankin–Selberg data with
`|R(x)| ≤ C x^{3/5}`. For every real `c₁` and `X`, `A(x) − c x < −c₁ x^β` and `> c₁ x^β` both
happen for some `x ≥ X`. -/
theorem rs_omega_pm (hm : 1 ≤ m) (hne : ∃ n, 0 < n ∧ a n ≠ 0) {C c : ℝ}
    (hR : ∀ x : ℝ, 1 ≤ x → ‖Rf a c x‖ ≤ C * x ^ ((3 : ℝ) / 5)) {β : ℝ} (hβ : β < 3 / 20)
    (c1 X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - c * x < -c1 * x ^ β) ∧
    (∃ x : ℝ, X ≤ x ∧ c1 * x ^ β < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - c * x) := by
  set β' : ℝ := max β (1 / 40) with hβ'
  have hβ'0 : 0 < β' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hβ'1 : β' < 3 / 20 := max_lt hβ (by norm_num)
  set X' : ℝ := max X 2 with hX'
  have hpow : ∀ x : ℝ, X' ≤ x → |c1| * x ^ β ≤ |c1| * x ^ β' := by
    intro x hx
    have hx1 : 1 ≤ x := le_trans (by norm_num) (le_trans (le_max_right _ _) hx)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _))
      (abs_nonneg _)
  have hreX : ∀ x : ℝ, X' ≤ x → (Rf a c x).re = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - c * x := by
    intro x hx
    exact Rf_re_of_one_lt c (lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hx))
  have hc1 : ∀ x : ℝ, X' ≤ x → -|c1| * x ^ β' ≤ -c1 * x ^ β := by
    intro x hx
    have h1 := hpow x hx
    have hx0 : 0 ≤ x ^ β := Real.rpow_nonneg (by linarith [le_max_right X 2]) β
    have : c1 * x ^ β ≤ |c1| * x ^ β := mul_le_mul_of_nonneg_right (le_abs_self c1) hx0
    linarith
  have hc1' : ∀ x : ℝ, X' ≤ x → c1 * x ^ β ≤ |c1| * x ^ β' := by
    intro x hx
    have h1 := hpow x hx
    have hx0 : 0 ≤ x ^ β := Real.rpow_nonneg (by linarith [le_max_right X 2]) β
    have : c1 * x ^ β ≤ |c1| * x ^ β := mul_le_mul_of_nonneg_right (le_abs_self c1) hx0
    linarith
  constructor
  · by_contra hcon
    push Not at hcon
    have h : ∀ x ≥ X', -|c1| * x ^ β' ≤ 1 * (Rf a c x).re := by
      intro x hx
      rw [one_mul, hreX x hx]
      exact (hc1 x hx).trans (hcon x (le_trans (le_max_left _ _) hx))
    exact false_of_conv d habs hm hne hR hβ'1
      (conv_of_one_sided d habs hR hβ'0 (by linarith) (Or.inl rfl) h)
  · by_contra hcon
    push Not at hcon
    have h : ∀ x ≥ X', -|c1| * x ^ β' ≤ -1 * (Rf a c x).re := by
      intro x hx
      rw [hreX x hx]
      have := (hcon x (le_trans (le_max_left _ _) hx))
      have := hc1' x hx
      linarith
    exact false_of_conv d habs hm hne hR hβ'1
      (conv_of_one_sided d habs hR hβ'0 (by linarith) (Or.inr rfl) h)

end Data

end RamanujanTau.RankinOmegaPM
