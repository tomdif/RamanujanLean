/-
# The Mellin mean-square core, under Mellin convergence only

`RankinOmega.rs_omega_core` proves `R(x) = Ω(x^{3/8})` by contradiction from a pointwise bound
`‖R(x)‖ ≤ c₀x^{3/8}`. Here the pointwise hypothesis is replaced by *Mellin convergence*
on `Re s > 3/8 + δ/2` plus `h_σ ∈ L²`:

* `Lam_eq_mellin_conv`: the functional-equation identity `Λ(s)γₘ(s)⁻¹ = ζ(2s)(sM(s) + cs/(s−1))`
  on `{Re s > θ} ∩ {Im s < 0}`, whenever `∫ R(x) x^{−s−1}` converges absolutely on `Re s > θ`;
* `core_lower`: `∫ |h_σ|² ≥ K₂/(8δ)` for `σ = 3/8 + δ`, `0 < δ ≤ 1/16`, `K₂` independent of `δ`.
-/
import RamanujanTau.RankinOmega.Main
import RamanujanTau.TauOmegaPM.Landau
import RamanujanTau.TauOmegaPM.OmegaPM

set_option autoImplicit false

namespace RamanujanTau.RankinOmegaPM

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open RamanujanTau.RankinOmega
open scoped Real Interval FourierTransform

section Core

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ)
variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

lemma Rf_zero_lt_one (c : ℝ) : ∀ t < 1, Rf a c t = 0 := fun _ ht => Rf_of_lt_one c ht

/-- `M(s) = ∫ R x^{−s−1}` is holomorphic on the half-plane of absolute convergence. -/
lemma differentiableAt_M {c θ : ℝ} (hconv : ∀ s : ℂ, θ < s.re → MellinConvergent (Rf a c) (-s))
    {s : ℂ} (hs : θ < s.re) : DifferentiableAt ℂ (fun s => mellin (Rf a c) (-s)) s :=
  (TauOmegaPM.hasDerivAt_mellin_neg (Rf_zero_lt_one c) (measurable_Rf c) hconv hs).differentiableAt

include habs in
/-- **The completed function in terms of `M`**, under Mellin convergence on `Re s > θ`. -/
theorem Lam_eq_mellin_conv (c : ℝ) {θ : ℝ}
    (hconv : ∀ s : ℂ, θ < s.re → MellinConvergent (Rf a c) (-s)) {s : ℂ} (hs : θ < s.re)
    (him : s.im < 0) :
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
    refine (hζ.mul ((differentiableAt_id.mul (differentiableAt_M hconv hz.1)).add
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

lemma integrable_hfun_of_mc {c σ : ℝ} (h : MellinConvergent (Rf a c) (-((σ : ℝ) : ℂ))) :
    Integrable (hfun a c σ) :=
  TauOmegaPM.integrable_of_mc h

include d habs in
/-- **Core lower bound.** There is `K₂ > 0` such that for `0 < δ ≤ 1/16`, whenever
`∫ R(x)x^{−s−1}` converges absolutely on `Re s > 3/8 + δ/2` and `h_σ ∈ L²` (`σ = 3/8 + δ`),
`∫ |h_σ|² ≥ K₂/(8δ)`. -/
theorem core_lower (hm : 1 ≤ m) {n0 : ℕ} (hn0 : 1 ≤ n0)
    (hlow : ∀ n, 0 < n → n < n0 → a n = 0) (ha0 : a n0 ≠ 0) (c : ℝ) :
    ∃ K2 : ℝ, 0 < K2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 16 →
      (∀ s : ℂ, 3 / 8 + δ / 2 < s.re → MellinConvergent (Rf a c) (-s)) →
      MemLp (hfun a c (3 / 8 + δ)) 2 →
      K2 / (8 * δ) ≤ ∫ u, ‖hfun a c (3 / 8 + δ) u‖ ^ 2 := by
  obtain ⟨K1, hK1, Ξ0, hΞ0, hblock⟩ := block_lower d habs hm hn0 hlow ha0 c
  refine ⟨K1 / (4 * Ξ0), by positivity, fun δ hδ0 hδ1 hconv hmem => ?_⟩
  set K2 := K1 / (4 * Ξ0) with hK2
  have hK20 : 0 < K2 := by rw [hK2]; positivity
  set σ : ℝ := 3 / 8 + δ with hσ
  have hσθ : 3 / 8 + δ / 2 < σ := by rw [hσ]; linarith
  have hi : Integrable (hfun a c σ) :=
    integrable_hfun_of_mc (hconv _ (by simpa using hσθ))
  obtain ⟨hF2, hpl⟩ := TauOmegaPartial.plancherel_of_integrable hi hmem
  set F : ℝ → ℂ := fun ξ => mellin (Rf a c) (-((σ : ℂ) - 2 * π * ξ * I)) with hF
  have hFeq : 𝓕 (hfun a c σ) = F := by
    funext ξ; exact fourier_hfun a c σ ξ
  rw [hFeq] at hF2 hpl
  have hFc : Continuous F := by
    refine continuous_iff_continuousAt.2 fun ξ => ?_
    have hre : 3 / 8 + δ / 2 < ((σ : ℂ) - 2 * π * ξ * I).re := by simpa using hσθ
    exact (differentiableAt_M hconv hre).continuousAt.comp
      (f := fun ξ : ℝ => (σ : ℂ) - 2 * π * ξ * I) (x := ξ) (by fun_prop)
  have hFi : Integrable (fun ξ => ‖F ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hFc.aestronglyMeasurable).1 hF2
  have hMid : ∀ ξ : ℝ, 1 ≤ ξ →
      Lam d (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) *
          invGamM m (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) =
        riemannZeta (2 * (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I)) *
          ((((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) *
              (fun s => mellin (Rf a c) (-s)) (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) +
            c * (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) /
              ((((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) - 1)) := by
    intro ξ hξ
    rw [← hσ]
    have hre : 3 / 8 + δ / 2 < ((σ : ℂ) - 2 * π * ξ * I).re := by simpa using hσθ
    have him : ((σ : ℂ) - 2 * π * ξ * I).im < 0 := by
      have : 0 < 2 * π * ξ := by have := Real.pi_pos; positivity
      simpa using this
    exact Lam_eq_mellin_conv d habs c hconv hre him
  have hMc : Continuous (fun ξ : ℝ =>
      (fun s => mellin (Rf a c) (-s)) (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I)) := by
    rw [← hσ]; exact hFc
  have hb := hblock δ hδ0 hδ1 (fun s => mellin (Rf a c) (-s)) hMid hMc
  simp only [← hσ] at hb
  set J : ℕ := ⌈1 / (8 * δ)⌉₊ with hJ
  set b : ℕ → ℝ := fun j => 2 ^ j * Ξ0 with hbdef
  have hsum : ∑ j ∈ Finset.range J, ∫ ξ in b j..b (j + 1), ‖F ξ‖ ^ 2 =
      ∫ ξ in b 0..b J, ‖F ξ‖ ^ 2 :=
    intervalIntegral.sum_integral_adjacent_intervals fun j _ =>
      (hFc.norm.pow 2).intervalIntegrable _ _
  have hle : ∫ ξ in b 0..b J, ‖F ξ‖ ^ 2 ≤ ∫ ξ, ‖F ξ‖ ^ 2 := by
    have h0J : b 0 ≤ b J := by
      simp only [hbdef, pow_zero, one_mul]
      exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
    rw [intervalIntegral.integral_of_le h0J]
    exact setIntegral_le_integral hFi (Eventually.of_forall fun _ => by positivity)
  have hblocks : ∀ j ∈ Finset.range J, K2 ≤ ∫ ξ in b j..b (j + 1), ‖F ξ‖ ^ 2 := by
    intro j hj
    have hjJ : j < J := Finset.mem_range.1 hj
    have hbj : Ξ0 ≤ b j := by
      simp only [hbdef]; exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
    have hbb := hb (b j) hbj
    have hnext : b (j + 1) = 2 * b j := by simp only [hbdef]; rw [pow_succ]; ring
    rw [hnext]
    have hw := dyadic_weight8 hΞ0 hδ0 hδ1 hjJ
    have : K2 ≤ K1 * (2 * b j) ^ (-(8 * δ)) := by
      rw [hK2, div_eq_mul_one_div]
      simp only [hbdef]
      exact mul_le_mul_of_nonneg_left hw hK1.le
    exact this.trans hbb
  have hlow' : (J : ℝ) * K2 ≤ ∫ ξ, ‖F ξ‖ ^ 2 := by
    have := Finset.sum_le_sum hblocks
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsum] at this
    exact this.trans hle
  have hJge : 1 / (8 * δ) ≤ (J : ℝ) := Nat.le_ceil _
  rw [hpl] at hlow'
  have : K2 / (8 * δ) ≤ (J : ℝ) * K2 := by
    rw [div_eq_mul_one_div, mul_comm]; exact mul_le_mul_of_nonneg_right hJge hK20.le
  linarith

end Core

end RamanujanTau.RankinOmegaPM
