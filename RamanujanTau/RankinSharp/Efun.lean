/-
# The entire function `E(s) = (s−1) ζ(2s) D(s)`

For `RSData a κ` put `Λ(s) = Λ₀(s) + κ(1/(s−1) − 1/s)` (so `Λ(1−s) = Λ(s)`) and

    E(s) = ((s−1)Λ₀(s) + κ) γ(s)⁻¹ − κ (s−1) γ₁(s)⁻¹,    γ₁(s)⁻¹ = γ(s)⁻¹/s,

an entire function with `E(s) = (s−1) Λ(s) γ(s)⁻¹` (`s ≠ 0, 1`). For `Re s > 2` it equals
`(s−1) ζ(2s) D(s)`; when the abscissa of absolute convergence of `D` is `≤ 1` the identity
theorem extends this to `Re s > 1` (`Efun_eq_LSeries'`). `Efun_growth`: `‖E(s)‖ ≤ K e^{L|t|}`
on `−3/2 ≤ Re s ≤ 5/2`, `|t| ≥ 1`.
-/
import RamanujanTau.RankinError.PowerSaving84
import RamanujanTau.RankinSharp.PL

set_option autoImplicit false

namespace RamanujanTau.RankinSharp

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.RankinError

/-- `γ(s)⁻¹/s`, entire. -/
noncomputable def invGam1 (s : ℂ) : ℂ :=
  (π : ℂ) ^ s * ((4 * π : ℝ) : ℂ) ^ (s + 11) / 2 * (Complex.Gamma (s + 1))⁻¹ *
    (Complex.Gamma (s + 11))⁻¹

lemma differentiable_invGam1 : Differentiable ℂ invGam1 := by
  intro s
  have h3 : DifferentiableAt ℂ (fun s => (Complex.Gamma (s + 1))⁻¹) s := by
    have := (Complex.differentiable_one_div_Gamma (s + 1)).comp s
      (differentiableAt_id.add_const (1 : ℂ))
    simpa [Function.comp_def] using this
  have h4 : DifferentiableAt ℂ (fun s => (Complex.Gamma (s + 11))⁻¹) s := by
    have := (Complex.differentiable_one_div_Gamma (s + 11)).comp s
      (differentiableAt_id.add_const (11 : ℂ))
    simpa [Function.comp_def] using this
  unfold invGam1
  exact ((((differentiableAt_id.const_cpow (Or.inl pi_ne_zero')).mul
    ((differentiableAt_id.add_const _).const_cpow (Or.inl fourpi_ne_zero))).div_const 2).mul
    h3).mul h4

lemma invGam_eq (s : ℂ) : invGam s = s * invGam1 s := by
  unfold invGam invGam1
  rcases eq_or_ne s 0 with rfl | hs
  · simp [Complex.Gamma_zero]
  · rw [Complex.Gamma_add_one s hs, mul_inv]
    have : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    linear_combination (-((π : ℂ) ^ s * ((4 * π : ℝ) : ℂ) ^ (s + 11) / 2 *
      (Complex.Gamma s)⁻¹ * (Complex.Gamma (s + 11))⁻¹)) * this

section E

variable {a : ℕ → ℝ} {κ : ℝ} (d : RSData a κ)

/-- The completed function with the pole at `1` removed by `(s−1)`. -/
noncomputable def Lam (s : ℂ) : ℂ := d.Λ₀ s + κ * (1 / (s - 1) - 1 / s)

lemma Lam_fe (s : ℂ) : Lam d (1 - s) = Lam d s := by
  unfold Lam
  rw [d.fe s, show 1 - s - 1 = -s by ring, show (1 : ℂ) - s = -(s - 1) by ring, one_div_neg_eq_neg_one_div,
    one_div_neg_eq_neg_one_div]
  ring

/-- `E(s) = ((s−1)Λ₀(s) + κ) γ(s)⁻¹ − κ(s−1) γ₁(s)⁻¹`. -/
noncomputable def Efun (s : ℂ) : ℂ :=
  ((s - 1) * d.Λ₀ s + κ) * invGam s - κ * (s - 1) * invGam1 s

lemma differentiable_Efun : Differentiable ℂ (Efun d) := by
  intro s
  unfold Efun
  exact ((((differentiableAt_id.sub_const 1).mul (d.diff s)).add_const _).mul
    (differentiable_invGam s)).sub
    (((differentiableAt_const _).mul (differentiableAt_id.sub_const 1)).mul
      (differentiable_invGam1 s))

lemma Efun_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    Efun d s = (s - 1) * Lam d s * invGam s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 h1
  unfold Efun Lam
  rw [invGam_eq s]
  field_simp
  ring

lemma Efun_eq_LSeries {s : ℂ} (hs : 2 < s.re) :
    Efun d s = (s - 1) * riemannZeta (2 * s) * LSeries (fun n => (a n : ℂ)) s := by
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  rw [Efun_eq d h0 h1]
  have hL : Lam d s = gam s * riemannZeta (2 * s) * LSeries (fun n => (a n : ℂ)) s := by
    unfold Lam; rw [d.unfold s hs]
  rw [hL]
  have := gam_mul_invGam (s := s) (by linarith)
  linear_combination ((s - 1) * riemannZeta (2 * s) * LSeries (fun n => (a n : ℂ)) s) * this

variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

include habs in
lemma LSeriesSummable_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (a n : ℂ)) s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re (lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.2 hs))

include habs in
/-- The identity `E(s) = (s−1) ζ(2s) D(s)` on `Re s > 1`. -/
lemma Efun_eq_LSeries' {s : ℂ} (hs : 1 < s.re) :
    Efun d s = (s - 1) * riemannZeta (2 * s) * LSeries (fun n => (a n : ℂ)) s := by
  set U : Set ℂ := {z : ℂ | 1 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : DifferentiableOn ℂ (Efun d) U := (differentiable_Efun d).differentiableOn
  have hg : DifferentiableOn ℂ
      (fun z => (z - 1) * riemannZeta (2 * z) * LSeries (fun n => (a n : ℂ)) z) U := by
    intro z hz
    simp only [hU, mem_setOf_eq] at hz
    have hz2 : 2 * z ≠ 1 := by
      intro h; have := congrArg re h; simp at this; linarith
    have hζ : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) z :=
      (differentiableAt_riemannZeta hz2).comp z (differentiableAt_id.const_mul 2)
    have hL : DifferentiableAt ℂ (LSeries (fun n => (a n : ℂ))) z := by
      have hlt : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) < (z.re : EReal) :=
        lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.2 hz)
      exact (LSeries_differentiableOn _ z hlt).differentiableAt
        ((isOpen_re_gt_EReal _).mem_nhds hlt)
    exact (((differentiableAt_id.sub_const 1).mul hζ).mul hL).differentiableWithinAt
  have h3 : (3 : ℂ) ∈ U := by simp [hU]
  have hev : Efun d =ᶠ[𝓝 (3 : ℂ)]
      fun z => (z - 1) * riemannZeta (2 * z) * LSeries (fun n => (a n : ℂ)) z := by
    have hV : {z : ℂ | 2 < z.re} ∈ 𝓝 (3 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp; norm_num)
    filter_upwards [hV] with z hz using Efun_eq_LSeries d hz
  exact (hf.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUo)
    (convex_halfSpace_re_gt 1).isPreconnected h3 hev hs

include habs in
/-- `Λ(s) = γ(s) ζ(2s) D(s)` on `Re s > 1`. -/
lemma Lam_eq {s : ℂ} (hs : 1 < s.re) :
    Lam d s = gam s * riemannZeta (2 * s) * LSeries (fun n => (a n : ℂ)) s := by
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have h1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 h1
  have e := (Efun_eq d h0 h1).symm.trans (Efun_eq_LSeries' d habs hs)
  have hg := gam_mul_invGam (s := s) (by linarith)
  have e2 : Lam d s * invGam s = riemannZeta (2 * s) * LSeries (fun n => (a n : ℂ)) s := by
    have := mul_left_cancel₀ hs1 (by rw [← mul_assoc, e]; ring :
      (s - 1) * (Lam d s * invGam s) = (s - 1) * (riemannZeta (2 * s) *
        LSeries (fun n => (a n : ℂ)) s))
    exact this
  calc Lam d s = Lam d s * (gam s * invGam s) := by rw [hg, mul_one]
    _ = gam s * (Lam d s * invGam s) := by ring
    _ = _ := by rw [e2]; ring

/-- Growth of `γ⁻¹` and `γ₁⁻¹`. -/
lemma invGam_growth : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, -3 / 2 ≤ s.re → s.re ≤ 5 / 2 → 1 ≤ |s.im| →
    ‖invGam s‖ ≤ K * Real.exp (2 * π * |s.im|) ∧
      ‖invGam1 s‖ ≤ K * Real.exp (2 * π * |s.im|) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_inv_Gamma_le (A := 3 / 2) (by norm_num)
  have hπ := Real.pi_pos
  refine ⟨(π ^ (3:ℝ) * (4 * π) ^ (14:ℝ)) * C ^ 2, by positivity, fun s h1 h2 ht => ?_⟩
  set t := |s.im|
  have hpre : ‖(π : ℂ) ^ s * ((4 * π : ℝ) : ℂ) ^ (s + 11) / 2‖ ≤ π ^ (3:ℝ) * (4 * π) ^ (14:ℝ) := by
    rw [norm_div, norm_mul, Complex.norm_two,
      show (π : ℂ) = ((π : ℝ) : ℂ) from rfl, norm_cpow_pos π hπ, norm_cpow_pos _ (by positivity)]
    have p1 : π ^ s.re ≤ π ^ (3:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
    have p2 : (4 * π) ^ (s + 11).re ≤ (4 * π) ^ (14:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [Real.pi_gt_three]) (by simp; linarith)
    calc π ^ s.re * (4 * π) ^ (s + 11).re / 2 ≤ π ^ (3:ℝ) * (4 * π) ^ (14:ℝ) / 1 := by
          gcongr; norm_num
      _ = _ := by ring
  have g11 := hC (s + 11) (by simp; linarith) (by simpa using ht)
  simp only [add_im, im_ofNat, add_zero] at g11
  have hexp : Real.exp (2 * π * t) = Real.exp (π * t) * Real.exp (π * t) := by
    rw [← Real.exp_add]; ring_nf
  constructor
  · have g1 := hC s (by linarith) ht
    unfold invGam
    rw [norm_mul, norm_mul, hexp]
    calc _ ≤ π ^ (3:ℝ) * (4 * π) ^ (14:ℝ) * (C * Real.exp (π * t)) * (C * Real.exp (π * t)) := by
          gcongr
      _ = _ := by ring
  · have g1 := hC (s + 1) (by simp; linarith) (by simpa using ht)
    simp only [add_im, one_im, add_zero] at g1
    unfold invGam1
    rw [norm_mul, norm_mul, hexp]
    calc _ ≤ π ^ (3:ℝ) * (4 * π) ^ (14:ℝ) * (C * Real.exp (π * t)) * (C * Real.exp (π * t)) := by
          gcongr
      _ = _ := by ring

lemma Efun_growth : ∃ K L : ℝ, ∀ s : ℂ, -3 / 2 ≤ s.re → s.re ≤ 5 / 2 → 1 ≤ |s.im| →
    ‖Efun d s‖ ≤ K * Real.exp (L * |s.im|) := by
  obtain ⟨K, hK0, hK⟩ := invGam_growth
  refine ⟨(4 * |d.L₀| + 5 * |κ|) * K, 2 * π + 1, fun s h1 h2 ht => ?_⟩
  set t := |s.im| with htdef
  obtain ⟨g0, g1⟩ := hK s h1 h2 ht
  have e2 : ‖s - 1‖ ≤ 4 * Real.exp t := by
    have h := norm_le_exp_abs_im (s := s - 1) (r := 3) (by norm_num)
      (by simp only [sub_re, one_re]; rw [abs_le]; constructor <;> linarith)
    simp only [sub_im, one_im, sub_zero] at h
    linarith
  have hL : ‖d.Λ₀ s‖ ≤ |d.L₀| := (d.bdd s h1 h2).trans (le_abs_self _)
  have het : 1 ≤ Real.exp t := Real.one_le_exp (abs_nonneg _)
  have hexp : Real.exp ((2 * π + 1) * t) = Real.exp t * Real.exp (2 * π * t) := by
    rw [← Real.exp_add]; ring_nf
  have hE : ‖Efun d s‖ ≤ (‖s - 1‖ * ‖d.Λ₀ s‖ + |κ|) * ‖invGam s‖ +
      |κ| * ‖s - 1‖ * ‖invGam1 s‖ := by
    unfold Efun
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul (((κ : ℂ)) * (s - 1)), norm_mul (κ : ℂ), Complex.norm_real,
      Real.norm_eq_abs]
    gcongr
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine hE.trans ?_
  have hG0 : 0 ≤ K * Real.exp (2 * π * t) := by positivity
  calc (‖s - 1‖ * ‖d.Λ₀ s‖ + |κ|) * ‖invGam s‖ + |κ| * ‖s - 1‖ * ‖invGam1 s‖
      ≤ (4 * Real.exp t * |d.L₀| + |κ| * Real.exp t) * (K * Real.exp (2 * π * t)) +
        |κ| * (4 * Real.exp t) * (K * Real.exp (2 * π * t)) := by
        gcongr
        · nlinarith [abs_nonneg κ]
    _ = (4 * |d.L₀| + 5 * |κ|) * K * (Real.exp t * Real.exp (2 * π * t)) := by ring
    _ = _ := by rw [hexp]

end E

end RamanujanTau.RankinSharp
