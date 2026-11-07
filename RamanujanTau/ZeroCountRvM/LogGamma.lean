/-
# A holomorphic logarithm of `Γ` on `Re s > 0` and the digamma series

`LG s = −γ s − log s + Σ_{j≥0} (s/(j+1) − log(1 + s/(j+1)))` (Weierstrass).

* `Gamma_eq_exp_LG`: `Γ(s) = exp(LG s)` for `Re s > 0` (from Mathlib's `GammaSeq_tendsto_Gamma`).
* `digamma_eq_series`: `ψ(s) = Γ'/Γ(s) = −γ − 1/s + Σ_{j≥0} (1/(j+1) − 1/(s+j+1))` for `Re s > 0`
  (termwise differentiation, Mathlib's `hasSum_deriv_of_summable_norm`).
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.PSeries

set_option autoImplicit false

namespace RamanujanTau.ZeroCountRvM

open Complex Filter Topology Set Metric
open scoped Real Nat

/-- `‖w − log(1+w)‖ ≤ 20‖w‖²` for `Re w ≥ 0`. -/
lemma norm_sub_log_one_add_le {w : ℂ} (hw : 0 ≤ w.re) : ‖w - log (1 + w)‖ ≤ 20 * ‖w‖ ^ 2 := by
  rcases lt_or_ge ‖w‖ (1 / 2) with h | h
  · have h1 := norm_log_one_add_sub_self_le (z := w) (by linarith)
    rw [norm_sub_rev]
    have h2 : (1 - ‖w‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc ‖log (1 + w) - w‖ ≤ ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 := h1
      _ ≤ ‖w‖ ^ 2 * 2 / 2 := by gcongr
      _ ≤ 20 * ‖w‖ ^ 2 := by nlinarith [sq_nonneg ‖w‖]
  · have hz1 : 1 ≤ ‖1 + w‖ := by
      have := Complex.re_le_norm (1 + w)
      simp at this; linarith
    have hlog : ‖log (1 + w)‖ ≤ ‖w‖ + π := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [log_re, log_im]
      have h0 : 0 ≤ Real.log ‖1 + w‖ := Real.log_nonneg hz1
      have h1 : Real.log ‖1 + w‖ ≤ ‖1 + w‖ - 1 := Real.log_le_sub_one_of_pos (by linarith)
      have h2 : ‖1 + w‖ ≤ 1 + ‖w‖ := by
        calc ‖1 + w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_add_le _ _
          _ = 1 + ‖w‖ := by simp
      rw [abs_of_nonneg h0]
      have := abs_arg_le_pi (1 + w)
      linarith
    calc ‖w - log (1 + w)‖ ≤ ‖w‖ + ‖log (1 + w)‖ := norm_sub_le _ _
      _ ≤ 2 * ‖w‖ + π := by linarith
      _ ≤ 20 * ‖w‖ ^ 2 := by nlinarith [Real.pi_le_four]

/-- The Weierstrass terms. -/
noncomputable def wt (j : ℕ) (s : ℂ) : ℂ := s / ((j : ℂ) + 1) - log (1 + s / ((j : ℂ) + 1))

/-- `{Re s > 0, |s| < R}`. -/
def UR (R : ℝ) : Set ℂ := {s | 0 < s.re} ∩ ball 0 R

lemma isOpen_UR (R : ℝ) : IsOpen (UR R) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ball

lemma jp_pos (j : ℕ) : (0 : ℝ) < (j : ℝ) + 1 := by positivity

lemma re_div_jp_nonneg {s : ℂ} (hs : 0 ≤ s.re) (j : ℕ) : 0 ≤ (s / ((j : ℂ) + 1)).re := by
  have : s / ((j : ℂ) + 1) = s / (((j : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.div_ofReal_re]
  exact div_nonneg hs (jp_pos j).le

lemma slit_one_add {s : ℂ} (hs : 0 ≤ s.re) (j : ℕ) : 1 + s / ((j : ℂ) + 1) ∈ slitPlane := by
  left; simp only [add_re, one_re]; linarith [re_div_jp_nonneg hs j]

lemma norm_wt_le {s : ℂ} (hs : 0 ≤ s.re) (j : ℕ) : ‖wt j s‖ ≤ 20 * ‖s‖ ^ 2 / ((j : ℝ) + 1) ^ 2 := by
  have h := norm_sub_log_one_add_le (re_div_jp_nonneg hs j)
  have hn : ‖s / ((j : ℂ) + 1)‖ = ‖s‖ / ((j : ℝ) + 1) := by
    rw [norm_div]; congr 1
    have : ((j : ℂ) + 1) = (((j : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (jp_pos j)]
  rw [wt]; rw [hn, div_pow] at h
  calc _ ≤ 20 * (‖s‖ ^ 2 / ((j : ℝ) + 1) ^ 2) := h
    _ = _ := by ring

lemma summable_inv_jp_sq : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using this

lemma wt_bound_UR (R : ℝ) (j : ℕ) (s : ℂ) (hs : s ∈ UR R) :
    ‖wt j s‖ ≤ 20 * R ^ 2 * (1 / ((j : ℝ) + 1) ^ 2) := by
  have h := norm_wt_le hs.1.le j
  have hsR : ‖s‖ ≤ R := by
    have := hs.2; rw [mem_ball, dist_zero_right] at this; exact this.le
  calc ‖wt j s‖ ≤ 20 * ‖s‖ ^ 2 / ((j : ℝ) + 1) ^ 2 := h
    _ ≤ 20 * R ^ 2 / ((j : ℝ) + 1) ^ 2 := by gcongr
    _ = _ := by ring

lemma hasDerivAt_wt {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    HasDerivAt (wt j) (1 / ((j : ℂ) + 1) - 1 / (s + ((j : ℂ) + 1))) s := by
  have hj : ((j : ℂ) + 1) ≠ 0 := by
    have := jp_pos j
    exact_mod_cast this.ne'
  have h1 : HasDerivAt (fun s : ℂ => s / ((j : ℂ) + 1)) (1 / ((j : ℂ) + 1)) s :=
    (hasDerivAt_id s).div_const _
  have h2 : HasDerivAt (fun s : ℂ => 1 + s / ((j : ℂ) + 1)) (1 / ((j : ℂ) + 1)) s :=
    h1.const_add 1
  have h3 := h2.clog (slit_one_add hs.le j)
  have h4 := h1.sub h3
  convert h4 using 1
  have hne : (1 + s / ((j : ℂ) + 1)) ≠ 0 := slitPlane_ne_zero (slit_one_add hs.le j)
  have hsplit : 1 + s / ((j : ℂ) + 1) = (s + ((j : ℂ) + 1)) / ((j : ℂ) + 1) := by
    rw [add_div, div_self hj]; ring
  congr 1
  rw [hsplit, div_div_div_cancel_right₀ hj]

lemma differentiableOn_wt (R : ℝ) (j : ℕ) : DifferentiableOn ℂ (wt j) (UR R) :=
  fun s hs => (hasDerivAt_wt hs.1 j).differentiableAt.differentiableWithinAt

lemma summable_wt {s : ℂ} (hs : 0 ≤ s.re) : Summable (fun j => wt j s) := by
  refine Summable.of_norm_bounded (g := fun j : ℕ => 20 * ‖s‖ ^ 2 * (1 / ((j : ℝ) + 1) ^ 2))
    (summable_inv_jp_sq.mul_left _) (fun j => ?_)
  have := norm_wt_le hs j
  calc ‖wt j s‖ ≤ 20 * ‖s‖ ^ 2 / ((j : ℝ) + 1) ^ 2 := this
    _ = _ := by ring

/-- The Weierstrass logarithm of `Γ`. -/
noncomputable def LG (s : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) * s - log s + ∑' j, wt j s

lemma mem_UR {s : ℂ} (hs : 0 < s.re) : s ∈ UR (‖s‖ + 1) :=
  ⟨hs, by rw [mem_ball, dist_zero_right]; linarith⟩

theorem differentiableAt_LG {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ LG s := by
  have hU := isOpen_UR (‖s‖ + 1)
  have hsum : DifferentiableOn ℂ (fun w => ∑' j, wt j w) (UR (‖s‖ + 1)) :=
    differentiableOn_tsum_of_summable_norm (summable_inv_jp_sq.mul_left _)
      (differentiableOn_wt _) hU (wt_bound_UR _)
  have h1 : DifferentiableAt ℂ (fun w => ∑' j, wt j w) s :=
    hsum.differentiableAt (hU.mem_nhds (mem_UR hs))
  have h2 : DifferentiableAt ℂ log s := differentiableAt_log (Or.inl hs)
  unfold LG
  exact ((differentiableAt_id.const_mul _).sub h2).add h1

theorem hasDerivAt_LG {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt LG (-(Real.eulerMascheroniConstant : ℂ) - 1 / s +
      ∑' j : ℕ, (1 / ((j : ℂ) + 1) - 1 / (s + ((j : ℂ) + 1)))) s := by
  have hU := isOpen_UR (‖s‖ + 1)
  have hsum := hasSum_deriv_of_summable_norm (summable_inv_jp_sq.mul_left _)
      (differentiableOn_wt _) hU (wt_bound_UR _) (mem_UR hs)
  have hder : ∀ j, deriv (wt j) s = 1 / ((j : ℂ) + 1) - 1 / (s + ((j : ℂ) + 1)) :=
    fun j => (hasDerivAt_wt hs j).deriv
  simp_rw [hder] at hsum
  have hsd : HasDerivAt (fun w => ∑' j, wt j w)
      (∑' j : ℕ, (1 / ((j : ℂ) + 1) - 1 / (s + ((j : ℂ) + 1)))) s := by
    rw [hsum.tsum_eq]
    have hdo : DifferentiableOn ℂ (fun w => ∑' j, wt j w) (UR (‖s‖ + 1)) :=
      differentiableOn_tsum_of_summable_norm (summable_inv_jp_sq.mul_left _)
        (differentiableOn_wt _) hU (wt_bound_UR _)
    exact (hdo.differentiableAt (hU.mem_nhds (mem_UR hs))).hasDerivAt
  have hlog : HasDerivAt log (s⁻¹) s := hasDerivAt_log (Or.inl hs)
  have := (((hasDerivAt_id s).const_mul (-(Real.eulerMascheroniConstant : ℂ))).sub hlog).add hsd
  unfold LG
  convert this using 1
  simp [one_div]

/-! ### `Γ = exp ∘ LG` -/

lemma prod_range_succ_shift (s : ℂ) (n : ℕ) :
    ∏ j ∈ Finset.range (n + 1), (s + j) =
      s * ((n ! : ℂ) * ∏ j ∈ Finset.range n, (1 + s / ((j : ℂ) + 1))) := by
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero]
  rw [mul_comm]
  congr 1
  have hfac : (n ! : ℂ) = ∏ j ∈ Finset.range n, ((j : ℂ) + 1) := by
    rw [← Finset.prod_range_add_one_eq_factorial]; push_cast; rfl
  rw [hfac, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast (jp_pos j).ne'
  push_cast
  field_simp
  ring

lemma exp_sum_wt (s : ℂ) (hs : 0 ≤ s.re) (n : ℕ) :
    exp (∑ j ∈ Finset.range n, wt j s) =
      exp (s * (harmonic n : ℂ)) * (∏ j ∈ Finset.range n, (1 + s / ((j : ℂ) + 1)))⁻¹ := by
  rw [exp_sum]
  unfold wt
  simp_rw [exp_sub]
  rw [Finset.prod_div_distrib]
  have hlog : ∀ j ∈ Finset.range n, exp (log (1 + s / ((j : ℂ) + 1))) = 1 + s / ((j : ℂ) + 1) :=
    fun j _ => exp_log (slitPlane_ne_zero (slit_one_add hs j))
  rw [Finset.prod_congr rfl hlog, div_eq_mul_inv, ← exp_sum]
  congr 2
  unfold harmonic
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [div_eq_mul_inv]

lemma GammaSeq_eq_exp {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq s n = exp (-(((harmonic n : ℝ) - Real.log n : ℝ) : ℂ) * s - log s +
      ∑ j ∈ Finset.range n, wt j s) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hfac : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hP : ∏ j ∈ Finset.range n, (1 + s / ((j : ℂ) + 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j _; exact slitPlane_ne_zero (slit_one_add hs.le j)
  rw [exp_add, exp_sub, exp_sum_wt s hs.le n, exp_log hs0]
  unfold GammaSeq
  rw [prod_range_succ_shift, cpow_def_of_ne_zero hnC]
  have hlogn : log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [hlogn]
  have hexp : exp (-(((harmonic n : ℝ) - Real.log n : ℝ) : ℂ) * s) =
      exp ((Real.log n : ℂ) * s) * (exp (s * (harmonic n : ℂ)))⁻¹ := by
    rw [← exp_neg, ← exp_add]; congr 1; push_cast; ring
  rw [hexp]
  have hE : exp (s * (harmonic n : ℂ)) ≠ 0 := exp_ne_zero _
  field_simp

theorem Gamma_eq_exp_LG {s : ℂ} (hs : 0 < s.re) : Gamma s = exp (LG s) := by
  have hlim : Tendsto (fun n : ℕ => exp (-(((harmonic n : ℝ) - Real.log n : ℝ) : ℂ) * s - log s +
      ∑ j ∈ Finset.range n, wt j s)) atTop (𝓝 (exp (LG s))) := by
    apply (continuous_exp.tendsto _).comp
    have h1 : Tendsto (fun n : ℕ => (((harmonic n : ℝ) - Real.log n : ℝ) : ℂ)) atTop
        (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log
    have h2 := (summable_wt hs.le).hasSum.tendsto_sum_nat
    unfold LG
    exact ((h1.neg.mul_const s).sub_const (log s)).add h2
  have hG := GammaSeq_tendsto_Gamma s
  have heq : GammaSeq s =ᶠ[atTop] fun n : ℕ => exp (-(((harmonic n : ℝ) - Real.log n : ℝ) : ℂ) * s -
      log s + ∑ j ∈ Finset.range n, wt j s) := by
    filter_upwards [eventually_ne_atTop 0] with n hn using GammaSeq_eq_exp hs hn
  exact tendsto_nhds_unique (hG.congr' heq) hlim

/-- **Digamma series** on `Re s > 0`. -/
theorem digamma_eq_series {s : ℂ} (hs : 0 < s.re) :
    digamma s = -(Real.eulerMascheroniConstant : ℂ) - 1 / s +
      ∑' j : ℕ, (1 / ((j : ℂ) + 1) - 1 / (s + ((j : ℂ) + 1))) := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : Gamma =ᶠ[𝓝 s] fun w => exp (LG w) := by
    filter_upwards [hopen.mem_nhds hs] with w hw using Gamma_eq_exp_LG hw
  have hd : HasDerivAt (fun w => exp (LG w)) (exp (LG s) * _) s := (hasDerivAt_LG hs).cexp
  rw [digamma_def, logDeriv_apply, heq.deriv_eq, hd.deriv, heq.eq_of_nhds]
  field_simp [exp_ne_zero]

end RamanujanTau.ZeroCountRvM
