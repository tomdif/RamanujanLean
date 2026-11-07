/-
# The case `n = 0`: `γ(0) = 32 ∫_0^∞ Φ(u) du`

For `n = 0` the integration by parts leaves a boundary term `h'(0) = Σ_k h_k'(0)`, and
`h'(0) = θ₀(1)/2 + 2θ₀'(1) = −1/4` is the derivative at `t = 1` of the theta functional equation
`θ(t) = t^{−1/2} θ(1/t)` (Mathlib's `evenKernel_functional_equation`), which gives `θ₀'(1) = −(2θ₀(1)+1)/8`.
Together with `γ(0) = 4 − 2F(0)` this gives **`gammaMathlib_zero_eq_mom`**.
-/
import RamanujanTau.GORZXiEff.PhiKernel

set_option autoImplicit false

namespace GORZXiEff

open Real Set MeasureTheory Filter Topology GORZXi

/-- the theta series `T(t) = Σ_k e^{−πKt}` and its termwise derivative. -/
noncomputable def Tth (t : ℝ) : ℝ := ∑' k, rexp (-π * Kk k * t)
noncomputable def Tth' (t : ℝ) : ℝ := ∑' k, -π * Kk k * rexp (-π * Kk k * t)

lemma Tth_eq {t : ℝ} (ht : 0 < t) : Tth t = theta0 t := by
  rw [← (theta0_hasSum ht).tsum_eq]; rfl

lemma summable_K_exp : Summable fun k : ℕ => π * Kk k * rexp (-π * Kk k / 2) := by
  have hs : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ 2 * rexp (-(π / 2) * ((k + 1 : ℕ) : ℝ)) :=
    (summable_nat_add_iff 1).2 (summable_pow_mul_exp_neg_nat_mul 2 (by positivity))
  refine Summable.of_nonneg_of_le (fun k => by have := Kk_ge_one k; positivity) (fun k => ?_)
    (hs.mul_left π)
  unfold Kk; push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : rexp (-π * ((k : ℝ) + 1) ^ 2 / 2) ≤ rexp (-(π / 2) * ((k : ℝ) + 1)) := by
    apply exp_le_exp.2
    have h1 : ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 pi_pos.le]
  calc π * ((k : ℝ) + 1) ^ 2 * rexp (-π * ((k : ℝ) + 1) ^ 2 / 2)
      ≤ π * ((k : ℝ) + 1) ^ 2 * rexp (-(π / 2) * ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

lemma hasDerivAt_Tth {t : ℝ} (ht : 1 / 2 < t) : HasDerivAt Tth (Tth' t) t := by
  refine hasDerivAt_tsum_of_isPreconnected (g := fun (k : ℕ) (t : ℝ) => rexp (-π * Kk k * t))
    (g' := fun (k : ℕ) (t : ℝ) => -π * Kk k * rexp (-π * Kk k * t)) summable_K_exp isOpen_Ioi
    isPreconnected_Ioi (fun k y _ => ?_) (fun k y hy => ?_) (y₀ := 1)
    (show (1 : ℝ) ∈ Ioi (1 / 2) by norm_num) ?_ ht
  · have := ((hasDerivAt_id y).const_mul (-π * Kk k)).exp
    convert this using 1; simp; ring
  · have hK := Kk_ge_one k
    have hy' : (1 : ℝ) / 2 < y := hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_pos _).le, abs_of_nonpos (by nlinarith [pi_pos])]
    have : rexp (-π * Kk k * y) ≤ rexp (-π * Kk k / 2) := by
      apply exp_le_exp.2; nlinarith [mul_pos pi_pos (show (0 : ℝ) < Kk k by linarith)]
    have h0 : 0 ≤ π * Kk k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  · rw [show (fun k => rexp (-π * Kk k * 1)) = fun k : ℕ => rexp (-π * ((k : ℝ) + 1) ^ 2 * 1) from rfl]
    exact (theta0_hasSum one_pos).summable

/-- **`θ₀'(1) = −(2θ₀(1) + 1)/8`** from the theta functional equation. -/
lemma Tth'_one : Tth' 1 = -(2 * Tth 1 + 1) / 8 := by
  have hT := hasDerivAt_Tth (t := 1) (by norm_num)
  have hf : HasDerivAt (fun t => 2 * Tth t + 1) (2 * Tth' 1) 1 := by
    simpa using (hT.const_mul 2).add_const 1
  have hinv : HasDerivAt (fun t : ℝ => t⁻¹) (-(1 : ℝ) ^ 2)⁻¹ 1 := by
    simpa using hasDerivAt_inv (one_ne_zero (α := ℝ))
  have hTi : HasDerivAt (fun t : ℝ => Tth t⁻¹) (Tth' 1 * -1) 1 := by
    have := (show HasDerivAt Tth (Tth' 1) (1 : ℝ)⁻¹ by simpa using hT).comp 1
      (by simpa using hasDerivAt_inv (one_ne_zero (α := ℝ)))
    simpa using this
  have hr : HasDerivAt (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) (-(1 / 2)) 1 := by
    simpa using Real.hasDerivAt_rpow_const (x := 1) (p := -(1 / 2)) (Or.inl one_ne_zero)
  have hg : HasDerivAt (fun t : ℝ => t ^ (-(1 / 2) : ℝ) * (2 * Tth t⁻¹ + 1))
      (-(1 / 2) * (2 * Tth 1 + 1) + 1 * (2 * (Tth' 1 * -1))) 1 := by
    have := hr.mul ((hTi.const_mul 2).add_const 1)
    simpa using this
  have heq : (fun t => 2 * Tth t + 1) =ᶠ[𝓝 1] fun t : ℝ => t ^ (-(1 / 2) : ℝ) * (2 * Tth t⁻¹ + 1) := by
    filter_upwards [Ioi_mem_nhds one_pos] with t ht
    have ht' : (0 : ℝ) < t := ht
    rw [Tth_eq ht', Tth_eq (inv_pos.2 ht')]
    have := HurwitzZeta.evenKernel_functional_equation 0 t
    rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero] at this
    simp only [theta0]
    rw [show (1 : ℝ) / t = t⁻¹ by ring] at this
    rw [this, Real.rpow_neg ht'.le, one_div]
    ring
  have := hf.unique (hg.congr_of_eventuallyEq heq)
  linarith

lemma hasSum_hk'_zero : HasSum (fun k => hk' k 0) (-(1 / 4)) := by
  have h1 := (theta0_hasSum one_pos).mul_left (1 / 2)
  have h2 : HasSum (fun k : ℕ => -π * Kk k * rexp (-π * Kk k * 1)) (Tth' 1) := by
    refine Summable.hasSum ?_
    exact Summable.of_norm_bounded summable_K_exp (fun k => by
      have hK := Kk_ge_one k
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_pos _).le,
        abs_of_nonpos (by nlinarith [pi_pos])]
      have : rexp (-π * Kk k * 1) ≤ rexp (-π * Kk k / 2) := by
        apply exp_le_exp.2; nlinarith [mul_pos pi_pos (show (0 : ℝ) < Kk k by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left this (show 0 ≤ π * Kk k by positivity)])
  have h3 := h1.add (h2.mul_left 2)
  rw [Tth'_one, Tth_eq one_pos] at h3
  convert h3 using 1
  · funext k; simp only [hk', mono, Kk, mul_zero, exp_zero]; ring
  · ring

/-- `γ(0) = 4 − 2F(0)` (Mathlib's `γ`). -/
lemma gammaMathlib_zero : gammaMathlib 0 = 4 - 2 * FXi 0 := by
  rw [gammaMathlib, iteratedDeriv_xiFun]
  simp only [Gch]
  have := Lch_even_zero 0
  simp only [mul_zero, pow_zero, one_mul] at this
  rw [this]
  simp; ring

/-- **`γ(0) = 32 ∫_0^∞ Φ(u) du`.** -/
theorem gammaMathlib_zero_eq_mom : gammaMathlib 0 = 32 * fq 0 * mom PhiR (2 * 0) := by
  have hI : ∀ k, ∫ u in Ioi (0 : ℝ), hk'' k u = 0 - hk' k 0 := fun k =>
    integral_Ioi_of_hasDerivAt_of_tendsto (hasDerivAt_hk' k 0).continuousAt.continuousWithinAt
      (fun x _ => hasDerivAt_hk' k x)
      (IntegrableOn.congr_fun (dom_hk''.int k 0) (fun u _ => by simp) measurableSet_Ioi)
      (by simpa using dom_hk'.decay k 0)
  have hm : mom PhiR 0 = ∑' k, ((1 / 2) * (0 - hk' k 0) - (1 / 8) * ∫ u in Ioi (0 : ℝ), u ^ 0 * hk k u) := by
    unfold mom PhiR
    rw [dom_phik.integral_tsum]
    congr 1; funext k
    rw [← hI, ← integral_const_mul, ← integral_const_mul, ← integral_sub]
    · refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      simp only [phik_eq]; ring
    · exact (IntegrableOn.congr_fun (dom_hk''.int k 0) (fun u _ => by simp) measurableSet_Ioi).const_mul _
    · exact (dom_hk.int k 0).const_mul _
  have hs1 : Summable fun k => (1 / 2) * (0 - hk' k 0) := (hasSum_hk'_zero.summable.neg.mul_left (1 / 2 : ℝ)).congr
    (fun k => by ring)
  rw [hm, Summable.tsum_sub hs1 ((dom_hk.summable_integral 0).mul_left _), tsum_mul_left, tsum_mul_left,
    ← dom_hk.integral_tsum, gammaMathlib_zero, FXi_eq_H]
  have : ∑' k, (0 - hk' k 0) = 1 / 4 := by
    rw [show (fun k => 0 - hk' k 0) = fun k => -hk' k 0 by funext k; ring]
    rw [tsum_neg, hasSum_hk'_zero.tsum_eq]; ring
  rw [this]
  simp [fq]
  ring

end GORZXiEff
