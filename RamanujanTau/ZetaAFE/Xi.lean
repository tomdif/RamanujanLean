/-
# The entire function `Ξ(s) = s(1−s)Λ₀(s) − 1 = s(1−s)Λ(s)`

* `differentiable_Xi`, `Xi_one_sub` (`Ξ(1−s) = Ξ(s)`), `Xi_eq_zeta` (`Ξ = s(1−s)Γ_ℝ(s)ζ(s)` on `Re s > 0`).
* `norm_Lambda0_le`: `Λ₀` is bounded on `−1 ≤ Re s ≤ 2` (from Riemann's formula
  `GORZXi.completedRiemannZeta₀_eq`, `Λ₀(s) = (M(s/2) + M((1−s)/2))/2`, `M = mellin (1_{t>1}(θ−1))`).
-/
import RamanujanTau.GORZXi.XiMellin
import RamanujanTau.ZetaAFE.Line

set_option autoImplicit false

namespace RamanujanTau.ZetaAFE

open Complex MeasureTheory Set Filter Topology

/-- `Ξ(s) = s(1−s)Λ₀(s) − 1`, entire, equal to `s(1−s)Λ(s)` off `{0,1}`. -/
noncomputable def Xi (s : ℂ) : ℂ := s * (1 - s) * completedRiemannZeta₀ s - 1

lemma differentiable_Xi : Differentiable ℂ Xi := by
  unfold Xi
  have := differentiable_completedZeta₀
  fun_prop

lemma Xi_one_sub (s : ℂ) : Xi (1 - s) = Xi s := by
  unfold Xi; rw [completedRiemannZeta₀_one_sub]; ring

lemma Xi_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    Xi s = s * (1 - s) * completedRiemannZeta s := by
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  unfold Xi; rw [completedRiemannZeta_eq]; field_simp; ring

lemma Xi_eq_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Xi s = s * (1 - s) * Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  rw [Xi_eq hs0 hs1, riemannZeta_def_of_ne_zero hs0]
  have := Gammaℝ_ne_zero_of_re_pos hs
  field_simp

/-- `B₀ = ∫_{t>0} ‖1_{t>1}(θ(t)−1)‖`. -/
noncomputable def B0 : ℝ := ∫ t in Ioi (0 : ℝ), ‖GORZXi.Aθ t‖

lemma integrableOn_Aθ : IntegrableOn GORZXi.Aθ (Ioi 0) := by
  have h := GORZXi.convA 1
  unfold MellinConvergent at h
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp

lemma norm_mellin_Aθ_le {w : ℂ} (hw : w.re ≤ 1) : ‖mellin GORZXi.Aθ w‖ ≤ B0 := by
  unfold mellin B0
  refine norm_integral_le_of_norm_le integrableOn_Aθ.norm ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  rw [norm_smul]
  by_cases h1 : t ∈ Ioi (1 : ℝ)
  · rw [norm_cpow_eq_rpow_re_of_pos ht]
    have : t ^ (w - 1).re ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt h1)
      simp; linarith
    have := norm_nonneg (GORZXi.Aθ t)
    nlinarith
  · have : GORZXi.Aθ t = 0 := by
      unfold GORZXi.Aθ; exact indicator_of_notMem h1 _
    simp [this]

lemma B0_nonneg : 0 ≤ B0 := setIntegral_nonneg measurableSet_Ioi fun _ _ => norm_nonneg _

lemma norm_Lambda0_le {s : ℂ} (h1 : -1 ≤ s.re) (h2 : s.re ≤ 2) :
    ‖completedRiemannZeta₀ s‖ ≤ B0 := by
  rw [GORZXi.completedRiemannZeta₀_eq, norm_div]
  have ha : ‖mellin GORZXi.Aθ (s / 2)‖ ≤ B0 := norm_mellin_Aθ_le (by simp; linarith)
  have hb : ‖mellin GORZXi.Aθ (1 / 2 - s / 2)‖ ≤ B0 := norm_mellin_Aθ_le (by simp; linarith)
  have := norm_add_le (mellin GORZXi.Aθ (s / 2)) (mellin GORZXi.Aθ (1 / 2 - s / 2))
  rw [show ‖(2 : ℂ)‖ = 2 by simp]
  linarith

lemma norm_Xi_le {s : ℂ} (h1 : -1 ≤ s.re) (h2 : s.re ≤ 2) :
    ‖Xi s‖ ≤ (1 + ‖s‖) ^ 2 * B0 + 1 := by
  unfold Xi
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_one]
  have h3 : ‖1 - s‖ ≤ 1 + ‖s‖ := by
    refine (norm_sub_le _ _).trans ?_; simp
  have h4 := norm_Lambda0_le h1 h2
  have h5 : ‖s‖ ≤ 1 + ‖s‖ := by linarith
  have := B0_nonneg
  calc ‖s‖ * ‖1 - s‖ * ‖completedRiemannZeta₀ s‖ + 1
      ≤ (1 + ‖s‖) * (1 + ‖s‖) * B0 + 1 := by gcongr
    _ = _ := by ring

/-- A polynomial is dominated by the Gaussian weight: `(A+|y|)⁴ ≤ 8(A⁴+8) e^{y²/2}`. -/
lemma poly_le_gauss {A : ℝ} (hA : 0 ≤ A) (y : ℝ) :
    (A + |y|) ^ 4 ≤ 8 * (A ^ 4 + 8) * Real.exp (y ^ 2 / 2) := by
  have hy4 : y ^ 4 ≤ 8 * Real.exp (y ^ 2 / 2) := by
    have := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ y ^ 2 / 2)
    nlinarith [sq_nonneg y]
  have hconv : (A + |y|) ^ 4 ≤ 8 * (A ^ 4 + y ^ 4) := by
    have hy : |y| ^ 4 = y ^ 4 := by rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
    have hb := abs_nonneg y
    nlinarith [sq_nonneg (A - |y|), sq_nonneg (A + |y|), mul_nonneg hA hb,
      sq_nonneg (A ^ 2 - |y| ^ 2), mul_nonneg (mul_nonneg hA hb) (sq_nonneg (A - |y|))]
  have he : 1 ≤ Real.exp (y ^ 2 / 2) := Real.one_le_exp (by positivity)
  have hA4 : 0 ≤ A ^ 4 := by positivity
  nlinarith

end RamanujanTau.ZetaAFE
