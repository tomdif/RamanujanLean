/-
# Mean square of the Euler–Maclaurin tail `I_N(s) = ∫_N^∞ {x} x^{−s−1} dx` by Plancherel

On the log scale `x = e^{−v}`, `I_N(u − 2πiξ)` is the Fourier transform of
`h(v) = e^{uv} {e^{−v}} 1_{e^{−v} > N}`, so for any interval

    ∫_a^b |I_N(u − it)|² dt ≤ 2π ∫_ℝ |h|² ≤ 2π ∫_{−∞}^{−log N} e^{2uv} dv = π N^{−2u}/u.

This is the `L²` replacement for the pointwise bound `|I_N(s)| ≤ N^{−u}/u`, and it is what lets the
approximation `ζ(s) ≈ ∑_{n≤N} n^{−s}` with `N ≍ T` work in mean square all the way down to `u > 1/2`.
-/
import RamanujanTau.RankinOmega.ZetaApprox
import RamanujanTau.TauOmegaPartial.Plancherel

set_option autoImplicit false

namespace RamanujanTau.ZetaMeanSquare

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.RankinOmega
open scoped Real FourierTransform

/-- `h(v) = e^{uv} g_N(e^{−v})`. -/
noncomputable def hT (N : ℕ) (u : ℝ) (v : ℝ) : ℂ := Real.exp (u * v) • gN N (Real.exp (-v))

lemma measurable_hT (N : ℕ) (u : ℝ) : Measurable (hT N u) := by
  unfold hT
  exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).smul
    ((measurable_gN N).comp (Real.measurable_exp.comp measurable_neg))

lemma fourier_hT (N : ℕ) (u ξ : ℝ) :
    𝓕 (hT N u) ξ = IN N ((u : ℂ) - ((2 * π * ξ : ℝ) : ℂ) * I) := by
  set w : ℂ := (u : ℂ) - ((2 * π * ξ : ℝ) : ℂ) * I with hw
  have hre : (-w).re = -u := by simp [hw]
  have him : (-w).im = 2 * π * ξ := by simp [hw]
  have h := mellin_eq_fourier (gN N) (s := -w)
  rw [hre, him] at h
  have e1 : (2 * π * ξ) / (2 * π) = ξ := by field_simp
  rw [e1] at h
  have e2 : (fun v : ℝ => Real.exp (-(-u) * v) • gN N (Real.exp (-v))) = hT N u := by
    funext v; simp [hT]
  rw [e2] at h
  rw [IN, h]

lemma norm_hT_le (N : ℕ) (hN : 1 ≤ N) (u v : ℝ) :
    ‖hT N u v‖ ≤ (Iic (-Real.log N)).indicator (fun v => Real.exp (u * v)) v := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold hT
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  by_cases hv : v ∈ Iic (-Real.log N)
  · rw [indicator_of_mem hv]
    have := norm_gN_le N (Real.exp (-v))
    have h0 := (Real.exp_pos (u * v)).le
    nlinarith
  · rw [indicator_of_notMem hv]
    have hv' : -Real.log N < v := by simpa using hv
    have hle : Real.exp (-v) ≤ N := by
      rw [← Real.exp_log hN0]; exact Real.exp_le_exp.2 (by linarith)
    have : gN N (Real.exp (-v)) = 0 := by
      unfold gN
      exact indicator_of_notMem (by simpa using hle) _
    rw [this, norm_zero, mul_zero]

lemma integrable_hT (N : ℕ) (hN : 1 ≤ N) {u : ℝ} (hu : 0 < u) : Integrable (hT N u) := by
  have hg : Integrable ((Iic (-Real.log N)).indicator (fun v => Real.exp (u * v))) :=
    (integrableOn_exp_mul_Iic hu _).integrable_indicator measurableSet_Iic
  exact hg.mono' (measurable_hT N u).aestronglyMeasurable
    (Eventually.of_forall fun v => norm_hT_le N hN u v)

lemma sq_norm_hT_le (N : ℕ) (hN : 1 ≤ N) {u : ℝ} (hu : 0 < u) (v : ℝ) :
    ‖hT N u v‖ ^ 2 ≤ (Iic (-Real.log N)).indicator (fun v => Real.exp ((2 * u) * v)) v := by
  have h := norm_hT_le N hN u v
  by_cases hv : v ∈ Iic (-Real.log N)
  · rw [indicator_of_mem hv] at h ⊢
    have e : Real.exp ((2 * u) * v) = Real.exp (u * v) ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  · rw [indicator_of_notMem hv] at h ⊢
    have : ‖hT N u v‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [this]; norm_num

lemma memLp_hT (N : ℕ) (hN : 1 ≤ N) {u : ℝ} (hu : 0 < u) : MemLp (hT N u) 2 := by
  have hg : Integrable ((Iic (-Real.log N)).indicator (fun v => Real.exp ((2 * u) * v))) :=
    (integrableOn_exp_mul_Iic (by linarith) _).integrable_indicator measurableSet_Iic
  refine (memLp_two_iff_integrable_sq_norm (measurable_hT N u).aestronglyMeasurable).2 ?_
  exact hg.mono' ((measurable_hT N u).norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun v => by
      rw [Real.norm_of_nonneg (by positivity)]; exact sq_norm_hT_le N hN hu v)

lemma integral_sq_hT_le (N : ℕ) (hN : 1 ≤ N) {u : ℝ} (hu : 0 < u) :
    ∫ v, ‖hT N u v‖ ^ 2 ≤ (N : ℝ) ^ (-(2 * u)) / (2 * u) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hg : Integrable ((Iic (-Real.log N)).indicator (fun v => Real.exp ((2 * u) * v))) :=
    (integrableOn_exp_mul_Iic (by linarith) _).integrable_indicator measurableSet_Iic
  have hsq : Integrable (fun v => ‖hT N u v‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (measurable_hT N u).aestronglyMeasurable).1 (memLp_hT N hN hu)
  calc ∫ v, ‖hT N u v‖ ^ 2
      ≤ ∫ v, (Iic (-Real.log N)).indicator (fun v => Real.exp ((2 * u) * v)) v :=
        integral_mono hsq hg (fun v => sq_norm_hT_le N hN hu v)
    _ = Real.exp ((2 * u) * (-Real.log N)) / (2 * u) := by
        rw [integral_indicator measurableSet_Iic, integral_exp_mul_Iic (by linarith)]
    _ = (N : ℝ) ^ (-(2 * u)) / (2 * u) := by
        rw [Real.rpow_def_of_pos hN0]; congr 2; ring

/-- **`L²` bound for the tail on any vertical segment.** -/
theorem tail_L2 (N : ℕ) (hN : 1 ≤ N) {u : ℝ} (hu : 0 < u) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, ‖IN N ((u : ℂ) - t * I)‖ ^ 2 ≤ Real.pi * (N : ℝ) ^ (-(2 * u)) / u := by
  obtain ⟨hF2, hpl⟩ := TauOmegaPartial.plancherel_of_integrable (integrable_hT N hN hu)
    (memLp_hT N hN hu)
  set F := 𝓕 (hT N u) with hF
  have hpi : 0 < 2 * π := by positivity
  have hFsq : Integrable (fun ξ => ‖F ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hF2.1).1 hF2
  have e : ∀ t : ℝ, ‖IN N ((u : ℂ) - t * I)‖ ^ 2 = (fun ξ => ‖F ξ‖ ^ 2) (t / (2 * π)) := by
    intro t
    simp only [hF, fourier_hT]
    congr 4
    push_cast; field_simp
  simp_rw [e]
  rw [intervalIntegral.integral_comp_div (fun ξ => ‖F ξ‖ ^ 2) hpi.ne', smul_eq_mul]
  have hab' : a / (2 * π) ≤ b / (2 * π) := div_le_div_of_nonneg_right hab hpi.le
  have h1 : ∫ ξ in a / (2 * π)..b / (2 * π), ‖F ξ‖ ^ 2 ≤ ∫ ξ, ‖F ξ‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab']
    exact setIntegral_le_integral hFsq (Eventually.of_forall fun _ => by positivity)
  have h2 := integral_sq_hT_le N hN hu
  rw [hpl] at h1
  calc 2 * π * ∫ ξ in a / (2 * π)..b / (2 * π), ‖F ξ‖ ^ 2
      ≤ 2 * π * ((N : ℝ) ^ (-(2 * u)) / (2 * u)) := by gcongr; exact h1.trans h2
    _ = Real.pi * (N : ℝ) ^ (-(2 * u)) / u := by field_simp

end RamanujanTau.ZetaMeanSquare
