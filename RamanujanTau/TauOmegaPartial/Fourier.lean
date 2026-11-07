/-
# The logarithmic-scale function `h_σ(u) = e^{σu} A(e^{−u})` and its Fourier transform

Under the growth hypothesis `‖A(x)‖ ≤ c₀ x^α` (`x ≥ X₀ ≥ 1`) and `σ = α + δ`, `δ > 0`:

* `h_σ ∈ L¹ ∩ L²` and `∫ |h_σ|² ≤ c₀²/(2δ) + S² log X₀`, where `S = ∑_{n ≤ X₀} |a(n)|`;
* `𝓕 h_σ (ξ) = L(f, σ − 2πiξ)/(σ − 2πiξ)` (`mellin_eq_fourier` + `mellin_A_eq`).
-/
import RamanujanTau.TauOmegaPartial.Mellin
import RamanujanTau.TauOmegaPartial.Plancherel

set_option autoImplicit false

namespace RamanujanTau.TauOmegaPartial

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups FourierTransform Real

variable {k : ℕ}

/-- `h_σ(u) = e^{σu} A(e^{−u})`. -/
noncomputable def hfun (f : CuspForm 𝒮ℒ (k : ℤ)) (σ : ℝ) (u : ℝ) : ℂ :=
  Real.exp (σ * u) • A f (Real.exp (-u))

/-- **Fourier transform of `h_σ`**: `𝓕 h_σ(ξ) = L(f, σ − 2πiξ)/(σ − 2πiξ)`. -/
theorem fourier_hfun (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {α c0 X0 : ℝ} (hα : 0 ≤ α)
    (hX : ∀ x ≥ X0, ‖A f x‖ ≤ c0 * x ^ α) {σ : ℝ} (hσ : α < σ) (ξ : ℝ) :
    𝓕 (hfun f σ) ξ = fL f ((σ : ℂ) - 2 * π * ξ * I) / ((σ : ℂ) - 2 * π * ξ * I) := by
  set w : ℂ := (σ : ℂ) - 2 * π * ξ * I with hw
  have hre : (-w).re = -σ := by simp [hw]
  have him : (-w).im = 2 * π * ξ := by simp [hw]
  have h := mellin_eq_fourier (A f) (s := -w)
  rw [hre, him] at h
  have e1 : (2 * π * ξ) / (2 * π) = ξ := by field_simp
  rw [e1] at h
  have e2 : (fun u : ℝ => Real.exp (-(-σ) * u) • A f (Real.exp (-u))) = hfun f σ := by
    funext u; simp [hfun]
  rw [e2] at h
  rw [← h]
  exact mellin_A_eq f hk hα hX (by rw [hw]; simpa using hσ)

lemma measurable_hfun (f : CuspForm 𝒮ℒ (k : ℤ)) (σ : ℝ) : Measurable (hfun f σ) := by
  unfold hfun
  exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).smul
    ((measurable_A f).comp (Real.measurable_exp.comp measurable_neg))

/-- The dominating function for `‖h_σ‖²`. -/
noncomputable def G2 (c0 δ L S : ℝ) (u : ℝ) : ℝ :=
  (Iic (0 : ℝ)).indicator (fun u => c0 ^ 2 * Real.exp ((2 * δ) * u)) u +
    (Icc (-L) 0).indicator (fun _ => S ^ 2) u

/-- The dominating function for `‖h_σ‖`. -/
noncomputable def G1 (c0 δ L S : ℝ) (u : ℝ) : ℝ :=
  (Iic (0 : ℝ)).indicator (fun u => c0 * Real.exp (δ * u)) u +
    (Icc (-L) 0).indicator (fun _ => S) u

/-- Pointwise bounds: `‖h_σ(u)‖ ≤ G1(u)` and `‖h_σ(u)‖² ≤ G2(u)`. -/
lemma norm_hfun_le (f : CuspForm 𝒮ℒ (k : ℤ)) {α c0 X0 σ : ℝ} (hα : 0 ≤ α) (hc0 : 0 ≤ c0)
    (hX0 : 1 ≤ X0) (hX : ∀ x ≥ X0, ‖A f x‖ ≤ c0 * x ^ α) (hσ : α ≤ σ) (u : ℝ) :
    ‖hfun f σ u‖ ≤ G1 c0 (σ - α) (Real.log X0) (∑ n ∈ Finset.Icc 1 ⌊X0⌋₊, ‖coef f n‖) u ∧
    ‖hfun f σ u‖ ^ 2 ≤
      G2 c0 (σ - α) (Real.log X0) (∑ n ∈ Finset.Icc 1 ⌊X0⌋₊, ‖coef f n‖) u := by
  set S := ∑ n ∈ Finset.Icc 1 ⌊X0⌋₊, ‖coef f n‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hn : ‖hfun f σ u‖ = Real.exp (σ * u) * ‖A f (Real.exp (-u))‖ := by
    rw [hfun, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hI1 : 0 ≤ (Iic (0 : ℝ)).indicator (fun u => c0 * Real.exp ((σ - α) * u)) u :=
    Set.indicator_nonneg (fun _ _ => by positivity) _
  have hI2 : 0 ≤ (Icc (-Real.log X0) 0).indicator (fun _ => S) u :=
    Set.indicator_nonneg (fun _ _ => hS0) _
  have hJ1 : 0 ≤ (Iic (0 : ℝ)).indicator (fun u => c0 ^ 2 * Real.exp ((2 * (σ - α)) * u)) u :=
    Set.indicator_nonneg (fun _ _ => by positivity) _
  have hJ2 : 0 ≤ (Icc (-Real.log X0) 0).indicator (fun _ => S ^ 2) u :=
    Set.indicator_nonneg (fun _ _ => by positivity) _
  unfold G1 G2
  rcases lt_or_ge 0 u with hu | hu
  · have h0 : hfun f σ u = 0 := by
      rw [hfun, A_of_lt_one f ((Real.exp_lt_exp.2 (by linarith : -u < 0)).trans_eq Real.exp_zero), smul_zero]
    rw [h0, norm_zero]
    exact ⟨by linarith, by nlinarith⟩
  rcases le_or_gt u (-Real.log X0) with hL | hL
  · -- far range: `e^{−u} ≥ X₀`
    have hx : X0 ≤ Real.exp (-u) := by
      rw [← Real.exp_log (by linarith : (0:ℝ) < X0)]; exact Real.exp_le_exp.2 (by linarith)
    have hA := hX _ hx
    rw [← Real.exp_mul] at hA
    have hb : ‖hfun f σ u‖ ≤ c0 * Real.exp ((σ - α) * u) := by
      rw [hn]
      calc Real.exp (σ * u) * ‖A f (Real.exp (-u))‖ ≤ Real.exp (σ * u) * (c0 * Real.exp (-u * α)) :=
            by gcongr
        _ = c0 * (Real.exp (σ * u) * Real.exp (-u * α)) := by ring
        _ = c0 * Real.exp ((σ - α) * u) := by rw [← Real.exp_add]; congr 2; ring
    have hmem : u ∈ Iic (0 : ℝ) := hu
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    refine ⟨by linarith, ?_⟩
    have h2 : ‖hfun f σ u‖ ^ 2 ≤ (c0 * Real.exp ((σ - α) * u)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    have e : (c0 * Real.exp ((σ - α) * u)) ^ 2 = c0 ^ 2 * Real.exp (2 * (σ - α) * u) := by
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    rw [e] at h2; linarith
  · -- near range: `e^{−u} < X₀`, `u ≤ 0`
    have hx : Real.exp (-u) ≤ X0 := by
      rw [← Real.exp_log (by linarith : (0:ℝ) < X0)]; exact Real.exp_le_exp.2 (by linarith)
    have hA := norm_A_le f hx
    have hb : ‖hfun f σ u‖ ≤ S := by
      rw [hn]
      have he : Real.exp (σ * u) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      calc Real.exp (σ * u) * ‖A f (Real.exp (-u))‖ ≤ 1 * S := by
            gcongr
        _ = S := one_mul S
    have hmem : u ∈ Icc (-Real.log X0) 0 := ⟨hL.le, hu⟩
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    refine ⟨by linarith, ?_⟩
    have h2 : ‖hfun f σ u‖ ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    linarith

lemma integrable_G1 {c0 δ L S : ℝ} (hδ : 0 < δ) : Integrable (G1 c0 δ L S) := by
  unfold G1
  refine Integrable.add ?_ ?_
  · exact (show IntegrableOn (fun u => c0 * Real.exp (δ * u)) (Iic 0) volume from
      (integrableOn_exp_mul_Iic hδ 0).const_mul c0).integrable_indicator measurableSet_Iic
  · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc

lemma integrable_G2 {c0 δ L S : ℝ} (hδ : 0 < δ) : Integrable (G2 c0 δ L S) := by
  unfold G2
  refine Integrable.add ?_ ?_
  · exact (show IntegrableOn (fun u => c0 ^ 2 * Real.exp ((2 * δ) * u)) (Iic 0) volume from
      (integrableOn_exp_mul_Iic (by linarith : 0 < 2 * δ) 0).const_mul (c0 ^ 2)).integrable_indicator
      measurableSet_Iic
  · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc

lemma integral_G2 {c0 δ L S : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L) :
    ∫ u, G2 c0 δ L S u = c0 ^ 2 / (2 * δ) + S ^ 2 * L := by
  unfold G2
  rw [integral_add, integral_indicator measurableSet_Iic, integral_indicator measurableSet_Icc,
    integral_const_mul, integral_exp_mul_Iic (by linarith : 0 < 2 * δ), setIntegral_const]
  · simp [Real.volume_real_Icc, hL]; ring
  · exact (show IntegrableOn (fun u => c0 ^ 2 * Real.exp ((2 * δ) * u)) (Iic 0) volume from
      (integrableOn_exp_mul_Iic (by linarith : 0 < 2 * δ) 0).const_mul (c0 ^ 2)).integrable_indicator
      measurableSet_Iic
  · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc

/-- **`h_σ ∈ L¹ ∩ L²` with the explicit `L²` bound.** -/
theorem hfun_L1L2 (f : CuspForm 𝒮ℒ (k : ℤ)) {α c0 X0 σ : ℝ} (hα : 0 ≤ α) (hc0 : 0 ≤ c0)
    (hX0 : 1 ≤ X0) (hX : ∀ x ≥ X0, ‖A f x‖ ≤ c0 * x ^ α) (hσ : α < σ) :
    Integrable (hfun f σ) ∧ MemLp (hfun f σ) 2 ∧
      ∫ u, ‖hfun f σ u‖ ^ 2 ≤ c0 ^ 2 / (2 * (σ - α)) +
        (∑ n ∈ Finset.Icc 1 ⌊X0⌋₊, ‖coef f n‖) ^ 2 * Real.log X0 := by
  have hδ : 0 < σ - α := by linarith
  have hb := norm_hfun_le f hα hc0 hX0 hX hσ.le
  have hm := (measurable_hfun f σ).aestronglyMeasurable (μ := volume)
  have hi : Integrable (hfun f σ) :=
    (integrable_G1 hδ).mono' hm (Eventually.of_forall fun u => (hb u).1)
  have hsq : Integrable (fun u => ‖hfun f σ u‖ ^ 2) :=
    (integrable_G2 hδ).mono' (hm.norm.pow 2) (Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (by positivity)]; exact (hb u).2)
  refine ⟨hi, (memLp_two_iff_integrable_sq_norm hm).2 hsq, ?_⟩
  rw [← integral_G2 hδ (Real.log_nonneg hX0)]
  exact integral_mono hsq (integrable_G2 hδ) fun u => (hb u).2

end RamanujanTau.TauOmegaPartial
