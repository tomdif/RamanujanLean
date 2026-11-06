/-
# Two-sided bounds `∫ |L(Δ,σ−2πiξ)/(σ−2πiξ)|² dξ ≍ 1/(σ − 23/4)`

For `σ = 23/4 + δ`, `0 < δ ≤ 1/16`:

* `Phi_upper`: `∫ |F_σ|² ≤ C/δ` (`Tail.tail_bound` on `y = 1/4 − δ`, plus a compact piece);
* `Phi_lower`: `∫ |F_σ|² ≥ K/δ` (dyadic blocks `TauOmegaPartial.block_lower`).
-/
import RamanujanTau.Voronoi.MeanSq

set_option autoImplicit false

namespace RamanujanTau.Voronoi

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.HeckeL RamanujanTau.HeckeConvexGeneral RamanujanTau.TauOmegaPartial
open scoped ComplexConjugate Real MatrixGroups Interval

lemma norm_Fs_sq (σ ξ : ℝ) : ‖Fs Dl σ ξ‖ ^ 2 = Psi σ (-(2 * π * ξ)) := by
  rw [Fs_eq]
  unfold Psi Gt
  congr 3 <;> push_cast <;> ring_nf

lemma integrable_Fs_sq {σ : ℝ} (hi : Integrable (Psi σ)) :
    Integrable fun ξ : ℝ => ‖Fs Dl σ ξ‖ ^ 2 := by
  simp_rw [norm_Fs_sq]
  exact hi.comp_neg.comp_mul_left' (by positivity : (2 * π : ℝ) ≠ 0)

lemma integral_Fs_sq (σ : ℝ) :
    ∫ ξ : ℝ, ‖Fs Dl σ ξ‖ ^ 2 = (2 * π)⁻¹ * ∫ u : ℝ, Psi σ u := by
  simp_rw [norm_Fs_sq]
  rw [Measure.integral_comp_mul_left (fun z => Psi σ (-z)) (2 * π), integral_neg_eq_self,
    abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹), smul_eq_mul]

lemma one_sub_two_rpow_ge {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16) :
    δ ≤ 1 - (2 : ℝ) ^ (-(4 * δ)) := by
  have hl : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have h1 : 1 + 2 * δ ≤ (2 : ℝ) ^ (4 * δ) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have := Real.add_one_le_exp (Real.log 2 * (4 * δ))
    nlinarith
  have h2 : (2 : ℝ) ^ (-(4 * δ)) ≤ 1 / (1 + 2 * δ) := by
    rw [Real.rpow_neg (by norm_num), ← one_div]
    exact one_div_le_one_div_of_le (by linarith) h1
  have h3 : 1 / (1 + 2 * δ) ≤ 1 - δ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- A uniform bound for `Ψ` on `[23/4, 6] × [−1, 1]`. -/
lemma Psi_compact_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ σ ∈ Icc (23 / 4 : ℝ) 6, ∀ u ∈ Icc (-1 : ℝ) 1,
    Psi σ u ≤ M := by
  have hK : IsCompact (Icc (23 / 4 : ℝ) 6 ×ˢ Icc (-1 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hc : ContinuousOn (fun p : ℝ × ℝ => Psi p.1 p.2) (Icc (23 / 4 : ℝ) 6 ×ˢ Icc (-1 : ℝ) 1) := by
    unfold Psi
    refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
    refine ContinuousOn.div (tauLSeries_entire.continuous.comp (by fun_prop)).continuousOn
      (by fun_prop) fun p hp => ne_zero_of_re_pos (by linarith [hp.1.1]) p.2
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max M 0, le_max_right _ _, fun σ hσ u hu => ?_⟩
  have h := hM (σ, u) ⟨hσ, hu⟩
  rw [Real.norm_of_nonneg (Psi_nonneg _ _)] at h
  exact h.trans (le_max_left _ _)

/-- **Upper bound** `∫ |F_σ|² ≤ C/δ`. -/
theorem Phi_upper : ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 16 →
    Integrable (fun ξ : ℝ => ‖Fs Dl (23 / 4 + δ) ξ‖ ^ 2) ∧
    ∫ ξ : ℝ, ‖Fs Dl (23 / 4 + δ) ξ‖ ^ 2 ≤ C / δ := by
  obtain ⟨K, hK0, hK⟩ := tail_bound
  obtain ⟨M, hM0, hM⟩ := Psi_compact_bound
  refine ⟨(2 * π)⁻¹ * (M / 8 + 2 * (16 * K / 3)), by positivity, fun δ hδ0 hδ1 => ?_⟩
  set y : ℝ := 1 / 4 - δ with hy
  have hσ : (23 / 4 + δ : ℝ) = 6 - y := by rw [hy]; ring
  have hy0 : 0 < y := by rw [hy]; linarith
  have hy1 : y < 1 / 4 := by rw [hy]; linarith
  have hy316 : 3 / 16 ≤ y := by rw [hy]; linarith
  obtain ⟨hint, hbd⟩ := hK y hy0 hy1 1 le_rfl
  rw [← hσ] at hint hbd
  have hsp := even_split (continuous_Psi (by linarith)) (Psi_neg _) zero_le_one hint
  refine ⟨integrable_Fs_sq hsp.1, ?_⟩
  rw [integral_Fs_sq, hsp.2.2]
  have hp : 1 - 4 * y = 4 * δ := by rw [hy]; ring
  rw [hp, Real.one_rpow, mul_one] at hbd
  have hden := one_sub_two_rpow_ge hδ0 hδ1
  have htail : ∫ u in Ioi (1 : ℝ), Psi (23 / 4 + δ) u ≤ (16 * K / 3) / δ := by
    refine hbd.trans ?_
    have hKy : K / y ≤ 16 * K / 3 := by
      rw [div_le_iff₀ hy0]; nlinarith
    calc K / y / (1 - 2 ^ (-(4 * δ))) ≤ (16 * K / 3) / (1 - 2 ^ (-(4 * δ))) := by
          gcongr; linarith
      _ ≤ (16 * K / 3) / δ := div_le_div_of_nonneg_left (by positivity) hδ0 hden
  have hcomp : ∫ u in Icc (-1 : ℝ) 1, Psi (23 / 4 + δ) u ≤ M / 8 / δ := by
    have h1 : ∫ u in Icc (-1 : ℝ) 1, Psi (23 / 4 + δ) u ≤ ∫ u in Icc (-1 : ℝ) 1, M :=
      setIntegral_mono_on (continuous_Psi (by linarith)).integrableOn_Icc
        (integrableOn_const (by simp)) measurableSet_Icc fun u hu =>
          hM _ ⟨by linarith, by linarith⟩ u hu
    rw [setIntegral_const, Real.volume_real_Icc] at h1
    norm_num at h1
    have h2 : 2 * M ≤ M / 8 / δ := by
      rw [le_div_iff₀ hδ0]; nlinarith
    linarith
  have h2pi : 0 < (2 * π)⁻¹ := by positivity
  calc (2 * π)⁻¹ * ((∫ u in Icc (-1 : ℝ) 1, Psi (23 / 4 + δ) u) +
        2 * ∫ u in Ioi (1 : ℝ), Psi (23 / 4 + δ) u)
      ≤ (2 * π)⁻¹ * (M / 8 / δ + 2 * ((16 * K / 3) / δ)) := by gcongr
    _ = (2 * π)⁻¹ * (M / 8 + 2 * (16 * K / 3)) / δ := by ring

/-- **Lower bound** `∫ |F_σ|² ≥ K/δ` (dyadic blocks). -/
theorem Phi_lower : ∃ K2 : ℝ, 0 < K2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 16 →
    K2 / (4 * δ) ≤ ∫ ξ : ℝ, ‖Fs Dl (23 / 4 + δ) ξ‖ ^ 2 := by
  obtain ⟨m, hm, hlow, hm0⟩ := exists_first_coef Dl
    RamanujanTau.HardyZerosGeneral.discriminant_ne_zero' (by norm_num)
  obtain ⟨K1, hK1, Ξ0, hΞ0, hblock⟩ := block_lower Dl (by norm_num) hm hlow hm0
  obtain ⟨C, _, hC⟩ := Phi_upper
  set K2 : ℝ := K1 / (4 * Ξ0) with hK2
  have hK20 : 0 < K2 := by positivity
  refine ⟨K2, hK20, fun δ hδ0 hδ1 => ?_⟩
  have hσe : (((12 : ℕ) : ℝ) - 1) / 2 + 1 / 4 + δ = 23 / 4 + δ := by norm_num
  set σ : ℝ := 23 / 4 + δ with hσ
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  have hFi : Integrable (fun ξ => ‖Fs Dl σ ξ‖ ^ 2) := (hC δ hδ0 hδ1).1
  have hFc := continuous_Fs Dl (by norm_num) hσ0
  set J : ℕ := ⌈1 / (4 * δ)⌉₊ with hJ
  set a : ℕ → ℝ := fun j => 2 ^ j * Ξ0 with ha
  have hsum : ∑ j ∈ Finset.range J, ∫ ξ in a j..a (j + 1), ‖Fs Dl σ ξ‖ ^ 2 =
      ∫ ξ in a 0..a J, ‖Fs Dl σ ξ‖ ^ 2 :=
    intervalIntegral.sum_integral_adjacent_intervals fun j _ =>
      (hFc.norm.pow 2).intervalIntegrable _ _
  have hle : ∫ ξ in a 0..a J, ‖Fs Dl σ ξ‖ ^ 2 ≤ ∫ ξ, ‖Fs Dl σ ξ‖ ^ 2 := by
    have h0J : a 0 ≤ a J := by
      simp only [ha, pow_zero, one_mul]
      exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
    rw [intervalIntegral.integral_of_le h0J]
    exact setIntegral_le_integral hFi (Eventually.of_forall fun _ => by positivity)
  have hblocks : ∀ j ∈ Finset.range J, K2 ≤ ∫ ξ in a j..a (j + 1), ‖Fs Dl σ ξ‖ ^ 2 := by
    intro j hj
    have hjJ : j < J := Finset.mem_range.1 hj
    have haj : Ξ0 ≤ a j := by
      simp only [ha]; exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
    have hb := hblock δ hδ0 hδ1 (a j) haj
    rw [hσe] at hb
    have hnext : a (j + 1) = 2 * a j := by simp only [ha]; rw [pow_succ]; ring
    rw [hnext]
    have hw := dyadic_weight hΞ0 hδ0 hδ1 hjJ
    have : K2 ≤ K1 * (2 * a j) ^ (-(4 * δ)) := by
      rw [hK2, div_eq_mul_one_div]
      simp only [ha]
      exact mul_le_mul_of_nonneg_left hw hK1.le
    exact this.trans hb
  have hlow' : (J : ℝ) * K2 ≤ ∫ ξ, ‖Fs Dl σ ξ‖ ^ 2 := by
    have := Finset.sum_le_sum hblocks
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsum] at this
    exact this.trans hle
  have hJge : 1 / (4 * δ) ≤ (J : ℝ) := Nat.le_ceil _
  have : K2 / (4 * δ) ≤ (J : ℝ) * K2 := by
    rw [div_eq_mul_one_div, mul_comm]; exact mul_le_mul_of_nonneg_right hJge hK20.le
  linarith

end RamanujanTau.Voronoi
