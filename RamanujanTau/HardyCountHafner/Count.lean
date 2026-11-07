/-
# From a mean-square bound to many zeros, with an exceptional set

As `HardyCountLinear.many_zeros_of_mean_sq`, but the window lower bound `A ≤ |I(t₀)|` is only
required off an exceptional set `E` with `|E ∩ [T,2T]| ≤ T/4` (the centres where the averaged
horizontal contour sides are large), and the mean square is `≤ A² T/4`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.HardyCountHafner

open MeasureTheory Set Filter

theorem many_zeros_of_mean_sq_exc {Z I : ℝ → ℝ} (hI : Continuous I) {T R A : ℝ} {E : Set ℝ}
    (hT : 0 < T) (hR : 0 < R) (hE : volume.real (E ∩ Icc T (2 * T)) ≤ T / 4)
    (hlow : ∀ t₀ ∈ Icc T (2 * T), t₀ ∉ E → (∀ t ∈ Icc (t₀ - R) (t₀ + R), Z t ≠ 0) →
      A ≤ |I t₀|)
    (hmean : ∫ t₀ in Icc T (2 * T), I t₀ ^ 2 ≤ A ^ 2 * T / 4) (hA : 0 < A) :
    ∃ S : Finset ℝ, (∀ γ ∈ S, γ ∈ Icc (T - R) (2 * T + R) ∧ Z γ = 0) ∧
      T / (4 * R) ≤ S.card := by
  classical
  set Z₀ : Set ℝ := {γ | γ ∈ Icc (T - R) (2 * T + R) ∧ Z γ = 0} with hZ₀
  by_cases hfin : Z₀.Finite
  swap
  · obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hfin ⌈T / (4 * R)⌉₊
    refine ⟨S, fun γ hγ => hS hγ, ?_⟩
    rw [hcard]; exact Nat.le_ceil _
  set S := hfin.toFinset with hSdef
  refine ⟨S, fun γ hγ => (hfin.mem_toFinset).mp hγ, ?_⟩
  set U : Set ℝ := ⋃ γ ∈ S, Icc (γ - R) (γ + R) with hU
  set B : Set ℝ := {t₀ | A ^ 2 ≤ I t₀ ^ 2} ∩ Icc T (2 * T) with hB
  have hcover : Icc T (2 * T) ⊆ U ∪ B ∪ (E ∩ Icc T (2 * T)) := by
    intro t₀ ht₀
    by_cases hE' : t₀ ∈ E
    · right; exact ⟨hE', ht₀⟩
    left
    by_cases hz : ∃ t ∈ Icc (t₀ - R) (t₀ + R), Z t = 0
    · obtain ⟨t, ht, hzt⟩ := hz
      left
      have hmem : t ∈ S := by
        rw [hSdef, hfin.mem_toFinset]
        exact ⟨⟨by linarith [ht.1, ht₀.1], by linarith [ht.2, ht₀.2]⟩, hzt⟩
      simp only [hU, mem_iUnion]
      exact ⟨t, hmem, by linarith [ht.2], by linarith [ht.1]⟩
    · push Not at hz
      right
      refine ⟨?_, ht₀⟩
      have := hlow t₀ ht₀ hE' hz
      show A ^ 2 ≤ I t₀ ^ 2
      have h0 : 0 ≤ A := hA.le
      rw [← sq_abs (I t₀)]
      exact pow_le_pow_left₀ h0 this 2
  have hbig : U ∪ B ⊆ Icc (T - 2 * R) (2 * T + 2 * R) := by
    intro x hx
    rcases hx with hx | hx
    · simp only [hU, mem_iUnion] at hx
      obtain ⟨γ, hγ, hx⟩ := hx
      have := (hfin.mem_toFinset).mp hγ
      exact ⟨by linarith [this.1.1, hx.1], by linarith [this.1.2, hx.2]⟩
    · exact ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
  have hbig' : U ∪ B ∪ (E ∩ Icc T (2 * T)) ⊆ Icc (T - 2 * R) (2 * T + 2 * R) := by
    refine union_subset hbig ?_
    intro x hx
    exact ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
  have hfinU : volume (U ∪ B ∪ (E ∩ Icc T (2 * T))) ≠ ⊤ :=
    (measure_mono hbig').trans_lt measure_Icc_lt_top |>.ne
  have h1 : T ≤ volume.real (U ∪ B ∪ (E ∩ Icc T (2 * T))) := by
    have := measureReal_mono (μ := volume) hcover hfinU
    rw [Real.volume_real_Icc_of_le (by linarith)] at this
    linarith
  have h2 : volume.real (U ∪ B ∪ (E ∩ Icc T (2 * T))) ≤
      volume.real U + volume.real B + volume.real (E ∩ Icc T (2 * T)) := by
    refine (measureReal_union_le _ _).trans ?_
    linarith [measureReal_union_le (μ := volume) U B]
  have h3 : volume.real U ≤ S.card * (2 * R) := by
    refine (measureReal_biUnion_finset_le S _).trans ?_
    rw [Finset.sum_congr rfl fun γ _ => Real.volume_real_Icc_of_le (by linarith)]
    rw [Finset.sum_congr rfl fun γ _ => (show γ + R - (γ - R) = 2 * R by ring),
      Finset.sum_const, nsmul_eq_mul]
  -- Chebyshev
  have h4 : volume.real B ≤ T / 4 := by
    have hint : Integrable (fun t₀ => I t₀ ^ 2) (volume.restrict (Icc T (2 * T))) :=
      (hI.pow 2).integrableOn_Icc
    have hcheb := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Icc T (2 * T)))
      (Eventually.of_forall fun t₀ => sq_nonneg (I t₀)) hint (A ^ 2)
    have hmeas : MeasurableSet {t₀ | A ^ 2 ≤ I t₀ ^ 2} :=
      measurableSet_le measurable_const (hI.pow 2).measurable
    rw [measureReal_restrict_apply hmeas] at hcheb
    have hA2 : 0 < A ^ 2 := by positivity
    have := hcheb.trans hmean
    have h5 : A ^ 2 * volume.real B ≤ A ^ 2 * (T / 4) := by
      rw [hB]; linarith
    exact le_of_mul_le_mul_left h5 hA2
  have hS : T ≤ S.card * (2 * R) + T / 2 := by linarith
  rw [div_le_iff₀ (by positivity)]
  linarith

end RamanujanTau.HardyCountHafner
