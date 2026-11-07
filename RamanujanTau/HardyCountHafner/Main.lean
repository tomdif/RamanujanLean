/-
# Hafner's theorem for `L(Δ,s)`: `N₀(T) ≫ T`

See `docs/HARDY_COUNT_HAFNER.md`.

Fix `σ₁ ≥ 7` with `|L(σ₁+iy) − 1| ≤ 1/4`, a large constant `r`, `α = π/2 − 1/T` and
`Iw(t₀) = ∫ Z(t) e^{αt} tri_{2r}(t − t₀) dt` (as in `HardyCountLinear`).

* upper (`HardyCountLinear.mean_sq_Iw`): `∫_T^{2T} Iw² ≤ 4 S² (2r)³`, `S ≪ T⁶`;
* exceptional set `E = {t₀ : F(t₀ ± r) ≥ r/4}`, `F(c) = ∫_6^{σ₁}|L(σ+ic)|dσ`: by
  `Horizontal.horizontal_mean` (`∫_T^{2T} F ≪ T`, from the uniform mean square) and Chebyshev,
  `|E ∩ [T,2T]| ≤ 32 C T / r ≤ T/4`;
* lower, off `E` (`Window.window_lower` + `HardyCountLinear.Iw_lower`): if `Z` has no zero
  within `2r` of `t₀ ∉ E` then `|Iw(t₀)| ≥ A = r e^{−3} c_Z (T/2)^{11/2} · r`;
* `4 S² (2r)³ ≤ A² T/4` once `r ≥ 256 π¹⁴ M² e⁶ / c_Z²`: `r` is a constant;
* `Count.many_zeros_of_mean_sq_exc`: `≥ T/(8r)` zeros of `Z` in `(0, 3T]`.
-/
import RamanujanTau.HardyCountHafner.Window
import RamanujanTau.HardyCountHafner.Count
import RamanujanTau.HardyCountLinear.Main

set_option autoImplicit false

namespace RamanujanTau.HardyCountHafner

open Complex MeasureTheory Set Filter
open RamanujanTau.HeckeL RamanujanTau.HardyZeros RamanujanTau.HardyCount
  RamanujanTau.HardyCountLinear
open scoped Real

/-- Chebyshev on `[T, 2T]`. -/
lemma vol_ge_le {G : ℝ → ℝ} (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t) {T l B : ℝ}
    (hl : 0 < l) (hB : ∫ t in Icc T (2 * T), G t ≤ B) :
    volume.real ({t | l ≤ G t} ∩ Icc T (2 * T)) ≤ B / l := by
  have hint : Integrable G (volume.restrict (Icc T (2 * T))) := hG.integrableOn_Icc
  have hcheb := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Icc T (2 * T)))
    (Eventually.of_forall hG0) hint l
  have hmeas : MeasurableSet {t | l ≤ G t} := measurableSet_le measurable_const hG.measurable
  rw [measureReal_restrict_apply hmeas] at hcheb
  rw [le_div_iff₀ hl]
  linarith

lemma Icc_eq_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Icc a b, f t = ∫ t in a..b, f t := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- The shifted horizontal mean: `∫_T^{2T} F(t ± r) dt ≤ 4 C T` for `r ≤ T/2`. -/
lemma integral_shift_le {σ₁ C : ℝ} (h7 : 7 ≤ σ₁) (hC0 : 0 ≤ C)
    (hC : ∀ S : ℝ, 1 ≤ S → ∫ t in Icc S (2 * S), Fh σ₁ t ≤ C * S) {T s : ℝ} (hT : 2 ≤ T)
    (hs : |s| ≤ T / 2) :
    ∫ t in Icc T (2 * T), Fh σ₁ (t + s) ≤ 4 * C * T := by
  have hFc := continuous_Fh σ₁
  have hF0 := Fh_nonneg (σ₁ := σ₁) (by linarith)
  have hS : ∀ S : ℝ, 1 ≤ S → ∫ t in S..2 * S, Fh σ₁ t ≤ C * S := by
    intro S hS1
    rw [← Icc_eq_interval (by linarith)]; exact hC S hS1
  have hs1 := neg_abs_le s
  have hs2 := le_abs_self s
  rw [Icc_eq_interval (by linarith), intervalIntegral.integral_comp_add_right (fun t => Fh σ₁ t)]
  have hmono : ∫ t in (T + s)..(2 * T + s), Fh σ₁ t ≤ ∫ t in (T / 2)..(4 * T), Fh σ₁ t :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Eventually.of_forall fun t => hF0 t) (hFc.intervalIntegrable _ _)
  refine hmono.trans ?_
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := T) (hFc.intervalIntegrable _ _)
      (hFc.intervalIntegrable _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := T) (b := 2 * T)
      (hFc.intervalIntegrable _ _) (hFc.intervalIntegrable _ _)]
  have h1 := hS (T / 2) (by linarith)
  have h2 := hS T (by linarith)
  have h3 := hS (2 * T) (by linarith)
  rw [show 2 * (T / 2) = T by ring] at h1
  rw [show 2 * (2 * T) = 4 * T by ring] at h3
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Core count**: `≥ T/(8r)` zeros of `Z` in `(0, 3T]`, with `r` a constant. -/
theorem core_count_linear : ∃ r T₀ : ℝ, 0 < r ∧ 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
    (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ Zr γ = 0) ∧ T / (8 * r) ≤ S.card := by
  obtain ⟨σ₁, h7, hρ⟩ := norm_tauL_sub_one_le (ρ := 1 / 4) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := horizontal_mean h7
  obtain ⟨M, hM0, hmean⟩ := mean_sq_Iw
  have hcZ := cZ_pos
  set D : ℝ := 256 * π ^ 14 * M ^ 2 * Real.exp 6 / cZ ^ 2 with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  set r : ℝ := D + 128 * C + 1 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hDr : D ≤ r := by rw [hrdef]; linarith
  have hCr : 128 * C ≤ r := by rw [hrdef]; linarith
  refine ⟨r, max 2 (4 * r), hrpos, (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _),
    fun T hT => ?_⟩
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hT4r : 4 * r ≤ T := (le_max_right _ _).trans hT
  have hT1 : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  -- the moments
  set α : ℝ := π / 2 - 1 / T with hα
  have hinv : 1 / T ≤ 1 := by rw [div_le_one hTpos]; exact hT1
  have hinvpos : 0 < 1 / T := by positivity
  have hα0 : 0 ≤ α := by rw [hα]; linarith [Real.pi_gt_three]
  have hαπ : α < π / 2 := by rw [hα]; linarith
  obtain ⟨hIc, hIm⟩ := hmean α hα0 hαπ (2 * r) (by positivity)
  set P : ℝ := (T / 2) ^ (11 / 2 : ℝ) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos (by linarith) _
  set A : ℝ := r * Real.exp (-3) * cZ * P * r with hA
  have hApos : 0 < A := by rw [hA]; positivity
  -- the exceptional set
  set E : Set ℝ := {t | r / 4 ≤ Fh σ₁ (t + -r)} ∪ {t | r / 4 ≤ Fh σ₁ (t + r)} with hE
  have hFc := continuous_Fh σ₁
  have hF0 := Fh_nonneg (σ₁ := σ₁) (by linarith)
  have hEvol : volume.real (E ∩ Icc T (2 * T)) ≤ T / 4 := by
    have hs1 : |(-r)| ≤ T / 2 := by rw [abs_neg, abs_of_pos hrpos]; linarith
    have hs2 : |r| ≤ T / 2 := by rw [abs_of_pos hrpos]; linarith
    have hv1 := vol_ge_le (G := fun t => Fh σ₁ (t + -r)) (hFc.comp (by fun_prop))
      (fun t => hF0 _) (l := r / 4) (by positivity) (integral_shift_le h7 hC0 hC hT2 hs1)
    have hv2 := vol_ge_le (G := fun t => Fh σ₁ (t + r)) (hFc.comp (by fun_prop))
      (fun t => hF0 _) (l := r / 4) (by positivity) (integral_shift_le h7 hC0 hC hT2 hs2)
    rw [hE, union_inter_distrib_right]
    refine (measureReal_union_le _ _).trans ?_
    have hb : 4 * C * T / (r / 4) ≤ T / 8 := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hCr hTpos.le
      nlinarith
    linarith
  -- the lower bound off `E`
  have hlow : ∀ t₀ ∈ Icc T (2 * T), t₀ ∉ E →
      (∀ t ∈ Icc (t₀ - 2 * r) (t₀ + 2 * r), Zr t ≠ 0) → A ≤ |Iw α (2 * r) t₀| := by
    intro t₀ ht₀ hnE hno
    have hn1 : Fh σ₁ (t₀ - r) ≤ ((t₀ + r) - (t₀ - r)) / 8 := by
      have : ¬ (r / 4 ≤ Fh σ₁ (t₀ + -r)) := fun h => hnE (Or.inl h)
      rw [← sub_eq_add_neg] at this
      push Not at this
      linarith
    have hn2 : Fh σ₁ (t₀ + r) ≤ ((t₀ + r) - (t₀ - r)) / 8 := by
      have : ¬ (r / 4 ≤ Fh σ₁ (t₀ + r)) := fun h => hnE (Or.inr h)
      push Not at this
      linarith
    have hw := window_lower h7 hρ (by linarith) hn1 hn2
    have hl := Iw_lower hT1 ht₀.1 ht₀.2 hrpos (by linarith) hno
    have hc : 0 ≤ r * Real.exp (-3) * cZ * P := by positivity
    calc A = r * Real.exp (-3) * cZ * P * (((t₀ + r) - (t₀ - r)) / 2) := by rw [hA]; ring
      _ ≤ r * Real.exp (-3) * cZ * P * ∫ t in (t₀ - r)..(t₀ + r), ‖tauL (6 + t * I)‖ :=
        mul_le_mul_of_nonneg_left hw hc
      _ ≤ |Iw α (2 * r) t₀| := hl
  -- the mean-square comparison
  have hm : ∫ t₀ in Icc T (2 * T), Iw α (2 * r) t₀ ^ 2 ≤ A ^ 2 * T / 4 := by
    refine (hIm T hTpos).trans ?_
    have hS : 2 * π * M / Real.cos α ^ 6 ≤ 2 * π * M * (π * T / 2) ^ 6 := by
      have := inv_cos_pow_le hT1
      rw [← hα] at this
      calc 2 * π * M / Real.cos α ^ 6 = 2 * π * M * (1 / Real.cos α ^ 6) := by ring
        _ ≤ _ := by gcongr
    have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαπ⟩
    have hS0 : 0 ≤ 2 * π * M / Real.cos α ^ 6 := by positivity
    have hP2 : P ^ 2 = (T / 2) ^ 11 := by
      rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    have hDe : D * Real.exp (-6) * cZ ^ 2 = 256 * π ^ 14 * M ^ 2 := by
      rw [hD]
      have hE6 : Real.exp 6 * Real.exp (-6) = 1 := by rw [← Real.exp_add]; simp
      field_simp
      rw [mul_assoc, hE6]; ring
    have hkey : 256 * π ^ 14 * M ^ 2 ≤ r * Real.exp (-6) * cZ ^ 2 := by
      rw [← hDe]; gcongr
    have hAeq : A ^ 2 * T / 4 = (r * Real.exp (-6) * cZ ^ 2) * (r ^ 3 * (T / 2) ^ 12) / 2 := by
      have hE : Real.exp (-3) ^ 2 = Real.exp (-6) := by
        rw [← Real.exp_nat_mul]; norm_num
      have h12 : (T / 2) ^ 12 = P ^ 2 * (T / 2) := by rw [hP2]; ring
      clear_value A P r
      rw [h12, ← hE, hA]; ring
    have hT12 : 0 ≤ r ^ 3 * (T / 2) ^ 12 := by positivity
    calc 4 * (2 * π * M / Real.cos α ^ 6) ^ 2 * (2 * r) ^ 3
        ≤ 4 * (2 * π * M * (π * T / 2) ^ 6) ^ 2 * (2 * r) ^ 3 := by gcongr
      _ = (256 * π ^ 14 * M ^ 2) * (r ^ 3 * (T / 2) ^ 12) / 2 := by ring
      _ ≤ (r * Real.exp (-6) * cZ ^ 2) * (r ^ 3 * (T / 2) ^ 12) / 2 := by gcongr
      _ = A ^ 2 * T / 4 := hAeq.symm
  obtain ⟨S, hS, hcard⟩ := many_zeros_of_mean_sq_exc (Z := Zr) hIc hTpos
    (by positivity : 0 < 2 * r) hEvol hlow hm hApos
  refine ⟨S, fun γ hγ => ?_, ?_⟩
  · obtain ⟨hγI, hz⟩ := hS γ hγ
    exact ⟨by linarith [hγI.1], by linarith [hγI.2], hz⟩
  · calc T / (8 * r) = T / (4 * (2 * r)) := by ring_nf
      _ ≤ S.card := hcard

/-- **Hafner's theorem for `L(Δ,s)`: `N₀(T) ≫ T`.**  There are `≫ T` distinct `t ∈ (0, T]` with
`L(Δ, 6+it) = 0`. -/
theorem tauL_critical_zeros_linear : ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
    (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ tauL (6 + t * I) = 0) ∧ c * T ≤ S.card := by
  obtain ⟨r, T₀, hr, hT₀1, hcore⟩ := core_count_linear
  refine ⟨1 / (24 * r), 3 * T₀, by positivity, fun T hT => ?_⟩
  obtain ⟨S, hS, hcard⟩ := hcore (T / 3) (by linarith)
  refine ⟨S, fun t ht => ?_, ?_⟩
  · obtain ⟨h0, h1, hz⟩ := hS t ht
    exact ⟨h0, by linarith, tauL_zero_of_Zr_zero hz⟩
  · calc 1 / (24 * r) * T = T / 3 / (8 * r) := by field_simp; ring
      _ ≤ S.card := hcard

/-- The same count for the completed `Λ(Δ, 6+it)`. -/
theorem heckeLambda_critical_zeros_linear : ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T →
    ∃ S : Finset ℝ, (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ heckeLambda (6 + t * I) = 0) ∧ c * T ≤ S.card := by
  obtain ⟨c, T₀, hc, h⟩ := tauL_critical_zeros_linear
  refine ⟨c, T₀, hc, fun T hT => ?_⟩
  obtain ⟨S, hS, hcard⟩ := h T hT
  refine ⟨S, fun t ht => ?_, hcard⟩
  obtain ⟨h0, h1, hz⟩ := hS t ht
  refine ⟨h0, h1, ?_⟩
  have hs : ∀ n : ℕ, (6 + t * I : ℂ) ≠ -n :=
    RamanujanTau.HeckeZeros.ne_neg_nat_of_re_pos (by simp)
  rw [heckeLambda_eq_tauL hs, hz, mul_zero]

end RamanujanTau.HardyCountHafner

#print axioms RamanujanTau.HardyCountHafner.tauL_critical_zeros_linear
#print axioms RamanujanTau.HardyCountHafner.heckeLambda_critical_zeros_linear
#print axioms RamanujanTau.HardyCountHafner.core_count_linear
#print axioms RamanujanTau.HardyCountHafner.mean_square_uniform
#print axioms RamanujanTau.HardyCountHafner.horizontal_mean
#print axioms RamanujanTau.HardyCountHafner.window_lower
#print axioms RamanujanTau.HardyCountHafner.many_zeros_of_mean_sq_exc
#print axioms RamanujanTau.HardyCountHafner.Fs_eq_fI
#print axioms RamanujanTau.HardyCountHafner.integral_tri_norm_fI_sq_le_gen
