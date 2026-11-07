/-
# Logarithmic averages of a function with a limit at `0⁺`

If `0 ≤ h ≤ H₀` on `(0,∞)` and `h(y) → c₀` as `y → 0⁺`, then

    (∑_{N ≤ ⌊1/κ⌋} h(κN)/N) / log(1/κ) → c₀      (κ → 0⁺).

Proof: the terms with `κN ≤ η` are within `ε` of `c₀` and contribute `(c₀ ± ε)·H_m` with
`H_m = log(1/κ) + O_η(1)`; the remaining terms `η < κN ≤ 1` contribute `≤ H₀ (1 + log(1/η))`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquareAsymp

open Filter Topology Set

lemma sum_range_inv_eq_harmonic (m : ℕ) :
    ∑ j ∈ Finset.range m, (1 : ℝ) / ((j : ℝ) + 1) = (harmonic m : ℝ) := by
  simp only [harmonic]
  push_cast
  simp [one_div]

lemma harmonic_lower (m : ℕ) : Real.log ((m : ℝ) + 1) ≤ (harmonic m : ℝ) := by
  have := log_add_one_le_harmonic m
  push_cast at this
  exact this

lemma harmonic_upper (m : ℕ) : (harmonic m : ℝ) ≤ 1 + Real.log m := harmonic_le_one_add_log m

/-- The core two-sided estimate. -/
lemma harm_sandwich {h : ℝ → ℝ} {c₀ H₀ ε η : ℝ}
    (h0 : ∀ y, 0 < y → 0 ≤ h y) (hH : ∀ y, 0 < y → h y ≤ H₀)
    (hε : 0 < ε) (hη0 : 0 < η) (hη1 : η < 1)
    (hη : ∀ y, 0 < y → y ≤ η → |h y - c₀| ≤ ε) {κ : ℝ} (hκ : 0 < κ) (hκη : κ < η) :
    |(∑ j ∈ Finset.range ⌊1 / κ⌋₊, h (κ * ((j : ℝ) + 1)) / ((j : ℝ) + 1)) -
        c₀ * Real.log (1 / κ)| ≤
      ε * Real.log (1 / κ) + (|c₀| + ε + H₀) * (1 - Real.log η) := by
  set L := Real.log (1 / κ) with hL
  set n := ⌊1 / κ⌋₊ with hn
  set m := ⌊η / κ⌋₊ with hm
  have hκ1 : κ < 1 := hκη.trans hη1
  have hL0 : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hκ]; linarith)
  have hlogη : Real.log η < 0 := Real.log_neg hη0 hη1
  have hH0 : 0 ≤ H₀ := (h0 1 one_pos).trans (hH 1 one_pos)
  have hmn : m ≤ n := Nat.floor_mono (div_le_div_of_nonneg_right hη1.le hκ.le)
  have hm_le : (m : ℝ) ≤ η / κ := Nat.floor_le (by positivity)
  have hm_gt : η / κ < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hn_le : (n : ℝ) ≤ 1 / κ := Nat.floor_le (by positivity)
  have hn1 : 1 ≤ n := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hκ]; linarith)
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  -- harmonic numbers
  set Hm := (harmonic m : ℝ)
  set Hn := (harmonic n : ℝ)
  have hlogm : Real.log (η / κ) = L + Real.log η := by
    rw [hL, Real.log_div hη0.ne' hκ.ne', one_div, Real.log_inv]; ring
  have hHm_lo : L + Real.log η ≤ Hm := by
    rw [← hlogm]
    exact (Real.log_le_log (by positivity) hm_gt.le).trans (harmonic_lower m)
  have hHn_hi : Hn ≤ 1 + L := by
    refine (harmonic_upper n).trans ?_
    have := Real.log_le_log (by linarith) hn_le
    linarith
  have hHm_eq : Hm = ∑ j ∈ Finset.range m, (1 : ℝ) / ((j : ℝ) + 1) :=
    (sum_range_inv_eq_harmonic m).symm
  have hHn_eq : Hn = ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) :=
    (sum_range_inv_eq_harmonic n).symm
  have hIco : Hn - Hm = ∑ j ∈ Finset.Ico m n, (1 : ℝ) / ((j : ℝ) + 1) := by
    rw [hHm_eq, hHn_eq, ← Finset.sum_range_add_sum_Ico _ hmn]; ring
  have hHmn : Hm ≤ Hn := by
    have : 0 ≤ ∑ j ∈ Finset.Ico m n, (1 : ℝ) / ((j : ℝ) + 1) :=
      Finset.sum_nonneg fun j _ => by positivity
    linarith
  -- split the sum
  set f : ℕ → ℝ := fun j => h (κ * ((j : ℝ) + 1)) / ((j : ℝ) + 1)
  have hsplit := Finset.sum_range_add_sum_Ico f hmn
  have hf0 : ∀ j : ℕ, 0 ≤ f j := fun j => div_nonneg (h0 _ (by positivity)) (by positivity)
  -- the first part
  have hfirst : ∀ j ∈ Finset.range m, |f j - c₀ * (1 / ((j : ℝ) + 1))| ≤ ε * (1 / ((j : ℝ) + 1)) := by
    intro j hj
    have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast Finset.mem_range.1 hj
    have hy : κ * ((j : ℝ) + 1) ≤ η := by
      calc κ * ((j : ℝ) + 1) ≤ κ * (η / κ) := by gcongr; linarith
        _ = η := by field_simp
    have := hη _ (by positivity) hy
    have e : f j - c₀ * (1 / ((j : ℝ) + 1)) = (h (κ * ((j : ℝ) + 1)) - c₀) * (1 / ((j : ℝ) + 1)) := by
      simp only [f]; ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1))]
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hS1 : |(∑ j ∈ Finset.range m, f j) - c₀ * Hm| ≤ ε * Hm := by
    rw [hHm_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hfirst)
  have hS2 : 0 ≤ ∑ j ∈ Finset.Ico m n, f j ∧ ∑ j ∈ Finset.Ico m n, f j ≤ H₀ * (Hn - Hm) := by
    refine ⟨Finset.sum_nonneg fun j _ => hf0 j, ?_⟩
    rw [hIco, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [f]
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (hH _ (by positivity)) (by positivity)
  have hHm_hi : Hm ≤ 1 + L := hHmn.trans hHn_hi
  have hHm0 : 0 ≤ Hm := by
    have := harmonic_lower m
    have : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
    linarith
  -- |Hm - L| ≤ 1 - log η
  have hr : |Hm - L| ≤ 1 - Real.log η := by
    rw [abs_le]; constructor <;> linarith
  rw [← hsplit]
  set S1 := ∑ j ∈ Finset.range m, f j
  set S2 := ∑ j ∈ Finset.Ico m n, f j
  have e : S1 + S2 - c₀ * L = (S1 - c₀ * Hm) + c₀ * (Hm - L) + S2 := by ring
  rw [e]
  have h1 : |c₀ * (Hm - L)| ≤ |c₀| * (1 - Real.log η) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hr (abs_nonneg _)
  have h2 : |S2| ≤ H₀ * (1 - Real.log η) := by
    rw [abs_of_nonneg hS2.1]
    refine hS2.2.trans (mul_le_mul_of_nonneg_left ?_ hH0)
    linarith
  have h3 : ε * Hm ≤ ε * L + ε * (1 - Real.log η) := by nlinarith
  calc |S1 - c₀ * Hm + c₀ * (Hm - L) + S2|
      ≤ |S1 - c₀ * Hm| + |c₀ * (Hm - L)| + |S2| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ ε * Hm + |c₀| * (1 - Real.log η) + H₀ * (1 - Real.log η) := by gcongr
    _ ≤ _ := by nlinarith

/-- **Logarithmic averages.** -/
theorem harm_tendsto {h : ℝ → ℝ} {c₀ H₀ : ℝ}
    (h0 : ∀ y, 0 < y → 0 ≤ h y) (hH : ∀ y, 0 < y → h y ≤ H₀)
    (hl : Tendsto h (𝓝[>] 0) (𝓝 c₀)) :
    Tendsto (fun κ : ℝ => (∑ j ∈ Finset.range ⌊1 / κ⌋₊, h (κ * ((j : ℝ) + 1)) / ((j : ℝ) + 1)) /
      Real.log (1 / κ)) (𝓝[>] 0) (𝓝 c₀) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨δ, hδ, hδh⟩ := (Metric.tendsto_nhdsWithin_nhds.1 hl) (ε / 2) hε2
  set η : ℝ := min (δ / 2) (1 / 2) with hηdef
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hηδ : η < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hη : ∀ y, 0 < y → y ≤ η → |h y - c₀| ≤ ε / 2 := by
    intro y hy hyη
    have := hδh (show y ∈ Ioi (0 : ℝ) from hy) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hy]; linarith)
    rw [Real.dist_eq] at this; exact this.le
  set D := (|c₀| + ε / 2 + H₀) * (1 - Real.log η) with hD
  have hlogη : Real.log η < 0 := Real.log_neg hη0 hη1
  have hH0 : 0 ≤ H₀ := (h0 1 one_pos).trans (hH 1 one_pos)
  have hD0 : 0 ≤ D := by rw [hD]; apply mul_nonneg <;> [positivity; linarith]
  set κ₀ := min η (Real.exp (-(4 * D / ε + 1))) with hκ₀
  have hκ₀0 : 0 < κ₀ := lt_min hη0 (Real.exp_pos _)
  filter_upwards [Ioo_mem_nhdsGT hκ₀0] with κ hκ
  obtain ⟨hκ0, hκ1⟩ := hκ
  have hκη : κ < η := lt_of_lt_of_le hκ1 (min_le_left _ _)
  have hκe : κ < Real.exp (-(4 * D / ε + 1)) := lt_of_lt_of_le hκ1 (min_le_right _ _)
  have hL : 4 * D / ε + 1 < Real.log (1 / κ) := by
    rw [one_div, Real.log_inv]
    have := Real.log_lt_log hκ0 hκe
    rw [Real.log_exp] at this; linarith
  have hL0 : 0 < Real.log (1 / κ) := by
    have : 0 ≤ 4 * D / ε := by positivity
    linarith
  have hs := harm_sandwich h0 hH hε2 hη0 hη1 hη hκ0 hκη
  rw [← hD] at hs
  rw [Real.dist_eq]
  have e : (∑ j ∈ Finset.range ⌊1 / κ⌋₊, h (κ * ((j : ℝ) + 1)) / ((j : ℝ) + 1)) /
      Real.log (1 / κ) - c₀ =
      ((∑ j ∈ Finset.range ⌊1 / κ⌋₊, h (κ * ((j : ℝ) + 1)) / ((j : ℝ) + 1)) -
        c₀ * Real.log (1 / κ)) / Real.log (1 / κ) := by
    field_simp
  rw [e, abs_div, abs_of_pos hL0, div_lt_iff₀ hL0]
  have hDL : D < ε / 4 * Real.log (1 / κ) := by
    have h1 : 4 * D / ε < Real.log (1 / κ) := by linarith
    rw [div_lt_iff₀ hε] at h1
    linarith
  linarith

end RamanujanTau.CriticalMeanSquareAsymp
