import RamanujanTau.StepanovAS.Main
import RamanujanTau.RankinSelberg.Main

/-! # Weil + Rankin–Selberg ⇒ `#{n ≤ N : τ(n) ≠ 0} ≫_ε N^{1/2−ε}`

* `tau_pointwise_weil`: `|τ(n)| ≤ C_ε n^{23/4+ε}` for all `n ≥ 1` (from the unconditional
  `StepanovAS.tau_isBigO_23_4_unconditional`, plus a finite-range constant).
* `tau_sq_div_le`: `τ(n)²/n¹¹ ≤ C_ε² n^{1/2+2ε}`.
* `card_tau_ne_zero_ge_rpow`: `∀ ε > 0, ∃ c > 0, ∀ N ≥ 1, c·N^{1/2−ε} ≤ #{n ∈ [1,N] : τ(n) ≠ 0}`,
  from `c₁ N ≤ ∑_{n ≤ N} τ(n)²/n¹¹` (`RankinSelberg.rankinSelberg_two_sided`).
-/

set_option autoImplicit false

namespace RamanujanTau.TauDensity
open RamanujanTau Finset Filter Asymptotics

/-- **Weil's bound, pointwise form:** `|τ(n)| ≤ C n^{23/4+ε}` for every `n ≥ 1`. -/
theorem tau_pointwise_weil (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → |(τ n : ℝ)| ≤ C * (n : ℝ) ^ ((23 / 4 : ℝ) + ε) := by
  obtain ⟨C, hC⟩ := (StepanovAS.tau_isBigO_23_4_unconditional ε hε).bound
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp hC
  set S : ℝ := ∑ m ∈ range n0, |(τ m : ℝ)|
  have hS : 0 ≤ S := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨max C 0 + S + 1, by positivity, fun n hn => ?_⟩
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ ((23 / 4 : ℝ) + ε) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by positivity)
  have hmax : C ≤ max C 0 := le_max_left _ _
  have hmax0 : 0 ≤ max C 0 := le_max_right _ _
  by_cases h : n0 ≤ n
  · have h1 := hn0 n h
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)] at h1
    nlinarith
  · have h1 : |(τ n : ℝ)| ≤ S :=
      single_le_sum (f := fun m => |(τ m : ℝ)|) (fun _ _ => abs_nonneg _)
        (mem_range.mpr (by omega))
    nlinarith

/-- `τ(n)²/n¹¹ ≤ C² n^{1/2+2ε}` from the pointwise bound. -/
theorem tau_sq_div_le {ε C : ℝ} (hC : ∀ n : ℕ, 1 ≤ n → |(τ n : ℝ)| ≤ C * (n : ℝ) ^ ((23 / 4 : ℝ) + ε))
    {n : ℕ} (hn : 1 ≤ n) :
    ((τ n : ℝ)) ^ 2 / (n : ℝ) ^ 11 ≤ C ^ 2 * (n : ℝ) ^ ((1 / 2 : ℝ) + 2 * ε) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ((τ n : ℝ)) ^ 2 ≤ (C * (n : ℝ) ^ ((23 / 4 : ℝ) + ε)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC n hn) 2
  have h2 : (C * (n : ℝ) ^ ((23 / 4 : ℝ) + ε)) ^ 2 =
      C ^ 2 * (n : ℝ) ^ ((1 / 2 : ℝ) + 2 * ε) * (n : ℝ) ^ 11 := by
    rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ _), ← Real.rpow_mul hn0.le, mul_assoc,
      ← Real.rpow_natCast (n : ℝ) 11, ← Real.rpow_add hn0]
    norm_num; left; ring_nf
  rw [div_le_iff₀ (by positivity), ← h2]
  exact h1

/-- **Analytic headline (Weil + Rankin–Selberg).** For every `ε > 0` there is `c > 0` with
`c·N^{1/2−ε} ≤ #{n ∈ [1,N] : τ(n) ≠ 0}` for all `N ≥ 1`. -/
theorem card_tau_ne_zero_ge_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
      c * (N : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤ (((Icc 1 N).filter (fun n => τ n ≠ 0)).card : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := tau_pointwise_weil (ε / 2) (by positivity)
  obtain ⟨c₁, c₂, hc₁, hc₂, hRS⟩ := RankinSelberg.rankinSelberg_two_sided
  refine ⟨c₁ / C ^ 2, by positivity, fun N hN => ?_⟩
  set S := (Icc 1 N).filter (fun n => τ n ≠ 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set b : ℝ := (1 / 2 : ℝ) + 2 * (ε / 2)
  have hNb : (0 : ℝ) < (N : ℝ) ^ b := Real.rpow_pos_of_pos hN0 _
  -- the sum only sees `S`
  have hsum : ∑ n ∈ Icc 1 N, ((τ n : ℝ)) ^ 2 / (n : ℝ) ^ 11 =
      ∑ n ∈ S, ((τ n : ℝ)) ^ 2 / (n : ℝ) ^ 11 := by
    rw [sum_filter_of_ne]
    intro n _ hne h0
    exact hne (by rw [h0]; simp)
  have hbound : ∑ n ∈ S, ((τ n : ℝ)) ^ 2 / (n : ℝ) ^ 11 ≤ S.card * (C ^ 2 * (N : ℝ) ^ b) := by
    rw [← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun n hn => ?_
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp (mem_filter.mp hn).1
    refine (tau_sq_div_le hC hn1).trans ?_
    gcongr
  have hmain : c₁ * N ≤ S.card * (C ^ 2 * (N : ℝ) ^ b) := ((hRS N hN).1.trans hsum.le).trans hbound
  have hsplit : (N : ℝ) = (N : ℝ) ^ ((1 / 2 : ℝ) - ε) * (N : ℝ) ^ b := by
    rw [← Real.rpow_add hN0]; simp only [b]; ring_nf; exact (Real.rpow_one _).symm
  have hmain' : c₁ * ((N : ℝ) ^ ((1 / 2 : ℝ) - ε) * (N : ℝ) ^ b) ≤ S.card * (C ^ 2 * (N : ℝ) ^ b) := by
    rw [← hsplit]; exact hmain
  have : c₁ * (N : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤ S.card * C ^ 2 := by
    by_contra hlt
    push Not at hlt
    have := mul_lt_mul_of_pos_right hlt hNb
    nlinarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  exact this

end RamanujanTau.TauDensity

#print axioms RamanujanTau.TauDensity.tau_pointwise_weil
#print axioms RamanujanTau.TauDensity.tau_sq_div_le
#print axioms RamanujanTau.TauDensity.card_tau_ne_zero_ge_rpow
