/-
# The exponent `δ = 1/84`

Same chain as `power_saving_of_RSData`, with the 20 halvings of `riesz_descend` replaced by
one 20-th order difference (`riesz_kdiff`): saving `(1/4)/21 = 1/84`.

**`rankinSelberg_power_saving_84`** (unconditional):
`|∑_{n≤N} τ(n)²/n¹¹ − (3/π)(4π)¹²‖Δ‖²/11! · N| ≤ C N^{1 − 1/84}`.
-/
import RamanujanTau.RankinError.RSUnfoldProof
import RamanujanTau.RankinError.RieszK

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Real
open RamanujanTau.RankinSelberg RamanujanTau.EisensteinReal

/-- Power saving `1/84` from the Rankin–Selberg data. -/
theorem power_saving_84_of_RSData (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0) {κ : ℝ}
    (hκ : 0 ≤ κ) (d : RSData a κ) (hsum : Summable fun n : ℕ => a n * (n : ℝ) ^ (-(5 / 2 : ℝ))) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, a n - κ * rsConst * N| ≤ C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) := by
  have hLS : LSeriesSummable (fun n => (a n : ℂ)) ((5 / 2 : ℝ) : ℂ) := by
    unfold LSeriesSummable
    refine Summable.of_norm ?_
    refine hsum.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [ha0]
    · rw [if_neg h.ne', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n),
        Real.rpow_neg (Nat.cast_nonneg n)]
      simp [div_eq_mul_inv]
  obtain ⟨B, hB⟩ := Ffun_bound d hLS
  have hR := rieszAsymp_of_continuation a ha ha0 (K := 19) (c := 5 / 2) (σ₀ := 1 / 2)
    (σ₁ := 3 / 4) (c₀ := κ * rsConst) (B := B) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hsum (Ffun d) (differentiableOn_Ffun d)
    (fun s hs => LSeries_eq_Ffun d (by rw [hs]; norm_num)) hB
  have hc0 : 0 ≤ κ * rsConst := mul_nonneg hκ (by unfold rsConst; positivity)
  have hD := riesz_kdiff a ha hc0 20 (θ := 1 - 3 / 4) (by norm_num) (by norm_num) hR
  obtain ⟨C, hC⟩ := partial_sum_of_riesz0 a hD
  refine ⟨C, fun N hN => ?_⟩
  have := hC N hN
  convert this using 3
  norm_num

/-- **Rankin–Selberg with error `O(N^{1−1/84})`, unconditionally.** -/
theorem rankinSelberg_power_saving_84 :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) := by
  obtain ⟨C, hC⟩ := power_saving_84_of_RSData aTau aTau_nonneg aTau_zero petNormSq_pos.le
    (rsData_of_unfold rsUnfold) summable_aTau
  refine ⟨C, fun N hN => ?_⟩
  have h := hC N hN
  have e : petNormSq * rsConst = 3 / π * (4 * π) ^ 12 * petNormSq / (Nat.factorial 11 : ℝ) := by
    unfold rsConst
    have hπ := Real.pi_pos
    field_simp
  rw [e] at h
  exact h

end RamanujanTau.RankinError

#print axioms RamanujanTau.RankinError.riesz_kdiff
#print axioms RamanujanTau.RankinError.rankinSelberg_power_saving_unconditional
#print axioms RamanujanTau.RankinError.rankinSelberg_power_saving_84
