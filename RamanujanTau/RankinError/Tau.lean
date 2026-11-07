/-
# The Rankin–Selberg error term for `τ`, conditional on the Rankin–Selberg data

`rankinSelberg_power_saving_of_RSData`: if `RSData aτ ‖Δ‖²` holds for `aτ(n) = τ(n)²/n¹¹`
(the continuation, functional equation and unfolding identity of the Rankin–Selberg
`L`-function), then

    |∑_{n≤N} τ(n)²/n¹¹ − (3/π)(4π)¹² ‖Δ‖²/11! · N| ≤ C N^{1 − 2^{−22}}.
-/
import RamanujanTau.RankinError.Landau3
import RamanujanTau.EisensteinReal.HoroIdent

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Real Finset
open RamanujanTau.RankinSelberg RamanujanTau.EisensteinReal

/-- `aτ(n) = τ(n)²/n¹¹`. -/
noncomputable def aTau (n : ℕ) : ℝ := ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11

lemma aTau_nonneg (n : ℕ) : 0 ≤ aTau n := by unfold aTau; positivity

lemma aTau_zero : aTau 0 = 0 := by simp [aTau]

lemma exists_aTau_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, aTau n ≤ K * n := by
  obtain ⟨K, hK0, hK⟩ := exists_sum_tau_sq_le
  refine ⟨K, hK0, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [aTau]
  · have h1 : ((tau n : ℝ)) ^ 2 ≤ K * (n : ℝ) ^ 12 := by
      refine le_trans ?_ (hK n)
      exact single_le_sum (f := fun m => ((tau m : ℝ)) ^ 2) (fun _ _ => sq_nonneg _)
        (mem_Icc.2 ⟨h, le_rfl⟩)
    have hn : (0:ℝ) < (n : ℝ) ^ 11 := by positivity
    unfold aTau
    rw [div_le_iff₀ hn]
    calc ((tau n : ℝ)) ^ 2 ≤ K * (n : ℝ) ^ 12 := h1
      _ = K * n * (n : ℝ) ^ 11 := by ring

lemma summable_aTau : Summable fun n : ℕ => aTau n * (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := exists_aTau_le
  have hs : Summable fun n : ℕ => K * (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    (Real.summable_nat_rpow.2 (by norm_num)).mul_left K
  refine hs.of_nonneg_of_le (fun n => mul_nonneg (aTau_nonneg n) (by positivity)) (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [aTau]
  · have hn : (0:ℝ) < n := by exact_mod_cast h
    calc aTau n * (n : ℝ) ^ (-(5 / 2 : ℝ)) ≤ K * n * (n : ℝ) ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (hK n) (by positivity)
      _ = K * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
          rw [mul_assoc]; congr 1
          rw [show -(3 / 2 : ℝ) = 1 + -(5 / 2) by norm_num, Real.rpow_add hn, Real.rpow_one]

lemma petNormSq_pos : 0 < petNormSq := by
  have := horocycleLimit_pos horocycleLimit_zagier
  have hπ := Real.pi_pos
  by_contra h
  push Not at h
  have : 3 / π * petNormSq ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
  linarith

/-- **Rankin–Selberg with a power-saving error term**, conditional on `RSData`. -/
theorem rankinSelberg_power_saving_of_RSData (d : RSData aTau petNormSq) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - 1 / 2 ^ 22 : ℝ) := by
  obtain ⟨C, hC⟩ := power_saving_of_RSData aTau aTau_nonneg aTau_zero petNormSq_pos.le d
    summable_aTau
  refine ⟨C, fun N hN => ?_⟩
  have h := hC N hN
  have e : petNormSq * rsConst = 3 / π * (4 * π) ^ 12 * petNormSq / (Nat.factorial 11 : ℝ) := by
    unfold rsConst
    have hπ := Real.pi_pos
    field_simp
  rw [e] at h
  exact h

end RamanujanTau.RankinError
