/-
# Tauberian step 4: Rankin short sums and the bound for `Σ_{n≤N} τ(n)τ(n+h)`

* `rankin_short`: `Σ_{a<n≤b} λ(n)² ≤ c(b−a) + 2C b^{1−ρ}`, `ρ = 2^{−22}`;
* `aabs_le_lam`: `|τ(n)τ(n+h)| ≤ (λ(n)² + λ(n+h)²)/2 · (n+h)^{11}`.
-/
import RamanujanTau.SCSProof.Tauber3
import RamanujanTau.SubconvexityCond.Defs
import RamanujanTau.RankinError.RSUnfoldProof

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open Finset
open RamanujanTau.SubconvexityCond RamanujanTau.RankinError RamanujanTau.EisensteinReal
open scoped Real

/-- `ρ = 2^{−22}`. -/
noncomputable def ρ : ℝ := 1 / 2 ^ 22

lemma ρ_pos : 0 < ρ := by unfold ρ; positivity
lemma ρ_le : ρ ≤ 1 / 8000 := by unfold ρ; norm_num

lemma lam_sq_eq (n : ℕ) : (tau n : ℝ) ^ 2 = lam n ^ 2 * (n : ℝ) ^ 11 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [RamanujanTau.tau_zero]
  rw [lam_sq]
  have : (0 : ℝ) < (n : ℝ) ^ 11 := by positivity
  field_simp

lemma aabs_le_lam (h n : ℕ) :
    aabs h n ≤ (lam n ^ 2 + lam (n + h) ^ 2) / 2 * ((n : ℝ) + h) ^ 11 := by
  refine (aabs_le h n).trans ?_
  rw [lam_sq_eq, lam_sq_eq]
  have h1 : (n : ℝ) ^ 11 ≤ ((n : ℝ) + h) ^ 11 := by
    gcongr; have := Nat.cast_nonneg (α := ℝ) h; linarith
  have h2 : ((n + h : ℕ) : ℝ) ^ 11 = ((n : ℝ) + h) ^ 11 := by push_cast; ring
  rw [h2]
  have := sq_nonneg (lam n)
  nlinarith

/-- The Rankin–Selberg partial sum `S(N) = Σ_{n≤N} λ(n)²`. -/
noncomputable def Slam (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, lam n ^ 2

lemma Slam_eq (N : ℕ) : Slam N = ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 := by
  unfold Slam; simp_rw [lam_sq]

/-- **Rankin short sums.** -/
theorem rankin_short : ∃ c C : ℝ, 0 ≤ c ∧ 0 ≤ C ∧ ∀ a b : ℕ, a ≤ b →
    Slam b - Slam a ≤ c * ((b : ℝ) - a) + 2 * C * (b : ℝ) ^ (1 - ρ) := by
  obtain ⟨C, hC⟩ := rankinSelberg_power_saving_unconditional
  set c := 3 / π * (4 * π) ^ 12 * petNormSq / (Nat.factorial 11 : ℝ)
  have hC0 : 0 ≤ C := by
    have := hC 1 le_rfl
    simp at this
    exact le_trans (abs_nonneg _) (by simpa using this)
  have hρ : (1 - 1 / 2 ^ 22 : ℝ) = 1 - ρ := by unfold ρ; ring
  refine ⟨|c|, C, abs_nonneg _, hC0, fun a b hab => ?_⟩
  rw [hρ] at hC
  have hb : ∀ N : ℕ, |Slam N - c * N| ≤ C * (N : ℝ) ^ (1 - ρ) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [Slam]
      have : (0 : ℝ) ^ (1 - ρ) = 0 := Real.zero_rpow (by have := ρ_le; linarith)
      rw [this]; simp
    · rw [Slam_eq]; exact hC N hN
  have h1 := hb b
  have h2 := hb a
  rw [abs_le] at h1 h2
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hpow : (a : ℝ) ^ (1 - ρ) ≤ (b : ℝ) ^ (1 - ρ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hab' (by have := ρ_le; linarith)
  have hcab : c * ((b : ℝ) - a) ≤ |c| * ((b : ℝ) - a) :=
    mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith)
  nlinarith

lemma sum_Icc_eq_Slam_sub (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Ioc a b, f n = ∑ n ∈ Icc 1 b, f n - ∑ n ∈ Icc 1 a, f n := by
  have : Icc 1 b = Icc 1 a ∪ Ioc a b := by
    ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  rw [this, sum_union (by
    rw [disjoint_left]; intro n h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega)]
  ring

end RamanujanTau.SCSProof
