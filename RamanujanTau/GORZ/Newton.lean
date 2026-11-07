/-
# The Newton forward-difference identity in every degree

`NewtonId d` (from `JensenThreshold.Tail.Box2`, proved there only for `d = 6, 7` by `ring`):
`Σ_j C(d,j) w_j (Z−1)^j = Σ_k C(d,k) Δ^k w(0) (Z−1)^k Z^{d−k}`. Here it is proved for all `d` from the
Gregory–Newton formula of Mathlib (`shift_eq_sum_fwdDiff_iter`, `fwdDiff_iter_eq_sum_shift`).
-/
import RamanujanTau.JensenThreshold.Tail.Box2

set_option autoImplicit false

namespace GORZ

open Finset JensenThreshold JensenThreshold.Tail

/-- the `k`-th forward difference at `0`, as a sum. -/
noncomputable def fd (w : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * w j

lemma fwdDiff_eq_fd (w : ℕ → ℝ) (k : ℕ) : (fwdDiff 1)^[k] w 0 = fd w k := by
  rw [fwdDiff_iter_eq_sum_shift]
  refine sum_congr rfl fun j _ => ?_
  simp [zsmul_eq_mul]

/-- Gregory–Newton: `w j = Σ_{k≤d} C(j,k) Δ^k w(0)` for `j ≤ d`. -/
lemma gregory_newton (w : ℕ → ℝ) {d j : ℕ} (hj : j ≤ d) :
    w j = ∑ k ∈ range (d + 1), (j.choose k : ℝ) * fd w k := by
  have h := shift_eq_sum_fwdDiff_iter (1 : ℕ) w j 0
  simp only [zero_add, smul_eq_mul, mul_one, nsmul_eq_mul] at h
  rw [h, ← Finset.sum_range_add_sum_Ico _ (show j + 1 ≤ d + 1 by omega)]
  have h0 : ∑ k ∈ Ico (j + 1) (d + 1), (j.choose k : ℝ) * fd w k = 0 :=
    sum_eq_zero fun k hk => by
      simp only [mem_Ico] at hk
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  rw [h0, add_zero]
  refine sum_congr rfl fun k _ => ?_
  rw [fwdDiff_eq_fd]

lemma choose_sum (d k : ℕ) (hk : k ≤ d) (Y : ℝ) :
    ∑ j ∈ range (d + 1), (d.choose j : ℝ) * (j.choose k : ℝ) * Y ^ j =
      (d.choose k : ℝ) * Y ^ k * (Y + 1) ^ (d - k) := by
  rw [show d + 1 = k + (d - k + 1) by omega, Finset.sum_range_add]
  have h0 : ∑ j ∈ range k, (d.choose j : ℝ) * (j.choose k : ℝ) * Y ^ j = 0 :=
    sum_eq_zero fun j hj => by
      simp only [mem_range] at hj
      rw [Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, mul_zero, zero_mul]
  rw [h0, zero_add, add_pow, Finset.mul_sum]
  refine sum_congr rfl fun m hm => ?_
  simp only [mem_range] at hm
  have hc := Nat.choose_mul (n := d) (k := k + m) (s := k) (by omega)
  rw [show k + m - k = m by omega] at hc
  have hc' : (d.choose (k + m) : ℝ) * ((k + m).choose k : ℝ) = (d.choose k : ℝ) * ((d - k).choose m : ℝ) := by
    exact_mod_cast hc
  rw [one_pow, mul_one, hc', pow_add]
  ring

/-- **The Newton identity in every degree.** -/
theorem newtonId (d : ℕ) : NewtonId d := by
  intro w Z
  set Y := Z - 1
  have hZ : Z = Y + 1 := by simp [Y]
  have e1 : ∀ j ∈ range (d + 1), (d.choose j : ℝ) * w j * Y ^ j =
      ∑ k ∈ range (d + 1), fd w k * ((d.choose j : ℝ) * (j.choose k : ℝ) * Y ^ j) := by
    intro j hj
    rw [gregory_newton w (show j ≤ d by simp at hj; omega), Finset.mul_sum, Finset.sum_mul]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [sum_congr rfl e1, Finset.sum_comm]
  refine sum_congr rfl fun k hk => ?_
  rw [← Finset.mul_sum, choose_sum d k (by simp at hk; omega), ← hZ]
  simp only [fd]
  ring

end GORZ
